"""
This file is part of nucypher.

nucypher is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

nucypher is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with nucypher.  If not, see <https://www.gnu.org/licenses/>.
"""


import datetime
from collections import OrderedDict
from queue import Queue, Empty
from typing import Callable, Tuple
from typing import Generator, Set, Optional

import math
import maya
import random
import time
from abc import ABC, abstractmethod
from bytestring_splitter import BytestringSplitter, VariableLengthBytestring
from constant_sorrow.constants import NOT_SIGNED, UNKNOWN_KFRAG
from twisted._threads import AlreadyQuit
from twisted.internet import reactor
from twisted.internet.defer import ensureDeferred, Deferred
from twisted.python.threadpool import ThreadPool
from umbral.keys import UmbralPublicKey
from umbral.kfrags import KFrag

from nucypher.blockchain.eth.actors import BlockchainPolicyAuthor
from nucypher.blockchain.eth.agents import PolicyManagerAgent, StakersReservoir
from nucypher.characters.lawful import Alice, Ursula
from nucypher.crypto.api import keccak_digest, secure_random
from nucypher.crypto.constants import HRAC_LENGTH, PUBLIC_KEY_LENGTH
from nucypher.crypto.kits import RevocationKit
from nucypher.crypto.powers import DecryptingPower, SigningPower, TransactingPower
from nucypher.crypto.utils import construct_policy_id
from nucypher.network.exceptions import NodeSeemsToBeDown
from nucypher.network.middleware import RestMiddleware
from nucypher.utilities.concurrency import WorkerPool, AllAtOnceFactory
from nucypher.utilities.logging import Logger


class Arrangement:
    """
    A Policy must be implemented by arrangements with n Ursulas.  This class tracks the status of that implementation.
    """
    ID_LENGTH = 32

    splitter = BytestringSplitter((UmbralPublicKey, PUBLIC_KEY_LENGTH),  # alice.stamp
                                  (bytes, ID_LENGTH),  # arrangement_ID
                                  (bytes, VariableLengthBytestring))  # expiration

    @classmethod
    def from_alice(cls, alice: Alice, expiration: maya.MayaDT):
        arrangement_id = secure_random(cls.ID_LENGTH)
        alice_verifying_key = alice.stamp
        return cls(alice_verifying_key, expiration, arrangement_id)

    def __init__(self,
                 alice_verifying_key,
                 expiration: maya.MayaDT,
                 arrangement_id: bytes,
                 ) -> None:
        """
        :param expiration: The moment which Alice wants the Arrangement to end.

        Other params are hopefully self-evident.
        """
        # TODO: do we really need different IDs for each arrangement in the policy?
        if len(arrangement_id) != self.ID_LENGTH:
            raise ValueError(f"Arrangement ID must be of length {self.ID_LENGTH}.")
        self.id = arrangement_id
        self.expiration = expiration
        self.alice_verifying_key = alice_verifying_key

    def __bytes__(self):
        return bytes(self.alice_verifying_key) + self.id + bytes(VariableLengthBytestring(self.expiration.iso8601().encode()))

    @classmethod
    def from_bytes(cls, arrangement_as_bytes):
        alice_verifying_key, arrangement_id, expiration_bytes = cls.splitter(arrangement_as_bytes)
        expiration = maya.MayaDT.from_iso8601(iso8601_string=expiration_bytes.decode())
        return cls(alice_verifying_key=alice_verifying_key, arrangement_id=arrangement_id, expiration=expiration)

    def __repr__(self):
        return f"Arrangement(client_key={self.alice_verifying_key})"


class NodeEngagementMutex:

    log = Logger('NodeEngagementMutex')

    def __init__(self,
                 worker, # TODO: typing.Protocol
                 nodes,
                 percent_to_complete_before_release=5,
                 threadpool_size=120,
                 timeout=20):

        self._total = len(nodes)
        self._block_until_this_many_are_complete = math.ceil(len(nodes) * percent_to_complete_before_release / 100)
        self._worker_pool = WorkerPool(worker=worker,
                                       value_factory=AllAtOnceFactory(nodes),
                                       target_successes=self._block_until_this_many_are_complete,
                                       timeout=timeout,
                                       stagger_timeout=0,
                                       threadpool_size=threadpool_size)

        self.log.info(f"NEM spinning up {self._worker_pool}")

    @property
    def completed(self):
        # TODO: lock dict before copying?
        return dict(self._worker_pool.successes)

    def start(self):
        self.log.info(f"NEM starting {self._worker_pool}")
        self._worker_pool.start()
        if reactor.running:
            reactor.callInThread(self.block_until_complete)

    def block_until_success_is_reasonably_likely(self):
        """
        https://www.youtube.com/watch?v=OkSLswPSq2o
        """
        self._worker_pool.block_until_target_successes()
        completed = self.completed
        self.log.debug(f"{len(completed)} nodes were contacted while blocking for a little while.")
        # TODO: len(successes) can be actually < than _block_until_this_many_are_complete
        # if there were too few successes in total. Raise an exception in this case?
        # Here or in WorkerPool?
        return completed

    def block_until_complete(self):
        self._worker_pool.join()


class LazyReservoir:

    def __init__(self, values, make_reservoir):
        self.values = list(values)
        self.make_reservoir = make_reservoir
        self.reservoir = None

    def __call__(self):
        if self.values:
            return self.values.pop(0)

        if self.reservoir is None:
            if self.make_reservoir is not None:
                self.reservoir = self.make_reservoir()
                self.make_reservoir = None
            else:
                return None

        if len(self.reservoir) > 0:
            return self.reservoir.draw(1)[0]
        else:
            return None


class PrefetchStrategy:

    def __init__(self, reservoir, need_successes):
        self.reservoir = reservoir
        self.need_successes = need_successes

    def __call__(self, successes):
        batch = []
        for i in range(self.need_successes - successes):
            value = self.reservoir()
            if value is None:
                break
            batch.append(value)
        return batch


class Policy(ABC):
    """
    An edict by Alice, arranged with n Ursulas, to perform re-encryption for a specific Bob
    for a specific path.

    Once Alice is ready to enact a Policy, she generates KFrags, which become part of the Policy.

    Each Ursula is offered a Arrangement (see above) for a given Policy by Alice.

    Once Alice has secured agreement with n Ursulas to enact a Policy, she sends each a KFrag,
    and generates a TreasureMap for the Policy, recording which Ursulas got a KFrag.
    """

    POLICY_ID_LENGTH = 16

    log = Logger("Policy")

    class NotEnoughUrsulas(Exception):
        """
        Raised when a Policy has been used to generate Arrangements with Ursulas insufficient number
        such that we don't have enough KFrags to give to each Ursula.
        """

    class EnactmentError(Exception):
        """
        Raise if one or more Ursulas failed to enact the policy.
        """

    def __init__(self,
                 alice: Alice,
                 label: bytes,
                 expiration: maya.MayaDT,
                 bob: 'Bob' = None,
                 kfrags: Tuple[KFrag, ...] = (UNKNOWN_KFRAG,),
                 public_key=None,
                 m: int = None,
                 ) -> None:

        """
        :param kfrags:  A list of KFrags to distribute per this Policy.
        :param label: The identity of the resource to which Bob is granted access.
        """
        self.m = m
        self.alice = alice
        self.label = label
        self.bob = bob
        self.kfrags = kfrags
        self.public_key = public_key
        self._id = construct_policy_id(self.label, bytes(self.bob.stamp))
        self.expiration = expiration

    @property
    def n(self) -> int:
        return len(self.kfrags)

    @property
    def id(self) -> bytes:
        return self._id

    def __repr__(self):
        return f"{self.__class__.__name__}:{self.id.hex()[:6]}"

    def hrac(self) -> bytes:
        """
        # TODO: #180 - This function is hanging on for dear life.  After 180 is closed, it can be completely deprecated.

        The "hashed resource authentication code".

        A hash of:
        * Alice's public key
        * Bob's public key
        * the label

        Alice and Bob have all the information they need to construct this.
        Ursula does not, so we share it with her.
        """
        return keccak_digest(bytes(self.alice.stamp) + bytes(self.bob.stamp) + self.label)[:HRAC_LENGTH]

    def make_treasure_map(self,
                          network_middleware: RestMiddleware,
                          arrangements,
                          blockchain_signer: Callable = None,
                          ) -> NodeEngagementMutex:

        treasure_map = self._treasure_map_class(m=self.m)

        for ursula, arrangement in arrangements.items():
            # TODO: Handle problem here - if the arrangement is bad, deal with it.
            treasure_map.add_arrangement(ursula, arrangement)

        treasure_map.prepare_for_publication(bob_encrypting_key=self.bob.public_keys(DecryptingPower),
                                             bob_verifying_key=self.bob.public_keys(SigningPower),
                                             alice_stamp=self.alice.stamp,
                                             label=self.label)

        if blockchain_signer is not None:
            treasure_map.include_blockchain_signature(blockchain_signer)

        return treasure_map

    def make_publishing_mutex(self,
                              treasure_map,
                              network_middleware: RestMiddleware,
                              ) -> NodeEngagementMutex:

        self.alice.block_until_number_of_known_nodes_is(8, timeout=2, learn_on_this_thread=True)
        target_nodes = self.bob.matching_nodes_among(self.alice.known_nodes)
        treasure_map_bytes = bytes(treasure_map) # prevent the closure from holding the reference

        def put_treasure_map_on_node(_cancel, node):
            try:
                response = network_middleware.put_treasure_map_on_node(node=node,
                                                                       map_payload=treasure_map_bytes)
            except Exception as e:
                self.log.warn(f"{node} failed: {e}")
                raise

            if response.status_code == 201:
                return response
            else:
                message = f"{node} failed with response status: {response.status}"
                self.log.warn(message)
                # TODO: What happens if this is a 300 or 400 level response?
                raise Exception(message)

        return NodeEngagementMutex(worker=put_treasure_map_on_node,
                                   nodes=target_nodes)

    def enact(self,
              network_middleware: RestMiddleware,
              handpicked_ursulas: Optional[Set[Ursula]] = None,
              discover_on_this_thread: bool = True,
              publish_treasure_map=True,
              ) -> 'EnactedPolicy':

        arrangements = self.make_arrangements(network_middleware=network_middleware,
                                              handpicked_ursulas=handpicked_ursulas,
                                              discover_on_this_thread=discover_on_this_thread)

        self.enact_arrangements(network_middleware=network_middleware,
                                arrangements=arrangements,
                                publish_treasure_map=publish_treasure_map,
                                make_enactment_payload=lambda kfrag: bytes(kfrag))

        treasure_map = self.make_treasure_map(network_middleware=network_middleware,
                                              arrangements=arrangements,
                                              blockchain_signer=self._blockchain_signer())
        publishing_mutex = self.make_publishing_mutex(treasure_map=treasure_map,
                                                      network_middleware=network_middleware)
        revocation_kit = RevocationKit(treasure_map, self.alice.stamp)

        enacted_policy = EnactedPolicy(self._id, self.hrac(), self.label, self.public_key, treasure_map, publishing_mutex, revocation_kit)

        self.alice.add_active_policy(enacted_policy)

        if publish_treasure_map is True:
            enacted_policy.publish_treasure_map()

        return enacted_policy

    def enact_arrangements(self,
                           network_middleware,
                           arrangements,
                           make_enactment_payload,
                           publish_treasure_map=True) -> dict:
        """
        Assign kfrags to ursulas_on_network, and distribute them via REST.
        """
        statuses = {}
        for ursula, kfrag in zip(arrangements, self.kfrags):
            arrangement = arrangements[ursula]

            # TODO: seems like it would be enough to just encrypt this with Ursula's public key,
            # and not create a whole capsule.
            # Can't change for now since it's node protocol.
            message_kit, _signature = self.alice.encrypt_for(ursula, make_enactment_payload(kfrag))

            try:
                # TODO: Concurrency
                response = network_middleware.enact_policy(ursula,
                                                           arrangement.id,
                                                           message_kit.to_bytes())
            except network_middleware.UnexpectedResponse as e:
                status = e.status
            else:
                status = response.status_code

            statuses[ursula.checksum_address] = status

        # TODO: Enable re-tries?

        if not all(status == 200 for status in statuses.values()):
            report = "\n".join(f"{address}: {status}" for address, status in statuses.items())
            self.log.debug(f"Policy enactment failed. Request statuses:\n{report}")

            # OK, let's check: if two or more Ursulas claimed we didn't pay,
            # we need to re-evaulate our situation here.
            number_of_claims_of_freeloading = sum(status == 402 for status in statuses.values())

            if number_of_claims_of_freeloading > 2:
                raise self.alice.NotEnoughNodes

            # otherwise just raise a more generic error
            raise Policy.EnactmentError()

    def _propose_arrangement(self, ursula, network_middleware: RestMiddleware, arrangement):
        self.log.debug(f"Proposing arrangement {arrangement} to {ursula}")
        negotiation_response = network_middleware.propose_arrangement(ursula, arrangement)
        status = negotiation_response.status_code

        if status == 200:
            self.log.debug(f"Arrangement accepted by {ursula}")
        else:
            message = f"Proposing arrangement to {ursula} failed with {status}"
            self.log.debug(message)
            raise RuntimeError(message)

    def _try_propose_arrangement(self, sleep, address,
            network_middleware: RestMiddleware,
            arrangement,
            discover_on_this_thread: bool = False,
            learner_timeout = 1, # TODO: remove hardcoding
        ):

        self.log.debug(f"Trying to learn about {address}")

        while True:
            self.alice.block_until_specific_nodes_are_known([address],
                                                            learn_on_this_thread=discover_on_this_thread,
                                                            allow_missing=1,
                                                            timeout=learner_timeout)
            if address in self.alice.known_nodes:
                break

            sleep(0) # checkpoint for canceling

        ursula = self.alice.known_nodes[address]
        self._propose_arrangement(ursula, network_middleware, arrangement)

        return (ursula, arrangement)

    def make_arrangements(self,
                              network_middleware: RestMiddleware,
                              handpicked_ursulas: Optional[Set[Ursula]] = None,
                              discover_on_this_thread: bool = True,
                              ) -> None:
        timeout = 10
        draw_timeout = 1

        accepted_arrangements = {}

        if handpicked_ursulas is None:
            handpicked_ursulas = set()
        handpicked_addresses = [ursula.checksum_address for ursula in handpicked_ursulas]

        # TODO: is there a better way to determine that?
        if isinstance(self, BlockchainPolicy):
            make_reservoir = lambda: self.alice.get_stakers_reservoir(duration=self.duration_periods,
                                                                      without=handpicked_addresses)
        else:
            addresses = {
                ursula.checksum_address: 1 for ursula in self.alice.known_nodes
                if ursula.checksum_address not in handpicked_addresses}
            # Or support an empty dict in StakersReservoir?
            if len(addresses) > 0:
                make_reservoir = lambda: StakersReservoir(addresses)
            else:
                make_reservoir = None

        lazy_reservoir = LazyReservoir(handpicked_addresses, make_reservoir)
        value_factory = PrefetchStrategy(lazy_reservoir, self.n)

        def worker(sleep, address):
            arrangement = Arrangement.from_alice(alice=self.alice, expiration=self.expiration)
            return self._try_propose_arrangement(
                sleep, address, network_middleware, arrangement, discover_on_this_thread, draw_timeout)

        worker_pool = WorkerPool(worker, value_factory, self.n, timeout, draw_timeout, threadpool_size=self.n)
        worker_pool.start()
        worker_pool.block_until_target_successes()
        worker_pool.cancel()
        worker_pool.join()
        arrangements = {key: val for key, val in list(worker_pool.successes.items())[:self.n]}
        failures = worker_pool.failures

        #arrangements, failures = run_workers_sync(worker, value_factory, self.n, timeout, draw_timeout)

        for ursula, arrangement in arrangements.values():
            accepted_arrangements[ursula] = arrangement

        accepted_addresses = ", ".join(ursula.checksum_address for ursula in accepted_arrangements)

        if len(arrangements) < self.n:

            rejected_proposals = "\n".join(f"{address}: {exception}" for address, exception in failures.items())

            self.log.debug(
                "Could not find enough Ursulas to accept proposals.\n"
                "Accepted: {accepted_addresses}\n"
                "Rejected:\n{rejected_proposals}")
            raise self._not_enough_ursulas_exception()
        else:
            self.log.debug("Finished proposing arrangements; accepted: {accepted_addresses}")

        return accepted_arrangements

    @abstractmethod
    def _blockchain_signer(self):
        raise NotImplementedError

    @abstractmethod
    def _not_enough_ursulas_exception(self):
        raise NotImplementedError


class FederatedPolicy(Policy):

    from nucypher.policy.collections import TreasureMap as _treasure_map_class  # TODO: Circular Import

    def _blockchain_signer(self):
        return None

    def _not_enough_ursulas_exception(self):
        return Policy.NotEnoughUrsulas


class BlockchainPolicy(Policy):
    """
    A collection of n Arrangements representing a single Policy
    """

    from nucypher.policy.collections import SignedTreasureMap as _treasure_map_class  # TODO: Circular Import

    class InvalidPolicyValue(ValueError):
        pass

    class NotEnoughBlockchainUrsulas(Policy.NotEnoughUrsulas):
        pass

    def __init__(self,
                 alice: Alice,
                 value: int,
                 rate: int,
                 duration_periods: int,
                 expiration: maya.MayaDT,
                 *args, **kwargs):

        super().__init__(alice=alice, expiration=expiration, *args, **kwargs)

        self.duration_periods = duration_periods
        self.value = value
        self.rate = rate

        self.validate_fee_value()

    def _not_enough_ursulas_exception(self):
        return BlockchainPolicy.NotEnoughBlockchainUrsulas

    def validate_fee_value(self) -> None:
        rate_per_period = self.value // self.n // self.duration_periods  # wei
        recalculated_value = self.duration_periods * rate_per_period * self.n
        if recalculated_value != self.value:
            raise ValueError(f"Invalid policy value calculation - "
                             f"{self.value} can't be divided into {self.n} staker payments per period "
                             f"for {self.duration_periods} periods without a remainder")

    @staticmethod
    def generate_policy_parameters(n: int,
                                   duration_periods: int,
                                   value: int = None,
                                   rate: int = None) -> dict:

        # Check for negative inputs
        if sum(True for i in (n, duration_periods, value, rate) if i is not None and i < 0) > 0:
            raise BlockchainPolicy.InvalidPolicyValue(f"Negative policy parameters are not allowed. Be positive.")

        # Check for policy params
        if not bool(value) ^ bool(rate):
            # TODO: Review this suggestion
            raise BlockchainPolicy.InvalidPolicyValue(f"Either 'value' or 'rate'  must be provided for policy.")

        if not value:
            value = rate * duration_periods * n

        else:
            value_per_node = value // n
            if value_per_node * n != value:
                raise BlockchainPolicy.InvalidPolicyValue(f"Policy value of ({value} wei) cannot be"
                                                          f" divided by N ({n}) without a remainder.")

            rate = value_per_node // duration_periods
            if rate * duration_periods != value_per_node:
                raise BlockchainPolicy.InvalidPolicyValue(f"Policy value of ({value_per_node} wei) per node "
                                                          f"cannot be divided by duration ({duration_periods} periods)"
                                                          f" without a remainder.")

        params = dict(rate=rate, value=value)
        return params

    def publish_to_blockchain(self, ursulas) -> dict:

        addresses = [ursula.checksum_address for ursula in ursulas]

        # Transact  # TODO: Move this logic to BlockchainPolicyActor
        receipt = self.alice.policy_agent.create_policy(
            policy_id=self.hrac(),  # bytes16 _policyID
            author_address=self.alice.checksum_address,
            value=self.value,
            end_timestamp=self.expiration.epoch,  # uint16 _numberOfPeriods
            node_addresses=addresses  # address[] memory _nodes
        )

        # Capture Response
        return receipt['transactionHash']

    def _blockchain_signer(self):
        transacting_power = self.alice._crypto_power.power_ups(TransactingPower)
        return transacting_power.sign_message

    def enact_arrangements(self,
                           network_middleware,
                           arrangements,
                           make_enactment_payload,
                           publish_treasure_map=True) -> NodeEngagementMutex:
        transaction = self.publish_to_blockchain(list(arrangements))
        return super().enact_arrangements(network_middleware=network_middleware,
                                          arrangements=arrangements,
                                          publish_treasure_map=publish_treasure_map,
                                          make_enactment_payload=lambda kfrag: bytes(transaction) + make_enactment_payload(kfrag))


class EnactedPolicy:

    def __init__(self, id, hrac, label, public_key, treasure_map, publishing_mutex, revocation_kit):
        self.id = id # TODO: is it even used anywhere?
        self.hrac = hrac
        self.label = label
        self.public_key = public_key
        self.treasure_map = treasure_map
        self.publishing_mutex = publishing_mutex
        self.revocation_kit = revocation_kit
        self.n = len(self.treasure_map.destinations)

    def publish_treasure_map(self):
        self.publishing_mutex.start()
