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
import trio
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
from nucypher.utilities.logging import Logger


class Arrangement:
    """
    A Policy must be implemented by arrangements with n Ursulas.  This class tracks the status of that implementation.
    """
    federated = True
    ID_LENGTH = 32

    splitter = BytestringSplitter((UmbralPublicKey, PUBLIC_KEY_LENGTH),  # alice.stamp
                                  (bytes, ID_LENGTH),  # arrangement_ID
                                  (bytes, VariableLengthBytestring))  # expiration

    def __init__(self,
                 alice: Alice,
                 expiration: maya.MayaDT,
                 arrangement_id: bytes = None,
                 ) -> None:
        """
        :param expiration: The moment which Alice wants the Arrangement to end.

        Other params are hopefully self-evident.
        """
        # TODO: do we really need different IDs for each arrangement in the policy?
        if arrangement_id:
            if len(arrangement_id) != self.ID_LENGTH:
                raise ValueError(f"Arrangement ID must be of length {self.ID_LENGTH}.")
            self.id = arrangement_id
        else:
            self.id = secure_random(self.ID_LENGTH)
        self.expiration = expiration
        self.alice = alice

    def __bytes__(self):
        return bytes(self.alice.stamp) + self.id + bytes(VariableLengthBytestring(self.expiration.iso8601().encode()))

    @classmethod
    def from_bytes(cls, arrangement_as_bytes):
        alice_verifying_key, arrangement_id, expiration_bytes = cls.splitter(arrangement_as_bytes)
        expiration = maya.MayaDT.from_iso8601(iso8601_string=expiration_bytes.decode())
        alice = Alice.from_public_keys(verifying_key=alice_verifying_key)
        return cls(alice=alice, arrangement_id=arrangement_id, expiration=expiration)

    def revoke(self) -> str:
        """Revoke this arrangement and return the transaction hash as hex."""
        txhash = self.alice.policy_agent.revoke_policy(self.id, author_address=self.alice.checksum_address)
        return txhash

    def __repr__(self):
        class_name = self.__class__.__name__
        r = "{}(client={})"
        r = r.format(class_name, self.alice)
        return r


class NodeEngagementMutex:
    """
    TODO: Does this belong on middleware?

    TODO: There are a couple of ways this can break.  If one fo the jobs hangs, the whole thing will hang.  Also,
       if there are fewer successfully completed than percent_to_complete_before_release, the partial queue will never
       release.

    TODO: Make registry per... I guess Policy?  It's weird to be able to accidentally enact again.
    """
    log = Logger("Policy")

    def __init__(self,
                 callable_to_engage,  # TODO: typing.Protocol
                 nodes,
                 network_middleware,
                 percent_to_complete_before_release=5,
                 note=None,
                 threadpool_size=120,
                 timeout=20,
                 *args,
                 **kwargs):
        self.f = callable_to_engage
        self.nodes = nodes
        self.network_middleware = network_middleware
        self.args = args
        self.kwargs = kwargs

        self.completed = {}
        self.failed = {}

        self._started = False
        self._finished = False
        self.timeout = timeout

        self.percent_to_complete_before_release = percent_to_complete_before_release
        self._partial_queue = Queue()
        self._completion_queue = Queue()
        self._block_until_this_many_are_complete = math.ceil(
            len(nodes) * self.percent_to_complete_before_release / 100)
        self.nodes_contacted_during_partial_block = False
        self.when_complete = Deferred()  # TODO: Allow cancelling via KB Interrupt or some other way?

        if note is None:
            self._repr = f"{callable_to_engage} to {len(nodes)} nodes"
        else:
            self._repr = f"{note}: {callable_to_engage} to {len(nodes)} nodes"

        self._threadpool = ThreadPool(minthreads=threadpool_size, maxthreads=threadpool_size, name=self._repr)
        self.log.info(f"NEM spinning up {self._threadpool}")
        self._threadpool.callInThread(self._bail_on_timeout)

    def __repr__(self):
        return self._repr

    def _bail_on_timeout(self):
        while True:
            if self.when_complete.called:
                return
            duration = datetime.datetime.now() - self._started
            if duration.seconds >= self.timeout:
                try:
                    self._threadpool.stop()
                except AlreadyQuit:
                    raise RuntimeError("Is there a race condition here?  If this line is being hit, it's a bug.")
                raise RuntimeError(f"Timed out.  Nodes completed: {self.completed}")
            time.sleep(.5)

    def block_until_success_is_reasonably_likely(self):
        """
        https://www.youtube.com/watch?v=OkSLswPSq2o
        """
        if len(self.completed) < self._block_until_this_many_are_complete:
            try:
                completed_for_reasonable_likelihood_of_success = self._partial_queue.get(timeout=self.timeout) # TODO: Shorter timeout here?
            except Empty:
                raise RuntimeError(f"Timed out.  Nodes completed: {self.completed}")
            self.log.debug(f"{len(self.completed)} nodes were contacted while blocking for a little while.")
            return completed_for_reasonable_likelihood_of_success
        else:
            return self.completed


    def block_until_complete(self):
        if self.total_disposed() < len(self.nodes):
            try:
                _ = self._completion_queue.get(timeout=self.timeout)  # Interesting opportuntiy to pass some data, like the list of contacted nodes above.
            except Empty:
                raise RuntimeError(f"Timed out.  Nodes completed: {self.completed}")
        if not reactor.running and not self._threadpool.joined:
            # If the reactor isn't running, the user *must* call this, because this is where we stop.
            self._threadpool.stop()

    def _handle_success(self, response, node):
        if response.status_code == 201:
            self.completed[node] = response
        else:
            assert False  # TODO: What happens if this is a 300 or 400 level response?  (A 500 response will propagate as an error and be handled in the errback chain.)
        if self.nodes_contacted_during_partial_block:
            self._consider_finalizing()
        else:
            if len(self.completed) >= self._block_until_this_many_are_complete:
                contacted = tuple(self.completed.keys())
                self.nodes_contacted_during_partial_block = contacted
                self.log.debug(f"Blocked for a little while, completed {contacted} nodes")
                self._partial_queue.put(contacted)
        return response

    def _handle_error(self, failure, node):
        self.failed[node] = failure  # TODO: Add a failfast mode?
        self._consider_finalizing()
        self.log.warn(f"{node} failed: {failure}")

    def total_disposed(self):
        return len(self.completed) + len(self.failed)

    def _consider_finalizing(self):
        if not self._finished:
            if self.total_disposed() == len(self.nodes):
                # TODO: Consider whether this can possibly hang.
                self._finished = True
                if reactor.running:
                    reactor.callInThread(self._threadpool.stop)
                self._completion_queue.put(self.completed)
                self.when_complete.callback(self.completed)
                self.log.info(f"{self} finished.")
        else:
            raise RuntimeError("Already finished.")

    def _engage_node(self, node):
        maybe_coro = self.f(node, network_middleware=self.network_middleware, *self.args, **self.kwargs)

        d = ensureDeferred(maybe_coro)
        d.addCallback(self._handle_success, node)
        d.addErrback(self._handle_error, node)
        return d

    def start(self):
        if self._started:
            raise RuntimeError("Already started.")
        self._started = datetime.datetime.now()
        self.log.info(f"NEM Starting {self._threadpool}")
        for node in self.nodes:
             self._threadpool.callInThread(self._engage_node, node)
        self._threadpool.start()


async def run_workers(worker, value_factory, max_successes, timeout, stagger_timeout):

    successes = {}
    failures = {}
    order = []

    async def worker_wrapper(worker, value, cancel):
        try:
            result = await worker(value)
            successes[value] = result
            if len(successes) >= max_successes:
                cancel()
        except Exception as e:
            import traceback
            traceback.print_exc()
            failures[value] = e

    with trio.move_on_after(timeout):
        async with trio.open_nursery() as nursery:
            cancel = nursery.cancel_scope.cancel

            while True:
                batch = value_factory(len(successes))

                if not batch:
                    break

                order += batch

                for value in batch:
                    nursery.start_soon(worker_wrapper, worker, value, cancel)

                await trio.sleep(stagger_timeout)

    ordered_successes = [successes[value] for value in order if value in successes]

    return ordered_successes, failures


def run_workers_sync(*args):
    return trio.run(run_workers, *args)


class LazyReservoir:

    def __init__(self, ursulas, make_reservoir):
        self.ursulas = list(ursulas)
        self.make_reservoir = make_reservoir
        self.reservoir = None

    def __call__(self):
        reservoir = self.reservoir if self.reservoir is None else (self.reservoir._sampler.elements, self.reservoir._sampler.totals)
        if self.ursulas:
            return self.ursulas.pop(0)

        if self.reservoir is None:
            if self.make_reservoir is not None:
                self.reservoir = self.make_reservoir()
                self.make_reservoir = None
            else:
                return None

        if len(self.reservoir) > 0:
            # TODO: can raise StakingEscrowAgent.NotEnoughStakers
            res = self.reservoir.draw(1)[0]
            return res
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

    class Rejected(RuntimeError):
        """Too many Ursulas rejected"""

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

        self._accepted_arrangements = {}    # type: Set[Arrangement]
        self._enacted_arrangements = {}

    class MoreKFragsThanArrangements(TypeError):
        """
        Raised when a Policy has been used to generate Arrangements with Ursulas insufficient number
        such that we don't have enough KFrags to give to each Ursula.
        """

    @property
    def n(self) -> int:
        return len(self.kfrags)

    @property
    def id(self) -> bytes:
        return self._id

    def __repr__(self):
        return f"{self.__class__.__name__}:{self.id.hex()[:6]}"

    @property
    def accepted_ursulas(self) -> Set[Ursula]:
        return set(self._accepted_arrangements)

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
                          blockchain_signer: Callable = None,
                          ) -> NodeEngagementMutex:

        treasure_map = self._treasure_map_class(m=self.m)

        for ursula, arrangement in self._enacted_arrangements.values():
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

        async def put_treasure_map_on_node(node, network_middleware):
            return network_middleware.put_treasure_map_on_node(node=node,
                                                               map_payload=treasure_map_bytes)

        return NodeEngagementMutex(callable_to_engage=put_treasure_map_on_node,
                                   nodes=target_nodes,
                                   network_middleware=network_middleware)

    @abstractmethod
    def _enactment_payload(self, kfrag):
        raise NotImplementedError

    def _encrypt_for_enactment(self, ursula, kfrag):
        """Craft an offer to send to Ursula."""
        # TODO: seems like it would be enough to just encrypt this with Ursula's public key,
        # and not create a whole capsule.
        # Can't change for now since it's node protocol.
        message_kit, _signature = self.alice.encrypt_for(ursula, self._enactment_payload(kfrag))
        return message_kit

    def enact(self, network_middleware, publish_treasure_map=True) -> dict:
        """
        Assign kfrags to ursulas_on_network, and distribute them via REST,
        populating enacted_arrangements
        """
        if len(self._accepted_arrangements) < self.n:
            raise self.MoreKFragsThanArrangements("Not enough candidate arrangements. "
                                                  "Call make_arrangements to make more.")

        arrangement_statuses = []
        for ursula, kfrag in zip(self._accepted_arrangements, self.kfrags):
            arrangement = self._accepted_arrangements[ursula]
            arrangement_message_kit = self._encrypt_for_enactment(ursula, kfrag)

            try:
                # TODO: Concurrency
                response = network_middleware.enact_policy(ursula,
                                                           arrangement.id,
                                                           arrangement_message_kit.to_bytes())
            except network_middleware.UnexpectedResponse as e:
                status = e.status
            else:
                status = response.status_code

            arrangement_statuses.append(status)

            # TODO: temporary, to make tests pass
            self._enacted_arrangements[kfrag] = (ursula, arrangement)

        # OK, let's check: if two or more Ursulas claimed we didn't pay,
        # we need to re-evaulate our situation here.
        number_of_claims_of_freeloading = sum(status == 402 for status in arrangement_statuses)

        if number_of_claims_of_freeloading > 2:
            raise self.alice.NotEnoughNodes  # TODO: Clean this up and enable re-tries.

        # TODO: Leave a note to try any failures later.
        pass

        # ...After *all* the arrangements are enacted

        treasure_map = self.make_treasure_map(network_middleware=network_middleware,
                                              blockchain_signer=self._blockchain_signer())
        publishing_mutex = self.make_publishing_mutex(treasure_map=treasure_map,
                                                      network_middleware=network_middleware)
        revocation_kit = RevocationKit(treasure_map, self.alice.stamp)

        enacted_policy = EnactedPolicy(self._id, self.hrac(), self.label, self.public_key, self._enacted_arrangements, treasure_map, publishing_mutex, revocation_kit)

        self.alice.add_active_policy(enacted_policy)

        if publish_treasure_map is True:
            enacted_policy.publish_treasure_map()

        return enacted_policy

    def _propose_arrangement(self, ursula, network_middleware: RestMiddleware, arrangement):
        negotiation_response = network_middleware.propose_arrangement(ursula, arrangement)
        is_accepted = negotiation_response.status_code == 200

        #except NodeSeemsToBeDown as e:  # TODO: #355 Also catch InvalidNode here?
        #    raise

        if not is_accepted:
            self.log.debug(f"Arrangement failed with {ursula}")
            raise Exception

        self.log.debug(f"Arrangement accepted by {ursula}")

    async def _try_propose_arrangement(self, address,
            network_middleware: RestMiddleware,
            arrangement,
            discover_on_this_thread: bool = False,
            learner_timeout = 1, # TODO: remove hardcoding
        ):

        while True:
            self.alice.block_until_specific_nodes_are_known([address],
                                                            learn_on_this_thread=discover_on_this_thread,
                                                            allow_missing=1,
                                                            timeout=learner_timeout)
            if address in self.alice.known_nodes:
                break

            await trio.sleep(0)

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

        if handpicked_ursulas is None:
            handpicked_ursulas = set()
        handpicked_addresses = [ursula.checksum_address for ursula in handpicked_ursulas]

        # TODO: is there a better way to determine that?
        if isinstance(self, BlockchainPolicy):
            make_reservoir = lambda: self.alice.get_stakers_reservoir(duration=self.duration_periods,
                                                                      without=handpicked_addresses)
        else:
            make_reservoir = lambda: StakersReservoir({ursula.checksum_address: 1 for ursula in self.alice.known_nodes})

        lazy_reservoir = LazyReservoir(handpicked_addresses, make_reservoir)
        value_factory = PrefetchStrategy(lazy_reservoir, self.n)

        async def worker(address):
            arrangement = self.make_arrangement()
            return await self._try_propose_arrangement(
                address, network_middleware, arrangement, discover_on_this_thread, draw_timeout)

        arrangements, failures = run_workers_sync(worker, value_factory, self.n, 10, 1)

        for ursula, arrangement in arrangements:
            self._accepted_arrangements[ursula] = arrangement

        if len(arrangements) < self.n:
            # TODO: can report on failures here
            raise self.Rejected(f"Only got {len(arrangements)} out of {self.n}.")

    def make_arrangement(self):
        return Arrangement(alice=self.alice, expiration=self.expiration)

    @abstractmethod
    def _blockchain_signer(self):
        raise NotImplementedError


class FederatedPolicy(Policy):

    from nucypher.policy.collections import TreasureMap as _treasure_map_class  # TODO: Circular Import

    def _enactment_payload(self, kfrag):
        return bytes(kfrag)

    def _blockchain_signer(self):
        return None


class BlockchainPolicy(Policy):
    """
    A collection of n Arrangements representing a single Policy
    """

    from nucypher.policy.collections import SignedTreasureMap as _treasure_map_class  # TODO: Circular Import

    class NoSuchPolicy(Exception):
        pass

    class InvalidPolicy(Exception):
        pass

    class InvalidPolicyValue(ValueError):
        pass

    class NotEnoughBlockchainUrsulas(Policy.MoreKFragsThanArrangements):
        pass

    def __init__(self,
                 alice: Alice,
                 value: int,
                 rate: int,
                 duration_periods: int,
                 expiration: maya.MayaDT,
                 *args, **kwargs):

        self.duration_periods = duration_periods
        self.expiration = expiration
        self.value = value
        self.rate = rate
        self.author = alice

        # Initial State
        self.publish_transaction = None
        self.receipt = None

        super().__init__(alice=alice, expiration=expiration, *args, **kwargs)

        self.validate_fee_value()

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

    def publish_to_blockchain(self) -> dict:

        prearranged_ursulas = list(ursula.checksum_address for ursula in self._accepted_arrangements)

        # Transact  # TODO: Move this logic to BlockchainPolicyActor
        receipt = self.author.policy_agent.create_policy(
            policy_id=self.hrac(),  # bytes16 _policyID
            author_address=self.author.checksum_address,
            value=self.value,
            end_timestamp=self.expiration.epoch,  # uint16 _numberOfPeriods
            node_addresses=prearranged_ursulas  # address[] memory _nodes
        )

        # Capture Response
        self.receipt = receipt
        self.publish_transaction = receipt['transactionHash']

    def _enactment_payload(self, kfrag):
        return bytes(self.publish_transaction) + bytes(kfrag)

    def _blockchain_signer(self):
        transacting_power = self.alice._crypto_power.power_ups(TransactingPower)
        return transacting_power.sign_message

    def enact(self, network_middleware, publish_to_blockchain=True, publish_treasure_map=True) -> NodeEngagementMutex:
        """
        Assign kfrags to ursulas_on_network, and distribute them via REST,
        populating enacted_arrangements
        """
        if publish_to_blockchain is True:
            self.publish_to_blockchain()

        return super().enact(network_middleware, publish_treasure_map=publish_treasure_map)


class EnactedPolicy:

    def __init__(self, id, hrac, label, public_key, enacted_arrangements, treasure_map, publishing_mutex, revocation_kit):
        self.id = id # TODO: is it even used anywhere?
        self.hrac = hrac
        self.label = label
        self.public_key = public_key
        self.treasure_map = treasure_map
        self.publishing_mutex = publishing_mutex
        self.revocation_kit = revocation_kit
        self.n = len(enacted_arrangements)

    def publish_treasure_map(self):
        self.publishing_mutex.start()
