import weakref
import time
from queue import Queue, Empty
from threading import Event, Lock, Timer, get_ident

from twisted._threads import AlreadyQuit
from twisted.python.threadpool import ThreadPool


class Success:
    def __init__(self, value, result):
        self.value = value
        self.result = result

class Failure:
    def __init__(self, value, exception):
        self.value = value
        self.exception = exception


class Stopped:
    pass


class WorkerPool:

    def __init__(self, worker, value_factory, target_successes, timeout, stagger_timeout, threadpool_size=None):

        # TODO: make stagger_timeout a part of the value factory?

        self.worker = worker
        self.value_factory = value_factory
        self.timeout = timeout
        self.stagger_timeout = stagger_timeout
        self.target_successes = target_successes

        thread_pool_kwargs = {}
        if threadpool_size is not None:
            thread_pool_kwargs['minthreads'] = threadpool_size
            thread_pool_kwargs['maxthreads'] = threadpool_size
        self.threadpool = ThreadPool(**thread_pool_kwargs)

        self.threadpool.callInThread(self._bail_on_timeout)
        self.threadpool.callInThread(self._start_batch)
        self.threadpool.callInThread(self._process_results)

        self.successes = {}
        self.failures = {}
        self._tasks = 0
        self._cancelled = 0

        self._cancel_event = Event()
        self._result_queue = Queue()
        self._success_event = Event()
        self._producer_finished = Event()
        self._processor_finished = Event()
        self._stopped = False

    def start(self):
        self.threadpool.start()

    def _bail_on_timeout(self):
        print("    * _bail_on_timeout() running in thread", get_ident())
        self._cancel_event.wait(timeout=self.timeout)
        print("    _bail_on_timeout() finished waiting")
        self._cancel_event.set()

    def _cancel(self):
        print("    _cancel()")
        self._cancel_event.set()

    def join(self):
        print("    * join() running in thread", get_ident())
        if self._stopped:
            return # or raise AlreadyStopped?

        self._producer_finished.wait()
        self._processor_finished.wait()
        print("    join() stopping pool")
        # protect from a possible race
        try:
            self.threadpool.stop()
        except AlreadyQuit:
            pass
        print("    join() done")
        self._stopped = True

    class _Cancelled(Exception):
        pass

    def _sleep(self, timeout):
        if self._cancel_event.wait(timeout):
            print("    _sleep() raising Cancelled")
            raise self._Cancelled

    def block_until_target_successes(self, timeout=None):
        self._success_event.wait(timeout=timeout)

    def worker_wrapper(self, value):
        print("    Starting worker for", value)
        try:
            result = self.worker(self._sleep, value)
            self._result_queue.put(Success(value, result))
        except self._Cancelled as e:
            self._result_queue.put(e)
        except Exception as e:
            self._result_queue.put(Failure(value, str(e)))

    def _process_results(self):
        print("    * _process_results() running in thread", get_ident())
        producer_stopped = False
        while True:
            result = self._result_queue.get()

            if isinstance(result, Stopped):
                print("    _process_results() producer stopped")
                producer_stopped = True
                continue

            if isinstance(result, Success):
                self.successes[result.value] = result.result
            elif isinstance(result, Failure):
                print("    _process_results() failure", result.exception)
                self.failures[result.value] = result.exception
            elif isinstance(result, self._Cancelled):
                self._cancelled += 1

            print("    _process_results()", len(self.successes), len(self.failures), self._cancelled, self._tasks)

            if len(self.successes) == self.target_successes:
                self._success_event.set()

            if producer_stopped and len(self.successes) + len(self.failures) + self._cancelled == self._tasks:
                self._cancel() # to cancel the timeout
                self._success_event.set() # to prevent infinite blocking for threads waiting on it

                # For some reason thread_pool.stop() does not wait for all threads to stop. Go figure.
                # So we're adding an explicit event to know that all workers are finished.
                self._processor_finished.set()
                break

    def _start_batch(self):
        print("    * _start_batch() running in thread", get_ident())
        while True:
            # TODO: what if it raises something?
            batch = self.value_factory(len(self.successes))
            print("    _start_batch()", batch)
            if not batch:
                break

            print("    _start_batch() creating threads")
            self._tasks += len(batch)
            for value in batch:
                self.threadpool.callInThread(self.worker_wrapper, value)

            try:
                self._sleep(self.stagger_timeout)
            except self._Cancelled:
                break

        print("    _start_batch() finishing")
        self._producer_finished.set()
        self._result_queue.put(Stopped())


    #def __del__(self):
    #    print(self, "__del__()")
    #    self.stop()


class AllAtOnceFactory:

    def __init__(self, values):
        self.values = values
        self._produced = False

    def __call__(self, _successes):
        if self._produced:
            return None
        else:
            self._produced = True
            return self.values

