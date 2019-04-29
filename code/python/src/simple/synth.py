import time
from typing import Optional, Tuple

from z3 import unknown

from .enumerator import Program, Stack, enumerator
from .library import Library
from .solver import solver
from .types import IO

# ==============================================================================
#                                  Synthesis
# ==============================================================================


# TODO: stack as optional parameter
# TODO: other configuration options
def synthesize(ios: Tuple[IO, ...], lib: Library, stack: Stack) \
    -> Optional[Program]:

    learner = enumerator(ios=ios, lib=lib, stack=stack)
    oracle = solver(timeout=None)

    # timeout = 10 * 1000
    # oracle = solver(timeout=timeout)

    # print(f'Warning: z3 call timeout of {timeout / 1000} seconds.')

    try:
        problem = next(learner)
        next(oracle)

        while True:
            names = [f.name for f in problem.fs]
            print(f'{names}', end=': ', flush=True)

            start = time.time()
            res, maybe_model_or_reason = oracle.send(problem)
            end = time.time()

            print(f'{repr(res).upper()} ({end - start:.3f} seconds)')

            if res == unknown:
                reason = maybe_model_or_reason
                print(f'Reason: {reason}')

            problem = learner.send((res, maybe_model_or_reason))
    except StopIteration as e:
        return e.value
