from typing import Generator, Optional, Tuple, Union

from z3 import CheckSatResult, ModelRef, Solver, sat, unsat

from . import enumerator
from .encoding import program_constraint
from .types import Constraint, Kind

# ==============================================================================
#                                    Types
# ==============================================================================

FailReason = str
Query = 'enumerator.Problem'
Response = Tuple[CheckSatResult, Optional[Union[ModelRef, FailReason]]]

# ==============================================================================
#                                   Formula
# ==============================================================================


def formula(problem: 'enumerator.Problem') -> Constraint:
    C = problem.C
    fs = problem.fs

    for is_, o in problem.sios:
        yield from program_constraint(is_, C, fs, o)


# ==============================================================================
#                                    Solver
# ==============================================================================


def solver(timeout=None) -> Generator[Query, Response, None]:
    problem = yield

    while True:
        constraint = formula(problem)
        ctx = problem.ctx

        solver = Solver(ctx=ctx)
        if timeout:
            solver.set(timeout=timeout)
        else:
            solver.set(max_conflicts=20 * 1000)
        solver.add(*constraint)

        res = solver.check()

        if res == sat:
            problem = yield res, solver.model()
        elif res == unsat:
            problem = yield res, None
        else:  # res == unknown
            problem = yield res, solver.reason_unknown()
