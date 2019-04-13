import itertools
from dataclasses import dataclass
from typing import Any, Generator, Optional, Tuple, Union

import z3
from z3 import Context, ModelRef, sat, unknown

from .library import Library, Sig, Spec
from .solver import Query, Response
from .types import IO, Const, Input, Kind, Line, SIO
from .utils import z3_as

# ==============================================================================
#                                    Types
# ==============================================================================


Domain = Tuple[Tuple[Kind, Line], ...]


@dataclass
class RetKind:
    kind: Kind
    line: Line


@dataclass
class Component:
    id: int

    sig: Sig
    domain: Domain
    ret_type: RetKind

    @classmethod
    def mk(cls, sig: Sig, id: int, ctx: Context) -> 'Component':
        line = lambda name, ctx: z3.Int(name, ctx)

        domain = tuple((kind, line(f'line_{sig.name}_id{id}_p{k}', ctx))
                       for k, kind in enumerate(sig.domain, start=1))

        ret_type = RetKind(sig.ret_type, \
                           line(f'line_{sig.name}_id{id}_ret', ctx))

        return cls(id, sig, domain, ret_type)

    @property
    def line(self) -> Line:
        return self.ret_type.line

    @property
    def name(self) -> str:
        return self.sig.name

    @property
    def spec(self) -> Spec:
        return self.sig.spec


Stack = Tuple[Tuple[Kind, int], ...]


@dataclass
class Problem:
    sios: Tuple[SIO, ...]
    C: Tuple[Const, ...]
    fs: Tuple[Component, ...]
    ctx: Context

    @classmethod
    def mk(cls, ios, stack: Stack, lib: Library) \
        -> 'Problem':
        ctx = Context()

        inputno = len(ios[0].inputs)
        lineno = itertools.count(inputno + 1)

        C = tuple(Const(id=n - inputno, kind=kind, lineno=n, ctx=ctx) \
                  for kind, count in stack
                  for _ in range(count)
                  for n in [next(lineno)])

        fs = tuple(Component.mk(sig, id, ctx) \
                   for id, sig in enumerate(lib, start=1))

        sios = tuple(SIO.mk(io, last_line(ios[0].inputs, C, fs), ctx) \
                     for io in ios)

        return cls(sios, C, fs, ctx)


# FIXME
@dataclass
class Param:
    name: str

    def __str__(self):
        return self.name


# FIXME
@dataclass
class Var:
    val: Any

    def __str__(self):
        if isinstance(self.val, str):
            return repr(self.val)
        return str(self.val)


# FIXME
@dataclass
class Program:
    node: Union[Sig, Param, Var]
    children: Tuple['Program', ...]

    @classmethod
    def mk(cls, problem: Problem, model: ModelRef) -> 'Program':
        I = problem.sios[0].inputs
        C = problem.C
        fs = problem.fs

        r = {i: n for n, i in enumerate(I)}

        def rename(i: Input) -> str:
            return f'arg{r[i]}'

        def eval(x):
            return z3_as(model.eval(x))

        # from_line : int -> Union[Const, SymComponent]
        from_line = {eval(x.line): x for x in I + C + fs}

        def rec(line: int) -> 'Program':
            x = from_line[line]

            if isinstance(x, Input):
                return Param(rename(x))
            elif isinstance(x, Const):
                return Var(eval(x.expr))
            elif isinstance(x, Component):
                children = tuple(rec(eval(line)) for _, line in x.domain)
                return Program(node=x.sig, children=children)
            else:
                raise RuntimeError()

        last_line = max([eval(x.line) for x in fs])
        return rec(last_line)

    def __str__(self):
        if isinstance(self.node, Param):
            return self.node.name
        if isinstance(self.node, Var):
            return str(self.node.val)
        if isinstance(self.node, Sig):
            return self.node.name + \
                '(' + ', '.join(map(str, self.children)) + ')'


# ==============================================================================
#                                  Enumerator
# ==============================================================================


def enumerator(ios: Tuple[IO, ...], lib: Library, stack: Stack) \
    -> Generator[Response, Query, Optional[Program]]:

    for size in itertools.count(start=1):
        for sigs in itertools.combinations_with_replacement(lib, size):
            problem = Problem.mk(ios=ios, stack=stack, lib=sigs)

            res, maybe_model_or_reason = yield problem

            if res == sat:
                model = maybe_model_or_reason
                return Program.mk(problem, model)
            elif res == unknown:
                reason = maybe_model_or_reason
                print(f'Reason: {reason}')


# ==============================================================================
#                                   Helpers
# ==============================================================================


def last_line(I, C, F) -> int:
    return len(I) + len(C) + len(F)
