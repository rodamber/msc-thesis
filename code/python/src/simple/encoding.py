from dataclasses import dataclass
from itertools import combinations, product
from typing import NamedTuple, Tuple

from z3 import Context, FreshConst, Implies, Length, Or

from . import enumerator
from .library import Spec
from .types import Const, Constraint, Input, Kind, Line, Output, Symbol

# ==============================================================================
#                                    Types
# ==============================================================================


class Param(Symbol):
    def __init__(self, kind: Kind, line: Line, name: str, id: int, n: int):
        ctx = line.ctx
        super().__init__(expr=FreshConst(kind.to_z3_sort(ctx), \
                                         f'{name}_id{id}_p{n}'),
                         kind=kind,
                         line=line)


class RetVal(Symbol):
    def __init__(self, kind: Kind, line: Line, name: str, id: int):
        ctx = line.ctx
        super().__init__(expr=FreshConst(kind.to_z3_sort(ctx), \
                                         f'{name}_id{id}_ret'),
                         kind=kind,
                         line=line)


@dataclass
class SymComponent:
    name: str
    params: Tuple[Param, ...]
    ret_val: RetVal
    _spec: Spec

    @classmethod
    def mk(cls, f: 'enumerator.Component') -> 'SymComponent':
        name = f.name

        params = tuple(
            Param(kind=kind, name=name, line=line, id=f.id, n=n)
            for n, (kind, line) in enumerate(f.domain, start=1))

        ret_val = RetVal(kind=f.ret_type.kind, line=f.ret_type.line, \
                         name=name, id=f.id)

        return cls(name, params, ret_val, f.spec)

    @property
    def line(self) -> Line:
        return self.ret_val.line

    @property
    def kind(self) -> Kind:
        return self.ret_val.kind

    @property
    def ctx(self) -> Context:
        return self.ret_val.ctx

    @property
    def spec(self) -> Constraint:
        return self._spec(self.params, self.ret_val)


class Env(NamedTuple):
    I: Tuple[Input, ...]
    C: Tuple[Const, ...]
    F: Tuple[SymComponent, ...]
    P: Tuple[Param, ...]
    R: Tuple[RetVal, ...]
    o: Output


# ==============================================================================
#                                 Constraints
# ==============================================================================


def well_formedness_constraint(env: Env) -> Constraint:
    I, C, F, P, R, o = env

    n = len(I) + len(C)

    # Parameter line range
    for f in F:
        for p in f.params:
            yield 1 <= p.line
            yield p.line < f.line

    # Return value line range
    for r in R:
        yield n + 1 <= r.line
        yield r.line <= n + len(R)

    # One component per line
    for x, y in combinations(R, 2):
        yield x.line != y.line

    # Different sorts imply different lines
    for p, x in product(P, I + C + R + (o, )):
        if p.kind != x.kind:
            yield p.line != x.line
    for r in R:
        if r.kind != o.kind:
            yield r.line != o.line


def spec_constraint(env: Env) -> Constraint:
    _, _, F, _, _, _ = env
    for f in F:
        if f.name != 'replace': # XXX
            yield f.spec
        else:
            yield from [p.line <= len(env.I) + len(env.C) \
                        for p in f.params[1:]]
            yield f.params[1].expr != f.params[2].expr # XXX
            yield f.spec

def dataflow_constraint(env: Env) -> Constraint:
    I, C, F, P, R, o = env

    # On one case the call to the solver was much faster without this.
    # R_ = lambda p: tuple(f.ret_val for f in F if p not in f.params)

    for p in P:
        for x in I + C + R:  #R_(p):
            if p.kind == x.kind:
                yield Implies(p.line == x.line, p == x)

    for r in R:
        if r.kind == o.kind:
            yield Implies(r.line == o.line, r == o)


def all_input_used_constraint(env: Env) -> Constraint:
    I, _, _, P, _, _ = env

    for i in I:
        yield Or([p.line == i.line for p in P], i.ctx)


def all_ret_val_used_constraint(env: Env) -> Constraint:
    I, C, F, P, _, o = env

    for f in F:
        # TODO Check if there's any performance gain from verifying if p is in
        # TODO Also, remove kind check if we're only checking for line equality
        # f.params.
        constr = Or([f.line == p.line \
                     for p in P
                     if p not in [q for q in f.params if p.kind == q.kind]
                     #\ and f.kind == p.kind # unplugable components
        ], f.ctx)
        if f.kind == o.kind:
            yield Or(constr, f.line == o.line, f.ctx)
        else:
            yield constr


def const_max_size(env: Env) -> Constraint:
    _, C, _, _, _, _ = env

    for c in C:
        if c.kind == Kind.STR:
            # XXX
            yield Length(c.expr) <= 5


def extra_constraint(env: Env) -> Constraint:
    yield from all_input_used_constraint(env)
    yield from all_ret_val_used_constraint(env)
    yield from const_max_size(env)


def program_constraint(I: Tuple[Input, ...], \
                       C: Tuple[Const, ...],
                       fs: Tuple['enumerator.Component', ...],
                       o: Output) -> Constraint:

    F = tuple(SymComponent.mk(f) for f in fs)
    P = tuple(p for f in F for p in f.params)
    R = tuple(f.ret_val for f in F)

    env = Env(I, C, F, P, R, o)

    yield from well_formedness_constraint(env)
    yield from spec_constraint(env)
    yield from dataflow_constraint(env)
    yield from extra_constraint(env)
