# Common types

from dataclasses import dataclass
from enum import Enum
from typing import Any, NamedTuple, Tuple, Union

import z3
from z3 import (ArithRef, BoolRef, Context, IntSort, IntVal, SeqRef, SortRef,
                StringSort)

from .utils import z3_val

Line = ArithRef
Constraint = BoolRef


class Kind(Enum):
    INT = 1
    STR = 2

    def to_z3_sort(self, ctx: Context) -> SortRef:
        if self == Kind.INT:
            return IntSort(ctx)
        if self == Kind.STR:
            return StringSort(ctx)
        raise RuntimeError(self)


def kind(x: Any) -> Kind:
    if isinstance(x, int):
        return Kind.INT
    if isinstance(x, str):
        return Kind.STR
    raise ValueError(x)


@dataclass
class IO:
    inputs: Tuple[Kind, ...]
    output: Kind


@dataclass(frozen=True)
class Symbol:
    expr: Union[ArithRef, BoolRef, SeqRef]
    kind: Kind
    line: Line

    @property
    def name(self) -> str:
        return str(expr)

    @property
    def ctx(self) -> Context:
        return self.line.ctx

    def __eq__(self, other):
        if isinstance(other, Symbol):
            return self.expr == other.expr
        else:
            return self.expr == other


SBool = Symbol
SInt = Symbol
SStr = Symbol


# FIXME NOTE that outsystems' strings provide no way to escape characters (apart
# from quotes, I believe), so we might be generating things that do not make
# sense.
class Const(Symbol):
    def __init__(self, id: int, kind: Kind, lineno: int, ctx: Context):
        super().__init__(expr=z3.Const(f'const_{id}', \
                                       kind.to_z3_sort(ctx)),
                         kind=kind,
                         line=IntVal(lineno, ctx))


class Input(Symbol):
    def __init__(self, val: Any, lineno: int, ctx: Context):
        super().__init__(expr=z3_val(val, ctx), kind=kind(val), \
                         line=IntVal(lineno, ctx))


class Output(Symbol):
    def __init__(self, val: Any, lineno: int, ctx: Context):
        super().__init__(expr=z3_val(val, ctx), kind=kind(val), \
                         line=IntVal(lineno, ctx))


class SIO(NamedTuple):
    inputs: Tuple[Input, ...]
    output: Output

    @classmethod
    def mk(cls, io: IO, last_line: int, ctx: Context) -> 'SIO':
        inputs = tuple(Input(val=i_, lineno=n, ctx=ctx) \
                       for n, i_ in enumerate(io.inputs, start=1))
        output = Output(val=io.output, lineno=last_line, ctx=ctx)

        return cls(inputs, output)
