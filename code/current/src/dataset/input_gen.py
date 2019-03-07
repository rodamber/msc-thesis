from dataclasses import dataclass, field
from typing import Any, List, Generator

import pysmt.shortcuts as smt

from pysmt.typing import STRING, INT

from component import (visit_all, StrHole, IntHole, StrConst, IntConst, Concat,
                       Index, Length, Replace, Substr)
import utils
from visitor import visitor


# TODO This may still not give small enough examples. Let's see.
@dataclass
class InputGenSMT():
    fresh: Generator[str, None, None] = field(
        default_factory=utils.fresh, init=False, repr=False)

    @visitor(StrHole)
    def visit(self, hole):
        return smt.Symbol(hole.name, STRING), smt.TRUE()

    @visitor(IntHole)
    def visit(self, hole):
        return smt.Symbol(hole.name, INT), smt.TRUE()

    def make_const(self, const, type_, cons):
        x = smt.Symbol(next(self.fresh), type_)
        formula = smt.Equals(x, cons(const.value))
        return x, formula

    @visitor(StrConst)
    def visit(self, const):
        return self.make_const(const, STRING, smt.String)

    @visitor(IntConst)
    def visit(self, const):
        return self.make_const(const, INT, smt.Int)

    @visitor(Concat)
    def visit(self, concat):
        (x, fx), (y, fy) = visit_all(self, concat)

        z = smt.FreshSymbol(STRING)
        fz = smt.And(fx, fy, smt.Equals(z, smt.StrConcat(x, y)))

        return z, fz

    @visitor(Index)
    def visit(self, index):
        (x, fx), (y, fy) = visit_all(self, index)

        z = smt.FreshSymbol(INT)
        fz = smt.And(fx, fy, smt.Equals(z, smt.StrIndexOf(x, y, smt.Int(0))))

        return z, fz

    @visitor(Length)
    def visit(self, length):
        x, fx = next(visit_all(self, length))

        z = smt.FreshSymbol(INT)
        fz = smt.And(fx, smt.Equals(z, smt.StrLength(x)))

        return z, fz

    @visitor(Replace)
    def visit(self, replace):
        (text, f_text), (old, f_old), (new, f_new) = visit_all(self, replace)

        res = smt.FreshSymbol(STRING)
        f_res = smt.And(f_text, f_old, f_new,
                        smt.Equals(res, smt.StrReplace(text, old, new)))

        return res, f_res

    @visitor(Substr)
    def visit(self, substr):
        (text, f_text), (i, f_i), (j, f_j) = visit_all(self, substr)

        offset = smt.Minus(j, i)

        res = smt.FreshSymbol(STRING)
        f_res = smt.And(f_text, f_i, f_j,
                        smt.Equals(res, smt.StrSubstr(text, i, offset)))

        return res, f_res


def input_gen(prog):
    _, formula = InputGenSMT().visit(prog)
    return smt.simplify(formula)
