from dataclasses import dataclass, field
import string
from typing import Generator, Dict

import z3

from component import (visit_all, StrHole, IntHole, StrConst, IntConst, Concat,
                       Index, Length, Replace, Substr)
import utils
from visitor import visitor


# FIXME Bias!!
@dataclass
class InputGenSMT():
    fresh: Generator[str, None, None] = field(
        default_factory=utils.fresh, init=False, repr=False)
    solver: z3.Solver = field(default_factory=z3.Solver, repr=False)
    holes_z3: Dict = field(default_factory=dict)

    def fresh_z3(self, z3cons):
        return z3cons(next(self.fresh))

    @visitor(StrHole)
    def visit(self, hole):
        x = z3.String(hole.name)
        self.holes_z3[hole] = x

        lowercase_word = z3.Star(
            z3.Union(*(z3.Re(letter) for letter in string.ascii_lowercase)))

        self.solver.add(z3.Length(x) >= 10)
        self.solver.add(z3.Length(x) <= 20)
        self.solver.add(z3.InRe(x, lowercase_word))

        return x

    @visitor(IntHole)
    def visit(self, hole):
        x = z3.Int(hole.name)
        self.holes_z3[hole] = x
        return x

    def visit_const(self, const, z3cons, z3val):
        x = fresh_z3(z3cons)
        self.solver.add(x == z3val(const.value))
        return x

    @visitor(StrConst)
    def visit(self, const):
        return self.visit_const(const, z3.String, z3.StringVal)

    @visitor(IntConst)
    def visit(self, const):
        return self.visit_const(const, z3.Int, z3.IntVal)

    def visit_component(self, component, z3cons, z3fun):
        z = self.fresh_z3(z3cons)
        self.solver.add(z == z3fun(*visit_all(self, component)))
        return z

    @visitor(Concat)
    def visit(self, c):
        return self.visit_component(c, z3.String, z3.Concat)

    @visitor(Index)
    def visit(self, c):
        x, y = visit_all(self, c)

        z = self.fresh_z3(z3.Int)

        self.solver.add(z == z3.IndexOf(x, y, 0))
        self.solver.add(z3.Contains(x, y))

        return z

    @visitor(Length)
    def visit(self, c):
        return self.visit_component(c, z3.Int, z3.Length)

    @visitor(Replace)
    def visit(self, c):
        text, old, new = visit_all(self, c)

        z = self.fresh_z3(z3.String)

        self.solver.add(z == z3.Replace(text, old, new))
        self.solver.add(z3.Contains(text, old))

        return z

    @visitor(Substr)
    def visit(self, c):
        text, i, j = visit_all(self, c)

        z = self.fresh_z3(z3.String)

        self.solver.add(z == z3.SubString(text, i, j - i))
        self.solver.add(0 <= i)
        self.solver.add(i <= j)
        self.solver.add(j <= z3.Length(text))

        return z


def cast_z3(x):
    if z3.is_int_value(x):
        return x.as_long()
    elif z3.is_string_value(x):
        return x.as_string()
    else:
        raise ValueError(f'Input Gen: Unsupported type: {type(x)}')


def enumerate_models(solver):
    while solver.check() == z3.sat:
        model = solver.model()
        yield model
        solver.add(z3.Or(*(x != model[x] for x in model)))


def input_gen(prog, count=None):
    def helper():
        ig = InputGenSMT()
        ig.visit(prog)

        model = enumerate_models(ig.solver)

        while True:
            try:
                yield {
                    hole: cast_z3(next(model).eval(x))
                    for hole, x in ig.holes_z3.items()
                }
            except StopIteration:
                break

    return itertools.islice(helper(), count)
