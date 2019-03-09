import itertools
import string
from dataclasses import dataclass, field
from typing import Dict, Generator

import z3

from ..visitor import visitor
from .component import (Concat, Index, IntConst, IntHole, Length, Replace,
                        StrConst, StrHole, Substr, visit_all)

# Problemas com z3:
# - inputs nao sao naturais
# - inputs nao variam o suficiente
# - muitas vezes lento ou nao consegue encontrar solucao
# Problemas com hypothesis:
# - nao da como forcar as constraints e acaba por demorar demasiado tempo


# XXX FIXME copy
def fresh():
    for i in itertools.count():
        x = f'y{i}'
        yield x


# FIXME Bias!!
@dataclass
class InputGenSMT():
    fresh: Generator[str, None, None] = field(
        default_factory=fresh, init=False, repr=False)
    solver: z3.Solver = field(default_factory=z3.Solver, repr=False)
    holes_z3: Dict = field(default_factory=dict)

    def fresh_z3(self, z3cons):
        return z3cons(next(self.fresh))

    @visitor(StrHole)
    def visit(self, hole):
        if hole in self.holes_z3:
            return self.holes_z3[hole]

        x = z3.String(hole.name)
        self.holes_z3[hole] = x

        # Bias
        pool = string.ascii_letters + string.digits + './-_@\n <>'
        lowercase_word = z3.Star(
            z3.Union(*(z3.Re(letter) for letter in string.ascii_lowercase)))
        self.solver.add(z3.Length(x) >= 4)
        self.solver.add(z3.InRe(x, lowercase_word))

        return x

    @visitor(IntHole)
    def visit(self, hole):
        if hole in self.holes_z3:
            return self.holes_z3[hole]

        x = z3.Int(hole.name)
        self.holes_z3[hole] = x

        return x

    def visit_const(self, const, z3cons, z3val):
        x = self.fresh_z3(z3cons)
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

        # Bias
        self.solver.add(z3.Length(x) > z3.Length(y))
        self.solver.add(z3.Not(z3.SuffixOf(y, x)))

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

        # Bias
        self.solver.add(z3.Length(text) > z3.Length(old))

        return z

    @visitor(Substr)
    def visit(self, c):
        text, i, j = visit_all(self, c)

        z = self.fresh_z3(z3.String)

        self.solver.add(z == z3.SubString(text, i, j - i))
        self.solver.add(0 <= i)
        self.solver.add(i < j)
        self.solver.add(j <= z3.Length(text))

        return z


def cast_z3(x):
    if z3.is_int_value(x):
        return x.as_long()
    elif z3.is_string_value(x):
        return x.as_string()
    else:
        raise ValueError(f'Input Gen: Unsupported type: {type(x)}')


def input_gen(prog, count=None):
    def helper():
        ig = InputGenSMT()
        ig.visit(prog)

        while ig.solver.check() == z3.sat:
            model = ig.solver.model()

            # FIXME
            # We need to map the environment too because the interpretation of
            # some components is not mirrored exactly by z3. For example,
            # if x = 'johndoe@email.com', then
            # Substr(x, 4, Index(x, '@')) = 'doe',
            # but (str.substr x 4 (str.indexof x '@' 0)) == 'doe@ema'
            env = {
                hole: cast_z3(model.eval(x))
                for hole, x in ig.holes_z3.items()
            }

            yield env

            # FIXME Or vs And
            # ig.solver.add(
            #     z3.Or(*(x != model[x] for x in ig.holes_z3.values())))
            ig.solver.add(
                z3.And(*(x != model[x] for x in ig.holes_z3.values())))

    return itertools.islice(helper(), count)


def gen(prog):
    return next(input_gen(prog))
