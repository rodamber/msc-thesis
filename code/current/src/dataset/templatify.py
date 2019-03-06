from dataclasses import dataclass, field
import itertools
from typing import Generator, Dict

from expr_ast import Variable, Literal, KWArg, Func, Unop, Binop, Dot, Indexer
import utils
from visitor import visitor

# FIXME By having Expr implementing accept we could have the same benefits of a
# recursion schemes approach in fp.


@dataclass
class Templatify:
    gen: Generator[Variable, None, None] = field(
        default_factory=lambda: map(Variable, utils.fresh()),
        init=False,
        repr=False)
    vars_: Dict[Variable, Variable] = field(default_factory=dict)

    @visitor(Variable)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_[e]

    @visitor(Literal)
    def visit(self, e):
        return e

    @visitor(KWArg)
    def visit(self, e):
        if e.arg:
            self.visit(e.arg)
            return KWArg(e.keyword, self.visit(e.arg))
        else:
            return KWArg(e.keyword, None)

    @visitor(Func)
    def visit(self, e):
        for p in e.parameters:
            self.visit(p)
        params = tuple(self.visit(p) for p in e.parameters)
        return Func(e.name, params)

    @visitor(Unop)
    def visit(self, e):
        self.visit(e.parameter)
        return Unop(e.name, self.visit(e.parameter))

    @visitor(Binop)
    def visit(self, e):
        self.visit(e.left)
        self.visit(e.right)
        return Binop(e.name, self.visit(e.left), self.visit(e.right))

    @visitor(Dot)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_[e]

    @visitor(Indexer)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_[e]


def templatify(expr):
    return Templatify().visit(expr)


def test_templatify():
    from parser import parse

    def helper(test, expected):
        assert templatify(parse(test)) == expected

    helper('a.c[0] + b', Binop('+', Variable('x0'), Variable('x1')))
    helper(
        'f(a.c[0] + b, c)',
        Func('f', (
            Binop('+', Variable('x0'), Variable('x1')),
            Variable('x2'),
        )))
    helper(
        'f(a.c[0] + b, -c)',
        Func('f', (Binop('+', Variable('x0'), Variable('x1')),
                   Unop('-', Variable('x2')))))
