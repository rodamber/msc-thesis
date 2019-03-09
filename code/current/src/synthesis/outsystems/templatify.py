from dataclasses import dataclass, field
from typing import Dict, Generator

from .. import utils
from ..outsystems import expr_ast as ast
from ..visitor import visitor
from .parser import parse

# FIXME By having Expr implementing accept we could have the same benefits of a
# recursion schemes approach in fp.


@dataclass
class Templatify:
    gen: Generator[ast.Variable, None, None] = field(
        default_factory=lambda: map(ast.Variable, utils.fresh()),
        init=False,
        repr=False)
    vars_: Dict[ast.Variable, ast.Variable] = field(default_factory=dict)

    @visitor(ast.Variable)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_[e]

    @visitor(ast.Literal)
    def visit(self, e):
        return e

    @visitor(ast.KWArg)
    def visit(self, e):
        if e.arg:
            self.visit(e.arg)
            return ast.KWArg(e.keyword, self.visit(e.arg))
        else:
            return ast.KWArg(e.keyword, None)

    @visitor(ast.Func)
    def visit(self, e):
        for p in e.parameters:
            self.visit(p)
        params = tuple(self.visit(p) for p in e.parameters)
        return ast.Func(e.name, params)

    @visitor(ast.Unop)
    def visit(self, e):
        self.visit(e.parameter)
        return ast.Unop(e.name, self.visit(e.parameter))

    @visitor(ast.Binop)
    def visit(self, e):
        self.visit(e.left)
        self.visit(e.right)
        return ast.Binop(e.name, self.visit(e.left), self.visit(e.right))

    @visitor(ast.Dot)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_[e]

    @visitor(ast.Indexer)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_[e]


def templatify(expr):
    return Templatify().visit(expr)


def test_templatify():
    def helper(test, expected):
        assert templatify(parse(test)) == expected

    helper('a.c[0] + b', ast.Binop('+', ast.Variable('x0'),
                                   ast.Variable('x1')))
    helper(
        'f(a.c[0] + b, c)',
        ast.Func('f', (
            ast.Binop('+', ast.Variable('x0'), ast.Variable('x1')),
            ast.Variable('x2'),
        )))
    helper(
        'f(a.c[0] + b, -c)',
        ast.Func('f', (ast.Binop('+', ast.Variable('x0'), ast.Variable('x1')),
                       ast.Unop('-', ast.Variable('x2')))))
