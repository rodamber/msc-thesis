from dataclasses import dataclass, field
import itertools
from typing import Generator, Dict

from visitor import visitor
from expr_ast import Variable, Literal, KWArg, Func, Unop, Binop, Dot, Indexer

# FIXME Now that vars_ is "global" state, we could probably make the
# templification in one pass. But this way can be easier to test, I guess.

# FIXME By having Expr implementing accept we could have the same benefits of a
# recursion schemes approach in fp.


def fresh():
    for i in itertools.count():
        x = f'x{i}'
        yield Variable(x)


@dataclass
class BuildMap:
    gen: Generator[Variable, None, None] = field(
        default_factory=fresh, init=False, repr=False)

    vars_: Dict[Variable, Variable] = field(default_factory=dict)

    @visitor(Variable)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_

    @visitor(Literal)
    def visit(self, e):
        return self.vars_

    @visitor(KWArg)
    def visit(self, e):
        if e.arg:
            self.visit(e.arg)
        return self.vars_

    @visitor(Func)
    def visit(self, e):
        for p in e.parameters:
            self.visit(p)
        return self.vars_

    @visitor(Unop)
    def visit(self, e):
        self.visit(e.parameter)
        return self.vars_

    @visitor(Binop)
    def visit(self, e):
        self.visit(e.left)
        self.visit(e.right)
        return self.vars_

    @visitor(Dot)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_

    @visitor(Indexer)
    def visit(self, e):
        if e not in self.vars_:
            self.vars_[e] = next(self.gen)
        return self.vars_


def build_map(e):
    bm = BuildMap()
    return bm.visit(e)


def test_build_map():
    from parser import parse

    def tc(test):
        return build_map(parse(test))

    assert tc('a') == {Variable('a'): Variable('x0')}
    assert tc('a + b') == {
        Variable('a'): Variable('x0'),
        Variable('b'): Variable('x1')
    }
    assert tc('a.c + b') == {
        Dot(Variable('a'), Variable('c')): Variable('x0'),
        Variable('b'): Variable('x1')
    }
    assert tc('a[0].c + b') == {
        Dot(Indexer(Variable('a'), Literal('0')), Variable('c')):
        Variable('x0'),
        Variable('b'): Variable('x1')
    }
    assert tc('a.c[0] + b') == {
        Dot(Variable('a'), Indexer(Variable('c'), Literal('0'))):
        Variable('x0'),
        Variable('b'): Variable('x1')
    }
    assert tc('a[0] + b') == {
        Indexer(Variable('a'), Literal('0')): Variable('x0'),
        Variable('b'): Variable('x1')
    }


@dataclass
class MakeTemplate():
    vars_: Dict[Variable, Variable]

    @visitor(Variable)
    def visit(self, e):
        return self.vars_[e]

    @visitor(Literal)
    def visit(self, e):
        return e

    @visitor(KWArg)
    def visit(self, e):
        if e.arg:
            return KWArg(e.keyword, self.visit(e.arg))
        else:
            return KWArg(e.keyword, None)

    @visitor(Func)
    def visit(self, e):
        params = tuple(self.visit(p) for p in e.parameters)
        return Func(e.name, params)

    @visitor(Unop)
    def visit(self, e):
        return Unop(e.name, self.visit(e.parameter))

    @visitor(Binop)
    def visit(self, e):
        return Binop(e.name, self.visit(e.left), self.visit(e.right))

    @visitor(Dot)
    def visit(self, e):
        return self.vars_[e]

    @visitor(Indexer)
    def visit(self, e):
        return self.vars_[e]


def make_template(e, vars_):
    mt = MakeTemplate(vars_)
    return mt.visit(e)


def test_make_template():
    from parser import parse

    def helper(test, expected):
        expr = parse(test)
        vars_ = build_map(expr)
        return make_template(expr, vars_) == expected

    helper('a.c[0] + b', Binop('+', Variable('x0'), Variable('x1')))


def templatify(expr):
    vars_ = build_map(expr)
    return make_template(expr, vars_)


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
