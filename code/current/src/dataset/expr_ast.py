from abc import ABC, abstractmethod
from dataclasses import dataclass
import datetime
from typing import *

import anytree

# FIXME: It seems like having only functions, kwargs, variables and literals
# would make
# the code much simpler.


# Parse Tree
class Expr(ABC):
    @abstractmethod
    def build_map(self, vars, gen):
        pass

    @abstractmethod
    def make_template(self, vars):
        pass

    # FIXME: Visitor
    def templatify(self):
        vars = self.build_map({}, fresh())
        return self.make_template(vars)

    @abstractmethod
    def to_anytree(self):
        pass

    def height(self):
        return self.to_anytree().height

    def size(self):
        return 1 + len(
            [d for d in self.to_anytree().descendants if not d.is_leaf])

    def render(self):
        for pre, _, node in anytree.RenderTree(self.to_anytree()):
            print(f"{pre}{node.name}")


@dataclass(frozen=True)
class Variable(Expr):
    name: str

    def build_map(self, vars, gen):
        if self not in vars:
            vars[self] = next(gen)
        return vars

    def make_template(self, vars):
        return vars[self]

    def to_anytree(self):
        return anytree.Node(self.name, tag=type(self).__name__)


@dataclass(frozen=True)
class Literal(Expr):
    value: Any  # FIXME: Subclass this into string, number, date, etc.

    def build_map(self, vars, gen):
        return vars

    def make_template(self, vars):
        return self

    def to_anytree(self):
        return anytree.Node(self.value, tag=type(self).__name__)


@dataclass(frozen=True)
class KWArg(Expr):
    keyword: str
    arg: Optional[Expr]

    def build_map(self, vars, gen):
        return self.arg.build_map(vars, gen) if self.arg else vars

    def make_template(self, vars):
        if self.arg:
            return KWArg(self.keyword, self.arg.make_template(vars))
        else:
            KWArg(self.keyword, None)

    def to_anytree(self):
        c = [self.arg.to_anytree()] if self.arg else ()
        return anytree.Node(self.keyword, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Func(Expr):
    name: str
    parameters: Tuple[Union[Expr, KWArg], ...]

    def build_map(self, vars, gen):
        for p in self.parameters:
            vars = p.build_map(vars, gen)
        return vars

    def make_template(self, vars):
        params = tuple([p.make_template(vars) for p in self.parameters])
        return Func(self.name, params)

    def to_anytree(self):
        c = [p.to_anytree() for p in self.parameters]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Unop(Expr):
    name: str
    parameter: Expr

    def build_map(self, vars, gen):
        return self.parameter.build_map(vars, gen)

    def make_template(self, vars):
        return Unop(self.name, self.parameter.make_template(vars))

    def to_anytree(self):
        c = [self.parameter.to_anytree()]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Binop(Expr):
    name: str
    left: Expr
    right: Expr

    def build_map(self, vars, gen):
        vars = self.left.build_map(vars, gen)
        return self.right.build_map(vars, gen)

    def make_template(self, vars):
        return Binop(self.name, self.left.make_template(vars),
                     self.right.make_template(vars))

    def to_anytree(self):
        c = [self.left.to_anytree(), self.right.to_anytree()]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Dot(Expr):
    left: Expr
    right: Expr

    def build_map(self, vars, gen):
        if self not in vars:
            vars[self] = next(gen)
        return vars

    def make_template(self, vars):
        return vars[self]

    def to_anytree(self):
        c = [self.left.to_anytree(), self.right.to_anytree()]
        return anytree.Node('.', children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Indexer(Expr):
    list: Expr
    index: Expr

    def build_map(self, vars, gen):
        if self not in vars:
            vars[self] = next(gen)
        return vars

    def make_template(self, vars):
        return vars[self]

    def to_anytree(self):
        c = [self.list.to_anytree(), self.index.to_anytree()]
        return anytree.Node('[]', children=c, tag=type(self).__name__)


def fresh():
    import itertools
    for i in itertools.count():
        x = f'x{i}'
        yield Variable(x)


def test_build_map():
    from parser import parse

    def tc(test):
        return parse(test).build_map({}, fresh())

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


def test_make_template():
    from parser import parse

    def helper(test, expected):
        expr = parse(test)
        vars = expr.build_map({}, fresh())

        return expr.make_template(vars) == expected

    helper('a.c[0] + b', Binop('+', Variable('x0'), Variable('x1')))


def test_templatify():
    from parser import parse

    def helper(test, expected):
        assert parse(test).templatify() == expected

    helper('a.c[0] + b', Binop('+', Variable('x0'), Variable('x1')))
    helper(
        'f(a.c[0] + b, c)',
        Func('f', [Binop('+', Variable('x0'), Variable('x1')),
                   Variable('x2')]))
    helper(
        'f(a.c[0] + b, -c)',
        Func('f', [
            Binop('+', Variable('x0'), Variable('x1')),
            Unop('-', Variable('x2'))
        ]))
