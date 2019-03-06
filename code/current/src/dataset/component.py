from dataclasses import dataclass, field
import itertools
import string
from typing import Any, Dict, Tuple, Type, Union

from anytree import Node, RenderTree
from hypothesis import assume, strategies as st

import expr_ast as ast
from visitor import visitor


@dataclass(init=False)
class Component:
    slots: Tuple[Union['Hole', 'Component'], ...]

    def __init__(self, *slots, parent=None):
        self.slots = tuple(slots)


@dataclass(frozen=True)
class Hole:
    name: str


class StrHole(Hole):
    def __post_init__(self):
        assert isinstance(self.name, str)


class IntHole(Hole):
    def __post_init__(self):
        assert isinstance(self.name, int)


@dataclass(frozen=True)
class Const():
    value: Any


class StrConst(Const):
    def __post_init__(self):
        assert isinstance(self.value, str)


class IntConst(Const):
    def __post_init__(self):
        assert isinstance(self.value, int)


class Concat(Component):
    pass


class Index(Component):
    pass


class Length(Component):
    pass


class Replace(Component):
    pass


class Substr(Component):
    pass


def visit_all(v, c):
    return (v.visit(s) for s in c.slots)


@dataclass
class Run():
    env: Dict[str, Any]

    @visitor(StrHole)
    def visit(self, c):
        return self.env[c.name]

    @visitor(IntHole)
    def visit(self, c):
        return self.env[c.name]

    @visitor(StrConst)
    def visit(self, c):
        return c.value

    @visitor(IntConst)
    def visit(self, c):
        return c.value

    @visitor(Concat)
    def visit(self, c):
        x, y = visit_all(self, c)
        assert isinstance(x, str)
        assert isinstance(y, str)
        return x + y

    @visitor(Index)
    def visit(self, c):
        text, s = visit_all(self, c)
        assert isinstance(text, str)
        assert isinstance(s, str)
        return text.find(s)

    @visitor(Length)
    def visit(self, c):
        x = next(visit_all(self, c))
        assert isinstance(x, str)
        return len(x)

    @visitor(Replace)
    def visit(self, c):
        text, old, new = visit_all(self, c)
        assert isinstance(text, str)
        assert isinstance(old, str)
        assert isinstance(new, str)
        return text.replace(old, new)

    @visitor(Substr)
    def visit(self, c):
        text, i, j = visit_all(self, c)
        assert isinstance(text, str)
        assert isinstance(i, int)
        assert isinstance(j, int)
        return text[i:j]


def run(prog, input_source):
    return Run(input_source).visit(prog)


def test_run():
    x0 = StrHole('x0')
    x1 = StrHole('x1')
    zero = IntConst(0)

    prog = Substr(x0, zero, Index(x0, x1))
    env = {'x0': 'outsystems.com', 'x1': '.'}

    assert run(prog, env) == 'outsystems'


@dataclass
class Anytree():
    def to_node(self, c):
        return Node(name=c, children=visit_all(self, c), tag=type(c).__name__)

    @visitor(StrHole)
    def visit(self, c):
        return Node(name=c, tag=c)

    @visitor(IntHole)
    def visit(self, c):
        return Node(name=c, tag=c)

    @visitor(StrConst)
    def visit(self, c):
        return Node(name=c, tag=c)

    @visitor(IntConst)
    def visit(self, c):
        return Node(name=c, tag=c)

    @visitor(Concat)
    def visit(self, c):
        return self.to_node(c)

    @visitor(Index)
    def visit(self, c):
        return self.to_node(c)

    @visitor(Length)
    def visit(self, c):
        return self.to_node(c)

    @visitor(Replace)
    def visit(self, c):
        return self.to_node(c)

    @visitor(Substr)
    def visit(self, c):
        return self.to_node(c)


def to_anytree(prog):
    return Anytree().visit(prog)


def render(prog):
    for pre, _, node in RenderTree(to_anytree(prog)):
        print(f'{pre}{node.tag}')


def holes(prog):
    return set(
        x.name for x in to_anytree(prog).leaves if isinstance(x.name, Hole))


def test_holes():
    x0 = StrHole('x0')
    x1 = StrHole('x1')
    zero = IntConst(0)
    prog = Substr(x0, zero, Index(x0, x1))

    assert holes(prog) == set([x0, x1])


# def input_gen(prog):
#     from hypothesis import strategies as st

#     inputs = (st.from_type(type(h.name)).example() for h in holes(prog))
#     return {x.name: input_ for x, input_ in zip(holes(prog), inputs)}

# def test_input_gen():
#     x0 = StrHole('x0')
#     x1 = StrHole('x1')

#     zero = IntConst(0)

#     prog = Substr(x0, zero, Index(x0, x1))
#     env = input_gen(prog)

#     run(prog, env)

x0 = StrHole('x0')
x1 = StrHole('x1')
zero = IntConst(0)
prog = Substr(x0, zero, Index(x0, x1))


@dataclass
class InputStrategy():

    hole_strategies: Dict[Hole, st.SearchStrategy[Any]] = field(
        default_factory=dict, init=False)

    @visitor(StrHole)
    def visit(self, c):
        if c not in self.hole_strategies:
            self.hole_strategies[c] = st.text(
                alphabet=string.ascii_lowercase, min_size=1, max_size=10)
        return st.shared(self.hole_strategies[c], key=c.name)

    @visitor(IntHole)
    def visit(self, c):
        if c not in self.hole_strategies:
            self.hole_strategies[c] = st.integers()
        return st.shared(self.hole_strategies[c], key=c.name)

    @visitor(StrConst)
    def visit(self, c):
        return st.just(c.value)

    @visitor(IntConst)
    def visit(self, c):
        return st.just(c.value)

    @visitor(Concat)
    def visit(self, c):
        x, y = visit_all(self, c)
        return st.tuples(x, y)

    @visitor(Index)
    def visit(self, c):
        @st.composite
        def strat(draw):
            x, y = visit_all(self, c)
            assume(draw(y) in draw(x))
            return draw(st.tuples(x, y))

        return strat()

    @visitor(Length)
    def visit(self, c):
        return next(visit_all(self, c))

    @visitor(Replace)
    def visit(self, c):
        text, old, new = visit_all(self, c)
        return st.tuples(text, old, new)

    @visitor(Substr)
    def visit(self, c):
        @st.composite
        def strat(draw):
            text, i, j = visit_all(self, c)
            assume(0 <= draw(i) <= draw(j) <= len(draw(text)) - 1)
            return draw(st.tuples(text, i, j))

        return strat()


input_strategy = lambda prog: InputStrategy().visit(prog)
