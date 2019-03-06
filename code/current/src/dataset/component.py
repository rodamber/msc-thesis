from dataclasses import dataclass
from typing import Any, Callable, Tuple, Union

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


class Const(Component):
    pass


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
    input_src: Callable[[Hole], Any]

    @visitor(Hole)
    def visit(self, c):
        return self.input_src(c)

    @visitor(Const)
    def visit(self, c):
        return c.slots[0]

    @visitor(Concat)
    def visit(self, c):
        x, y = visit_all(self, c)
        return x + y

    @visitor(Index)
    def visit(self, c):
        text, s = visit_all(self, c)
        return text.find(s)

    @visitor(Length)
    def visit(self, c):
        x = visit_all(self, c)
        return len(x)

    @visitor(Replace)
    def visit(self, c):
        text, old, new = visit_all(self, c)
        return text.replace(old, new)

    @visitor(Substr)
    def visit(self, c):
        text, i, j = visit_all(self, c)
        return text[i:j]


def run(prog, input_source):
    return Run(input_source).visit(prog)


# We want the following:
#
# x0 = Hole('x0', str)
# x1 = Hole('x1', int)
#
# dot = Literal('.')
#
# index = Component(domain=(str, str), ret_type=int, run=...)
# substr = Component(domain=(str, int, int), ret_type=str, run=...)
#
# program = substr(x0, x1, index(x0, dot))
# program('google.com', 0) == 'google'

# TODO It would be nice to write new components like this:
# substr = Component('Substr', domain, impl)

# @dataclass
# class Component(ABC):
#     domain: Tuple[Type, ...] = field(init=False)
#     ret_type: Type = field(init=False)

#     # TODO Maybe include return type checks?
#     def typecheck(self, *args):
#         for arg, type_ in zip(args, self.domain):
#             assert isinstance(arg, Component)  # FIXME exception?
#             assert arg.ret_type == type_

#     @abstractmethod
#     def __call__(self, *args):
#         self.typecheck(*args)
#         assert len(args) == len(self.domain)  # FIXME exception?

# @dataclass
# class Literal(Component):
#     value: Any  # FIXME TypeVar?

#     def __post_init__(self):
#         self.domain = ()
#         self.ret_type = type(self.value)

#     def __call__(self):
#         return self.value

# period = Literal('.')
# slash = Literal('/')
# dash = Literal('-')
# underscore = Literal('_')
# at = Literal('@')
# newline = Literal('\n')

# @dataclass
# class Concat(Component):
#     def __post_init__(self):
#         self.domain = (str, str)
#         self.ret_type = str

#     def __call__(self, *args):
#         super().__call__(*args)
#         return args[0]() + args[1]()

# @dataclass
# class Length(Component):
#     def __post_init__(self):
#         self.domain = (str, )
#         self.ret_type = int

#     def __call__(self, *args):
#         super().__call__(*args)
#         return len(args[0]())

# @dataclass
# class Substr(Component):
#     def __post_init__(self):
#         self.domain = (str, int, int)
#         self.ret_type = str

#     def __call__(self, *args):
#         super().__call__(*args)
#         text, i, j = args
#         return text()[i():j()]

# @dataclass
# class Replace(Component):
#     def __post_init__(self):
#         self.domain = (str, str, str)
#         self.ret_type = str

#     def __call__(self, *args):
#         super().__call__(*args)
#         text, old, new = args
#         return text().replace(old(), new())

# # TODO Support for optional arguments
# @dataclass
# class Index(Component):
#     def __post_init__(self):
#         self.domain = (str, str)
#         self.ret_type = int

#     def __call__(self, *args):
#         super().__call__(*args)
#         text, s = args
#         return text().find(s())
