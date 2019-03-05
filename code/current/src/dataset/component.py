from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Type, TypeVar, Generic

import expr_ast

# TODO It would be nice to write new components like this:
# substr = Component('Substr', domain, impl)

T = TypeVar('T')


@dataclass
class Component(ABC):  # FIXME Generics
    domain: Tuple[Type, ...] = field(init=False)
    ret_type: Type = field(init=False)

    # TODO Maybe include return type checks?
    def typecheck(self, *args):
        for arg, type_ in zip(args, self.domain):
            assert isinstance(arg, Component)  # FIXME exception?
            assert arg.ret_type == type_

    @abstractmethod
    def __call__(self, *args):
        self.typecheck(*args)
        assert len(args) == len(self.domain)  # FIXME exception?


@dataclass
class Literal(Component):
    value: Any  # FIXME TypeVar?

    def __post_init__(self):
        self.domain = ()
        self.ret_type = type(self.value)

    def __call__(self):
        return self.value


period = Literal('.')
slash = Literal('/')
dash = Literal('-')
underscore = Literal('_')
at = Literal('@')
newline = Literal('\n')


@dataclass
class Concat(Component):
    def __post_init__(self):
        self.domain = (str, str)
        self.ret_type = str

    def __call__(self, *args):
        super().__call__(*args)
        return args[0]() + args[1]()


@dataclass
class Length(Component):
    def __post_init__(self):
        self.domain = (str, )
        self.ret_type = int

    def __call__(self, *args):
        super().__call__(*args)
        return len(args[0]())


@dataclass
class Substr(Component):
    def __post_init__(self):
        self.domain = (str, int, int)
        self.ret_type = str

    def __call__(self, *args):
        super().__call__(*args)
        text, i, j = args
        return text()[i():j()]


@dataclass
class Replace(Component):
    def __post_init__(self):
        self.domain = (str, str, str)
        self.ret_type = str

    def __call__(self, *args):
        super().__call__(*args)
        text, old, new = args
        return text().replace(old(), new())


# TODO Support for optional arguments
@dataclass
class Index(Component):
    def __post_init__(self):
        self.domain = (str, str)
        self.ret_type = int

    def __call__(self, *args):
        super().__call__(*args)
        text, s = args
        return text().find(s())
