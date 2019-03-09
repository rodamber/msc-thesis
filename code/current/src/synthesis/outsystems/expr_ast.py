from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import *

import anytree

from ..utils import ilen

# FIXME: It seems like having only functions, kwargs, variables and literals
# would make the code much simpler.

# FIXME: Dot and Indexer should be Binops


# Parse Tree
class Expr(ABC):
    @abstractmethod
    def __init__(self):
        pass

    @abstractmethod
    def _to_anytree(self):
        pass

    def __str__(self):
        return '\n'.join([
            f"{pre}{node.simple}"
            for pre, _, node in anytree.RenderTree(self._to_anytree())
        ])

    @abstractmethod
    def __repr__(self):
        pass

    def height(self):
        return self._to_anytree().height

    def size(self):
        node = self._to_anytree()

        if not node.descendants:
            return 0
        else:
            return 1 + ilen(filter(lambda d: not d.is_leaf, node.descendants))


@dataclass(frozen=True)
class Variable(Expr):
    name: str

    def _to_anytree(self):
        return anytree.Node(self, simple=self.name)


@dataclass(frozen=True)
class Literal(Expr):
    value: Any  # FIXME: Subclass this into string, number, date, etc.

    def _to_anytree(self):
        return anytree.Node(self, simple=self.value)


@dataclass(frozen=True)
class KWArg(Expr):
    keyword: str
    arg: Optional[Expr]

    def _to_anytree(self):
        c = [self.arg._to_anytree()] if self.arg else ()
        return anytree.Node(self, children=c, simple=self.keyword)


@dataclass(frozen=True)
class Func(Expr):
    name: str
    parameters: Tuple[Union[Expr, KWArg], ...]

    def _to_anytree(self):
        c = [p._to_anytree() for p in self.parameters]
        return anytree.Node(self, children=c, simple=self.name)


@dataclass(frozen=True)
class Unop(Expr):
    name: str
    parameter: Expr

    def _to_anytree(self):
        c = [self.parameter._to_anytree()]
        return anytree.Node(self, children=c, simple=self.name)


@dataclass(frozen=True)
class Binop(Expr):
    name: str
    left: Expr
    right: Expr

    def _to_anytree(self):
        c = [self.left._to_anytree(), self.right._to_anytree()]
        return anytree.Node(self, children=c, simple=self.name)


# FIXME Binary expression
@dataclass(frozen=True)
class Dot(Expr):
    left: Expr
    right: Expr

    def _to_anytree(self):
        c = [self.left._to_anytree(), self.right._to_anytree()]
        return anytree.Node(self, children=c, simple='.')


# FIXME Binary expression
@dataclass(frozen=True)
class Indexer(Expr):
    list: Expr
    index: Expr

    def _to_anytree(self):
        c = [self.list._to_anytree(), self.index._to_anytree()]
        return anytree.Node(self, children=c, simple='[]')
