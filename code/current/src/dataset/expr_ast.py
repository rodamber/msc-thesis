from abc import ABC, abstractmethod
from dataclasses import dataclass
import datetime
from typing import *

import anytree


# Parse Tree
class Expr(ABC):
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

    def to_anytree(self):
        return anytree.Node(self.name, tag=type(self).__name__)


@dataclass(frozen=True)
class Literal(Expr):
    value: Any

    def to_anytree(self):
        return anytree.Node(self.value, tag=type(self).__name__)


@dataclass(frozen=True)
class KWArg(Expr):
    keyword: str
    arg: Optional[Expr]

    def to_anytree(self):
        c = [self.arg.to_anytree()] if self.arg else ()
        return anytree.Node(self.keyword, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Func(Expr):
    name: str
    parameters: List[Union[Expr, KWArg]]

    def to_anytree(self):
        c = [p.to_anytree() for p in self.parameters]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Unop(Expr):
    name: str
    parameter: Expr

    def to_anytree(self):
        c = [self.parameter.to_anytree()]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Binop(Expr):
    name: str
    left: Expr
    right: Expr

    def to_anytree(self):
        c = [self.left.to_anytree(), self.right.to_anytree()]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Dot(Expr):
    left: Expr
    right: Expr

    def to_anytree(self):
        c = [self.left.to_anytree(), self.right.to_anytree()]
        return anytree.Node('.', children=c, tag=type(self).__name__)


@dataclass(frozen=True)
class Indexer(Expr):
    list: Expr
    index: Expr

    def to_anytree(self):
        c = [self.list.to_anytree(), self.index.to_anytree()]
        return anytree.Node('[]', children=c, tag=type(self).__name__)
