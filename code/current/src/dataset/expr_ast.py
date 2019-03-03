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
        return len(
            [d for d in self.to_anytree().descendants if not d.is_leaf()])

    def render(self):
        for pre, _, node in anytree.RenderTree(self.to_anytree()):
            print(f"{pre}{node.name}")


@dataclass
class Variable(Expr):
    name: str

    def to_anytree(self):
        return anytree.Expr(self.name, tag=type(self).__name__)


@dataclass
class Literal(Expr):
    value: Any

    def to_anytree(self):
        return anytree.Expr(self.value, tag=type(self).__name__)


@dataclass
class KWArg(Expr):
    keyword: str
    arg: Optional[Expr]

    def to_anytree(self):
        c = [self.arg.to_anytree()] if self.arg else ()
        return anytree.Expr(self.keyword, children=c, tag=type(self).__name__)


@dataclass
class Func(Expr):
    name: str
    parameters: List[Union[Expr, KWArg]]

    def to_anytree(self):
        c = [p.to_anytree() for p in self.parameters]
        return anytree.Expr(self.name, children=c, tag=type(self).__name__)


@dataclass
class Unop(Expr):
    name: str
    parameter: Expr

    def to_anytree(self):
        c = [self.parameter.to_anytree()]
        return anytree.Expr(self.name, children=c, tag=type(self).__name__)


@dataclass
class Binop(Expr):
    name: str
    left: Expr
    right: Expr

    def to_anytree(self):
        c = [self.left.to_anytree(), self.right.to_anytree()]
        return anytree.Expr(self.name, children=c, tag=type(self).__name__)


class Dot(Binop):
    pass


class Indexer(Binop):
    pass
