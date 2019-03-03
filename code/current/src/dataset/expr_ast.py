from abc import ABC, abstractmethod
from dataclasses import dataclass
import datetime
from typing import *

import anytree


# Parse Tree
class Node(ABC):
    @abstractmethod
    def to_anytree(self):
        pass

    def render(self):
        for pre, _, node in anytree.RenderTree(self.to_anytree()):
            print(f"{pre}{node.name}")


@dataclass
class Variable(Node):
    name: str

    def to_anytree(self):
        return anytree.Node(self.name, tag=type(self).__name__)


@dataclass
class Literal(Node):
    value: Any

    def to_anytree(self):
        return anytree.Node(self.value, tag=type(self).__name__)


@dataclass
class KWArg(Node):
    keyword: str
    arg: Optional[Node]

    def to_anytree(self):
        c = [self.arg.to_anytree()] if self.arg else ()
        return anytree.Node(self.keyword, children=c, tag=type(self).__name__)


@dataclass
class Func(Node):
    name: str
    parameters: List[Union[Node, KWArg]]

    def to_anytree(self):
        c = [p.to_anytree() for p in self.parameters]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass
class Unop(Node):
    name: str
    parameter: Node

    def to_anytree(self):
        c = [self.parameter.to_anytree()]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


@dataclass
class Binop(Node):
    name: str
    left: Node
    right: Node

    def to_anytree(self):
        c = [self.left.to_anytree(), self.right.to_anytree()]
        return anytree.Node(self.name, children=c, tag=type(self).__name__)


class Indexer(Binop):
    pass
