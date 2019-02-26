from dataclasses import dataclass
from enum import Enum
from typing import *
from parsy import *


@dataclass
class Expr:
    pass


@dataclass
class Function(Expr):
    name: str
    args: List[Expr]


class Var(Expr):
    pass


@dataclass
class Const(Expr):
    val: Any


# @generate
# def function():
#     name = yield identifier << lparen
#     args = yield expr.sep_by(comma) << rparen
#     return Function(name=name, args=args)
