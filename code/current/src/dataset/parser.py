from dataclasses import dataclass
from enum import Enum
from typing import *
from parsy import letter, regex, string, seq


@dataclass
class Expr:
    name: str


@dataclass
class Function(Expr):
    args: List[Expr]


class Var(Expr):
    pass


@dataclass
class Const(Expr):
    val: Any


# Lexer (adapted from https://parsy.readthedocs.io/en/latest/howto/other_examples.html)

Token = Enum('Token', 'LPAREN, RPAREN, COMMA')

fname = regex(r'[A-Za-z0-9]+')

whitespace = regex(r'\s*')
lexeme = lambda p: p << whitespace

lparen = lexeme(string('(')).result(Token.LPAREN)
rparen = lexeme(string(')')).result(Token.RPAREN)
comma = lexeme(string(',')).result(Token.COMMA)

until = lambda marker: (string(marker).should_fail("not " + marker) >> letter).many().concat()

# function = seq(fname, parens(args))
# @generate
# def function():
#     name = yield fname
#     yield lparen
#     args_ = yield args
#     yield rparen

expr = function | ()
