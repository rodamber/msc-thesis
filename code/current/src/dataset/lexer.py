from dataclasses import dataclass
from parsy import char_from, generate, regex, string, string_from, whitespace
from typing import Any


@dataclass
class Token():
    val: Any


class Var(Token):
    pass


class String(Token):
    pass


class Number(Token):
    pass


class Op(Token):
    pass


lexeme = lambda p: p << whitespace.optional()

identifier = lexeme(
    regex(r'[_A-Za-z][_A-Za-z0-9]*')).desc('identifier').map(Var)
number = lexeme(regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).desc(
    'number').map(Number)

lparen = lexeme(string('('))
rparen = lexeme(string(')'))

comma = lexeme(string(','))
dot = lexeme(string('.'))

op = lexeme(
    string_from('+', '-', '*', '/', '=', '<>', '>', '<', '>=', '<=', 'not',
                'or', 'and')).map(Op)

string_part = regex(r'[^"]+')
string_esc = string("\"\"").result('"')


@generate
def quoted():
    yield string('"')
    val = yield (string_part | string_esc).many().concat()
    yield string('"') << whitespace.optional()
    return String(val)


@generate
def dotted():
    base = (yield identifier).val
    field = (yield (dot + dotted.map(lambda t: t.val)).optional()) or ''
    return Var(base + field)


lexer = whitespace.optional() >> (quoted | number | op | dotted | lparen
                                  | rparen | comma).many()
