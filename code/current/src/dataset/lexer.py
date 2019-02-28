from dataclasses import dataclass
from parsy import alt, char_from, generate, regex, string, string_from
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


class Keyword(Token):
    pass


class Op(Token):
    pass


whitespace = regex(r'\s*')
lexeme = lambda p: p << whitespace

identifier = lexeme(
    regex(r'[_A-Za-z][_A-Za-z0-9]*')).desc('identifier').map(Var)
number = lexeme(regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).desc(
    'number').map(Number)

lparen = lexeme(string('('))
rparen = lexeme(string(')'))

comma = lexeme(string(','))
dot = lexeme(string('.'))

op = lexeme(char_from('+-*/=')).map(Op)
keyword = lexeme(string_from('not', 'or', 'and') << char_from(' ')).map(
    Keyword)

string_part = regex(r'[^"\\]+')
string_esc = string('\\') >> (
    string('\\')
    | string('/')
    | string('"')
    | string('b').result('\b')
    | string('f').result('\f')
    | string('n').result('\n')
    | string('r').result('\r')
    | string('t').result('\t')
    | regex(r'u[0-9a-fA-F]{4}').map(lambda s: chr(int(s[1:], 16))))


@generate
def quoted():
    yield string('"')
    val = yield (string_part | string_esc).many().concat()
    yield string('"') << whitespace
    return String(val)


def test_quoted():
    assert quoted.parse('\"hello\"')


@generate
def dotted():
    base = (yield identifier).val
    field = (yield (dot + dotted.map(lambda t: t.val)).optional()) or ''
    return Var(base + field)


def test_dotted():
    assert dotted.parse('this.should.succeed')
    assert dotted.parse('this  . should.succeed  ')


lexer = alt(quoted, number, keyword, dotted, lparen, rparen, comma, op).many()
