from abc import ABC, abstractmethod
import anytree
from dataclasses import dataclass
import datetime
import parsy

from typing import *


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


class Dot(Binop):
    pass


class Indexer(Binop):
    pass


# Lexemes
whitespace = parsy.regex(r'\s*')


def lexeme(p):
    if isinstance(p, str):
        p = parsy.string(p)
    return p << whitespace


def test_lexeme():
    assert lexeme('abc').parse_partial('abc  def') == ('abc', 'def')


LPAREN = lexeme('(')
RPAREN = lexeme(')')
LBRACK = lexeme('[')
RBRACK = lexeme(']')
COMMA = lexeme(',')
DOT = lexeme('.')
COLON = lexeme(':')
POUND = lexeme('#')
DASH = lexeme('-')

# Identifier
identifier = lexeme(parsy.regex(r'[_A-Za-z][_A-Za-z0-9]*')).desc('identifier')

# Number
number_lit = lexeme(
    parsy.regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).map(
        Literal).desc('number')

# Boolean
boolean_lit = (lexeme('true')
               | lexeme('false')).map(bool).map(Literal).desc('boolean')

# String
string_part = parsy.regex(r'[^"]+')
string_esc = parsy.string('""').result('"')
string_lit = (
    parsy.string('"') >>
    (string_part
     | string_esc).many().concat() << lexeme('"')).map(Literal).desc('string')


def test_string_lit():
    assert string_lit.parse('"hello"')


# Date and Time
def datetime_helper(digit_num, desc):
    return parsy.regex(f'[0-9]{{{digit_num}}}').map(int).desc(
        f'{digit_num} digit {desc}')


year = datetime_helper(4, 'year')
month = datetime_helper(2, 'month')
day = datetime_helper(2, 'day')
hour = datetime_helper(2, 'hour')
minute = datetime_helper(2, 'minute')
second = datetime_helper(2, 'second')

date_lit = parsy.seq(POUND >> year, DASH >> month << DASH,
                     day << POUND).combine(
                         datetime.date).map(Literal).desc('date')
time_lit = parsy.seq(POUND >> hour, COLON >> minute << COLON,
                     second << POUND).combine(
                         datetime.time).map(Literal).desc('time')
datetime_lit = parsy.seq(POUND >> year, DASH >> month << DASH, lexeme(day),
                         hour, COLON >> minute << COLON,
                         second << POUND).combine(
                             datetime.datetime).map(Literal).desc('datetime')


def test_dates():
    assert date_lit.parse('#1988-08-28#')
    assert time_lit.parse('#12:20:56#')
    assert datetime_lit.parse('#1988-08-28 23:59:59#')


# Operators
op_prec_table = {
    '[]': 10,
    '.': 9,
    'not': 8,
    '*': 7,
    '/': 7,
    '+': 6,
    '-': 6,
    '<': 5,
    '>': 5,
    '<=': 5,
    '>=': 5,
    '=': 4,
    '<>': 4,
    'and': 2,
    'or': 1,
}
prec = lambda op: op_prec_table[op]

operator = lexeme(parsy.string_from(*op_prec_table))

unary_op_list = ['-', 'not']
unary_op = lexeme(parsy.string_from(*unary_op_list))

symbol_op_list = [
    '[]', '.', '+', '-', '*', '/', '=', '<>', '>', '<', '>=', '<='
]
ascii_op_list = ['and', 'or', 'not']


def test_op_table():
    assert set(symbol_op_list) | set(ascii_op_list) == set(op_prec_table)
    assert set(unary_op_list) < set(op_prec_table)


# Parser
@parsy.generate
def expr():
    yield whitespace
    return (yield binop | paren | unop | func | literal | variable)


@parsy.Parser
def peek_op(stream, index):
    try:
        res, _ = operator.parse_partial(stream[index:])
        return parsy.Result.success(index, res)
    except parsy.ParseError:
        return parsy.Result.success(index, None)


@parsy.generate
def binop():
    def prec_parse(lhs, lvl):
        @parsy.generate
        def helper():
            lookahead = yield peek_op

            while lookahead and prec(lookahead) >= lvl:
                op = yield operator
                rhs = yield expr

                lookahead = yield peek_op
                while lookahead and prec(lookahead) > prec(op):
                    rhs = yield prec_parse(rhs, lvl=prec(lookahead))
                    lookahead = yield peek_op

                nonlocal lhs
                lhs = Binop(name=op, left=lhs, right=rhs)
            return lhs

        return helper

    lhs = yield unop | func | paren | literal | variable

    lookahead = (yield peek_op)
    if not lookahead:
        return parsy.fail('binary operator')

    return (yield prec_parse(lhs, lvl=0))


indexer = (LBRACK >> expr << RBRACK)


@parsy.generate('variable')
def variable():
    var = yield identifier.map(Variable)
    ix = yield indexer.optional()

    return Indexer(name='[]', left=var, right=ix) if ix else var


literal = number_lit | boolean_lit | string_lit | date_lit | time_lit | datetime_lit

paren = (LPAREN >> expr << RPAREN)  #.desc('parenthesized expression')

kwarg = parsy.seq(identifier << COLON,
                  expr.optional()).combine(KWArg)  #.desc('kwarg')

func = parsy.seq(identifier,
                 LPAREN >> (kwarg | expr).sep_by(COMMA) << RPAREN).combine(
                     Func)  #.desc('function')

unop = parsy.seq(unary_op, expr).combine(Unop)  #.desc('unary operator')

parse = lambda stream: expr.parse(stream)
parse_partial = lambda stream: expr.parse_partial(stream)
