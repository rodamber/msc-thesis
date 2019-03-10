import datetime
import sys

import jsonlines
import parsy

from ..outsystems import expr_ast as ast
from ..utils import LineError

# Lexemes
whitespace = parsy.regex(r'\s*')


def lexeme(p):
    if isinstance(p, str):
        p = parsy.string(p)
    return p << whitespace


LPAREN = lexeme('(')
RPAREN = lexeme(')')
LBRACK = lexeme('[')
RBRACK = lexeme(']')
COMMA = lexeme(',')
DOT = lexeme('.')
COLON = lexeme(':')
POUND = lexeme('#')
DASH = lexeme('-')

# Literals

# Identifier
identifier = lexeme(parsy.regex(r'[_A-Za-z][_A-Za-z0-9]*')).desc('identifier')

# Number
number_lit = lexeme(
    parsy.regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).map(
        ast.lit).desc('number')

# Boolean
boolean_lit = (lexeme('true')
               | lexeme('false')).map(bool).map(ast.lit).desc('boolean')

# String
string_part = parsy.regex(r'[^"]+')
string_esc = parsy.string('""').result('"')
string_lit = (parsy.string('"') >>
              (string_part
               | string_esc).many().concat() << lexeme('"')).map(
                   ast.lit).desc('string')


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
                     day << POUND).combine(datetime.date).map(
                         ast.lit).desc('date')
time_lit = parsy.seq(POUND >> hour, COLON >> minute << COLON,
                     second << POUND).combine(datetime.time).map(
                         ast.lit).desc('time')
datetime_lit = parsy.seq(POUND >> year, DASH >> month << DASH, lexeme(day),
                         hour, COLON >> minute << COLON,
                         second << POUND).combine(datetime.datetime).map(
                             ast.lit).desc('datetime')

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


# Parser helper combinators
def peek(parser):
    @parsy.Parser
    def helper(stream, index):
        try:
            res, _ = operator.parse_partial(stream[index:])
            return parsy.Result.success(index, res)
        except parsy.ParseError:
            return parsy.Result.success(index, None)

    return helper


# Parser
@parsy.generate
def expr():
    yield whitespace
    return (yield
            binop | paren(expr) | unop | indexer | func | literal | variable)


@parsy.generate
def binop():
    def prec_parse(lhs, lvl):
        @parsy.generate
        def helper():
            lookahead = yield peek(operator)

            while lookahead and prec(lookahead) >= lvl:
                op = yield operator
                rhs = yield indexer | func | unop | paren(
                    expr) | literal | variable

                lookahead = yield peek(operator)
                while lookahead and prec(lookahead) > prec(op):
                    rhs = yield prec_parse(rhs, lvl=prec(lookahead))
                    lookahead = yield peek(operator)

                nonlocal lhs
                if op == '.':
                    lhs = ast.dot(lhs, rhs)
                else:
                    lhs = ast.func(op, lhs, rhs)

            return lhs

        return helper

    lhs = yield indexer | func | unop | paren(expr) | literal | variable

    if not (yield peek(operator)):
        return parsy.fail('binary operator')

    return (yield prec_parse(lhs, lvl=0))


variable = identifier.map(ast.var).desc('variable')

literal = number_lit | boolean_lit | string_lit | date_lit | time_lit | datetime_lit

paren = lambda x: (LPAREN >> x << RPAREN).desc('parenthesized expression')

kwarg = parsy.seq(identifier << COLON,
                  expr.optional()).combine(ast.kwarg).desc('kwarg')

func = parsy.seq(
    identifier, LPAREN >> (kwarg | expr).sep_by(COMMA) <<
    RPAREN).combine(lambda x, ys: ast.func(x, *ys)).desc('function')

unop = parsy.seq(unary_op, expr).combine(ast.func).desc('unary operator')

indexer = parsy.seq(func | variable, LBRACK >> expr << RBRACK).combine(
    ast.indexer).desc('indexed expression')

parse = lambda stream: expr.parse(stream)
parse_partial = lambda stream: expr.parse_partial(stream)


def test_expr():
    # Lexeme
    assert lexeme('abc').parse_partial('abc  def') == ('abc', 'def')

    # Quote escape
    assert parse('"hello ""friend"""') == ast.lit('hello "friend"')

    # Date and Time
    assert date_lit.parse('#1988-08-28#')
    assert time_lit.parse('#12:20:56#')
    assert datetime_lit.parse('#1988-08-28 23:59:59#')

    # Operator table
    assert set(symbol_op_list) | set(ascii_op_list) == set(op_prec_table)
    assert set(unary_op_list) < set(op_prec_table)

    # ast.lit
    assert parse('0') == ast.lit('0')

    # ast.dot
    assert parse('a.b.c') == ast.dot(
        ast.dot(ast.var('a'), ast.var('b')), ast.var('c'))
    assert parse('a(x).b.c') == ast.dot(
        ast.dot(ast.func('a', ast.var('x')), ast.var('b')), ast.var('c'))

    # ast.indexer
    assert parse('x[0]') == ast.indexer(ast.var('x'), ast.lit('0'))
    assert parse('f(x)[0]') == ast.indexer(
        ast.func('f', ast.var('x')), ast.lit('0'))

    # ast.Dot + ast.Indexer
    assert parse('a[0].b')
    assert parse('a.b()[0].c')
    assert parse('a.b.c[0]')
    assert parse('a(x).b[1].c()[0]')

    assert parse('f()')
    assert parse('f(1, 2)')
    assert parse('f("Hello ", "world!")')
    assert parse('f(f("Hello", " "), "world!")')
    assert parse('f(1, -2)')
    assert parse('f(1, 2 * 3)')

    assert parse('-x')
    assert parse('not true')

    assert parse('x + y')
    assert parse('x + (y)')
    assert parse('(x) + (y)')
    assert parse('(x) + y')
    assert parse('x * (-y)')

    assert parse('a * b + c') == ast.func(
        '+', ast.func('*', ast.var('a'), ast.var('b')), ast.var('c'))

    assert parse('c + a * b') == ast.func(
        '+', ast.var('c'), ast.func('*', ast.var('a'), ast.var('b')))

    assert parse('1 + 1 / n + n')
    assert parse('f(x) + 1')
    assert parse('f(x) + 1 - 2')
    assert parse('f(x) + 1 -2')

    x = 'f(g(h(a.b.c.d.e)/1000-60*f(a.b.c.d.e/60000),3,"."," "),6,6,True,"0")'
    assert parse(x)

    x = 'a(b(c.d.e.f.g) >= 236, h(i.j.k.l.m, 0, 230), n.o.p.q.r)'
    assert parse(x)

    assert parse('(x - 1)')
    assert parse('(x - (1))')
    assert parse('(x) - 1')

    assert parse('f((g(x)-1)/7)')
    assert parse('f(g(x) + "abc" + "def")')
    assert parse('((x) + 1)')
    assert parse('(f(x))')
    assert parse('f((x))')

    assert parse('f(x)[0]')
    assert parse('f(x)[0].c')
    assert parse('f(x).b[0].c')
    assert parse('h(g(f(x).b[0]).c)[i(j)]')


def _test_dataset():
    # Track how many recursion error we get
    recursion_errors_count = 0

    with jsonlines.open('dataset/__exprs.jsonl') as reader:
        for line, obj in enumerate(reader, 1):
            try:
                parse(obj['text'])
            except RecursionError:
                recursion_errors_count += 1
            except Exception as e:
                raise LineError(line) from e

    print(f'Got {recursion_errors_count} recursion errors', file=sys.stderr)
