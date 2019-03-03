import datetime

from expr_ast import Variable, Literal, KWArg, Func, Unop, Binop, Dot, Indexer
import parsy

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
    return (yield
            binop | paren(expr) | unop | indexer | func | literal | variable)


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
                rhs = yield paren(
                    expr) | unop | indexer | func | literal | variable

                lookahead = yield peek_op
                while lookahead and prec(lookahead) > prec(op):
                    rhs = yield prec_parse(rhs, lvl=prec(lookahead))
                    lookahead = yield peek_op

                nonlocal lhs
                if op == '.':
                    lhs = Dot(left=lhs, right=rhs)
                else:
                    lhs = Binop(name=op, left=lhs, right=rhs)
            return lhs

        return helper

    lhs = yield unop | indexer | func | paren(expr) | literal | variable

    lookahead = (yield peek_op)
    if not lookahead:
        return parsy.fail('binary operator')

    return (yield prec_parse(lhs, lvl=0))


variable = identifier.map(Variable).desc('variable')

literal = number_lit | boolean_lit | string_lit | date_lit | time_lit | datetime_lit

paren = lambda x: (LPAREN >> x << RPAREN).desc('parenthesized expression')

kwarg = parsy.seq(identifier << COLON,
                  expr.optional()).combine(KWArg).desc('kwarg')

func = parsy.seq(identifier, LPAREN >> (kwarg | expr).sep_by(COMMA).map(tuple)
                 << RPAREN).combine(Func).desc('function')

unop = parsy.seq(unary_op, expr).combine(Unop).desc('unary operator')

indexer = parsy.seq(
    func | variable,
    LBRACK >> expr << RBRACK).combine(Indexer).desc('indexed expression')

parse = lambda stream: expr.parse(stream)
parse_partial = lambda stream: expr.parse_partial(stream)


def test_expr():
    # Quote escape
    assert parse('"hello ""friend"""""')

    # Dot
    assert parse('a.b.c')
    assert parse('a  . b.c  ')

    # Indexer
    assert parse('x[0]') == Indexer(Variable('x'), Literal('0'))
    assert parse('f(x)[0]') == Indexer(
        Func('f', (Variable('x'), )), Literal('0'))

    # Dot + Indexer
    assert parse('a[0].b')
    assert parse('a.b[0].c')
    assert parse('a.b.c[0]')
    assert parse('a.b[1].c[0]')

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

    assert parse('a * b + c') == Binop(
        '+', Binop('*', Variable('a'), Variable('b')), Variable('c'))

    assert parse('c + a * b') == Binop(
        '+', Variable('c'), Binop('*', Variable('a'), Variable('b')))

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
