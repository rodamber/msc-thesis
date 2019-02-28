from anytree import DoubleStyle, Node, RenderTree
from collections import deque, namedtuple
from enum import Enum
from parsy import fail, generate, match_item, Parser, Result, test_item

from lexer import lexer, Token, Var, String, Number, Keyword, Op


def except_(*items):
    @generate
    def parser():
        func = lambda y: y not in items
        desc = 'anything but any of \'{}\''.format(items)
        return (yield test_item(func, desc))

    return parser


@Parser
def peek(stream, index):
    try:
        return Result.success(index, stream[index])
    except:
        return Result.success(index, None)


any_ = test_item(lambda _: True, 'anything')

# TODO Careful: check if this doesn't override anything in the lexer module.
lparen = match_item('(')
rparen = match_item(')')
comma = match_item(',')

token = test_item(lambda x: isinstance(x, Token), 'token')
var = test_item(lambda x: isinstance(x, Var), 'var')
string = test_item(lambda x: isinstance(x, String), 'string')
number = test_item(lambda x: isinstance(x, Number), 'number')
keyword = test_item(lambda x: isinstance(x, Keyword), 'keyword')
op = test_item(lambda x: isinstance(x, Op), 'op')


@generate
def atom():
    return (yield token.map(Node))


@generate
def func():
    name = yield var
    yield lparen
    args = yield expr.sep_by(comma)
    yield rparen
    return Node(name, children=args)


def test_func():
    assert parse_(func, 'Plus(1, 2)')
    assert parse_(func, 'Concat(\"Hello \", \"world!\")')
    assert parse_(func, 'Concat(Concat(\"Hello\", \" \"), \"world!\")')
    assert parse_(func, 'Plus(1, -2)')
    assert parse_(func, 'Plus(1, 2 * 3)')


@generate
def unop():
    name = yield op | keyword

    if name.val in ['-', 'not']:
        child = yield expr
        return Node(name, children=[child])
    else:
        return fail("unary op must be 'not'")


def test_unop():
    assert parse_(unop, '-x')
    assert parse_(unop, 'not true')


# FIXME
# [ ] Arbitrary expressions as arguments, not just atoms
# [ ] Keywords ('or', 'and')
@generate
def binop():
    '''
    Implementation of the precedence climbing algorithm for operator-precedence parsing.
    https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
    '''
    Operator = namedtuple('Operator', 'prec assoc')
    Assoc = Enum('Assoc', 'Left Right')

    ops = {
        '*': Operator(3, Assoc.Left),
        '/': Operator(3, Assoc.Left),
        '+': Operator(2, Assoc.Left),
        '-': Operator(2, Assoc.Left),
    }

    def prec(op):
        return ops[op.val].prec

    def assoc(op):
        return ops[op.val].assoc

    parse_primary = expr  # FIXME

    def prec_parse(lhs, lvl):
        @generate
        def helper():
            lookahead = yield peek

            while isinstance(lookahead, Op) and prec(lookahead) >= lvl:
                op = lookahead
                yield any_  # advance to the next token
                rhs = yield parse_primary
                lookahead = yield peek

                while lookahead and isinstance(lookahead, Op) and \
                      (prec(lookahead) > prec(op) or \
                       assoc(lookahead) == Assoc.Right and prec(lookahead) == prec(op)):
                    rhs = yield prec_parse(rhs, lvl=prec(lookahead))
                    lookahead = yield peek

                nonlocal lhs
                lhs = Node(op, children=[lhs, rhs])
            return lhs

        return helper

    lhs = yield (paren | func | unop | atom)
    return (yield prec_parse(lhs, lvl=0))


def test_binop_unary():
    assert parse_(binop, 'x')
    assert parse_(binop, '-x')


def test_binop_simple():
    assert parse_(binop, 'x + y')
    assert parse_(binop, 'x + (y)')
    assert parse_(binop, 'x * (-y)')


def test_binop_complex():
    assert parse_(binop, '1 + 1 / n + n')


@generate
def paren():
    yield lparen
    res = expr
    yield rparen

    return res


@generate
def expr():
    return (yield paren | func | binop | unop | atom)


def test_expr():
    assert parse_(expr, 'Plus(1, 2)')
    assert parse_(expr, 'Concat(\"Hello \", \"world!\")')
    assert parse_(expr, 'Concat(Concat(\"Hello\", \" \"), \"world!\")')
    assert parse_(expr, 'Plus(1, -2)')
    assert parse_(expr, 'Plus(1, 2 * 3)')
    assert parse_(expr, 'x + y')
    # assert parse_(expr, 'x + (y)')
    # assert parse_(expr, 'x * (-y)')
    # assert parse_(expr, '1 + 1 / n + n')
    # assert parse_(expr, '-x')
    # assert parse_(expr, 'not true')


parse_ = lambda p, x: p.parse(lexer.parse(x))


def pt(tree):
    for pre, _, node in RenderTree(tree, style=DoubleStyle):
        print('%s%s' % (pre, node.name))
