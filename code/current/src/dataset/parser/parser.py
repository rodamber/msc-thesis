# Basic parser for outsystems expressions.
#
# Notes
# -----
# 1. Does not support indexer declarations.
#
# These are not problems for our use case because (1) we're discarding the
# variables anyway.

from anytree import DoubleStyle, Node, RenderTree
from collections import namedtuple
from enum import Enum
from parsy import fail, generate, match_item, Parser, Result, test_item

from lexer import lex, Token, Var, String, Number, Op, Keyword

any_ = test_item(lambda _: True, 'anything')

lparen = match_item('(')
rparen = match_item(')')
comma = match_item(',')

token = test_item(lambda x: isinstance(x, Token), 'token')
var = test_item(lambda x: isinstance(x, Var), 'var')
# string = test_item(lambda x: isinstance(x, String), 'string')
number = test_item(lambda x: isinstance(x, Number), 'number')
op = test_item(lambda x: isinstance(x, Op), 'op')
keyword = test_item(lambda x: isinstance(x, Keyword), 'keyword')


@Parser
def peek(stream, index):
    try:
        return Result.success(index, stream[index])
    except:
        return Result.success(index, None)


@generate
def atom():
    return (yield token.map(lambda x: Node(x, tag='atom')))


@generate
def func():
    name = yield var
    yield lparen
    args = yield (kwarg | expr).sep_by(comma).optional()
    yield rparen
    return Node(name, children=args, tag='func')


@generate
def kwarg():
    name = yield keyword
    arg = yield expr.optional()
    return Node(name, children=[arg] if arg else (), tag='kwarg')


@generate
def unop():
    name = yield op

    if name.val in ['-', 'not']:
        child = yield expr
        return Node(name, children=[child], tag='unop')
    else:
        return fail("unary op must be 'not'")


@generate
def binop():
    '''
    Implementation of the precedence climbing algorithm for operator-precedence parsing.
    https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
    '''
    Operator = namedtuple('Operator', 'prec assoc')
    Assoc = Enum('Assoc', 'Left Right')

    ops = {
        'not': Operator(8, Assoc.Left),
        '*': Operator(7, Assoc.Left),
        '/': Operator(7, Assoc.Left),
        '+': Operator(6, Assoc.Left),
        '-': Operator(6, Assoc.Left),
        '<': Operator(5, Assoc.Left),
        '>': Operator(5, Assoc.Left),
        '<=': Operator(5, Assoc.Left),
        '>=': Operator(5, Assoc.Left),
        '=': Operator(4, Assoc.Left),
        '<>': Operator(4, Assoc.Left),
        'and': Operator(2, Assoc.Left),
        'or': Operator(1, Assoc.Left),
    }

    def prec(op):
        return ops[op.val].prec

    def assoc(op):
        return ops[op.val].assoc

    def prec_parse(lhs, lvl):
        @generate
        def helper():
            lookahead = yield peek

            while isinstance(lookahead, Op) and prec(lookahead) >= lvl:
                op = lookahead
                yield any_  # advance to the next token
                rhs = yield expr

                lookahead = yield peek
                while lookahead and isinstance(lookahead, Op) and \
                      (prec(lookahead) > prec(op) or \
                       assoc(lookahead) == Assoc.Right and prec(lookahead) == prec(op)):
                    rhs = yield prec_parse(rhs, lvl=prec(lookahead))
                    lookahead = yield peek

                nonlocal lhs
                lhs = Node(op, children=[lhs, rhs], tag='binop')
            return lhs

        return helper

    lhs = yield unop | func | paren | atom

    lookahead = yield peek
    if not isinstance(lookahead, Op):
        return fail('binary operator')

    return (yield prec_parse(lhs, lvl=0))


@generate
def paren():
    yield lparen
    res = yield expr
    yield rparen

    return res


@generate
def expr():
    return (yield binop | paren | unop | func | atom)


def parse(stream):
    tks = lex(stream)
    return expr.parse(tks)


def parse_partial(stream):
    tks = lex(stream)
    return expr.parse_partial(tks)


def pt(tree):
    for pre, _, node in RenderTree(tree, style=DoubleStyle):
        print('%s%s (%s)' % (pre, node.name.val, node.tag))
