import pyrsistent as p

from ..outsystems import expr_ast as ast
from ..utils import fresh_gen
from .parser import parse


def templatify(tree):
    fresh = fresh_gen()
    variables = {}

    def helper(tree):
        if ast.expr(tree) == ast.Expr.Var or \
           (ast.expr(tree) == ast.Expr.Func and ast.val(tree) in ['.', '[]']):
            if tree not in variables:
                variables[tree] = next(fresh)
            return ast.var(variables[tree])

        children = ast.children(tree).transform([p.ny], helper)
        return tree.set('children', children)

    return helper(tree)


def test_templatify():
    def helper(test, expected):
        # from ..tree import Tree
        # assert isinstance(parse(test), Tree)
        assert templatify(parse(test)) == expected

    helper('a.c[0] + b', ast.func('+', ast.var('x0'), ast.var('x1')))
    helper(
        'f(a.c[0] + b, c)',
        ast.func('f', ast.func('+', ast.var('x0'), ast.var('x1')),
                 ast.var('x2')))
    helper(
        'f(a.c[0] + b, -c)',
        ast.func('f', ast.func('+', ast.var('x0'), ast.var('x1')),
                 ast.func('-', ast.var('x2'))))

    text = 'f(a.c[0] + b, -c)'
    assert templatify(parse(text)) == templatify(parse(text))
    assert templatify(templatify(parse(text))) == templatify(parse(text))
