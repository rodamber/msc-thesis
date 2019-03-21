import pyrsistent as p
from toolz import interpose

from . import expr_ast as ast


def render(tree):
    children = ast.children(tree).transform([p.ny], render)

    if ast.expr(tree) == ast.Expr.Var:
        return str(ast.val(tree))
    if ast.expr(tree) == ast.Expr.Lit:
        return repr(ast.val(tree)).replace("'", '"')  # XXX
    if ast.expr(tree) == ast.Expr.Func:
        return ast.val(tree) + '(' + ', '.join(children) + ')'
    if ast.expr(tree) == ast.Expr.KwArg:
        return ast.val(tree) + ': ' + children[0]


def test_render():
    from .parser import parse

    test_cases = ('x', 'f(x)', '0', '"hello"', 'f(kwarg: 0, x)',
                  'f(f(x, y), z)')

    for case in test_cases:
        assert render(parse(case)) == case
