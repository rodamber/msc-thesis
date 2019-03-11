from enum import Enum

import pyrsistent as p
from toolz import curry

from .. import tree
from ..tree import children, tag

Expr = Enum('Expr', 'Var, Lit, Func, KwArg')


class ASTRec(p.PRecord):
    expr = p.field(mandatory=True, type=Expr)
    val = p.field(mandatory=True, initial=None)  # type=optional[str]


ast = curry(lambda expr, val, *children:
            tree.tree(ASTRec(expr=expr, val=val), *children))

expr = lambda ast: tag(ast).expr
val = lambda ast: tag(ast).val
children = tree.children

var = ast(Expr.Var)
lit = ast(Expr.Lit)

_ref = curry(lambda t, x, *ys: ast(t, x, *ys))

func = _ref(Expr.Func)
kwarg = _ref(Expr.KwArg)

dot = lambda *ys: func('.', *ys)
indexer = lambda *ys: func('[]', *ys)

render = tree.render


def test_ast():
    x = var('x')
    y = var('y')
    z = var('z')

    xy = func('*', x, y)
    kw = func('substr', kwarg('str', z), x, y)
    d = dot(xy, y)
    dd = dot(d, x)
    i = indexer(x, y)

    assert all(isinstance(t, tree.Tree) for t in (x, y, z, xy, kw, d, dd, i))
