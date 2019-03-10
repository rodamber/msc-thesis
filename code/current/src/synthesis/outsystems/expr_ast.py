from enum import Enum

import pyrsistent as p
from toolz import curry

from ..tree import tree

Expr = Enum('Expr', 'Var, Lit, Func, KwArg')


class ASTRec(p.PRecord):
    expr = p.field(mandatory=True, type=Expr)
    val = p.field(mandatory=True, initial=None)  # type=optional[str]
    type = p.field(mandatory=True, initial=None)  # type=optional[type]


@curry
def ast(expr, val, children=p.pvector()):
    return tree(ASTRec(expr=expr, val=val), children=children)


var = ast(Expr.Var)
lit = ast(Expr.Lit)

_ref = curry(lambda t, x, *ys: ast(t, x, p.pvector(ys)))

func = _ref(Expr.Func)
kwarg = _ref(Expr.KwArg)

dot = lambda *ys: func('.', *ys)
indexer = lambda *ys: func('[]', *ys)


def test_ast():
    x = var('x')
    y = var('y')
    z = var('z')

    xy = func('*', x, y)
    kw = func('substr', kwarg('str', z), x, y)
    d = dot(xy, y)
    dd = dot(d, x)
    i = indexer(x, y)
