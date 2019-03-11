from enum import Enum

import pyrsistent as p
from toolz import curry

from .. import tree
from ..tree import children, tag

Expr = Enum('Expr', 'Var, Lit, Func, KwArg')


class ASTRec(p.PRecord):
    expr = p.field(mandatory=True, type=Expr)
    val = p.field(mandatory=True)
    type = p.field(mandatory=False, initial=None)


ast = curry(lambda expr, val, *children:
            tree.tree(ASTRec(expr=expr, val=val), *children))

# XXX
typed_ast = curry(lambda expr, val, type_, *children:
                  tree.tree(ASTRec(expr=expr, val=val, type=type_), *children))

expr = lambda ast: tag(ast).expr
val = lambda ast: tag(ast).val
type_ = lambda ast: tag(ast).type
children = tree.children

var = ast(Expr.Var)
typed_var = curry(lambda ty, val: typed_ast(Expr.Var, val, ty))

lit = ast(Expr.Lit)
typed_lit = curry(lambda ty, val: typed_ast(Expr.Lit, val, ty))

_ref = curry(lambda t, x, *ys: ast(t, x, *ys))

func = _ref(Expr.Func)
typed_func = lambda ty, t, x, *ys: typed_ast(t, x, ty, *ys)

kwarg = _ref(Expr.KwArg)
typed_kwarg = lambda ty, t, x, *ys: typed_ast(t, x, ty, *ys)

dot = lambda *ys: func('.', *ys)
indexer = lambda *ys: func('[]', *ys)

render = tree.render
ast2anynode = tree.tree2anynode


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
