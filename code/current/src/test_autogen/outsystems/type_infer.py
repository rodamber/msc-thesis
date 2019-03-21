# FIXME Not yet implemented.

from enum import Enum

import pyrsistent as p

from ..outsystems import expr_ast as ast
from .api import Function, build

# OutSystems type
OSType = Enum('OSType',
              'INTEGER DECIMAL TEXT BOOLEAN DATE TIME DATETIME OBJECT')

mapping = {
    ('+', OSType.INTEGER, OSType.INTEGER): 'Add',
    ('+', OSType.DECIMAL, OSType.DECIMAL): 'Add',
    ('+', OSType.TEXT, OSType.TEXT): 'Concat',
    ('-', OSType.INTEGER, OSType.INTEGER): 'Sub',
    ('-', OSType.DECIMAL, OSType.DECIMAL): 'Sub',
    ('-', OSType.INTEGER): 'Neg',
}


def type_infer_leaves(tree):
    def traverse(subtree):
        expr = ast.expr(subtree)

        if expr in [ast.Expr.Var, ast.Expr.Lit]:
            val = ast.val(expr)
            # type_ =
            return ast.typed_ast(expr)

    ast.children(tree).transform([p.ny], traverse)


def type_infer(tree):
    pass


def disambiguate(tree):
    '''
    Rename overloaded operators in the tree with an unambiguous name.
    '''

    children = ast.children(tree).transform([n.py], disambiguate)

    if ast.expr(tree) == ast.Expr.Func:
        pass
