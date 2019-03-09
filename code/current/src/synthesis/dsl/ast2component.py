from dataclasses import dataclass
from typing import Type

from ..outsystems import expr_ast as ast
from ..visitor import visitor
from . import component as comp


def ast2comp(e):
    return Ast2Component().visit(Typer().visit(e))


@dataclass
class TypeTag():
    x: ast.Expr
    tag: Type


# XXX FIXME TODO
class Ast2Component():
    def visit_all(self, xs):
        return tuple(self.visit(x) for x in xs)

    @visitor(ast.Func)
    def visit(self, e):
        if e.name == 'Concat':
            return comp.Concat(*self.visit_all(e.parameters))
        if e.name == 'Index':
            return comp.Index(*self.visit_all(e.parameters))
        if e.name == 'Length':
            return comp.Length(*self.visit_all(e.parameters))
        if e.name == 'Replace':
            return comp.Replace(*self.visit_all(e.parameters))
        if e.name == 'Substr':
            return comp.Substr(*self.visit_all(e.parameters))
        return Func(e.name, params)

    @visitor(TypeTag)
    def visit(self, tt):
        if isinstance(tt.x, ast.Variable):
            if tt.tag == str:
                return comp.StrHole()
            if tt.tag == int:
                return comp.IntHole()
        if isinstance(tt.x, ast.Literal):
            if tt.tag == str:
                return comp.StrHole()
                # XXX FIXME TODO
                # even if we were to do this, we should be careful to subst
                # equal consts by the "same" hole
                # return comp.StrConst(tt.x.value)
            if tt.tag == int:
                return comp.IntHole()
                # XXX FIXME TODO
                # even if we were to do this, we should be careful to subst
                # equal consts by the "same" hole
                # return comp.IntConst(int(tt.x.value))
        if isinstance(tt.x, ast.Func):
            return self.visit(tt.x)


# XXX FIXME TODO
class Typer():
    @visitor(ast.Variable)
    def visit(self, e):
        return e

    @visitor(ast.Literal)
    def visit(self, e):
        return e

    def type_(self, params, types):
        ps = (self.visit(p) for p in params)
        return tuple(TypeTag(p, t) for p, t in zip(ps, types))

    @visitor(ast.Func)
    def visit(self, e):
        if e.name == 'Concat':
            params = self.type_(e.parameters, [str, str])
        elif e.name == 'Index':
            params = self.type_(e.parameters, [str, str])
        elif e.name == 'Length':
            params = self.type_(e.parameters, [str])
        elif e.name == 'Replace':
            params = self.type_(e.parameters, [str, str, str])
        elif e.name == 'Substr':
            params = self.type_(e.parameters, [str, int, int])
        else:
            raise ValueError(str(e))
        return ast.Func(e.name, params)
