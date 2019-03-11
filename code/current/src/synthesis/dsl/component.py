from collections import namedtuple
from enum import Enum

import pyrsistent as p
from toolz import compose, curry

from .. import tree, utils
from ..outsystems.templatify import templatify
from ..tree import children, tag

Component = Enum('Component', 'CONCAT INDEX LENGTH REPLACE SUBSTR ADD1 SUB1')

Hole = namedtuple('Hole', 'id')
Const = namedtuple('Const', 'val')

program = tree.tree

hole = compose(program, Hole)
const = compose(program, Const)

concat = lambda x, y: program(Component.CONCAT, x, y)
index = lambda x, y: program(Component.INDEX, x, y)
length = lambda x: program(Component.LENGTH, x)
replace = lambda x, y, z: program(Component.REPLACE, x, y, z)
substr = lambda x, y, z: program(Component.SUBSTR, x, y, z)
add1 = lambda x: program(Component.ADD1, x)
sub1 = lambda x: program(Component.SUB1, x)

render = tree.render


# TODO Extend this to support binding a hole to a tree. Next step would be to
# support partial evaluation.
@curry
def run(env, prog):
    if isinstance(tag(prog), Hole):
        return env[prog]
    elif isinstance(tag(prog), Const):
        return tag(prog).val
    elif isinstance(tag(prog), Component):
        vals = children(prog).transform([p.ny], run(env))

        if tag(prog) == Component.CONCAT:
            return ''.join(vals)
        elif tag(prog) == Component.INDEX:  # FIXME Binary index
            return vals[0].find(vals[1])
        elif tag(prog) == Component.LENGTH:
            return len(vals[0])
        elif tag(prog) == Component.REPLACE:
            return vals[0].replace(vals[1], vals[2])
        elif tag(prog) == Component.SUBSTR:
            return vals[0][vals[1]:vals[2]]
        elif tag(prog) == Component.ADD1:
            return vals[0] + 1
        elif tag(prog) == Component.SUB1:
            return vals[0] - 1


def test_run():
    fresh = utils.fresh_gen()

    x0 = hole(next(fresh))
    x1 = hole(next(fresh))
    x2 = hole(next(fresh))

    assert run({x0: 'Hello'}, concat(x0, const(' world!'))) == 'Hello world!'
    assert run({x0: 'outsystems.com'}, index(x0, const('.'))) == 10
    assert run({x0: 'cmu'}, length(x0)) == 3
    assert run({
        x0: 'dd-mm-yyyy',
        x1: '-',
        x2: '/'
    }, replace(x0, x1, x2)) == 'dd/mm/yyyy'
    assert run({x0: 'www.outsystems.com'}, substr(x0, const(3), const(14)))

    # Example of a complex program. Let expressions could reduce complexity here.
    env = {x0: 'www.outsystems.com', x1: '.'}
    prog = substr(
        substr(x0, add1(index(x0, x1)), length(x0)), const(0),
        index(substr(x0, add1(index(x0, x1)), length(x0)), x1))

    assert run(env, prog) == 'outsystems'


def holes(prog):
    return set(
        x.tag for x in tree.tree2anynode(prog).leaves
        if isinstance(x.tag, Hole))


def test_holes():
    fresh = utils.fresh_gen()

    x0 = hole(next(fresh))
    x1 = hole(next(fresh))

    zero = const(0)

    prog = substr(x0, zero, index(x0, x1))

    assert holes(prog) == set(map(tag, [x0, x1]))


def from_ast(ast):
    template = templatify(ast)

    children = children(template)\
        .transform([p.ny], from_ast)

    if expr(template) == ast.Expr.Var:
        return hole(val(template))
    elif expr(template) == ast.Expr.Lit:
        return const(val(template))
    elif expr(template) == ast.Expr.Func:
        return match_component(val(template))
    elif expr(template) == ast.Expr.KwArg:
        raise Exception('keyword args are not supported yet')


class UnsupportedComponent(Exception):
    pass


def match_component(name: str) -> Component:
    try:
        return Component[name]
    except KeyError as e:
        raise UnsupportedComponent from e
