import pyrsistent as p

from .types import Const
from .utils import z3_as


# XXX
def pretty_program(program, model, example=None):
    consts = program.consts
    inputs = program.inputs
    outputs = p.pvector(line.output for line in program.lines)
    holes = p.pvector(h for line in program.lines for h in line.holes)

    def eval(c):
        # with suppress(ValueError):
        return z3_as(model[c])

    line2val = p.pmap(
        (eval(c.lineno.get), c) for c in p.v(*consts, *inputs, *outputs))

    for c in program.consts:
        x = f'{eval(c.lineno.get)} | c_{eval(c.lineno.get)} = {repr(eval(c.get))}'
        print(x)

    for n, i in enumerate(program.inputs, 1):
        print(f'{eval(i.lineno.get)} | {i.map.values()[0]} = _{n}')

    for l in sorted(program.lines, key=lambda l: eval(l.output.lineno.get)):
        print(
            f'{eval(l.output.lineno.get)} | {l.output.map.values()[0]}',
            end=' = ')
        print(l.component.name, end='')

        def hole_ref(h):
            c = line2val[eval(h.lineno.get)]
            if isinstance(c, Const):
                return c.get
            else:
                return c.map.values()[0]

        print(
            '(' + ', '.join(map(lambda h: str(hole_ref(h)), l.holes)) + ')',
            end=' ' if example else '\n')

        if example:
            print(f'# {eval(l.output.map[example])}')
