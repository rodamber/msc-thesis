from contextlib import suppress

import pyrsistent as p

from .types import Const
from .utils import z3_as


def eval(c, model):
    # XXX
    with suppress(ValueError):
        return z3_as(model[c])


def pretty_oneliner(program, model):
    import string

    show = {}
    inputs = dict(
        (i.lineno, x) for i, x in zip(program.inputs, string.ascii_lowercase))

    for c in program.consts:
        show.update({eval(c.lineno.get, model): repr(eval(c.get, model))})

    for i in program.inputs:
        show.update({eval(i.lineno.get, model): inputs[i.lineno]})

    for line in sorted(
            program.lines, key=lambda x: eval(x.output.lineno.get, model)):
        hs = (show[eval(h.lineno.get, model)] for h in line.holes)
        s = line.component.name + '(' + ', '.join(hs) + ')'
        show.update({eval(line.output.lineno.get, model): s})

    print(f"({', '.join(inputs.values())}) \u21A6 ", end='')
    print(show[max(show, key=show.get)])


# XXX
def pretty_lines(program, model, example=None):
    consts = program.consts
    inputs = program.inputs
    outputs = p.pvector(line.output for line in program.lines)
    holes = p.pvector(h for line in program.lines for h in line.holes)

    line2val = p.pmap((eval(c.lineno.get, model), c)
                      for c in p.v(*consts, *inputs, *outputs))

    for c in program.consts:
        x = f'{eval(c.lineno.get, model)} | c_{eval(c.lineno.get, model)} = {repr(eval(c.get, model))}'
        print(x)

    for n, i in enumerate(program.inputs, 1):
        print(f'{eval(i.lineno.get, model)} | {i.map.values()[0]} = _{n}')

    for l in sorted(
            program.lines, key=lambda l: eval(l.output.lineno.get, model)):
        print(
            f'{eval(l.output.lineno.get, model)} | {l.output.map.values()[0]}',
            end=' = ')
        print(l.component.name, end='')

        def hole_ref(h):
            c = line2val[eval(h.lineno.get, model)]
            if isinstance(c, Const):
                return c.get
            else:
                return c.map.values()[0]

        print(
            '(' + ', '.join(map(lambda h: str(hole_ref(h)), l.holes)) + ')',
            end=' ' if example else '\n')

        if example:
            print(f'# {repr(eval(l.output.map[example], model))}')
