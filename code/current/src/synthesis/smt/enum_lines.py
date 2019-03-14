from collections import Counter, namedtuple
from contextlib import suppress
from dataclasses import dataclass
from itertools import (combinations, combinations_with_replacement, count,
                       product)

import pyrsistent as p
import z3

# -----
# Types
# -----


class Component(p.PClass):
    name = p.field(type=str)
    domain = p.pvector_field(item_type=type)
    ret_type = p.field(mandatory=True, type=type)
    function = p.field(mandatory=True, type=object)


class Example(p.PClass):
    inputs = p.pvector_field(object)
    output = p.field(mandatory=True, type=object)


class Lineno(p.PClass):
    get = p.field(mandatory=True, type=object)


class Const(p.PClass):
    get = p.field(mandatory=True, type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class Input(p.PClass):
    map = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class Output(p.PClass):
    map = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class Hole(p.PClass):
    map = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class ProgramLine(p.PClass):
    output = p.field(mandatory=True, type=Output)
    component = p.field(mandatory=True, type=Component)
    holes = p.pvector_field(item_type=Hole)


class Program(p.PClass):
    consts = p.pvector_field(item_type=Const)
    inputs = p.pvector_field(item_type=Input)
    lines = p.pvector_field(item_type=ProgramLine)


class UnplugableComponents(Exception):
    pass


class UnusableInput(Exception):
    pass


# ---------------
# Pretty printing
# ---------------


# FIXME This should print according to the model obtained from the solver.
# - constants should be printed correctly
# - holes should be substituted
# - lines should be substituted
# - program lines should be sorted
def pretty_program(prog, example):
    for c in prog.consts:
        pretty_const(c)
    for pi, pj in zip(prog.inputs, example.inputs):
        pretty_input(pi, pj, example)
    for l in prog.lines:
        pretty_line(l, example)


def pretty_const(const):
    print(f'{const.lineno.get} | {const.get} = ?')


def pretty_input(pi, pj, example):
    const = pi.map[example]
    print(f'{pi.lineno.get} | {const} = {repr(pj)}')


def pretty_line(l, example):
    pretty_output(l.output, example)
    pretty_component(l.component)
    pretty_holes(l.holes, example)


def pretty_output(o, example):
    const = o.map[example]
    print(f'{o.lineno.get} | {const}', end=' = ')


def pretty_component(c):
    print(c.name, end='')


def pretty_holes(hs, example):
    consts = map(lambda h: str(h.map[example]), hs)
    print('(' + ', '.join(consts) + ')')


# ----------
# Components
# ----------

concat = Component(
    name='concat',
    domain=(str, str),
    ret_type=str,
    function=lambda x, y: z3.Concat(x, y))
index = Component(
    name='index',
    domain=(str, str),
    ret_type=int,
    function=lambda text, x: z3.IndexOf(text, x, 0))
length = Component(
    name='length',
    domain=(str, ),
    ret_type=int,
    function=lambda x: z3.Length(x))
replace = Component(
    name='replace',
    domain=(str, str, str),
    ret_type=str,
    function=lambda x, y, z: z3.Replace(x, y, z))
substr = Component(
    name='substr',
    domain=(str, int, int),
    ret_type=str,
    function=lambda text, i, j: z3.SubString(text, i, j - i))

library = p.v(concat, index, length, replace, substr)

# -----
# Utils
# -----


def type2sort(typ):
    if typ == int:
        return z3.IntSort()
    elif typ == str:
        return z3.StringSort()
    else:
        raise ValueError(f'Unsupported type: {typ}')


def _z3_smt_const(typ, prefix, *ix):
    ix = '_'.join(map(str, ix))
    return z3.Const(f'{prefix}_{ix}', type2sort(typ))


def z3_const(typ, x):
    return _z3_smt_const(typ, 'c', x)


def z3_input(typ, x, y):
    return _z3_smt_const(typ, 'i', x, y)


def z3_output(typ, x, y):
    return _z3_smt_const(typ, 'o', x, y)


def z3_hole(typ, x, y, z):
    return _z3_smt_const(typ, 'h', x, y, z)


def z3_line():
    return z3.FreshInt(prefix='l')


def z3_val(val):
    if isinstance(val, int):
        return z3.IntVal(val)
    elif isinstance(val, str):
        return z3.StringVal(val)
    else:
        raise ValueError(f'z3_val: invalid typ ({typ})')


# ---------
# Constants
# ---------


def generate_program(components, examples):
    consts = generate_consts(components, examples)
    inputs = generate_inputs(examples)
    lines = generate_program_lines(components, examples)

    return Program(consts=consts, inputs=inputs, lines=lines)


def generate_consts(components, examples):
    type_counter = Counter()

    for c in components:
        for typ in c.domain:
            type_counter[typ] += 1
        type_counter[c.ret_type] -= 1

    for i in examples[0].inputs:
        type_counter[type(i)] -= 1

    def _():
        x = 1

        for typ, cnt in type_counter.items():
            for i in range(cnt + 1):
                yield Const(get=z3_const(typ, x), lineno=Lineno(get=z3_line()))
                x += 1

    return p.pvector(_())


def generate_inputs(examples):
    def _():
        for n, i in enumerate(examples[0].inputs, 1):
            map = p.pmap((e, z3_input(type(i), m, n))
                         for m, e in enumerate(examples, 1))
            lineno = Lineno(get=z3_line())

            yield Input(map=map, lineno=lineno)

    return p.pvector(_())


def generate_program_lines(components, examples):
    outputs = generate_outputs(components, examples)
    holes = p.pmap((c, generate_holes(c, examples, n))
                   for n, c in enumerate(components, 1))
    lines = p.pvector(
        ProgramLine(output=o, component=c, holes=holes[c])
        for o, c in zip(outputs, components))

    return lines


def generate_outputs(components, examples):
    def _():
        for n, c in enumerate(components, 1):
            map = p.pmap((e, z3_output(c.ret_type, n, m))
                         for m, e in enumerate(examples, 1))
            lineno = Lineno(get=z3_line())

            yield Output(map=map, lineno=lineno)

    return p.pvector(_())


def generate_holes(component, examples, n):
    def _():
        for m, typ in enumerate(component.domain, 1):
            map = p.pmap(
                (e, z3_hole(typ, n, m, k)) for k, e in enumerate(examples, 1))
            lineno = Lineno(get=z3_line())

            yield Hole(map=map, lineno=lineno)

    return p.pvector(_())


# -----------
# Constraints
# -----------


def generate_constraints(program, examples):
    consts = program.consts
    inputs = program.inputs
    outputs = p.pvector(l.output for l in program.lines)
    holes = p.pvector(h for l in program.lines for h in l.holes)

    input_count = len(examples[0].inputs)
    component_count = len(program.lines)
    hole_count = sum(len(l.component.domain) for l in program.lines)

    yield from gen_input_line_constraints(inputs, hole_count, component_count)
    yield from gen_output_line_constraints(outputs, hole_count,
                                           component_count)
    yield from gen_hole_line_constraints(program, examples)
    yield from gen_sort_line_constraints(inputs, holes, outputs)
    yield from gen_well_formedness_constraints(holes, consts, inputs, outputs,
                                               examples)
    yield from gen_output_soundness_constraints(program.lines, examples)
    yield from gen_input_output_completeness_constraints(
        inputs, outputs, holes, examples)
    yield from gen_correctness_constraints(hole_count, program.lines, examples)
    yield from gen_input_value_constraints(inputs, examples)


def gen_input_line_constraints(inputs, hole_count, component_count):
    start = hole_count - component_count - len(inputs) + 1

    for lineno, i in enumerate(inputs, start):
        yield i.lineno.get == lineno


def gen_output_line_constraints(outputs, hole_count, component_count):
    start = hole_count + 1 - component_count

    for lineno, o in enumerate(outputs, start):
        yield o.lineno.get == lineno


def gen_hole_line_constraints(program, examples):
    for line in program.lines:
        for hole in line.holes:
            yield z3.And(
                z3_val(1) <= hole.lineno.get,
                hole.lineno.get <= line.output.lineno.get)


def gen_sort_line_constraints(inputs, outputs, holes):
    all_consts = p.pvector(
        (l, x) for i, o, h in zip(inputs, outputs, holes)
        for l, x in zip((i.lineno, o.lineno,
                         h.lineno), (*i.map.values(), *o.map.values(),
                                     *h.map.values())))

    for (l1, c1), (l2, c2) in combinations(all_consts, r=2):
        if c1.sort() != c2.sort():
            yield l1 != l2


def gen_well_formedness_constraints(holes, consts, inputs, outputs, examples):
    for e in examples:
        for h, c in product(holes, p.v(*consts, *inputs, *outputs)):
            h_const = h.map[e]

            if isinstance(c, Const):
                c_const = c.get
            else:
                c_const = c.map[e]

            if h_const.sort() == c_const.sort():
                yield z3.Implies(h.lineno.get == c.lineno.get,
                                 h_const == c_const)


def gen_output_soundness_constraints(program_lines, examples):
    for line in program_lines:
        for e in examples:
            output = line.output.map[e]
            component = line.component.function
            holes = p.pvector(h.map[e] for h in line.holes)

            yield output == component(*holes)


def gen_input_output_completeness_constraints(inputs, outputs, holes,
                                              examples):
    for i, o in zip(inputs, outputs):
        for e in examples:
            input_constraints = p.pvector(
                i.map[e] == h.map[e] for h in holes
                if i.map[e].sort() == h.map[e].sort())

            if not input_constraints:
                raise UnusableInput()

            output_constraints = p.pvector(
                o.map[e] == h.map[e] for h in holes
                if o.map[e].sort() == h.map[e].sort())

            if not output_constraints:
                raise UnplugableComponents()

            yield z3.And(z3.Or(*input_constraints), z3.Or(*output_constraints))


def gen_correctness_constraints(hole_count, program_lines, examples):
    last_lineno = z3_val(hole_count + 1)
    for e in examples:
        for l in program_lines:
            if l.output.map[e].sort() != type2sort(type(examples[0].output)):
                yield l.output.lineno.get != last_lineno
            else:
                yield z3.Implies(l.output.lineno.get == last_lineno,
                                 l.output.map[e] == z3_val(e.output))


def gen_input_value_constraints(inputs, examples):
    for e in examples:
        for i, ei in zip(inputs, e.inputs):
            yield i.map[e] == z3_val(ei)


# ---------
# Synthesis
# ---------


# FIXME
def reconstruct(program, model):
    return None


def synth(library, examples, program_size):
    for components in combinations_with_replacement(library, program_size):
        solver = z3.Solver()

        with suppress(UnplugableComponents, UnusableInput):
            program = generate_program(components, examples)
            solver.add(*generate_constraints(program, examples))

            if solver.check() == z3.sat:
                model = solver.model()
                return reconstruct(program, model)
    else:
        print('Unable to synthesize :\'(')
