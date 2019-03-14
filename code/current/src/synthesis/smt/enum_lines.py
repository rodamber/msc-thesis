from collections import Counter, namedtuple
from contextlib import suppress
from dataclasses import dataclass
from itertools import (chain, combinations, combinations_with_replacement,
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
    # consts = p.pvector_field(item_type=Const)
    inputs = p.pvector_field(item_type=Input)
    lines = p.pvector_field(item_type=ProgramLine)


class UnplugableComponents(Exception):
    pass


class UnusableInput(Exception):
    pass


# ---------------
# Pretty printing
# ---------------


# TODO This could be better.
# FIXME It orders lines as they appear in the record, not by the value assigned
# to z3 (duh)
def pretty_program(prog, example):
    for pi, pj in zip(prog.inputs, example.inputs):
        pretty_input(pi, pj, example)
    for l in prog.lines:
        pretty_line(l, example)


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


def z3_fresh_const(typ, prefix='c'):
    return z3.FreshConst(type2sort(typ), prefix)


def z3_fresh_line():
    return z3_fresh_const(int, prefix='l')


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
    # consts = generate_consts(components, examples)
    inputs = generate_inputs(examples)
    lines = generate_program_lines(components, examples)

    # return Program(consts=consts, inputs=inputs, lines=lines)
    return Program(inputs=inputs, lines=lines)


# TODO While this doesn't seem to be strictly necessary, it is nice to have
# for pretty printing.
# def generate_consts(components, examples):
#     type_counter = Counter()

#     import pdb; pdb.set_trace()

#     for c in components:
#         for typ in c.domain:
#             type_counter[typ] += 1
#         type_counter[c.ret_type] -= 1

#     for i in examples[0].inputs:
#         type_counter[type(i)] -= 1

#     return p.pvector(
#         Const(get=z3_fresh_const(typ, prefix='c'),
#               lineno=Lineno(get=z3_fresh_line()))
#         for typ, cnt in type_counter.items()
#         for _ in range(cnt + 1))


def generate_inputs(examples):
    return p.pvector(
        Input(
            map=p.pmap((e, z3_fresh_const(type(i), prefix='i'))
                       for e in examples),
            lineno=Lineno(get=z3_fresh_line())) for i in examples[0].inputs)


def generate_program_lines(components, examples):
    outputs = generate_outputs(components, examples)
    holes = p.pvector(generate_holes(c, examples) for c in components)
    lines = p.pvector(
        ProgramLine(output=o, component=c, holes=hs)
        for o, c, hs in zip(outputs, components, holes))

    return lines


def generate_outputs(components, examples):
    return p.pvector(
        Output(
            map=p.pmap((e, z3_fresh_const(c.ret_type, prefix='o'))
                       for e in examples),
            lineno=Lineno(get=z3_fresh_line())) for c in components)


def generate_holes(component, examples):
    return p.pvector(
        Hole(
            map=p.pmap((e, z3_fresh_const(typ, prefix='h')) for e in examples),
            lineno=Lineno(get=z3_fresh_line())) for typ in component.domain)


# -----------
# Constraints
# -----------


def generate_constraints(program, examples):
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
    yield from gen_well_formedness_constraints(holes, inputs, outputs,
                                               examples)
    yield from gen_constant_constraints(holes, component_count, input_count)
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


def gen_well_formedness_constraints(holes, inputs, outputs, examples):
    for e in examples:
        for h, c in product(holes, p.v(*inputs, *outputs)):
            h_const = h.map[e]
            c_const = c.map[e]

            if h_const.sort() == c_const.sort():
                yield z3.Implies(h.lineno.get == c.lineno.get,
                                 h_const == c_const)


def gen_constant_constraints(holes, component_count, input_count):
    hole_count = len(holes)
    consts_count = hole_count - component_count - input_count

    all_hole_consts = p.pvector(
        (c, h.lineno.get) for h in holes for c in h.map.values())

    for (c1, l1), (c2, l2) in combinations(all_hole_consts, r=2):
        if c1.sort() != c2.sort() and c1 is not c2:
            yield z3.Implies(
                z3.And(l1 == l2, l1 <= z3_val(consts_count)), c1 == c2)


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

# def reconstruct(program, model):
#     for i in program.inputs:
#         i.


def synth(library, examples, program_size):
    for components in combinations_with_replacement(library, program_size):
        import pdb; pdb.set_trace()
        solver = z3.Solver()

        with suppress(UnplugableComponents, UnusableInput):
            program = generate_program(components, examples)
            solver.add(*generate_constraints(program, examples))

            print(list(map(lambda c: c.name, components)), solver.check())
            if solver.check() == z3.sat:
                model = solver.model()

                print(f'SAT! Model:\n{model}')
                return solver
    else:
        print('Unable to synthesize :\'(')
