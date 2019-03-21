import collections
import itertools

import pyrsistent as p

from .types import *
from .utils import *

# ---------
# Constants
# ---------


def generate_program(components, examples, ctx):
    fresh = itertools.count(1)

    consts = generate_consts(components, examples, fresh, ctx)
    inputs = generate_inputs(examples, fresh, ctx)
    lines = generate_program_lines(components, examples, fresh, ctx)

    return Program(consts=consts, inputs=inputs, lines=lines)


def generate_consts(components, examples, fresh, ctx):
    type_counter = collections.Counter()

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
                yield Const(
                    get=z3_const(typ, x, ctx),
                    lineno=Lineno(get=z3_line(fresh, ctx)))
                x += 1

    return p.pvector(_())


def generate_inputs(examples, fresh, ctx):
    def _():
        for n, i in enumerate(examples[0].inputs, 1):
            map = p.pmap((e, z3_input(type(i), n, m, ctx))
                         for m, e in enumerate(examples, 1))
            lineno = Lineno(get=z3_line(fresh, ctx))

            yield Input(map=map, lineno=lineno)

    return p.pvector(_())


def generate_program_lines(components, examples, fresh, ctx):
    outputs = generate_outputs(components, examples, fresh, ctx)
    holes = p.pmap((n, generate_holes(c, examples, n, fresh, ctx))
                   for n, c in enumerate(components, 1))
    lines = p.pvector(
        ProgramLine(output=o, component=c, holes=holes[n])
        for o, (n, c) in zip(outputs, enumerate(components, 1)))

    return lines


def generate_outputs(components, examples, fresh, ctx):
    def _():
        for n, c in enumerate(components, 1):
            map = p.pmap((e, z3_output(c.ret_type, n, m, ctx))
                         for m, e in enumerate(examples, 1))
            lineno = Lineno(get=z3_line(fresh, ctx))

            yield Output(map=map, lineno=lineno)

    return p.pvector(_())


def generate_holes(component, examples, n, fresh, ctx):
    def _():
        for m, typ in enumerate(component.domain, 1):
            map = p.pmap((e, z3_hole(typ, n, k, m, ctx))
                         for k, e in enumerate(examples, 1))
            lineno = Lineno(get=z3_line(fresh, ctx))

            yield Hole(map=map, lineno=lineno)

    return p.pvector(_())


# -----------
# Constraints
# -----------


def generate_constraints(program, examples, const_max_len, ctx):
    consts = program.consts
    inputs = program.inputs
    outputs = p.pvector(l.output for l in program.lines)
    holes = p.pvector(h for l in program.lines for h in l.holes)

    const_count = len(consts)
    input_count = len(examples[0].inputs)
    component_count = len(program.lines)
    hole_count = sum(len(l.component.domain) for l in program.lines)

    last_lineno = len(consts) + len(inputs) + len(outputs)

    yield from gen_const_line_constraints(consts, ctx)
    yield from gen_input_line_constraints(inputs, const_count, ctx)
    yield from gen_output_line_constraints(outputs, const_count, input_count,
                                           ctx)
    yield from gen_hole_line_constraints(program, ctx)
    yield from gen_sort_line_constraints(consts, inputs, holes, outputs, ctx)

    yield from gen_well_formedness_constraints(holes, consts, inputs, outputs,
                                               examples, ctx)

    yield from gen_output_soundness_constraints(program.lines, examples, ctx)

    yield from gen_input_output_completeness_constraints(
        last_lineno, inputs, outputs, holes, examples, ctx)

    yield from gen_correctness_constraints(last_lineno, program.lines,
                                           examples, ctx)

    yield from gen_input_value_constraints(inputs, examples, ctx)

    # New
    yield from gen_const_size_constraints(consts, const_max_len, ctx)


def gen_const_line_constraints(consts, ctx):
    for n, c in enumerate(consts, 1):
        yield c.lineno.get == z3_val(n, ctx)


def gen_input_line_constraints(inputs, const_count, ctx):
    start = const_count + 1

    for lineno, i in enumerate(inputs, start):
        yield i.lineno.get == z3_val(lineno, ctx)


def gen_output_line_constraints(outputs, const_count, input_count, ctx):
    start = const_count + input_count + 1
    end = start + len(outputs)

    # Define bounds
    for o in outputs:
        yield z3_val(start, ctx) <= o.lineno.get
        yield o.lineno.get < z3_val(end, ctx)

    # Each output is defined in a different line
    for (o1, o2) in itertools.combinations(outputs, r=2):
        yield o1.lineno.get != o2.lineno.get


def gen_hole_line_constraints(program, ctx):
    for line in program.lines:
        for hole in line.holes:
            yield z3_val(1, ctx) <= hole.lineno.get
            yield hole.lineno.get < line.output.lineno.get


def gen_sort_line_constraints(consts, inputs, outputs, holes, ctx):
    line_inputs = ((x.lineno.get, i) for x in inputs for i in x.map.values())
    line_outputs = ((x.lineno.get, o) for x in outputs for o in x.map.values())
    line_holes = ((x.lineno.get, h) for x in holes for h in x.map.values())
    line_consts = ((x.lineno.get, x.get) for x in consts)

    all_ = p.v(*line_inputs, *line_outputs, *line_holes, *line_consts)

    for (l1, c1), (l2, c2) in itertools.combinations(all_, r=2):
        if c1.sort() != c2.sort():
            yield l1 != l2


def gen_well_formedness_constraints(holes, consts, inputs, outputs, examples,
                                    ctx):
    for e in examples:
        for h, c in itertools.product(holes, p.v(*consts, *inputs, *outputs)):
            h_const = h.map[e]

            if isinstance(c, Const):
                c_const = c.get
            else:
                c_const = c.map[e]

            if h_const.sort() == c_const.sort():
                yield z3.Implies(h.lineno.get == c.lineno.get,
                                 h_const == c_const, ctx)


def gen_output_soundness_constraints(program_lines, examples, ctx):
    for line in program_lines:
        for e in examples:
            output = line.output.map[e]
            component = line.component.function
            holes = p.pvector(h.map[e] for h in line.holes)

            yield output == component(*holes)


def gen_input_output_completeness_constraints(last_lineno, inputs, outputs,
                                              holes, examples, ctx):
    for e in examples:  # FIXME check if this needs to be done for every example.
        for i in inputs:
            input_constraints = p.pvector(
                i.lineno.get == h.lineno.get for h in holes
                if i.map[e].sort() == h.map[e].sort())

            if not input_constraints:
                raise UnusableInput()

            yield z3.Or(*input_constraints, ctx)

        for o in outputs:
            output_constraints = p.pvector(
                o.lineno.get == h.lineno.get for h in holes
                if o.map[e].sort() == h.map[e].sort())

            # # FIXME
            # if not output_constraints:
            #     raise UnplugableComponents()

            # TODO Either this, or add a return hole constant
            yield z3.Implies(o.lineno.get < z3_val(last_lineno, ctx),
                             z3.Or(*output_constraints, ctx), ctx)


def gen_correctness_constraints(last_lineno, program_lines, examples, ctx):
    for e in examples:
        for l in program_lines:
            # Outputs of the last component and the examples must have the
            # same sort and value. If any of these conditions are not met, then
            # this component cannot be the last component of the program.
            if l.output.map[e].sort() != type2sort(
                    type(examples[0].output), ctx):
                yield l.output.lineno.get != last_lineno
            else:
                yield z3.Implies(l.output.lineno.get == last_lineno,
                                 l.output.map[e] == z3_val(e.output, ctx), ctx)


def gen_input_value_constraints(inputs, examples, ctx):
    for e in examples:
        for i, ei in zip(inputs, e.inputs):
            yield i.map[e] == z3_val(ei, ctx)


def gen_const_size_constraints(consts, max_size, ctx):
    for const in consts:
        if const.get.sort() == z3.StringSort(ctx):
            yield z3.Length(const.get) <= z3_val(max_size, ctx)
