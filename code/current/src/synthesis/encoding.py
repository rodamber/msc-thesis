import collections
import itertools

import pyrsistent as p
from z3 import *

from . import types
from .utils import *


def program_spec(components, examples, local_max_len):
    ctx = z3.Context()

    program = generate_program(components, examples, ctx)
    constraints = generate_constraints(program, examples, local_max_len, ctx)

    return ctx, program, constraints


# ---------
# Constants
# ---------


def generate_program(components, examples, ctx):
    fresh = itertools.count(1)

    locals_ = generate_locals(components, examples, fresh, ctx)
    inputs = generate_inputs(examples, fresh, ctx)
    lines = generate_program_lines(components, examples, fresh, ctx)

    return types.Program(locals_=locals_, inputs=inputs, lines=lines)


def generate_program_lines(components, examples, fresh, ctx):
    outputs = generate_outputs(components, examples, fresh, ctx)

    holes = p.pvector(
        generate_holes(comp, examples, comp_ix, fresh, ctx)
        for comp_ix, comp in enumerate(components, 1))

    lines = p.pvector(
        types.ProgramLine(output=o, component=c, holes=hs)
        for o, c, hs in zip(outputs, components, holes))

    return lines


def generate_locals(components, examples, fresh, ctx):
    """
    Generate local variables of the program, i.e., values that are not
    defined in the inputs and that are the same in every run.
    """

    # Assuming that every input and output is consumed, let's count how many
    # locals_ we may need, for each type.
    type_counter = collections.Counter()

    for c in components:
        # Add one for each hole.
        for typ in c.domain:
            type_counter[typ] += 1

        # Every output should be used, so subtract one for that.
        type_counter[c.ret_type] -= 1

    # Every input should be used, so subtract one for each.
    for i in examples[0].inputs:
        type_counter[type(i)] -= 1

    n = itertools.count(start=1)

    for typ, cnt in type_counter.items():
        # FIXME We're creating plus one local variable per type here, but I
        # don't remember why.
        for i in range(cnt + 1):
            yield types.make_local(typ, next(n), next(fresh), ctx)


def generate_inputs(examples, fresh, ctx):
    # Assuming all examples share the same type signature:
    for ix, input in enumerate(examples[0].inputs, 1):
        yield types.make_input(examples, ix, type(input), next(fresh), ctx)


def generate_outputs(components, examples, fresh, ctx):
    """
    Create one output variable for each of the given components per
    example.
    """
    for ix, comp in enumerate(components, 1):
        yield types.make_output(examples, ix, comp.ret_type, next(fresh), ctx)


def generate_holes(component, examples, component_ix, fresh, ctx):
    """
    Create one variable for each argument of the given component per example.
    """
    for domain_ix, typ in enumerate(component.domain, 1):
        yield types.make_hole(examples, component_ix, domain_ix, typ,
                              next(fresh), ctx)


# -----------
# Constraints
# -----------


def generate_constraints(program, examples, local_max_len, ctx):
    locals_ = program.locals_
    inputs = program.inputs
    outputs = p.pvector(line.output for line in program.lines)
    holes = p.pvector(hole for line in program.lines for hole in line.holes)

    local_count = len(locals_)
    input_count = len(inputs)
    output_count = len(outputs)
    hole_count = len(holes)

    last_lineno = local_count + input_count + output_count

    yield from generate_local_line_constraints(locals_, ctx)
    yield from generate_input_line_constraints(inputs, local_count, ctx)
    yield from generate_output_line_constraints(outputs, local_count,
                                                input_count, ctx)
    yield from generate_hole_line_constraints(program, ctx)
    yield from generate_sort_line_constraints(locals_, inputs, holes, outputs,
                                              ctx)

    yield from generate_well_formedness_constraints(holes, locals_, inputs,
                                                    outputs, examples, ctx)

    yield from generate_output_soundness_constraints(program.lines, examples,
                                                     ctx)

    yield from generate_input_output_completeness_constraints(
        last_lineno, inputs, outputs, holes, examples, ctx)

    yield from generate_correctness_constraints(last_lineno, program.lines,
                                                examples, ctx)

    yield from generate_input_value_constraints(inputs, examples, ctx)

    # New
    yield from generate_local_size_constraints(locals_, local_max_len, ctx)
    yield from generate_input_neq_local_constraints(locals_, inputs)
    # yield from generate_local_not_contains_input_constraints(locals_, inputs, ctx)


def generate_local_line_constraints(locals_, ctx):
    for n, c in enumerate(locals_, 1):
        yield c.lineno.get == z3_val(n, ctx)


def generate_input_line_constraints(inputs, local_count, ctx):
    start = local_count + 1

    for lineno, i in enumerate(inputs, start):
        yield i.lineno.get == z3_val(lineno, ctx)


def generate_output_line_constraints(outputs, local_count, input_count, ctx):
    start = local_count + input_count + 1
    end = start + len(outputs)

    # Define bounds
    for o in outputs:
        yield z3_val(start, ctx) <= o.lineno.get
        yield o.lineno.get < z3_val(end, ctx)

    # Each output is defined in a different line
    for (o1, o2) in itertools.combinations(outputs, r=2):
        yield o1.lineno.get != o2.lineno.get


def generate_hole_line_constraints(program, ctx):
    for line in program.lines:
        for hole in line.holes:
            yield z3_val(1, ctx) <= hole.lineno.get
            yield hole.lineno.get < line.output.lineno.get


def generate_sort_line_constraints(locals_, inputs, outputs, holes, ctx):
    line_inputs = ((x.lineno.get, i) for x in inputs
                   for i in x.from_example.values())
    line_outputs = ((x.lineno.get, o) for x in outputs
                    for o in x.from_example.values())
    line_holes = ((x.lineno.get, h) for x in holes
                  for h in x.from_example.values())
    line_consts = ((x.lineno.get, x.get) for x in locals_)

    all_ = p.v(*line_inputs, *line_outputs, *line_holes, *line_consts)

    for (l1, c1), (l2, c2) in itertools.combinations(all_, r=2):
        if c1.sort() != c2.sort():
            yield l1 != l2


def generate_well_formedness_constraints(holes, locals_, inputs, outputs,
                                         examples, ctx):
    for e in examples:
        for h, c in itertools.product(holes, p.v(*locals_, *inputs, *outputs)):
            h_const = h.from_example[e]

            if isinstance(c, types.Local):
                c_const = c.get
            else:
                c_const = c.from_example[e]

            if h_const.sort() == c_const.sort():
                yield z3.Implies(h.lineno.get == c.lineno.get,
                                 h_const == c_const, ctx)


def generate_output_soundness_constraints(program_lines, examples, ctx):
    for line in program_lines:
        for e in examples:
            output = line.output.from_example[e]
            component = line.component.function
            holes = p.pvector(h.from_example[e] for h in line.holes)

            yield output == component(*holes)

            if line.component.spec:
                yield line.component.spec(ctx, *holes)


def generate_input_output_completeness_constraints(
        last_lineno, inputs, outputs, holes, examples, ctx):
    for i in inputs:
        input_constraints = p.pvector(i.lineno.get == h.lineno.get
                                      for h in holes
                                      if i.from_example.values()[0].sort() ==
                                      h.from_example.values()[0].sort())

        if not input_constraints:
            raise UnusableInput()

        yield z3.Or(*input_constraints, ctx)

    for o in outputs:
        output_constraints = p.pvector(o.lineno.get == h.lineno.get
                                       for h in holes
                                       if o.from_example.values()[0].sort() ==
                                       h.from_example.values()[0].sort())

        # # FIXME
        # if not output_constraints:
        #     raise UnplugableComponents()

        # TODO Either this, or add a return hole constant
        yield z3.Implies(o.lineno.get < z3_val(last_lineno, ctx),
                         z3.Or(*output_constraints, ctx), ctx)


def generate_correctness_constraints(last_lineno, program_lines, examples,
                                     ctx):
    for e in examples:
        for l in program_lines:
            # Outputs of the last component and the examples must have the
            # same sort and value. If any of these conditions are not met, then
            # this component cannot be the last component of the program.
            if l.output.from_example[e].sort() != type2sort(
                    type(examples[0].output), ctx):
                yield l.output.lineno.get != last_lineno
            else:
                yield z3.Implies(
                    l.output.lineno.get == last_lineno,
                    l.output.from_example[e] == z3_val(e.output, ctx), ctx)


def generate_input_value_constraints(inputs, examples, ctx):
    for e in examples:
        for i, ei in zip(inputs, e.inputs):
            yield i.from_example[e] == z3_val(ei, ctx)


def generate_local_size_constraints(locals_, max_size, ctx):
    for local in locals_:
        if local.get.sort() == z3.StringSort(ctx):
            yield z3.Length(local.get) <= z3_val(max_size, ctx)


def generate_input_neq_local_constraints(locals_, inputs):
    for i in inputs:
        for local in locals_:
            for x in filter(lambda x: x.sort() == local.get.sort(),
                            i.from_example.values()):
                yield local.get != x


# FIXME z3 ignores these constraints, so I'm turning them off
# FIXME If this worked, we wouldn't need the constraints preventing string
# constants from being equal to the inputs
def generate_local_not_contains_input_constraints(locals_, inputs, ctx):
    for i in inputs:
        for local in locals_:
            if local.get.sort() == i.from_example.values()[0].sort() \
               == z3.StringSort(ctx):
                for x in i.from_example.values():
                    yield z3.Not(z3.Contains(local.get, x), ctx)
