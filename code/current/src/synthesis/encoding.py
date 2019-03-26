import collections
import itertools

import pyrsistent as p
from z3 import *

from . import types
from .utils import *


def program_spec(components, examples, local_max_len, fix_lines, stack_space):
    context = z3.Context()

    program = generate_program(components, examples, stack_space, context)
    constraints = generate_constraints(program, examples, local_max_len,
                                       fix_lines, context)

    return context, program, constraints


# ---------
# Constants
# ---------


def generate_program(components, examples, stack_space, context):
    locals_ = generate_locals(components, examples, stack_space, context)
    inputs = generate_inputs(examples, context)
    lines = generate_program_lines(components, examples, context)

    return types.Program(locals_=locals_, inputs=inputs, lines=lines)


def generate_program_lines(components, examples, context):
    outputs = generate_outputs(components, examples, context)

    holes = p.pvector(
        generate_holes(comp, examples, comp_ix, context)
        for comp_ix, comp in enumerate(components, 1))

    lines = p.pvector(
        types.ProgramLine(output=o, component=c, holes=hs)
        for o, c, hs in zip(outputs, components, holes))

    return lines


def generate_locals(components, examples, stack_space, context):
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
            x = next(n)

            if x <= stack_space:
                yield types.make_local(typ, x, context)


def generate_inputs(examples, context):
    # Assuming all examples share the same type signature:
    for ix, input in enumerate(examples[0].inputs, 1):
        yield types.make_input(examples, ix, type(input), context)


def generate_outputs(components, examples, context):
    """
    Create one output variable for each of the given components per
    example.
    """
    for ix, comp in enumerate(components, 1):
        yield types.make_output(examples, ix, comp.ret_type, context)


def generate_holes(component, examples, component_ix, context):
    """
    Create one variable for each argument of the given component per example.
    """
    for domain_ix, typ in enumerate(component.domain, 1):
        yield types.make_hole(examples, component_ix, domain_ix, typ, context)


# -----------
# Constraints
# -----------


class ConstraintEnv(p.PClass):
    program = p.field(type=types.Program)
    examples = p.pvector_field(types.Example)
    locals_ = p.pvector_field(types.Local)
    inputs = p.pvector_field(types.Input)
    outputs = p.pvector_field(types.Output)
    holes = p.pvector_field(types.Hole)
    last_lineno = p.field(type=int)
    local_max_len = p.field()
    fix_lines = p.field()
    context = p.field()


def generate_constraints(program, examples, local_max_len, fix_lines, context):
    outputs = p.pvector(line.output for line in program.lines)
    holes = p.pvector(hole for line in program.lines for hole in line.holes)
    last_lineno = len(program.locals_) + len(program.inputs) + len(outputs)

    env = ConstraintEnv(
        program=program,
        examples=examples,
        locals_=program.locals_,
        inputs=program.inputs,
        outputs=outputs,
        holes=holes,
        last_lineno=last_lineno,
        local_max_len=local_max_len,
        fix_lines=fix_lines,
        context=context)

    yield from generate_local_line_constraints(env)
    yield from generate_input_line_constraints(env)
    yield from generate_output_line_constraints(env)
    yield from generate_hole_line_constraints(env)
    yield from generate_sort_line_constraints(env)
    yield from generate_well_formedness_constraints(env)
    yield from generate_output_soundness_constraints(env)
    yield from generate_input_output_completeness_constraints(env)
    yield from generate_correctness_constraints(env)
    yield from generate_input_value_constraints(env)

    # New
    yield from generate_local_size_constraints(env)
    yield from generate_input_neq_local_constraints(env)
    # yield from generate_local_not_contains_input_constraints(env)


def generate_local_line_constraints(env):
    for n, c in enumerate(env.locals_, 1):
        yield c.lineno.get == z3_val(n, env.context)


def generate_input_line_constraints(env):
    start = len(env.locals_) + 1

    for lineno, i in enumerate(env.inputs, start):
        yield i.lineno.get == z3_val(lineno, env.context)


def generate_output_line_constraints(env):
    # Define bounds
    start = len(env.locals_) + len(env.inputs) + 1
    end = start + len(env.outputs)

    if env.fix_lines:
        for n, output in enumerate(env.outputs):
            yield output.lineno.get == z3_val(start + n, env.context)
    else:
        for o in env.outputs:
            yield z3_val(start, env.context) <= o.lineno.get
            yield o.lineno.get < z3_val(end, env.context)

        # Each output is defined in a different line
        for (o1, o2) in itertools.combinations(env.outputs, r=2):
            yield o1.lineno.get != o2.lineno.get


def generate_hole_line_constraints(env):
    for line in env.program.lines:
        for hole in line.holes:
            yield z3_val(1, env.context) <= hole.lineno.get
            yield hole.lineno.get < line.output.lineno.get


def generate_sort_line_constraints(env):
    line_inputs = ((x.lineno.get, i) for x in env.inputs
                   for i in x.from_example.values())
    line_outputs = ((x.lineno.get, o) for x in env.outputs
                    for o in x.from_example.values())
    line_holes = ((x.lineno.get, h) for x in env.holes
                  for h in x.from_example.values())
    line_consts = ((x.lineno.get, x.get) for x in env.locals_)

    all_ = p.v(*line_inputs, *line_outputs, *line_holes, *line_consts)

    for (l1, c1), (l2, c2) in itertools.combinations(all_, r=2):
        if c1.sort() != c2.sort():
            yield l1 != l2


def generate_well_formedness_constraints(env):
    for e in env.examples:
        for h, c in itertools.product(
                env.holes, p.v(*env.locals_, *env.inputs, *env.outputs)):
            h_const = h.from_example[e]

            if isinstance(c, types.Local):
                c_const = c.get
            else:
                c_const = c.from_example[e]

            if h_const.sort() == c_const.sort():
                yield z3.Implies(h.lineno.get == c.lineno.get,
                                 h_const == c_const, env.context)


def generate_output_soundness_constraints(env):
    for line in env.program.lines:
        for e in env.examples:
            output = line.output.from_example[e]
            component = line.component.function
            holes = p.pvector(h.from_example[e] for h in line.holes)

            yield output == component(*holes)

            if line.component.spec:
                yield line.component.spec(env.context, *holes)


def generate_input_output_completeness_constraints(env):
    for i in env.inputs:
        input_constraints = p.pvector(i.lineno.get == h.lineno.get
                                      for h in env.holes
                                      if i.from_example.values()[0].sort() == \
                                         h.from_example.values()[0].sort())

        if not input_constraints:
            raise types.UnusableInput()

        yield z3.Or(*input_constraints, env.context)

    if env.fix_lines:
        for line in env.program.lines[:-1]:
            o = line.output

            # XXX
            output_constraints = p.pvector(o.lineno.get == h.lineno.get
                                        for h in env.holes
                                        if o.from_example.values()[0].sort() == \
                                           h.from_example.values()[0].sort())

            yield z3.Or(*output_constraints, env.context)
    else:
        for o in env.outputs:
            # XXX
            output_constraints = p.pvector(o.lineno.get == h.lineno.get
                                        for h in env.holes
                                        if o.from_example.values()[0].sort() == \
                                            h.from_example.values()[0].sort())

            # # FIXME
            # if not output_constraints:
            #     raise types.UnplugableComponents()

            # TODO Either this, or add a return hole constant
            yield z3.Implies(
                o.lineno.get < z3_val(env.last_lineno, env.context),
                z3.Or(*output_constraints, env.context), env.context)


def generate_correctness_constraints(env):
    for e in env.examples:
        if env.fix_lines:
            output = env.program.lines[-1].output

            if output.from_example[e].sort() != type2sort(
                        type(env.examples[0].output), env.context):
                raise types.UnplugableComponents()
            else:
                yield output.from_example[e] == z3_val(e.output, env.context)
        else:
            for l in env.program.lines:
                # Outputs of the last component and the examples must have the same
                # sort and value.
                if l.output.from_example[e].sort() != type2sort(
                        type(env.examples[0].output), env.context):
                    yield l.output.lineno.get != env.last_lineno
                else:
                    yield z3.Implies(
                        l.output.lineno.get == env.last_lineno,
                        l.output.from_example[e] == z3_val(
                            e.output, env.context), env.context)


def generate_input_value_constraints(env):
    for e in env.examples:
        for i, ei in zip(env.inputs, e.inputs):
            yield i.from_example[e] == z3_val(ei, env.context)


def generate_local_size_constraints(env):
    for local in env.locals_:
        if local.get.sort() == z3.StringSort(env.context):
            yield z3.Length(local.get) <= z3_val(env.local_max_len,
                                                 env.context)


def generate_input_neq_local_constraints(env):
    for i in env.inputs:
        for local in env.locals_:
            for x in filter(lambda x: x.sort() == local.get.sort(),
                            i.from_example.values()):
                yield local.get != x


# FIXME z3 ignores these constraints, so I'm turning them off
# FIXME If this worked, we wouldn't need the constraints preventing string
# constants from being equal to the inputs
def generate_local_not_contains_input_constraints(env):
    for i in env.inputs:
        for local in env.locals_:
            if local.get.sort() == i.from_example.values()[0].sort() \
               == z3.StringSort(env.context):
                for x in i.from_example.values():
                    yield z3.Not(z3.Contains(local.get, x), env.context)
