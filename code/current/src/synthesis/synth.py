import itertools as it
import logging
from contextlib import suppress

import pyrsistent as p
import z3
from toolz import curry

from .components import *
from .encoding import *
from .types import *
from .utils import *


def default_library(*args):
    return (concat, index, length, replace, substr) + tuple(args)


def config(library=default_library(),
           program_min_size=1,
           program_max_size=None,
           max_conflicts=None,
           string_constant_max_len=5):
    return Config(
        library=library,
        program_min_size=program_min_size,
        program_max_size=program_max_size,
        max_conflicts=max_conflicts,
        string_constant_max_len=string_constant_max_len)


# ==============================================================================
# Synthesis


def enum(library, min_size, max_size):
    start = min_size
    stop = max_size + 1 if max_size else None

    for size in it.islice(it.count(), start, stop):
        logging.debug(f'Enumerating program size: {size}')

        for components in it.combinations_with_replacement(library, size):
            components_names = tuple(c.name for c in components)
            logging.debug(f'Enumerated components: {components_names}')

            yield components


def oracle(components, examples, max_conflicts, const_max_len):
    ctx, program, constraints = \
        program_spec(components, examples, const_max_len)

    solver = z3.Solver(ctx=ctx)
    solver.add(*constraints)

    if max_conflicts:
        solver.set('max_conflicts', max_conflicts)

    check = solver.check()
    logging.debug(f'Solver result: {repr(check).upper()}')

    if check == z3.unknown:
        reason = solver.reason_unknown()
        logging.debug(f'Reason: {reason}')
    elif check == z3.sat:
        model = solver.model()
        return (program, model)


def synth(config, examples):
    synth_log_parameters(config)

    library = config.library
    min_size = config.program_min_size
    max_size = config.program_max_size
    max_conflicts = config.max_conflicts
    const_max_len = config.string_constant_max_len

    for components in enum(library, min_size, max_size):
        res = oracle(components, examples, max_conflicts, const_max_len)

        if res:
            return res



# ==============================================================================
# Logging


def synth_log_parameters(config):
    synth_log_library(config.library)
    synth_log_program_size(config.program_min_size, config.program_max_size)
    synth_log_timeout(config.max_conflicts)


def synth_log_library(library):
    logging.debug(f'Library of components:')

    for name in (c.name for c in library):
        logging.debug(f'\t{name}')


def synth_log_program_size(program_min_size, program_max_size):
    logging.debug(f'Min size: {program_min_size}')
    logging.debug(f'Max size: {program_max_size}')


def synth_log_timeout(max_conflicts):
    logging.debug(f'Z3 max_conflicts: {max_conflicts}')


# ==============================================================================
# Program reconstruction


def reconstruct(program, model):
    consts = p.pvector(
        Const(
            get=z3_as(model[c.get]),
            lineno=Lineno(get=z3_as(model[c.lineno.get])))
        for c in program.consts)

    inputs = p.pvector(
        Input(map=i.map, lineno=Lineno(get=z3_as(model[i.lineno.get])))
        for i in program.inputs)

    def _line():
        for line in program.lines:
            output = Output(
                map=line.output.map,
                lineno=Lineno(get=z3_as(model[line.output.lineno.get])))

            component = line.component

            holes = p.pvector(
                Hole(map=h.map, lineno=Lineno(get=z3_as(model[h.lineno.get])))
                for h in line.holes)

            yield ProgramLine(output=output, component=component, holes=holes)

    lines = p.pvector(_line())

    return Program(consts=consts, inputs=inputs, lines=lines)
