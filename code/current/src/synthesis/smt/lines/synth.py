import itertools as it
import logging
from contextlib import suppress

import pyrsistent as p
import z3

from .components import *
from .encoding import *
from .types import *
from .utils import *

# Ideas:
# - Incremental solving?
# - OGIS loop?
# - Active learning
# - Distinguishing inputs (offline/online)
# - Better sketch enumeration
# - Partial evaluation

# TODO Better "debugability" (ucores, for example)

# FIXME synthesis results depend on previous runs because the solver is
# retaining constants.


def synth(examples,
          library=default_library,
          program_min_size=1,
          program_max_size=None,
          timeout=None):

    synth_log_parameters(examples, library, program_min_size, program_max_size,
                         timeout)

    for size in it.islice(it.count(), program_min_size - 1, program_max_size):
        logging.debug(f'Enumerating program size: {size}')

        for components in it.combinations_with_replacement(library, size):
            components_names = tuple(c.name for c in components)
            logging.debug(f'Enumerated components: {components_names}')

            solver = z3.Solver(  # ctx=z3.Context()
            )

            try:
                program = generate_program(components, examples)
                constraints = generate_constraints(program, examples)

                solver.add(*constraints)

                if timeout:
                    solver.set('timeout', timeout)

                check = solver.check()

                logging.debug(f'Solver result: {repr(check).upper()}')

                if check == z3.sat:
                    model = solver.model()
                    return True, (program, model)

            except UnplugableComponents:
                logging.debug(f'Unplugable components')
            except UnusableInput as e:
                logging.debug(f'Unusable input {e.input}')

    return False, ()


def synth_log_parameters(examples, library, program_min_size, program_max_size,
                         timeout):
    synth_log_examples(examples)
    synth_log_library(library)
    synth_log_program_size(program_min_size, program_max_size)
    synth_log_timeout(timeout)


def synth_log_examples(examples):
    logging.debug('Examples:')
    for ex in examples:
        logging.debug(f'\t{tuple(ex.inputs)} --> {repr(ex.output)}')


def synth_log_library(library):
    logging.debug(f'Library of components:')

    for name in (c.name for c in library):
        logging.debug(f'\t{name}')


def synth_log_program_size(program_min_size, program_max_size):
    logging.debug(f'Min size: {program_min_size}')
    logging.debug(f'Max size: {program_max_size}')


def synth_log_timeout(timeout):
    logging.debug(f'Z3 timeout: {timeout}')


# TODO Should we use a different representation for symbolic and concrete
# programs?
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
