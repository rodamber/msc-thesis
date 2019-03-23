import itertools as it
import logging
import time
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
           local_string_max_len=5,
           fix_lines=False):
    return Config(
        library=library,
        program_min_size=program_min_size,
        program_max_size=program_max_size,
        max_conflicts=max_conflicts,
        local_string_max_len=local_string_max_len,
        fix_lines=fix_lines)


# ==============================================================================
# Synthesis


def enum(library, min_size, max_size, fix_lines):
    start = min_size
    stop = max_size + 1 if max_size else None

    for size in it.islice(it.count(), start, stop):
        logging.debug(f'Enumerating program size: {size}')

        if fix_lines:
            iter_ = it.product(library, repeat=size)
        else:
            iter_ = it.combinations_with_replacement(library, size)

        for components in iter_:
            components_names = tuple(c.name for c in components)
            logging.debug(f'Enumerated components: {components_names}')

            yield components


def oracle(components, examples, max_conflicts, local_max_len, fix_lines):
    ctx, program, constraints = \
        program_spec(components, examples, local_max_len, fix_lines)

    solver = z3.Solver(ctx=ctx)
    solver.add(*constraints)

    if max_conflicts:
        solver.set('max_conflicts', max_conflicts)

    start = time.time()
    check = solver.check()
    end = time.time()

    elapsed = end - start
    logging.debug(f'Solver result: {repr(check).upper()} ({elapsed:.3f} seconds)')

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
    local_max_len = config.local_string_max_len
    fix_lines = config.fix_lines

    for components in enum(library, min_size, max_size, fix_lines):
        res = oracle(components, examples, max_conflicts, local_max_len,
                     fix_lines)
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
