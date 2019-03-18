import itertools as it
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
def synth(examples, library=default_library, program_size=None):
    for size in it.islice(it.count(start=1), program_size):
        for components in it.combinations_with_replacement(library, size):
            solver = z3.Solver()

            with suppress(UnplugableComponents, UnusableInput):
                program = generate_program(components, examples)
                constraints = generate_constraints(program, examples)

                solver.add(*constraints)
                check = solver.check()

                if check == z3.sat:
                    model = solver.model()

                    from collections import OrderedDict
                    m = OrderedDict(sorted({repr(d): model[d] for d in model}.items()))

                    return True, (program, model)
    return False, ()


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
