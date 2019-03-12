import itertools

import pyrsistent as p
import z3
from toolz import mapcat

from ..dsl import component as comp
from ..dsl.component import Component


# Components
def concat(x, y):
    return z3.Concat(x, y)


def length(x):
    return z3.Length(x)


def replace(x, y, z):
    return z3.Replace(x, y, z)


def index(text, x):
    return z3.IndexOf(text, x, 0)  # OutSystems' Binary index


def substr(text, i, j):
    return z3.SubString(text, i, j - i)


# index = lambda text, x: z3.IndexOf(text, x, 0)  # OutSystems' Binary index
# substr = lambda text, i, j: z3.SubString(text, i, j - i)

components = (concat, index, length, replace, substr)

domains = {
    concat: (str, str),
    index: (str, str),
    length: (str, ),
    replace: (str, str, str),
    substr: (str, int, int),
}

ret_types = {
    concat: str,
    index: int,
    length: int,
    replace: str,
    substr: str,
}


class Example(p.PRecord):
    inputs = p.pvector_field(object)
    output = p.field(mandatory=True)


def z3const(letter, ix, typ):
    name = f'{letter}{ix}'

    if typ == int:
        return z3.Int(name)
    elif typ == str:
        return z3.String(name)
    else:
        raise ValueError(f'z3const: invalid typ ({typ})')


def z3val(val):
    if isinstance(val, int):
        return z3.IntVal(val)
    elif isinstance(val, str):
        return z3.StringVal(val)
    else:
        raise ValueError(f'z3val: invalid typ ({typ})')


def product(size):
    """
    Enumerate components. Order matters: components that appear first here will
    appear first in the lines of the synthesized program. Meaning, if the result
    is (INDEX, LENGTH, SUBSTR) then the program would be something like:
    o1 = INDEX(.,.)
    o2 = LENGTH(.)
    o3 = SUBSTR(.,.,.)
    """
    for pair in itertools.product(components, repeat=size):
        yield tuple(zip(itertools.count(1), pair))


def inputs(solver, example):
    """
    Example input variables (which are actually z3 values).
    """
    return p.pvector(z3val(x) for x in example.inputs)


def _holes(fresh, component):
    """
    Hole variables. Given a component, create z3 variables for each
    of its holes.
    """
    return p.pvector(
        z3const('h', next(fresh), typ) for typ in domains[component])


def _output(fresh, component):
    """
    Component output variable.
    """
    return z3const('o', next(fresh), ret_types[component])


def holes_and_outputs(fresh_hole, fresh_output, components):
    """
    Return a dictionary mapping components to their holes and output variables.
    """

    def gen():
        for line, c in components:
            holes = _holes(fresh_hole, c)
            output = _output(fresh_output, c)

            yield (line, c), (holes, output)

    return p.pmap(gen())


"""
# Constraints
 1. Components output variables must indeed have the same value as the outputs of
  running the components on their input holes.
 2. Aciclicity: variables cannot be used before they are defined.
 3. All inputs must be used (otherwise the synthesized program might be trash)
 4. All but the last of the component output variables must be used (in order to
  ensure that the every component is used).
 5. Correctness: The last output variable must equal the output of the test case.
"""


# Constraint 01
def output_soundness(solver, holes_and_outputs):
    """
    Components output variables must indeed have the same value as the outputs
    of running the components on their input holes.
    """
    for (_, component), (holes, output) in holes_and_outputs.items():
        solver.add(output == component(*holes))


# Constraint 02
# FIXME The enconding prevents holes from taking arbitrary values, which is
# basically the whole point of doing this. I believe that in order to get this
# property while allowing holes to take arbitrary values we must use a line
# enconding.
def aciclicity(solver, inputs, holes_and_outputs):
    """
    Make sure that no variable is used before it is defined.
    """
    hs_os = holes_and_outputs

    for (k, c), (holes, _) in hs_os.items():
        outputs = p.pvector(
            o for (line, _), (_, o) in hs_os.items() if line < k)

        for h in holes:
            cons1 = p.pvector(h == i for i in inputs if h.sort() == i.sort())
            cons2 = p.pvector(h == o for o in outputs if h.sort() == o.sort())

            solver.add(z3.Or(*cons1, *cons2))


# Constraint 03
def all_inputs_are_used(solver, inputs, holes_and_outputs):
    """
    All inputs must be used (otherwise the synthesized program might be trash).
    """
    holes = p.pvector(
        h for _, (holes, _) in holes_and_outputs.items() for h in holes)

    for i in inputs:
        eqs = tuple(h == i for h in holes if h.sort() == i.sort())

        if eqs:
            solver.add(z3.Or(eqs))


# Constraint 04
# FIXME In the disjunction, there are some redundant assertions being generated
# here, namely those that would be unsatisfiable by aciclicity, like h1 == o2,
# for example.
def all_outputs_are_used(solver, holes_and_outputs, size):
    """
    All but the last of the component output variables must be used (in order to
    ensure that the every component is used).
    """
    hs_os = holes_and_outputs

    holes = p.pvector(h for _, (holes, _) in hs_os.items() for h in holes)
    outputs = p.pvector(
        o for (line, _), (_, o) in hs_os.items() if line < size)

    eqs = tuple(h == o for h in holes for o in outputs if h.sort() == o.sort())

    if eqs:
        solver.add(z3.Or(eqs))


# Constraint 05
def correctness(solver, example, holes_and_outputs, size):
    """
    The last output variable must equal the output of the test case.
    """
    hs_os = holes_and_outputs

    output = next(o for (line, _), (_, o) in hs_os.items() if line == size)
    solver.add(output == z3val(example.output))


class z3_scope:
    def __init__(self, solver):
        self.solver = solver

    def __enter__(self):
        self.solver.push()

    def __exit__(self, type, value, traceback):
        self.solver.pop()


def all_equal(xs):
    return xs[1:] == xs[:-1]


# FIXME Generalize to more than one example
# TODO tag fresh ids with example #
def synth(size, examples):
    assert all_equal(list(list(map(type, e.inputs)) for e in examples))
    assert all_equal(list(type(e.output) for e in examples))

    for components in product(size):
        fresh_hole = itertools.count(1)
        fresh_output = itertools.count(1)

        if not isinstance(examples[0].output, ret_types[components[-1][1]]):
            continue

        solver = z3.Solver()

        for example in examples:
            is_ = inputs(solver, example)
            hs_os = holes_and_outputs(fresh_hole, fresh_output, components)

            output_soundness(solver, hs_os)
            aciclicity(solver, is_, hs_os)
            all_inputs_are_used(solver, is_, hs_os)
            all_outputs_are_used(solver, hs_os, size)
            correctness(solver, example, hs_os, size)

        if solver.check() == z3.sat:
            model = solver.model()

            # FIXME I think that to be able to reconstruct the program we need
            # to use a line enconding.

            print(model)
            # print(solver.assertions())

            for (line, component), (holes, output) in hs_os.items():
                print(f'{line}: {component} {tuple(holes)} {output}')

            return


def test_synth():
    # example = Example(inputs=('John', 'Doe'), output='John Doe')

    # example = Example(inputs=('Hello', ' world!'), output='Hello world!')
    # synth(1, example)

    # print('=================================================================')

    # example = Example(inputs=('Hello', ' ', 'world!'), output='Hello world!')
    # synth(2, example)

    # print('=================================================================')

    # example = Example(inputs=('outsystems.com', '.', 0), output='outsystems')
    # synth(3, example)

    print('=================================================================')

    examples = [
        Example(
            inputs=('outsystems.com', 'outsystems', 'cmu', 0, '.'),
            output='cmu'),
        Example(inputs=('xyz.com', 'xyz', 'abc', 0, '.'), output=('abc'))
    ]
    # substr(replace(_1, _2, _3), _4, index(_1, _5))
    synth(3, examples)

    print('=================================================================')
