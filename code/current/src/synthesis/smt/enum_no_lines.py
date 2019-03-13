import itertools
from contextlib import suppress

import pyrsistent as p
import z3



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
    return set(tuple(zip(itertools.count(1), pair))
               for pair in itertools.product(components, repeat=size))


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

    # TODO Not sure if there's any real reason to return a map instead of a
    # vector.
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

class UnplugableComponents(Exception):
    pass

class UnusableInput(Exception):
    pass

# Constraint 01
def output_soundness(solver, holes_and_outputs):
    """
    Components output variables must indeed have the same value as the outputs
    of running the components on their input holes.
    """
    for (_, component), (holes, output) in holes_and_outputs.items():
        solver.add(output == component(*holes))


# Constraint 02
# FIXME The encoding prevents holes from taking arbitrary values, which is
# basically the whole point of doing this. (Note that maybe this only makes sense
# for some specific args of some specific functions, but this is domain specific
# knowledge).
# I believe that in order to get this property while allowing holes to take
# arbitrary values we must use a line encoding. I think it would also be needed
# to reconstruct the program.
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

        if not eqs:
            raise UnusableInput()
        solver.add(z3.Or(eqs))


# Constraint 04
# TODO In the disjunction, there are some redundant assertions being generated
# here, namely those that would be unsatisfiable by aciclicity, like h1 == o2,
# for example.
# FIXME The idea of this constraint is so that no component is redundant, but if
# there is no way to plug them together there's no point in considering them
# anyway.
def all_outputs_are_used(solver, holes_and_outputs, size):
    """
    All but the last of the component output variables must be used (in order to
    ensure that the every component is used).
    """
    hs_os = holes_and_outputs

    holes = p.pvector(h for _, (holes, _) in hs_os.items() for h in holes)
    outputs = p.pvector(
        o for (line, _), (_, o) in hs_os.items() if line < size)

    for o in outputs:
        eqs = tuple(h == o for h in holes if h.sort() == o.sort())

        if not eqs:
            raise UnplugableComponents()

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


# TODO tag fresh ids with example #
def synth(size, examples):
    assert all_equal(list(list(map(type, e.inputs)) for e in examples))
    assert all_equal(list(type(e.output) for e in examples))

    for components in product(size):
        if not isinstance(examples[0].output, ret_types[components[-1][1]]):
            continue

        fresh_hole = itertools.count(1)
        fresh_output = itertools.count(1)
        solver = z3.Solver()

        with suppress(UnplugableComponents, UnusableInput):
            for example in examples:
                is_ = inputs(solver, example)
                hs_os = holes_and_outputs(fresh_hole, fresh_output, components)

                output_soundness(solver, hs_os)
                correctness(solver, example, hs_os, size)
                aciclicity(solver, is_, hs_os)
                all_inputs_are_used(solver, is_, hs_os)
                all_outputs_are_used(solver, hs_os, size)

            if solver.check() == z3.sat:
                model = solver.model()

                print(solver.assertions())
                print(model)

                return solver


def test_synth():
    print('=================================================================')

    examples = [Example(inputs=('John', 'Doe'), output='John Doe'),
                Example(inputs=('Jane', 'Doe'), output='Jane Doe'),
                Example(inputs=('James', 'Brown'), output='James Brown')]
    synth(2, examples)

    print('=================================================================')

    # If the output appears directly in the input, there's a big possibility of
    # a replacing messing everything up.
    examples = [
        Example(
            inputs=('outsystems.com', 'outsystems', 'cmu', 0, '.'),
            output='cmu.com'),
        Example(inputs=('xyz.com', 'xyz', 'abc', 0, '.'), output=('abc.com'))
    ]

    # substr(replace(_1, _2, _3), _4, index(_1, _5))
    synth(2, examples)

    print('=================================================================')
