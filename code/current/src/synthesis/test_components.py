import pytest
import z3

from .components import *
from .utils import z3_val, z3_as


@pytest.mark.parametrize(
    'spec,inputs,output',
    [
        # Replace 01
        (replace_spec_01, ['22/10/1994', '/', '-'], '22-10-1994'),
        (replace_spec_01, ['#22/10/1994#', '#', '|'], '|22/10/1994|'),

        # Replace 02
        (replace_spec_02, ['22/10/1994', '/', '-'], '22-10-1994'),
        (replace_spec_02, ['#22/10/1994#', '#', '|'], '|22/10/1994|'),

        # Lower
        (lower_spec, ['ABCDEF'], 'abcdef'),
        (lower_spec, ['abcDef'], 'abcdef'),
        (lower_spec, ['aB1cDeF0'], 'ab1cdef0'),

        # Upper
        (upper_spec, ['abcdef'], 'ABCDEF'),
        (upper_spec, ['abCdef'], 'ABCDEF'),
        (upper_spec, ['Ab1CdEf0'], 'AB1CDEF0'),

        # Trim left
        (ltrim_spec, ['    abc'], 'abc'),
        (ltrim_spec, ['abc'], 'abc'),
        (ltrim_spec, ['a b c '], 'a b c '),

        # Trim right
        (rtrim_spec, ['abc    '], 'abc'),
        (rtrim_spec, ['abc'], 'abc'),
        (rtrim_spec, [' a b c'], ' a b c'),

        # Trim
        (trim_spec, ['abc    '], 'abc'),
        (trim_spec, ['abc'], 'abc'),
        (trim_spec, [' a b c'], 'a b c'),
    ])
def test_spec(spec, inputs, output):
    ctx = z3.Context()

    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=1 * 60 * 1000)

    _inputs = [z3_val(i, ctx) for i in inputs]
    _output = z3_val(output, ctx)

    solver.add(spec(ctx, _output, *_inputs))
    assert solver.check() == z3.sat


@pytest.mark.parametrize('text,expected', [('A', 'a'), ('B', 'b'), ('C', 'c'),
                                           ('D', 'd'), ('E', 'e'), ('F', 'f')])
def test_lower_char(text, expected):
    ctx = z3.Context()

    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=1 * 60 * 1000)

    char = z3.StringVal(text, ctx)
    output = z3.FreshConst(z3.StringSort(ctx))

    solver.add(output == lower_char(ctx)(char))

    assert solver.check() == z3.sat
    assert solver.model().eval(lower_char(ctx)(char)).as_string() == expected
    # assert solver.model().eval(output).as_string() == expected
