from typing import Callable, Tuple, Union

import pytest
from z3 import Context, ExprRef, Solver, StringVal, sat, unsat

from simple.functions import *
from simple.types import Kind, kind, Const
from simple.utils import z3_val

# ==============================================================================
#                               Symbol Functions
# ==============================================================================


def abstract_sfun_test(fun: Callable[..., ExprRef], \
                       params: Tuple[Union[str, int], ...],
                       expected: Union[str, int],
                       xfail=False):
    ctx = Context()
    solver = Solver(ctx=ctx)

    cs = [Const(k, kind(p), k, ctx) for k, p in enumerate(params)]

    solver.add([c == z3_val(p, ctx) for c, p in zip(cs, params)])
    solver.add(z3_val(expected, ctx) == fun(*cs))

    if not xfail:
        assert solver.check() == sat
    else:
        assert solver.check() == unsat


@pytest.mark.parametrize('params,expected', [
    (['John Doe', ' ', '_'], 'John_Doe'), \
    (['Michael Scott', ' ', '_'], 'Michael_Scott'),
    (['01/02/2000', '/', '-'], '01-02-2000'),
])
def test_sreplace(params, expected):
    abstract_sfun_test(SReplace, params, expected)


@pytest.mark.parametrize('params,expected', [
    (['#01/23/4567#', '#', '|', '/', '-'], '|01-23-4567|'),
])
def test_sreplace2(params, expected):
    ctx = Context()
    solver = Solver(ctx=ctx)

    cs = [Const(k, kind(p), k, ctx) for k, p in enumerate(params)]
    r = Const(5, Kind.STR, 5, ctx)

    solver.add([c == z3_val(p, ctx) for c, p in zip(cs, params)])
    solver.add(r == SReplace(cs[0], cs[1], cs[2]))
    solver.add(z3_val(expected, ctx) == SReplace(r, cs[3], cs[4]))

    assert solver.check() == sat


@pytest.mark.parametrize('params,expected', [
    (['abc'], 'abc'), \
    (['ABC'], 'abc'),
    (['aBc'], 'abc'),
    (['aBC'], 'abc'),
    (['a B C'], 'a b c'),
])
def test_stolower(params, expected):
    abstract_sfun_test(SToLower, params, expected)


@pytest.mark.parametrize('params,not_expected', [
    (['01/02/2000'], '01-02-2000'), \
    (['02/03/1999'], '02-03-1999'),
])
def test_stolower_fail(params, not_expected):
    abstract_sfun_test(SToLower, params, not_expected, xfail=True)


@pytest.mark.parametrize('params,expected', [
    (['abc'], 'ABC'),
    (['ABC'], 'ABC'),
    (['aBc'], 'ABC'),
    (['aBC'], 'ABC'),
    (['a B C'], 'A B C'),
])
def test_stoupper(params, expected):
    abstract_sfun_test(SToUpper, params, expected)


@pytest.mark.parametrize('params,expected', [
    ([' abc '], 'abc'),
    (['  abc'], 'abc'),
    (['abc  '], 'abc'),
    (['\tabc\t \n'], 'abc'),
    (['   a b c   '], 'a b c'),
])
def test_strim(params, expected):
    abstract_sfun_test(STrim, params, expected)


@pytest.mark.parametrize('params,expected', [
    ([' abc'], 'abc'),
    (['  abc'], 'abc'),
    (['abc  '], 'abc  '),
    (['\tabc\t \n'], 'abc\t \n'),
    (['   a b c   '], 'a b c   '),
])
def test_strim_start(params, expected):
    abstract_sfun_test(STrimStart, params, expected)


@pytest.mark.parametrize('params,expected', [
    ([' abc '], ' abc'),
    (['  abc'], '  abc'),
    (['abc  '], 'abc'),
    (['\tabc\t \n'], '\tabc'),
    (['   a b c   '], '   a b c'),
])
def test_strim_end(params, expected):
    abstract_sfun_test(STrimEnd, params, expected)


# ==============================================================================
#                                   Helpers
# ==============================================================================


def abstract_helper_test(fun: Callable[..., ExprRef], \
                         params: Tuple[ExprRef, ...],
                         expected: ExprRef,
                         xfail=False):
    ctx = Context()
    solver = Solver(ctx=ctx)

    args = [z3_val(p, ctx) for p in params]
    solver.add(fun(*args) == z3_val(expected, ctx))

    if not xfail:
        assert solver.check() == sat
    else:
        assert solver.check() == unsat


@pytest.mark.parametrize('params,expected', [
    (['John Doe'], 'J'), \
    (['Michael Scott'], 'M'),
    (['01/02/2000'], '0'),
    ([''], ''),
])
def test_head(params, expected):
    abstract_helper_test(head, params, expected)


@pytest.mark.parametrize('params,expected', [
    (['John Doe'], 'ohn Doe'), \
    (['Michael Scott'], 'ichael Scott'),
    (['01/02/2000'], '1/02/2000'),
    ([''], ''),
])
def test_tail(params, expected):
    abstract_helper_test(tail, params, expected)


@pytest.mark.parametrize('params,expected', [
    (['John Doe'], 'eoD nhoJ'), \
    (['Michael Scott'], 'ttocS leahciM'),
    (['01/02/2000'], '0002/20/10'),
    ([''], ''),
])
def test_reverse(params, expected):
    abstract_helper_test(reverse, params, expected)
