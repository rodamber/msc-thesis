import pytest

from parser import parse


def test_expr():
    assert parse('\"hello\"')

    assert parse('this.should.succeed')
    assert parse('this  . should.succeed  ')

    assert parse('Null()')
    assert parse('Plus(1, 2)')
    assert parse('Concat(\"Hello \", \"world!\")')
    assert parse('Concat(Concat(\"Hello\", \" \"), \"world!\")')
    assert parse('Plus(1, -2)')
    assert parse('Plus(1, 2 * 3)')

    assert parse('-x')
    assert parse('not true')

    assert parse('x + y')
    assert parse('x + (y)')
    assert parse('(x) + (y)')
    assert parse('(x) + y')
    assert parse('x * (-y)')

    assert parse('1 + 1 / n + n')
    assert parse('Sqrt(x) + 1')
    assert parse('Sqrt(x) + 1 - 2')
    assert parse('Sqrt(x) + 1 -2')

    x = 'f(g(h(a.b.c.d.e)/1000-60*f(a.b.c.d.e/60000),3,"."," "),6,6,True,"0")'
    assert parse(x)

    x = 'a(b(c.d.e.f.g) >= 236, h(i.j.k.l.m, 0, 230), n.o.p.q.r)'
    assert parse(x)

    assert parse('(x - 1)')
    assert parse('(x - (1))')
    assert parse('(x) - 1')

    assert parse('f((g(x)-1)/7)')
    assert parse('f(g(x) + "abc" + "def")')
    assert parse('((x) + 1)')
    assert parse('(f(x))')
    assert parse('f((x))')
