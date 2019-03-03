import pytest

from parser import parse


def test_expr():
    assert parse('"hello ""friend"""""')

    assert parse('a.b.c')
    assert parse('a  . b.c  ')

    assert parse('a[0].b.c')
    assert parse('a.b[0].c')
    assert parse('a.b.c[0]')
    assert parse('a.b[1].c[0]')

    assert parse('f()')
    assert parse('f(1, 2)')
    assert parse('f("Hello ", "world!")')
    assert parse('f(f("Hello", " "), "world!")')
    assert parse('f(1, -2)')
    assert parse('f(1, 2 * 3)')

    assert parse('-x')
    assert parse('not true')

    assert parse('x + y')
    assert parse('x + (y)')
    assert parse('(x) + (y)')
    assert parse('(x) + y')
    assert parse('x * (-y)')

    assert parse('1 + 1 / n + n')
    assert parse('f(x) + 1')
    assert parse('f(x) + 1 - 2')
    assert parse('f(x) + 1 -2')

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
