from lexer import lexer
from parser import atom, func, unop, binop, expr

parse_ = lambda p, x: p.parse(lexer.parse(x))


def test_func():
    assert parse_(func, 'Plus(1, 2)')
    assert parse_(func, 'Concat(\"Hello \", \"world!\")')
    assert parse_(func, 'Concat(Concat(\"Hello\", \" \"), \"world!\")')
    assert parse_(func, 'Plus(1, -2)')
    assert parse_(func, 'Plus(1, 2 * 3)')


def test_unop():
    assert parse_(unop, '-x')
    assert parse_(unop, 'not true')


def test_binop_unary():
    assert parse_(binop, 'x')
    assert parse_(binop, '-x')


def test_binop_simple():
    assert parse_(binop, 'x + y')
    assert parse_(binop, 'x + (y)')
    assert parse_(binop, 'x * (-y)')


def test_binop_complex():
    assert parse_(binop, '1 + 1 / n + n')


def test_expr():
    assert parse_(expr, 'Plus(1, 2)')
    assert parse_(expr, 'Concat(\"Hello \", \"world!\")')
    assert parse_(expr, 'Concat(Concat(\"Hello\", \" \"), \"world!\")')
    assert parse_(expr, 'Plus(1, -2)')
    assert parse_(expr, 'Plus(1, 2 * 3)')

    assert parse_(expr, '-x')
    assert parse_(expr, 'not true')

    assert parse_(expr, 'x + y')
    assert parse_(expr, 'x + (y)')
    assert parse_(expr, 'x * (-y)')
    assert parse_(expr, '1 + 1 / n + n')

    assert parse_(expr, 'Sqrt(x) + 1')
    assert parse_(expr, 'Sqrt(x) + 1 - 2')
    assert parse_(expr, 'Sqrt(x) + 1 -2')

    test = 'FormatText(FormatDecimal(IntegerToDecimal(AuditList.List.Current.AUDIT.Duration)/1000-60*Trunc(AuditList.List.Current.AUDIT.Duration/60000),3,"."," "),6,6,True,"0")'
    assert parse_(expr, test)
