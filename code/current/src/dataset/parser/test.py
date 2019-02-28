import pytest

from lexer import lexer, quoted, dotted
from parser import atom, func, unop, binop, expr, parse, parse_partial, pt

parse_ = lambda p, x: p.parse(lexer.parse(x))


def test_quoted():
    assert quoted.parse('\"hello\"')


def test_dotted():
    assert dotted.parse('this.should.succeed')
    assert dotted.parse('this  . should.succeed  ')


def helper(stream):
    return lexer.parse(stream) and parse(stream)


def test_expr():
    assert helper('Null()')
    assert helper('Plus(1, 2)')
    assert helper('Concat(\"Hello \", \"world!\")')
    assert helper('Concat(Concat(\"Hello\", \" \"), \"world!\")')
    assert helper('Plus(1, -2)')
    assert helper('Plus(1, 2 * 3)')

    assert helper('-x')
    assert helper('not true')

    assert helper('x + y')
    assert helper('x + (y)')
    assert helper('x * (-y)')
    assert helper('1 + 1 / n + n')

    assert helper('Sqrt(x) + 1')
    assert helper('Sqrt(x) + 1 - 2')
    assert helper('Sqrt(x) + 1 -2')

    x = 'FormatText(FormatDecimal(IntegerToDecimal(AuditList.List.Current.AUDIT.Duration)/1000-60*Trunc(AuditList.List.Current.AUDIT.Duration/60000),3,"."," "),6,6,True,"0")'
    assert helper(x)


def dataset():
    import jsonlines

    with jsonlines.open('../../../dataset/exprs-3-6.jsonl') as reader:
        for obj in reader:
            try:
                if not helper(obj['text']):
                    return obj['text']
            except:
                return obj['text']
