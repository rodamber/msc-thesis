import datetime
from datetime import datetime as dt

from dataclasses import dataclass

import parsy
from parsy import generate

from typing import Any


@dataclass
class Token():
    val: Any


class Var(Token):
    pass


class String(Token):
    pass


class Number(Token):
    pass


class Op(Token):
    pass


class Keyword(Token):
    pass


class Date(Token):
    pass


@dataclass
class Time(Token):
    pass


@dataclass
class DateTime(Token):
    pass


whitespace = parsy.regex(r'\s*')
lexeme = lambda p: p << whitespace

lparen = lexeme(parsy.string('('))
rparen = lexeme(parsy.string(')'))
comma = lexeme(parsy.string(','))
dot = lexeme(parsy.string('.'))
colon = lexeme(parsy.string(':'))
pound = lexeme(parsy.string('#'))
dash = lexeme(parsy.string('-'))

simple_toks = [
    lparen,
    rparen,
    comma,
    # dot,
    colon,
    pound,
    dash
]

identifier = lexeme(
    parsy.regex(r'[_A-Za-z][_A-Za-z0-9]*')).desc('identifier').map(Var)
number = lexeme(
    parsy.regex(r'(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).desc(
        'number').map(Number)
keyword = (identifier.map(lambda x: x.val) << colon).map(Keyword)

op_list = ['+', '-', '*', '/', '=', '<>', '>', '<', '>=', '<=']
op = lexeme(parsy.string_from(*op_list)).map(Op)


@generate
def op_alpha():
    ops = ['not', 'or', 'and']
    tok = yield identifier
    return Op(tok.val) if tok.val in ops else parsy.fail('not, or, and')


string_part = parsy.regex(r'[^"]+')
string_esc = parsy.string("\"\"").result('"')


@generate
def string_lit():
    yield parsy.string('"')
    val = yield (string_part | string_esc).many().concat()
    yield parsy.string('"') << whitespace
    return String(val)


@generate
def dotted():
    base = (yield identifier).val
    field = (yield (dot + dotted.map(lambda t: t.val)).optional()) or ''
    return Var(base + field)


def dt_helper(digit_num, desc):
    return parsy.regex(f'[0-9]{{{digit_num}}}').map(int).desc(
        f'{digit_num} digit {desc}')


year = dt_helper(4, 'year')
month = dt_helper(2, 'month')
day = dt_helper(2, 'day')
hour = dt_helper(2, 'hour')
minute = dt_helper(2, 'minute')
second = dt_helper(2, 'second')

_date = parsy.seq(year, dash >> month, dash >> day).combine(datetime.date)
date = (pound >> _date << pound).map(Date)

_time = parsy.seq(hour, colon >> minute,
                  colon >> second).combine(datetime.time)
time = (pound >> _time << pound).map(Time)


@generate
def datetime():
    yield pound
    date = yield _date
    yield whitespace
    time = yield _time
    yield pound

    return DateTime(
        dt(date.year, date.month, date.day, time.hour, time.minute,
           time.second))


def test_dates():
    assert date.parse('#1988-08-28#')
    assert time.parse('#12:20:56#')
    assert datetime.parse('#1988-08-28 23:59:59#')


lexer = whitespace >> (string_lit | number | op | op_alpha | keyword | dotted
                       | date | time | datetime
                       | parsy.alt(*simple_toks)).many()


def lex(stream):
    return lexer.parse(stream)
