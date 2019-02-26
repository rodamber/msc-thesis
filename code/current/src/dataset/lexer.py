from parsy import *

whitespace = regex(r'\s*')
lexeme = lambda p: p << whitespace

identifier = lexeme(regex(r'[_A-Za-z][_A-Za-z0-9]+')).desc('identifier')
number = lexeme(
    regex(r'-?(0|[1-9][0-9]*)([.][0-9]+)?([eE][+-]?[0-9]+)?')).desc('number')

lparen = lexeme(string('('))
rparen = lexeme(string(')'))

comma = lexeme(string(','))
dot = lexeme(string('.'))

op = lexeme(char_from('+-*/='))
keyword = lexeme(string_from('not', 'or', 'and') << char_from(' '))

string_part = regex(r'[^"\\]+')
string_esc = string('\\') >> (
    string('\\')
    | string('/')
    | string('"')
    | string('b').result('\b')
    | string('f').result('\f')
    | string('n').result('\n')
    | string('r').result('\r')
    | string('t').result('\t')
    | regex(r'u[0-9a-fA-F]{4}').map(lambda s: chr(int(s[1:], 16))))


@generate
def quoted():
    yield string('"')
    res = yield (string_part | string_esc).many().concat()
    yield string('"') << whitespace
    return res


def test_quoted():
    assert quoted.parse('\"hello\"')


@generate
def dotted():
    base = yield identifier
    field = (yield (dot + dotted).optional()) or ''
    return base + field


def test_dotted():
    assert dotted.parse('this.should.succeed')
    assert dotted.parse('this  . should.succeed  ')


lexer = (quoted | number | dotted | lparen | rparen | comma | op
         | keyword).many()
