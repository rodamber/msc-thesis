import string
from typing import Callable, Dict

import z3

from .types import SInt, SStr

# ==============================================================================
#                               Symbolic Functions
# ==============================================================================

# ==============================================================================
# Text


def SChr(code: SInt) -> z3.SeqRef:
    raise NotImplementedError()


def SConcat(x: SStr, y: SStr) -> z3.SeqRef:
    return z3.Concat(x.expr, y.expr)


# TODO Support for searchFromEnd and ignoreCase
def SIndex(haystack: SStr, needle: SStr, offset: SInt) -> z3.ArithRef:
    return z3.IndexOf(haystack.expr, needle.expr, offset.expr)


def SLength(text: SStr) -> z3.ArithRef:
    return z3.Length(text.expr)


def SNewLine(ctx: z3.Context) -> z3.SeqRef:
    return z3.StringVal('\n', ctx=ctx)


# TODO Check out these:
# https://stackoverflow.com/questions/13198158/proving-inductive-facts-in-z3
# https://stackoverflow.com/questions/10473042/list-concat-in-z3
# https://www.youtube.com/watch?v=o9wWQ7KPxW8&t=844s
# TODO Try this:
# (define-fun-rec replaceAll ((s String) (t1 String) (t2 String)) String
#  (let ((start (str.indexof s t1 0)))
#   (ite (= (- 1) start)
#    s
#    (let ((end (+ start (str.len t1))))
#     (str.++ (str.substr s 0 start)
#      t2
#      (replaceAll (str.substr s end (- (str.len s) end))
#       t1
#       t2))))))
def SReplace(text: SStr, old: SStr, new: SStr) -> z3.SeqRef:
    ctx = text.ctx

    text, old, new = text.expr, old.expr, new.expr
    empty = z3.StringVal("", ctx)

    replace_all = z3.RecFunction('replace_all', \
        z3.StringSort(ctx), z3.StringSort(ctx), z3.StringSort(ctx), # from
        z3.StringSort(ctx))                                         # to

    z3.RecAddDefinition(replace_all, [text, old, new], \
        z3.If(z3.Or(old == empty, \
                    z3.Not(z3.Contains(text, old)), ctx),\
              text,
              replace_all(z3.Replace(text, old, new), \
                          old,
                          new)))

    return replace_all(text, old, new)


def SSubstr(text: SStr, offset: SInt, length: SInt) -> z3.SeqRef:
    return z3.SubString(text.expr, offset.expr, length.expr)


def SToLower(text: SStr) -> z3.SeqRef:
    return to_case('lower', lower_char, text.expr)


def SToUpper(text: SStr) -> z3.SeqRef:
    return to_case('upper', upper_char, text.expr)


def STrim(text: SStr) -> z3.SeqRef:
    return trim_end(trim_start(text.expr))


def STrimStart(text: SStr) -> z3.SeqRef:
    return trim_start(text.expr)


def STrimEnd(text: SStr) -> z3.SeqRef:
    return trim_end(text.expr)


# ==============================================================================
# Arithmetic


def SAdd(x: SInt, y: SInt) -> z3.ArithRef:
    return x.expr + y.expr


def SSub(x: SInt, y: SInt) -> z3.ArithRef:
    return x.expr - y.expr


# ==============================================================================
# Helpers
# ==============================================================================

# ==============================================================================
# General Helpers


def head(s: z3.SeqRef) -> z3.SeqRef:
    ctx = s.ctx
    zero = z3.IntVal(0, ctx)
    return s[zero]


def last(s: z3.SeqRef) -> z3.SeqRef:
    ctx = s.ctx
    one = z3.IntVal(1, ctx)
    return s[z3.Length(s) - one]


def tail(s: z3.SeqRef) -> z3.SeqRef:
    ctx = s.ctx
    one = z3.IntVal(1, ctx)
    return z3.SubString(s, one, z3.Length(s))


def init(s: z3.SeqRef) -> z3.SeqRef:
    ctx = s.ctx
    zero = z3.IntVal(0, ctx)
    one = z3.IntVal(1, ctx)
    return z3.SubString(s, zero, z3.Length(s) - one)


# ==============================================================================
# ToLower and ToUpper Helpers


def case_char(name: str, map_: Dict[str, str], ctx: z3.Context) \
    -> z3.FuncDeclRef:
    char = z3.FreshConst(z3.StringSort(ctx))

    const = char
    for x, y in map_:
        const = z3.If(char == z3.StringVal(x, ctx), \
                      z3.StringVal(y, ctx),
                      const, ctx)

    f = z3.RecFunction(f'{name}_char', z3.StringSort(ctx), z3.StringSort(ctx))
    z3.RecAddDefinition(f, char, const)

    return f


def lower_char(ctx: z3.Context) -> z3.FuncDeclRef:
    map_ = zip(string.ascii_uppercase, string.ascii_lowercase)
    return case_char('lower', map_, ctx)


def upper_char(ctx: z3.Context) -> z3.FuncDeclRef:
    map_ = zip(string.ascii_lowercase, string.ascii_uppercase)
    return case_char('upper', map_, ctx)


def to_case(name: str, name_char: Callable[[z3.Context], z3.FuncDeclRef], \
            text: z3.SeqRef) -> z3.SeqRef:
    ctx = text.ctx
    empty = z3.StringVal("", ctx)

    f = z3.RecFunction(name, z3.StringSort(ctx), z3.StringSort(ctx))
    z3.RecAddDefinition(f, text, \
        z3.If(text == empty, \
              empty,
              z3.Concat(name_char(ctx)(head(text)), \
                        f(tail(text)))))

    return f(text)


# ==============================================================================
# Trim helpers


def reverse(s: z3.SeqRef) -> z3.SeqRef:
    ctx = s.ctx

    empty = z3.StringVal("", ctx)
    acc = z3.FreshConst(z3.StringSort(ctx), 'acc')

    tail_rev = z3.RecFunction('reverse', \
                              z3.StringSort(ctx), z3.StringSort(ctx), \
                              z3.StringSort(ctx))
    z3.RecAddDefinition(tail_rev, [s, acc], \
                        z3.If(s == empty, \
                              acc,
                              tail_rev(tail(s),
                                       z3.Concat(head(s), acc))))

    rev = z3.RecFunction('reverse', z3.StringSort(ctx), \
                         z3.StringSort(ctx))
    z3.RecAddDefinition(rev, s, tail_rev(s, empty))

    return rev(s)


def is_whitespace(c: z3.SeqRef) -> z3.BoolRef:
    ctx = c.ctx
    space = z3.StringVal(" ", ctx)
    newline = z3.StringVal("\n", ctx)
    tab = z3.StringVal("\t", ctx)
    return z3.Or(c == space, c == newline, c == tab, ctx)


def trim_start(s: z3.SeqRef) -> z3.SeqRef:
    ctx = s.ctx

    trim_start = z3.RecFunction('trim_start', z3.StringSort(ctx), \
                                z3.StringSort(ctx))
    z3.RecAddDefinition(trim_start, s, \
        z3.If(is_whitespace(head(s)), \
              trim_start(tail(s)),
              s))

    return trim_start(s)


def trim_end(s: z3.SeqRef) -> z3.SeqRef:
    return reverse(trim_start(reverse(s)))
