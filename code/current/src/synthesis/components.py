import string
import z3

from .types import Component
from .utils import z3_val


def concat_spec(context, output, x, y):
    return output == z3.Concat(x, y)


concat = Component(
    name='concat', domain=(str, str), ret_type=str, spec=concat_spec)


def index_spec(context, output, haystack, needle):
    return z3.And(output == z3.IndexOf(haystack, needle, 0),
                  needle != z3_val('', context), context)


index = Component(
    name='index', domain=(str, str), ret_type=int, spec=index_spec)


def index3_spec(context, output, haystack, needle, start_index):
    return z3.And(
        output == z3.IndexOf(haystack, needle, start_index),
        needle != z3_val('', context),
        start_index > z3_val(0, context),  # use index otherwise
        context)


index3 = Component(
    name='index3', domain=(str, str, int), ret_type=int, spec=index3_spec)


def length_spec(context, output, text):
    return output == z3.Length(text)


length = Component(
    name='length', domain=(str, ), ret_type=int, spec=length_spec)


def replace_spec_01(context, output, text, old, new):
    f = z3.RecFunction('replace_all', z3.StringSort(context),
                       z3.StringSort(context), z3.StringSort(context),
                       z3.StringSort(context))

    neg_one = z3.IntVal(-1, context)
    zero = z3.IntVal(0, context)

    left = lambda text, old: \
        z3.SubString(text,
                     zero,
                     z3.IndexOf(text, old, zero))
    right = lambda text, old: \
        z3.SubString(text,
                     z3.IndexOf(text, old, zero) + z3.Length(old),
                     z3.Length(text))

    # FIXME Should use new consts as args
    z3.RecAddDefinition(
        f, [text, old, new],
        z3.If(
            z3.IndexOf(text, old, zero) == neg_one, text,
            z3.Concat(left(text, old), new, f(right(text, old), old, new)),
            context))

    return output == f(text, old, new)


def replace_spec_02(context, output, text, old, new):
    f = z3.RecFunction('replace_all', z3.StringSort(context),
                       z3.StringSort(context), z3.StringSort(context),
                       z3.StringSort(context))

    # FIXME Should use new consts as args
    z3.RecAddDefinition(
        f, [text, old, new],
        z3.If(
            z3.Or(old == new, z3.Not(z3.Contains(text, old),
                                     context), context), text,
            f(z3.Replace(text, old, new), old, new), context))

    return output == f(text, old, new)


replace = Component(
    name='replace',
    domain=(str, str, str),
    ret_type=str,
    spec=replace_spec_02,
    # spec=lambda ctx, x, y, z: z3.And(x != y, z3.Contains(x, y), ctx)
)


# FIXME: Partial specifications probably don't work well with magic constants
def replace_over_spec(context, output, text, old, new):
    zero = z3.IntVal(0, context)
    empty = z3.StringVal('', context)

    ix_old = z3.IndexOf(text, old, zero)
    ix_new = z3.IndexOf(output, new, zero)

    c1 = ix_old == ix_new
    c2 = z3.Contains(text, old)
    c3 = z3.Contains(output, new)
    c4 = old != new
    c5 = old != empty

    c6 = z3.SubString(text, 0, ix_old) == z3.SubString(output, 0, ix_new)

    return z3.And(c1, c2, c3, c4, c5, c6, context)


replace_over = Component(
    name='replace',
    domain=(str, str, str),
    ret_type=str,
    spec=replace_over_spec,
)


def substr_spec(context, output, text, start, length):
    return output == z3.SubString(text, start, length)


substr = Component(
    name='substr',
    domain=(str, int, int),
    ret_type=str,
    spec=substr_spec,
    # spec=lambda ctx, text, i, n: n == z3.Length(z3.SubString(text, i, n))
)


def add_spec(context, output, x, y):
    return output == x + y


add = Component(name='add', domain=(int, int), ret_type=int, spec=add_spec)


def sub_spec(context, output, x, y):
    return output == x - y


sub = Component(name='sub', domain=(int, int), ret_type=int, spec=sub_spec)


def head(context, s):
    zero = z3_val(0, context)
    return s[zero]


def last(context, s):
    one = z3_val(1, context)
    return s[z3.Length(s) - one]


def tail(context, s):
    one = z3_val(1, context)
    return z3.SubString(s, one, z3.Length(s))


def init(context, s):
    zero = z3_val(0, context)
    one = z3_val(1, context)
    return z3.SubString(s, zero, z3.Length(s) - one)


def is_whitespace(context, c):
    space = z3_val(" ", context)
    newline = z3_val("\n", context)
    tab = z3_val("\t", context)
    return z3.Or(c == space, c == newline, c == tab, context)


def trim_left(context, text):
    f = z3.RecFunction('trim_left', z3.StringSort(context),
                       z3.StringSort(context))

    z3.RecAddDefinition(
        f, text,
        z3.If(
            is_whitespace(context, head(context, text)), f(
                tail(context, text)), text, context))

    return f(text)


def trim_right(context, text):
    f = z3.RecFunction('trim_right', z3.StringSort(context),
                       z3.StringSort(context))

    z3.RecAddDefinition(
        f, text,
        z3.If(
            is_whitespace(context, last(context, text)), f(
                init(context, text)), text, context))

    return f(text)


def ltrim_spec(context, output, text):
    return output == trim_left(context, text)


def rtrim_spec(context, output, text):
    return output == trim_right(context, text)


def trim_spec(context, output, text):
    return output == trim_left(context, trim_right(context, text))


ltrim = Component(name='ltrim', domain=(str, ), ret_type=str, spec=ltrim_spec)
rtrim = Component(name='rtrim', domain=(str, ), ret_type=str, spec=rtrim_spec)
trim = Component(name='trim', domain=(str, ), ret_type=str, spec=trim_spec)


def newline_spec(context, output):
    return output == z3.StringVal('\n', context)


newline = Component(name='newline', domain=(), ret_type=str, spec=newline_spec)


def case_char(name, map_, ctx=z3.main_ctx()):
    char = z3.FreshConst(z3.StringSort(ctx))
    const = char
    for x, y in map_:
        const = z3.If(char == z3.StringVal(x, ctx), z3.StringVal(y, ctx),
                      const, ctx)

    f = z3.RecFunction(f'{name}_char', z3.StringSort(ctx), z3.StringSort(ctx))
    z3.RecAddDefinition(f, char, const)

    return f


def lower_char(ctx=z3.main_ctx()):
    map_ = zip(string.ascii_uppercase, string.ascii_lowercase)
    return case_char('lower', map_, ctx)


def upper_char(ctx=z3.main_ctx()):
    map_ = zip(string.ascii_lowercase, string.ascii_uppercase)
    return case_char('upper', map_, ctx)


def case_spec(name, name_char, ctx, output, text):
    f = z3.RecFunction(name, z3.StringSort(ctx), z3.StringSort(ctx))

    empty = z3.StringVal("", ctx)

    z3.RecAddDefinition(
        f, text,
        z3.If(text == empty, empty,
              z3.Concat(name_char(ctx)(head(ctx, text)), f(tail(ctx, text)))))

    return output == f(text)


def lower_spec(ctx, output, text):
    return case_spec('lower', lower_char, ctx, output, text)


def upper_spec(ctx, output, text):
    return case_spec('upper', upper_char, ctx, output, text)


lower = Component(name='lower', domain=(str, ), ret_type=str, spec=lower_spec)
upper = Component(name='upper', domain=(str, ), ret_type=str, spec=upper_spec)

# Missing:
# chr, encodehtml, encodejavascript, encodesql, encodeurl
