import z3

from .types import Component
from .utils import z3_val

concat = Component(
    name='concat',
    domain=(str, str),
    ret_type=str,
    function=lambda x, y: z3.Concat(x, y))

index = Component(
    name='index',
    domain=(str, str),
    ret_type=int,
    function=lambda text, x: z3.IndexOf(text, x, 0),
    spec=lambda ctx, text, x: x != z3_val('', ctx))

index3 = Component(
    name='index3',
    domain=(str, str, int),
    ret_type=int,
    function=lambda text, x, y: z3.IndexOf(text, x, y),
    spec=lambda ctx, text, x, y: \
        z3.And(x != z3_val('', ctx),
               y > z3_val(0, ctx), # use index otherwise
               ctx))

length = Component(
    name='length',
    domain=(str, ),
    ret_type=int,
    function=lambda x: z3.Length(x))

replace = Component(
    name='replace',
    domain=(str, str, str),
    ret_type=str,
    function=lambda x, y, z: z3.Replace(x, y, z),
    # spec=lambda ctx, x, y, z: z3.And(x != y, z3.Contains(x, y), ctx)
)

substr = Component(
    name='substr',
    domain=(str, int, int),
    ret_type=str,
    function=lambda text, i, n: z3.SubString(text, i, n),
    # spec=lambda ctx, text, i, n: n == z3.Length(z3.SubString(text, i, n))
)

add = Component(
    name='add', domain=(int, int), ret_type=int, function=lambda x, y: x + y)

minus = Component(
    name='minus', domain=(int, int), ret_type=int, function=lambda x, y: x - y)

# replaceall = Component(
#     name='replaceall',
#     domain=(str, str, str),
#     ret_type=str,
#     function=lambda # Fuck, we need the context here. Time to refactor this.
#     )


def replace_all_z3(ctx, text, old, new):
    f = z3.RecFunction('replace_all', z3.StringSort(ctx), z3.StringSort(ctx),
                       z3.StringSort(ctx))
    z3.RecAddDefinition(
        f, [text, old, new],
        z3.If(
            z3.Or(old == new, z3.Not(z3.Contains(text, old), ctx), ctx), text,
            f(z3.Replace(text, old, new), old, new), ctx))
    return f(text, old, new)
