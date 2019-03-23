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
    function=lambda text, x: z3.IndexOf(text, x, 0))

index3 = Component(
    name='index3',
    domain=(str, str, int),
    ret_type=int,
    function=lambda text, x, y: z3.IndexOf(text, x, y))

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
    spec=lambda ctx, x, y, z: z3.And(x != y,
                                     z3.Contains(x, y),
                                     y != z3_val('', ctx),
                                     ctx))

substr = Component(
    name='substr',
    domain=(str, int, int),
    ret_type=str,
    function=lambda text, i, n: z3.SubString(text, i, n),
    # spec=lambda ctx, text, i, n: n == z3.Length(z3.SubString(text, i, n))
)

# Other components (sketches, really)

replace2 = Component(
    name='replace2',
    domain=(str, str, str, str),
    ret_type=str,
    function=lambda x, y, z, w: z3.Replace(z3.Replace(x, y, z), y, w))

# Using these, besides reducing the number of components used, reduces the
# ambiguity that the associativity of concat introduces, by fixing the
# arguments. This reduces solver overhead.
#
# It would be nice if we could have varargs components.
concat3 = Component(
    name='concat3',
    domain=(str, str, str),
    ret_type=str,
    function=lambda x, y, z: z3.Concat(z3.Concat(x, y), z))

concat4 = Component(
    name='concat4',
    domain=(str, str, str, str),
    ret_type=str,
    function=lambda x, y, z, w: z3.Concat(z3.Concat(z3.Concat(x, y), z), w))

concat5 = Component(
    name='concat5',
    domain=(str, str, str, str, str),
    ret_type=str,
    function=lambda x, y, z, w, v: z3.Concat(z3.Concat(z3.Concat(z3.Concat(x, y), z), w), v))
