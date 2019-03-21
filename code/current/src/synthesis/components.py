import pyrsistent as p
import z3

from .types import Component

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
    spec=lambda ctx, x, y, z: z3.And(x != y, z3.Contains(x, y), ctx))

substr = Component(
    name='substr',
    domain=(str, int, int),
    ret_type=str,
    function=lambda text, i, j: z3.SubString(text, i, j))

# Other components (sketches, really)

replace2 = Component(
    name='replace2',
    domain=(str, str, str, str),
    ret_type=str,
    function=lambda x, y, z, w: z3.Replace(z3.Replace(x, y, z), y, w))

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
