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

length = Component(
    name='length',
    domain=(str, ),
    ret_type=int,
    function=lambda x: z3.Length(x))

replace = Component(
    name='replace',
    domain=(str, str, str),
    ret_type=str,
    function=lambda x, y, z: z3.Replace(x, y, z))

substr = Component(
    name='substr',
    domain=(str, int, int),
    ret_type=str,
    function=lambda text, i, j: z3.SubString(text, i, j - i))

default_library = p.v(concat, index, length, replace, substr)
