from dataclasses import dataclass
from typing import *

from z3 import And, FreshConst, StringSort

from .functions import (SAdd, SConcat, SIndex, SLength, SNewLine, SReplace,
                        SSub, SSubstr, SToLower, SToUpper, STrim, STrimEnd,
                        STrimStart)
from .types import Constraint, Kind, SInt, SStr, Symbol
from .utils import z3_val

# ==============================================================================
#                                    Types
# ==============================================================================

Domain = Tuple[Kind, ...]
Spec = Callable[[Tuple[Symbol, ...], Symbol], Constraint]


@dataclass
class Sig:
    name: str
    domain: Domain
    ret_type: Kind
    spec: Spec


Library = Tuple[Sig, ...]

# ==============================================================================
#                                  Signatures
# ==============================================================================

# ==============================================================================
# Text


concat = Sig(name='concat', domain=(Kind.STR, Kind.STR), ret_type=Kind.STR, \
             spec=lambda args, ret: ret == SConcat(args[0], args[1]))


def index_spec(args: Tuple[SStr, SStr], ret: SInt) -> Constraint:
    ctx = ret.ctx

    haystack, needle, offset = args
    extra = needle != z3_val('', ctx)  # forall x . IndexOf(x, '') == 0

    return And(ret == SIndex(haystack, needle, offset), \
               extra, ctx)


index = Sig(name='index', domain=(Kind.STR, Kind.STR, Kind.INT), \
            ret_type=Kind.INT, spec=index_spec)

length = Sig(
    name='length',
    domain=(Kind.STR, ),
    ret_type=Kind.INT,
    spec=lambda args, ret: ret == SLength(args[0]))

newline = Sig(
    name='newline',
    domain=(),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == SNewLine(ret.ctx))

replace = Sig(
    name='replace',
    domain=(Kind.STR, Kind.STR, Kind.STR),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == SReplace(args[0], args[1], args[2]))

substr = Sig(
    name='substr',
    domain=(Kind.STR, Kind.INT, Kind.INT),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == SSubstr(args[0], args[1], args[2]))

to_lower = Sig(
    name='to_lower',
    domain=(Kind.STR, ),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == SToLower(args[0]))

to_upper = Sig(
    name='to_upper',
    domain=(Kind.STR, ),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == SToUpper(args[0]))

trim = Sig(
    name='trim',
    domain=(Kind.STR, ),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == STrim(args[0]))

trim_start = Sig(
    name='trim_start',
    domain=(Kind.STR, ),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == STrimStart(args[0]))

trim_end = Sig(
    name='trim_end',
    domain=(Kind.STR, ),
    ret_type=Kind.STR,
    spec=lambda args, ret: ret == STrimEnd(args[0]))

# ==============================================================================
# Arithmetic

add = Sig(
    name='add',
    domain=(Kind.INT, Kind.INT),
    ret_type=Kind.INT,
    spec=lambda args, ret: ret == SAdd(args[0], args[1]))

sub = Sig(
    name='sub',
    domain=(Kind.INT, Kind.INT),
    ret_type=Kind.INT,
    spec=lambda args, ret: ret == SSub(args[0], args[1]))
