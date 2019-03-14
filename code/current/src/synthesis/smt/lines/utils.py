import z3


def type2sort(typ):
    if typ == int:
        return z3.IntSort()
    elif typ == str:
        return z3.StringSort()
    else:
        raise ValueError(f'Unsupported type: {typ}')


def _z3_smt_const(typ, prefix, *ix):
    ix = '_'.join(map(str, ix))
    return z3.Const(f'{prefix}_{ix}', type2sort(typ))


def z3_const(typ, x):
    return _z3_smt_const(typ, 'c', x)


def z3_input(typ, x, y):
    return _z3_smt_const(typ, 'i', x, y)


def z3_output(typ, x, y):
    return _z3_smt_const(typ, 'o', x, y)


def z3_hole(typ, x, y, z):
    return _z3_smt_const(typ, 'h', x, y, z)


def z3_line(fresh):
    return z3.Int(f'l_{next(fresh)}')


def z3_val(val):
    if isinstance(val, int):
        return z3.IntVal(val)
    elif isinstance(val, str):
        return z3.StringVal(val)
    else:
        raise ValueError(f'z3_val: unsupported typ ({typ})')


def z3_as(ref):
    if isinstance(ref, z3.ArithRef):
        return ref.as_long()
    elif isinstance(ref, z3.SeqRef):
        return ref.as_string()
    else:
        raise ValueError(f'z3_val: unsupported ref type ({type(ref)})')
