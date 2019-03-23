import z3


def type2sort(typ, ctx):
    if typ == int:
        return z3.IntSort(ctx)
    elif typ == str:
        return z3.StringSort(ctx)
    else:
        raise ValueError(f'Unsupported type: {typ}')


def z3_const(ctx, typ, prefix, *ix):
    ix = '_'.join(map(str, ix))
    return z3.Const(f'{prefix}_{ix}', type2sort(typ, ctx))


def z3_val(val, ctx):
    if isinstance(val, int):
        return z3.IntVal(val, ctx)
    elif isinstance(val, str):
        return z3.StringVal(val, ctx)
    else:
        raise ValueError(f'z3_val: unsupported typ ({type(val)})')


def z3_as(ref):
    if isinstance(ref, z3.ArithRef):
        return ref.as_long()
    elif isinstance(ref, z3.SeqRef):
        return ref.as_string()
    else:
        raise ValueError(f'z3_val: unsupported ref type ({type(ref)})')
