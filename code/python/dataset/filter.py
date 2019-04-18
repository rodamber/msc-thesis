import pyrsistent as p
import jsonlines
import json
import itertools

from test_autogen import parse
from test_autogen import templatify
from test_autogen import expr_ast as ast


def allin(xs, ys):
    '''true iff all elements of xs are also elements of ys'''
    return all(x in ys for x in xs)


def oneof(xs, ys):
    '''true iff at least one element of xs is also an element of ys '''
    return any(x in ys for x in xs)


def myfilter():
    funs0 = {'Concat', 'Length', 'Substr', 'Index', 'Replace'}
    funs1 = {'ToLower', 'ToUpper', 'Trim', 'TrimEnd', 'TrimStart'}

    infile = open('./__exprs.jsonl', mode='r')
    outfile = open(input('Enter output file name: '), mode='w')

    reader = jsonlines.Reader(infile)
    writer = jsonlines.Writer(outfile)

    pred = lambda x: len(x['text']) < 300 and \
        allin(x['functions'], funs0.union(funs1)) and \
        oneof(x['functions'], funs0) and \
        oneof(x['functions'], funs1)

    filtered = dict((x['text'], x) for x in reader if pred(x)).values()

    sorted_ = sorted(filtered, key=lambda x: len(x['functions']), reverse=True)
    writer.write_all(sorted_)

    # slice = itertools.islice(filtered, 10)
    # print(list(slice))

    reader.close()
    infile.close()

    writer.close()
    outfile.close()


def swapsort(infile):
    '''swap order of functions and text, and sort functions'''
    outfile = infile[:infile.index('.')] + "-sorted.jsonl"

    with jsonlines.open(infile, 'r') as reader:
        with jsonlines.open(outfile, 'w') as writer:
            xs = sorted(reader, key=lambda x: len(x['functions']))

            for x in xs:
                writer.write({
                    'functions': sorted(x['functions']),
                    'text': x['text']
                })


def try_parse(infile):
    with jsonlines.open(infile, 'r') as reader:
        for i, x in enumerate(reader, 1):
            try:
                parse(x['text'])
            except:
                print(f'bad: line {i}')
    print('ok')


def run(env, tree):
    if ast.expr(tree) == ast.Expr.Var:
        return env[ast.val(tree)]
    elif ast.expr(tree) == ast.Expr.Lit:
        return ast.val(tree)
    elif ast.expr(tree) == ast.Expr.Func:
        children = ast.children(tree).transform([p.ny], lambda x: run(env, x))
        return funcall(ast.val(tree), children)
    else:
        raise RuntimeError('run')


def typecheck(args, types):
    for x, t in zip(args, types):
        if not isinstance(x, t):
            raise RuntimeError(
                f'Typechecking error: value={x}, expected={t}, actual={type(x)}'
            )


def funcall(fname, args):
    def _BINOP(binop, args):
        return binop(args[0], args[1])

    if fname == 'Concat':
        typecheck(args, [str, str])
        return _BINOP(lambda x, y: x + y, args)
    elif fname == 'Index':
        typecheck(args, [str, str, int])
        return args[0].find(args[1], args[2])
    elif fname == 'Length':
        typecheck(args, [str])
        return len(args[0])
    elif fname == 'Replace':
        typecheck(args, [str, str, str])
        return args[0].replace(args[1], args[2])
    elif fname == 'Substr':
        typecheck(args, [str, int, int])
        assert args[1] >= 0 and args[2] >= 0
        return args[0][args[1]:args[1] + args[2]]
    elif fname == 'ToLower':
        typecheck(args, [str])
        return args[0].lower()
    elif fname == 'ToUpper':
        typecheck(args, [str])
        return args[0].upper()
    elif fname == 'Trim':
        typecheck(args, [str])
        return args[0].strip()
    elif fname == 'TrimStart':
        typecheck(args, [str])
        return args[0].lstrip()
    elif fname == 'TrimEnd':
        typecheck(args, [str])
        return args[0].rstrip()
    elif fname == 'Add':
        typecheck(args, [int, int])
        return _BINOP(lambda x, y: x + y, args)
    elif fname == 'Sub':
        typecheck(args, [int, int])
        return _BINOP(lambda x, y: x - y, args)
    else:
        raise ValueError(fname)


def is2j(xs, prog):
    '''takes inputs, gets the output, and returns a dict with both'''
    env = dict((f'x{i}', x) for i, x in enumerate(xs))
    y = run(env, parse(prog))
    return {'inputs': xs, 'output': y}


def exs(jobj, xss):
    '''add examples field (xss as a json array) to jobj, and return json object'''
    examples = [is2j(xs, jobj['text']) for xs in xss]
    print(json.dumps({'examples': examples, **jobj}))


if __name__ == '__main__':
    try_parse('templates.jsonl')
    # myfilter()
    # swapsort('templates.jsonl')
    pass
'''
examples
components
prog
'''
