import pyrsistent as p
import jsonlines
import json
import itertools

from outsystems_lang import parse
from outsystems_lang import expr_ast as ast


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
        atleast = lambda n, x: n if x < n else x
        return args[0][args[1]:atleast(0, args[1]) + atleast(0, args[2])]
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


def split_jsonlines(fin, fout_prefix='examples', dout='examples'):
    '''takes the name of jsonlines file and writes each json object to a new
    file'''
    with jsonlines.open(fin) as reader:
        for i, json in enumerate(reader, 1):
            fout = f'{dout}/{fout_prefix}-{i}.json'
            with jsonlines.open(fout, mode='w') as writer:
                writer.write(json)


def pretty_all(dir='examples'):
    import json, os

    for file in os.listdir(dir):
        with open(f'{dir}/{file}') as json_file:
            data = json.load(json_file)
            with open(f'{dir}/{file}.pretty', mode='w') as outfile:
                json.dump(data, outfile, indent=4, sort_keys=True)


def map_example(f, g, dir='examples', ext='map'):
    import os

    for file in os.listdir(dir):
        with open(f'{dir}/{file}') as infile:
            data = f(infile)
            with open(f'{dir}/{file}.{ext}', mode='w') as outfile:
                g(data, outfile)


def to_either(x):
    if isinstance(x, str):
        return {"Left": x}
    if isinstance(x, int):
        return {"Right": x}
    raise ValueError(f'{str(x)}: {type(x)}')


def add_either():
    def f(infile):
        return json.load(infile)

    def g(data, outfile):
        for example in data['examples']:
            example['inputs'] = \
                [to_either(x) for x in example['inputs']]
            example['output'] = to_either(example['output'])
        return json.dump(data, outfile, indent=4, sort_keys=True)

    map_example(f, g, dir='examples', ext='either')

