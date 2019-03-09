import itertools
import jsonlines
import sys

from parser import *
from expr_ast import *
from templatify import *
from component import *
from ast2component import *
from input_gen import *

dataset = '../../dataset/dsl01/exprs-short300-dsl01-size2.jsonl'


def read_line(n, dataset=dataset, field='text'):
    with jsonlines.open(dataset) as reader:
        for line, obj in enumerate(reader, 1):
            if line == n:
                return obj[field]


def simplify(src=dataset, dst='simplify'):
    with jsonlines.open(src, 'r') as reader:
        with jsonlines.open(dst, 'w') as writer:
            for x in reader:
                writer.write({'text': x['text'], 'functions': x['functions']})


def experiment(n):
    line = read_line(n)
    expr = parse(line)
    temp = templatify(expr)
    prog = ast2comp(temp)
    env = gen(prog)

    print('Program:')
    print(render(prog))

    print('Environment:')
    for k, v in env.items():
        print(f'{k}: {v}')

    print('Output:')
    print(run(prog, env))

    return prog, env


# def benchmarks()
