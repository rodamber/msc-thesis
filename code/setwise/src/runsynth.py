import argparse
from dataclasses import dataclass

from read_example import read_examples_from_file
from simple import (IO, Kind, add, concat, index, length, newline, replace,
                    sub, substr, synthesize, to_lower, to_upper, trim,
                    trim_end, trim_start)


@dataclass
class Opts:
    file: str
    num_examples: int
    num_consts_int: int
    num_consts_str: int


def runsynth(opts: Opts):
    examples = read_examples_from_file(opts.file)[:opts.num_examples]
    stack = [(Kind.INT, opts.num_consts_int), (Kind.STR, opts.num_consts_str)]

    lib = (concat,\
           index,
           length,
           replace,
           substr,
           to_lower,
           to_upper,
           trim,
           trim_start,
           trim_end,
           add,
           sub
    )

    print(f'=== Examples ({opts.file})')
    for ex in examples:
        print(ex)

    print('=== Library')
    for f in lib:
        print(f.name)

    print('=== Synthesis')
    prog = synthesize(ios=examples, lib=lib, stack=stack)

    if prog:
        print(prog)
    else:
        print(f'No program found.')


def add_example_arg(parser):
    parser.add_argument(
        '-e',
        '--examples',
        metavar='EXAMPLES',
        default=1,
        type=int,
        help='How many examples to use')


def add_consts_args(parser):
    parser.add_argument(
        '-cs',
        '--consts-str',
        metavar='CONSTS-STR',
        default=1,
        type=int,
        help='How many constants of type str to use')
    parser.add_argument(
        '-ci',
        '--consts-int',
        metavar='CONSTS-INT',
        default=1,
        type=int,
        help='How many constants of type int to use')


def add_file_arg(parser):
    parser.add_argument(
        'file', metavar='FILE', type=str, help='The file with the examples')


def argparser():
    parser = argparse.ArgumentParser(
        description='outsynth1 -- a PBE synthesizer for OutSystems expressions'
    )
    add_example_arg(parser)
    add_consts_args(parser)
    add_file_arg(parser)
    return parser


if __name__ == '__main__':
    parser = argparser()
    args = parser.parse_args()
    opts = Opts(
        file=args.file,
        num_examples=args.examples,
        num_consts_int=args.consts_int,
        num_consts_str=args.consts_str)
    runsynth(opts)
