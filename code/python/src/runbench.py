import argparse
from dataclasses import dataclass
import subprocess

import runsynth


@dataclass
class Opts():
    time_limit: int
    mem_limit: int
    output_dir: str
    files: [str]
    num_examples: int
    num_consts_int: int
    num_consts_str: int


def runbench(opts: Opts):
    directory = opts.output_dir
    if not os.path.exists(directory):
        os.makedirs(directory)

    for file in opts.files:
        subprocess.run(
            'runsolver',
            [
                '--wall-clock-limit',
                opts.time_limit,
                '--mem-limit',
                opts.mem_limit * 1000,  # megabytes
                '--solver-data',
                f'{opts.outputDir}/{file}.out',
                '--timestamp',
                'outsynth2',
                '--examples',
                opts.num_examples,
                '--constants',
                opts.num_consts,
                file
            ])


def add_res_args(parser):
    parser.add_argument(
        '-t',
        '--time-limit',
        metavar='TIME-LIMIT',
        default=1,
        type=int,
        help='Time limit (wall-clock time) in seconds')
    parser.add_argument(
        '-m',
        '--mem-limit',
        default=12,
        type=int,
        help='Memory limit in gigabytes')


def add_dir_arg(parser):
    parser.add_argument(
        '-d',
        '--output-dir',
        metavar='OUTPUT-DIR',
        help='Directory where to save the benchmarks')


def add_files_arg(parser):
    parser.add_argument(
        'file',
        metavar='FILE',
        type=str,
        nargs='+',
        help='The file with the examples')


def argparser():
    parser = argparse.ArgumentParser(
        description='outsynth2 benchmark runner')
    add_res_args(parser)
    add_dir_arg(parser)
    add_files_arg(parser)
    runsynth.add_example_arg(parser)
    runsynth.add_consts_args(parser)
    return parser


if __name__ == '__main__':
    parser = argparser()
    args = parser.parse_args()
    opts = Opts(
        time_limit=args.time_limit,
        mem_limit=args.mem_limit,
        output_dir=args.output_dir,
        file=args.file,
        num_examples=args.examples,
        num_consts_int=args.consts_int,
        num_consts_str=args.consts_str)
    runsynth(opts)
