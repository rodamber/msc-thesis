import fileinput
import time

import z3

import test_cases
from simple import (IO, Kind, add, concat, index, length, newline, replace,
                    sub, substr, synthesize, to_lower, to_upper, trim,
                    trim_end, trim_start)

stdlib = (concat, index, length, replace, substr, to_lower, to_upper,
          trim, trim_start, trim_end, add, sub)

stack = [(Kind.INT, 2), (Kind.STR, 2)]


def bench(ios, lib=stdlib):
    print('Examples:')

    for io in ios:
        print(f'\t{io.inputs} --> {repr(io.output)}')

    start = time.time()
    prog = synthesize(ios=ios, lib=lib, stack=stack)
    end = time.time()

    print(f'Elapsed time: {end - start:.3f}')
    print(prog)

    print('==================================================')


def bench_all():
    print('Started synthesis tests')

    for ios in test_cases.all_test_cases():
        bench(ios)

    print('Finished synthesis tests')


def examples_stdin():
    for line in fileinput.input():
        if line == 'synth\n':
            return

        contents = line.rstrip().split(',')
        inputs = tuple(contents[:-1])
        output = contents[-1]

        yield IO(inputs, output)


def main():
    lib = (concat, index, length, # replace,
           substr,
          # to_lower, to_upper,
          # trim, trim_start, trim_end, add, sub
    )
    ios = list(examples_stdin())
    stack = [(Kind.INT, 2), (Kind.STR, 2)]
    prog = synthesize(ios=ios, lib=lib, stack=stack)

    if prog:
        print(f'Program: {prog}')
    else:
        print(f'No program found.')


if __name__ == '__main__':
    main()
