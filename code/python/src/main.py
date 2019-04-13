import time

import z3

import test_cases
from simple import (IO, Kind, add, concat, index, length, newline, replace,
                    sub, substr, synthesize, to_lower, to_upper, trim,
                    trim_end, trim_start)

stdlib = (concat, index, length, newline, replace, substr, to_lower, to_upper,
          trim, trim_start, trim_end, add, sub)

stack = [(Kind.INT, 2), (Kind.STR, 2)]


def bench(ios):
    print('Examples:')

    for io in ios:
        print(f'\t{io.inputs} --> {repr(io.output)}')

    start = time.time()
    prog = synthesize(ios=ios, lib=stdlib, stack=stack)
    end = time.time()

    print(f'Elapsed time: {end - start:.3f}')
    print(prog)

    print('==================================================')


def main():
    print('Started synthesis tests')

    for ios in test_cases.all_test_cases():
        bench(ios)

    print('Finished synthesis tests')


if __name__ == '__main__':
    main()
