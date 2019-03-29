import logging
import time

import test_cases
from synthesis import components as comp
from synthesis.pretty import pretty_oneliner
from synthesis.synth import config, synth, example


def log_examples(examples):
    logging.info('Examples:')

    for ex in examples:
        logging.info(f'\t{tuple(ex.inputs)} --> {repr(ex.output)}')


def bench(config, examples):
    log_examples(examples)

    start = time.time()
    res = synth(config, examples)
    end = time.time()

    logging.info(f'Elapsed time: {end - start:.3f} seconds')

    if res:
        program, model = res
        pretty = pretty_oneliner(program, model)

        logging.info(f'Program:\t{pretty}')

    logging.info('==================================================')


def main(log_level=logging.INFO):
    logging.basicConfig(format='%(levelname)s:%(message)s', level=log_level)

    logging.info('Started synthesis tests')

    my_config = config(
        max_conflicts=20 * 1000,
        timeout=5 * 60 * 1000,
        program_min_size=1,
        program_max_size=6,
        library=[
            comp.add,
            comp.concat,
            comp.index,
            comp.index3,
            comp.length,
            comp.newline,
            # comp.replace_over,
            # comp.replace,
            comp.sub,
            comp.substr,
            comp.ltrim,
            # comp.rtrim,
            comp.trim,
            comp.lower,
            comp.upper,
        ],
        fix_lines=False,
        stack_space=None)

    # buggy01 = [
    #     example(['John   Doe'], 'John Doe'),
    #     example(['A B'], 'A')
    # ]

    # examples = [
    #     example(['John   Doe'], 'John Doe'),
    #     example(['A B'], 'A B')
    # ]
    # bench(examples=examples, config=my_config)

    for examples in test_cases.all_test_cases():
        bench(examples=examples, config=my_config)

    logging.info('Finished synthesis tests')


if __name__ == '__main__':
    main(logging.DEBUG)
