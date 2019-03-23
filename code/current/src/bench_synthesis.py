import logging
import time

import test_cases
from synthesis import components as comp
from synthesis.pretty import pretty_oneliner
from synthesis.synth import config, default_library, synth
from synthesis.types import example


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
        max_conflicts=1 * (10 ** 4),
        program_min_size=3,
        program_max_size=3,
        library=[comp.replace, comp.concat], # default_library(),
        fix_lines=True
    )

    # examples = test_cases.concat.cases[9]
    # bench(my_config, examples)

    for examples in test_cases.concat.cases[:9]:
        bench(examples=examples, config=my_config)

    logging.info('Finished synthesis tests')


if __name__ == '__main__':
    main(logging.DEBUG)
