import logging
import time

import test_cases
from synthesis.pretty import pretty_oneliner
from synthesis.synth import config, default_library, synth


def log_examples(examples):
    logging.info('Examples:')

    for ex in examples:
        logging.info(f'\t{tuple(ex.inputs)} --> {repr(ex.output)}')


def bench(config, examples):
    log_examples(examples)

    start = time.time()
    is_ok, res = synth(config, examples)
    end = time.time()

    logging.info(f'Elapsed time: {end - start:.3f} seconds')

    if is_ok:
        program, model = res
        pretty = pretty_oneliner(program, model)

        logging.info(f'Program:\t{pretty}')

    logging.info('==================================================')


def main(log_level=logging.INFO):
    logging.basicConfig(format='%(levelname)s:%(message)s', level=log_level)

    logging.info('Started synthesis tests')

    library = default_library()
    timeout = 10 * 1000

    for examples in test_cases.all_test_cases():
        bench(
            examples=examples,
            config=config(
                timeout=timeout,
                program_min_size=1,
                program_max_size=6,
                library=library
            ))

    logging.info('Finished synthesis tests')


if __name__ == '__main__':
    main(logging.DEBUG)
