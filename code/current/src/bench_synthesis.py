import logging
import time

from test_cases import all_test_cases

from synthesis.smt.lines.pretty import pretty_oneliner
from synthesis.smt.lines.synth import synth, config


def bench(config, test_cases):
    logging.info('Started synthesis tests')

    for test_case in test_cases:
        log_examples(test_case)

        start = time.time()
        is_ok, res = synth(config, test_case)
        end = time.time()

        logging.info(f'Elapsed time: {end - start:.3f} seconds')

        if is_ok:
            program, model = res
            logging.info(f'Program:\t{pretty_oneliner(program, model)}')

        logging.info('==================================================')

    logging.info('Finished synthesis tests')


def log_examples(examples):
    logging.info('Examples:')

    for ex in examples:
        logging.info(f'\t{tuple(ex.inputs)} --> {repr(ex.output)}')

if __name__ == '__main__':
    logging.basicConfig(
        format='%(levelname)s:%(message)s', level=logging.INFO)

    bench(config(timeout=1000), all_test_cases())
