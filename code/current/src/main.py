from z3 import *

from synthesis.smt.lines.components import *
from synthesis.smt.lines.pretty import pretty_oneliner
from synthesis.smt.lines.synth import *
from synthesis.smt.lines.types import *
from timewith import timewith


def synth_test(examples, library, min_size, max_size, timeout):
    with timewith('synthesis'):
        is_ok, res = synth(
            examples,
            library=library,
            program_min_size=min_size,
            program_max_size=max_size,
            timeout=timeout)
    if is_ok:
        return res


def main(test_list, library, min_size, max_size, timeout):
    logging.basicConfig(
        format='%(levelname)s:%(message)s', level=logging.DEBUG)

    logging.info('Started synthesis tests')

    for test_case in test_list.test_cases:
        res = synth_test(test_case.examples, library, min_size, max_size,
                         timeout)

        if res:
            program, model = res
            logging.info(f'Program:\t{pretty_oneliner(program, model)}')

        logging.info('==================================================')

    logging.info('Finished synthesis tests')


if __name__ == '__main__':
    raise Exception()
