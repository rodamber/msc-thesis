#!/usr/bin/env python
from tyrell.spec import parse_file
from tyrell.dsl import Builder
from tyrell.interpreter import PostOrderInterpreter, GeneralError
from tyrell.enumerator import ExhaustiveEnumerator, SmtEnumerator
from tyrell.decider import Example, ExampleDecider, ExampleConstraintDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger

logger = get_logger('tyrell')
logger.setLevel('DEBUG')


def _IF(args):
    if args[0]:
        args[1]
    else:
        args[2]


def _BINOP(binop, args):
    return binop(args[0], args[1])


def _EQ(args):
    return _BINOP(lambda x, y: x == y, args)


def _LEQ(args):
    return _BINOP(lambda x, y: x <= y, args)


class Interpreter(PostOrderInterpreter):
    def typecheck(self, node, args, types):
        for i, t in enumerate(types):
            self.assertArg(
                node, args, index=i, cond=lambda x: isinstance(x, t))

    def eval_Char(self, v):
        return str(v)

    def eval_SmallInt(self, v):
        return int(v)

    def eval_const_char(self, node, args):
        self.typecheck(node, args, [str])
        return args[0]

    def eval_const_int(self, node, args):
        self.typecheck(node, args, [int])
        return args[0]

    def eval_if_text(self, node, args):
        self.typecheck(node, args, [bool, str, str])
        return _IF(args)

    def eval_if_int(self, node, args):
        self.typecheck(node, args, [bool, int, int])
        return _IF(args)

    def eval_if_bool(self, node, args):
        self.typecheck(node, args, [bool, bool, bool])
        return _IF(args)

    def eval_length(self, node, args):
        self.typecheck(node, args, [str])
        return len(args[0])

    def eval_substr(self, node, args):
        self.typecheck(node, args, [str, int, int])
        return args[0][args[1]:args[2]]

    def eval_concat(self, node, args):
        self.typecheck(node, args, [str, str])
        return _BINOP(lambda x, y: x + y, args)

    def eval_chr(self, node, args):
        self.typecheck(node, args, [int])
        if args[0] not in range(0x110000):
            raise GeneralError()
        return chr(args[0])

    def eval_index0(self, node, args):
        self.typecheck(node, args, [str, int])
        return args[0].find(args[1])

    def eval_index1(self, node, args):
        self.typecheck(node, args, [str, str, int])
        return args[0].find(args[1], args[2])

    def eval_replace(self, node, args):
        self.typecheck(node, args, [str, str, str])
        return args[0].replace(args[1], args[2])

    def eval_lower(self, node, args):
        self.typecheck(node, args, [str])
        return args[0].lower()

    def eval_upper(self, node, args):
        self.typecheck(node, args, [str])
        return args[0].upper()

    def eval_ltrim(self, node, args):
        self.typecheck(node, args, [str])
        return args[0].lstrip()

    def eval_rtrim(self, node, args):
        self.typecheck(node, args, [str])
        return args[0].rstrip()

    def eval_trim(self, node, args):
        self.typecheck(node, args, [str])
        return args[0].strip()

    def eval_text_eq(self, node, args):
        self.typecheck(node, args, [str, str])
        return _EQ(args)

    def eval_text_leq(self, node, args):
        self.typecheck(node, args, [str, str])
        return _LEQ(args)

    def eval_or(self, node, args):
        self.typecheck(node, args, [bool, bool])
        return _BINOP(lambda x, y: x or y, args)

    def eval_not(self, node, args):
        self.typecheck(node, args, [bool])
        return not args[0]

    def eval_eq_bool(self, node, args):
        self.typecheck(node, args, [bool, bool])
        return _EQ(args)

    def eval_minus(self, node, args):
        self.typecheck(node, args, [int, int])
        return _BINOP(lambda x, y: x - y, args)

    def eval_plus(self, node, args):
        self.typecheck(node, args, [int, int])
        return _BINOP(lambda x, y: x + y, args)

    def eval_mult(self, node, args):
        self.typecheck(node, args, [int, int])
        return _BINOP(lambda x, y: x * y, args)

    def eval_div(self, node, args):
        self.typecheck(node, args, [int, int])
        self.assertArg(node, args, index=1, cond=lambda x: x > 0)
        return _BINOP(lambda x, y: x / y, args)

    def eval_eq_int(self, node, args):
        self.typecheck(node, args, [int, int])
        return _EQ(args)

    def eval_leq_int(self, node, args):
        self.typecheck(node, args, [int, int])
        return _LEQ(args)


def synthesize(enumerator, decider):
    logger.info('Building synthesizer...')
    synthesizer = Synthesizer(enumerator=enumerator, decider=decider)

    logger.info('Synthesizing programs...')
    prog = synthesizer.synthesize()

    if prog is not None:
        logger.info('Solution found: {}'.format(prog))
        return 'SAT'
    else:
        logger.info('Solution not found!')
        return 'UNSAT'


def make_examples(pairs):
    return list(
        Example(input=inputs, output=output) for inputs, output in pairs)


def smt(spec, depth, loc, examples):
    enumerator = SmtEnumerator(spec, depth=depth, loc=loc)
    decider = ExampleConstraintDecider(
        spec=spec, interpreter=Interpreter(), examples=make_examples(examples))

    return enumerator, decider


def exhaustive(spec, max_depth, examples):
    enumerator = ExhaustiveEnumerator(spec, max_depth)
    decider = ExampleDecider(Interpreter(), make_examples(examples))

    return enumerator, decider


spec = parse_file('example/outsystems.tyrell')
examples = [
    (["John", "Doe"], 'doejohn'),
    # (["John   ", "  Doe"], 'doejohn'),
    # (["   John   ", "  Doe   "], 'doejohn'),
    # (["Jane", "Smith"], 'smithjane'),
    # (["Jane   ", "  Smith"], 'smithjane'),
    # (["   Jane   ", "  Smith   "], 'smithjane'),
]


def smt_main(spec):
    # for loc in range(1, 6):  # bug
    synthesize(*smt(spec, depth=6, loc=4, examples=examples))


def exhaustive_main(spec):
    # for max_depth in range(1, 4):
    synthesize(*exhaustive(spec, 3, examples))


if __name__ == '__main__':
    # smt_main(spec)
    exhaustive_main(spec)
