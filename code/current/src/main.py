from contextlib import suppress

import pyrsistent as p
from z3 import *

from synthesis.smt.lines.components import *
from synthesis.smt.lines.pretty import *
from synthesis.smt.lines.synth import *

test_set = p.v(
    p.v(
        Example(inputs=p.v('John', 'Doe'), output='John Doe'),
        Example(inputs=p.v('Anne', 'Smith'), output='Anne Smith')),
    p.v(Example(inputs=p.v('outsystems', 'com'), output='outsystems.com')),
    p.v(
        Example(inputs=p.v('outsystems.com'), output='outsystems'),
        Example(inputs=p.v('cmu.edu'), output='cmu')),
    p.v(
        Example(inputs=p.v('outsystems.com'), output='outsystems'),
        Example(inputs=p.v('cmu.edu'), output='cmu'),
        Example(inputs=p.v('tecnico.pt'), output='tecnico')),
    p.v(
        Example(
            inputs=p.v('rodrigo', 'bernardo', 'gmail', 'com'),
            output='rodrigo.bernardo@gmail.com'),
        Example(
            inputs=p.v('pedro', 'orvalho', 'tecnico', 'pt'),
            output='pedro.orvalho@tecnico.pt')),
)

for test_case in test_set:
    print('==========')
    for i, example in enumerate(test_case, 1):
        print(
            f'Example {i}: Inputs: {list(example.inputs)}. Output: {repr(example.output)}'
        )

    is_ok, res = synth(test_case)

    if is_ok:
        program, model = res
        example = test_case[0]

        pretty_program(program, model, example=test_case[0])
