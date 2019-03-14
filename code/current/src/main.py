from contextlib import suppress

import pyrsistent as p
from z3 import *

from synthesis.smt.lines.pretty import *
from synthesis.smt.lines.synth import *

test_set = p.v(
    p.v(Example(inputs=p.v('John', 'Doe'), output='John Doe'),
        Example(inputs=p.v('Anne', 'Smith'), output='Anne Smith')),

    p.v(Example(inputs=p.v('outsystems', 'com'), output='outsystems.com')),

    # Problems with replace
    p.v(Example(inputs=p.v('outsystems.com'), output='outsystems'),
        Example(inputs=p.v('cmu.edu'), output='cmu')),

    p.v(Example(inputs=p.v('outsystems', 'com'), output='www.outsystems.com'),
        Example(inputs=p.v('cmu', 'edu'), output='www.cmu.edu')),

    p.v(Example(inputs=p.v('rodrigo', 'bernardo', 'gmail', 'com'), output='rodrigo.bernardo@gmail.com'),
        Example(inputs=p.v('pedro', 'orvalho', 'tecnico', 'pt'), output='pedro.orvalho@tecnico.pt'))
)

# print('==========')
# pretty_program(*synth(default_library, test_set[0], 2), example=test_set[0][0])
# print('==========')
# pretty_program(*synth(default_library, test_set[1], 2), example=test_set[1][0])
print('==========')
pretty_program(*synth(p.v(substr, index), test_set[2], 2), example=test_set[2][0])
# print('==========')
# pretty_program(*synth(default_library, test_set[3], 3), example=test_set[3][0])
# print('==========')
# pretty_program(*synth(default_library, test_set[4], 6), example=test_set[4][0])
