from contextlib import suppress

import pyrsistent as p
from z3 import *

from synthesis.smt.lines.components import *
from synthesis.smt.lines.pretty import pretty_lines, pretty_oneliner
from synthesis.smt.lines.synth import *
from timewith import timewith

test_concat = p.v(
    p.v(
        # Bad: Size 2
        Example(inputs=p.v('John', 'Doe'), output='John Doe'), ),
    p.v(
        # Good: Size 2
        Example(inputs=p.v('John', 'Doe'), output='John Doe'),
        Example(inputs=p.v('Anne', 'Smith'), output='Anne Smith')),
    p.v(
        # Good: Size 3
        Example(inputs=p.v('John', 'Doe', '-Odoi'), output='John Doe-Odoi'),
        Example(
            inputs=p.v('Anne', 'Smith', '-Sonian'),
            output='Anne Smith-Sonian')),
    p.v(
        # Bad: size 3, learning the prefix
        Example(inputs=p.v('John', 'Doe'), output='Dr. John Doe'),
        Example(inputs=p.v('Anne', 'Smith'), output='Dr. Anne Smith')),
    p.v(
        # Good: size 3, same as before
        Example(inputs=p.v('John', 'Doe'), output='Dr. John Doe'),
        Example(inputs=p.v('Anne', 'Smith'), output='Dr. Anne Smith')),
    p.v(
        # Good: size 4
        Example(
            inputs=p.v('John', 'Michael', 'Doe'), output='John Michael Doe'),
        Example(
            inputs=p.v('Anne', 'Marie', 'Smith'), output='Anne Marie Smith')),
    p.v(
        # Good: size 5, learning the prefix
        Example(
            inputs=p.v('John', 'Michael', 'Doe'), output='Dr. John Michael Doe'),
        Example(
            inputs=p.v('Anne', 'Marie', 'Smith'), output='Dr. Anne Marie Smith')),
    p.v(
        # Good: size 6
        Example(
            inputs=p.v('John', 'Oliver', 'Michael', 'Doe'),
            output='John Oliver Michael Doe'),
        Example(
            inputs=p.v('Anne', 'Emily', 'Marie', 'Smith'),
            output='Anne Emily Marie Smith')),
)

test_index = p.v(
    # Try to find the index of '.'
    p.v(
        # Bad: One example doesn't work well if we don't explicitly say we're
        # looking for '.'
        Example(inputs=p.v('outsystems.com'), output=10)),
    p.v(
        # Good: It works well with one example if we say explicitly we're
        # looking for '.'
        Example(inputs=p.v('outsystems.com', '.'), output=10)),
    p.v(
        # Good: But it works well if we give it two examples.
        Example(inputs=p.v('outsystems.com'), output=10),
        Example(inputs=p.v('cmu.edu'), output=3),
    ),
    p.v(
        # Good: Adding more '.' shouldn't confuse the synthesizer.
        Example(inputs=p.v('outsystems.com'), output=10),
        Example(inputs=p.v('abc.gmail.com'), output=3)),
)

test_length = p.v(
    # Try to find the length of a string
    p.v(
        # Bad: One example. Seems like index can be used to do some nasty stuff.
        Example(inputs=p.v('abc'), output=3)),
    p.v(
        # Bad: Two examples. Again, index is at fault.
        Example(inputs=p.v('abc'), output=3),
        Example(inputs=p.v('rodrigo'), output=7),
    ),
    p.v(
        # Good: Three examples. It seems like it's easier to just use length
        # now.
        Example(inputs=p.v('abc'), output=3),
        Example(inputs=p.v('rodrigo'), output=7),
        Example(inputs=p.v('pedro'), output=5)),
)

test_replace = p.v(
    p.v(  # Bad
        Example(inputs=p.v('John Doe'), output='John_Doe')),
    p.v(  # Good
        Example(inputs=p.v('John Doe'), output='John_Doe'),
        Example(inputs=p.v('Michael Scott'), output='Michael_Scott')),
    p.v(  # Bad
        Example(inputs=p.v('01/01/2000'), output='01-01-2000')),
    p.v(  # Medium, Slow
        Example(inputs=p.v('01/01/2000', '/', '-'), output='01-01-2000'),
        Example(inputs=p.v('01/02/2000', '/', '-'), output='01-02-2000')),
    p.v(  # Too slow
        Example(inputs=p.v('01/01/2000', '/'), output='01-01-2000'),
        Example(inputs=p.v('01/02/2000', '/'), output='01-02-2000')),
    p.v(  # Too slow
        Example(inputs=p.v('01/01/2000'), output='01-01-2000'),
        Example(inputs=p.v('01/02/2000'), output='01-02-2000')))

test_substr = p.v(
    p.v(  # Bad
        Example(
            inputs=p.v('Text longer than thirty characters.'),
            output='Text longer than thirty charac')),
    p.v(  # Bad
        Example(
            inputs=p.v('Text longer than thirty characters.'),
            output='Text longer than thirty charac'),
        Example(inputs=p.v('Small text.'), output='Small text.')),
    p.v(  # Good!
        Example(
            inputs=p.v('Text longer than thirty characters.'),
            output='Text longer than thirty charac'),
        Example(inputs=p.v('Small text.'), output='Small text.'),
        Example(
            inputs=p.v('This text is also longer than thirty characters.'),
            output='This text is also longer than ')),
    p.v(  # Bad
        Example(inputs=p.v('01/04/2000'), output='01')),
    p.v(  # Good
        Example(inputs=p.v('01/04/2000'), output='01'),
        Example(inputs=p.v('02/05/2000'), output='02')),
    p.v(  # Good
        Example(inputs=p.v('01/04/2000'), output='04'),
        Example(inputs=p.v('02/05/2000'), output='05')),
    p.v(  # Kinda Good
        Example(inputs=p.v('01/04/2000'), output='2000'),
        Example(inputs=p.v('02/05/2001'), output='2001')),
    p.v(  # Good
        Example(inputs=p.v('#01-04-2000#'), output='2000'),
        Example(inputs=p.v('#02-05-2001#'), output='2001')),
)

test_substr_index = p.v(
    p.v(  # Bad
        Example(inputs=p.v('outsystems.com'), output='outsystems')),
    p.v(  # Bad
        Example(inputs=p.v('outsystems.com'), output='outsystems'),
        Example(inputs=p.v('cmu.edu'), output='cmu')),
    p.v(  # Good
        Example(inputs=p.v('outsystems.com'), output='outsystems'),
        Example(inputs=p.v('cmu.edu'), output='cmu'),
        Example(inputs=p.v('tecnico.pt'), output='tecnico')),
    p.v(  # Good
        Example(inputs=p.v('outsystems.com', '.'), output='outsystems'),
        Example(inputs=p.v('cmu.edu', '.'), output='cmu')),
    p.v(  # Too Slow
        Example(inputs=p.v('www.outsystems.com'), output='outsystems'),
        Example(inputs=p.v('www.cmu.edu'), output='cmu'),
        Example(inputs=p.v('www.tecnico.pt'), output='tecnico')),
)

test_substr_concat = p.v(
    p.v(  # Bad
        Example(
            inputs=p.v('Text longer than thirty characters.'),
            output='Text longer than thirty charac...')),
    p.v(  # Bad
        Example(
            inputs=p.v('Text longer than thirty characters.'),
            output='Text longer than thirty charac...'),
        Example(inputs=p.v('Small text.'), output='Small text.')),
    p.v(  # Too slow
        Example(
            inputs=p.v('Text longer than thirty characters.'),
            output='Text longer than thirty charac...'),
        Example(inputs=p.v('Small text.'), output='Small text.'),
        Example(
            inputs=p.v('This text is also longer than thirty characters.'),
            output='This text is also longer than ...')),
)

test_all = test_concat + test_index + test_length + test_replace + test_substr + \
    test_substr_concat + test_substr_index


def main(timeout, arg):
    test_set = eval('test_' + arg)

    for examples in test_set:
        print('Examples:')

        for example in examples:
            inputs = list(example.inputs)
            output = example.output

            print(f'\t{inputs} -> {repr(output)}')

        with timewith('synthesis'):
            is_ok, res = synth(
                examples,
                library=default_library,
                program_min_size=1,
                program_max_size=6,
                timeout=5000)

        if is_ok:
            program, model = res
            example = examples[0]

            print('Program:\n\t', end='')
            pretty_oneliner(program, model)
        else:
            print('Failure to synthesize.')

        print('==================================================')


if __name__ == '__main__':
    import sys
    main(int(sys.argv[1]), '_'.join(sys.argv[2:]))
