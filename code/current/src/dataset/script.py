import itertools
import jsonlines
import sys

dataset = '../../dataset/__exprs.jsonl'


def read_line(n, dataset=dataset, field='text'):
    with jsonlines.open(dataset) as reader:
        for line, obj in enumerate(reader, 1):
            if line == n:
                return obj[field]


def simplify(src=dataset, dst='simplify'):
    with jsonlines.open(src, 'r') as reader:
        with jsonlines.open(dst, 'w') as writer:
            for x in reader:
                writer.write({'text': x['text'], 'functions': x['functions']})


# Demonstration

import expr_ast as ast
from parser import parse
from templatify import templatify

expr = parse(read_line(15))
template = templatify(expr)

# components = to_components(template)

# inputs = {component: gen_inputs(component, 10) for component in components}
# outputs = {
#     component: ((input_, component(input_)) for input_ in inputs[component])
#     for component in components
# }

# Hypothesis demonstration

from hypothesis import assume, strategies as st
from string import ascii_letters


@st.composite
def substr(draw, alphabet=ascii_letters):
    text = draw(st.text(alphabet, min_size=1))

    middle = draw(st.integers(0, len(text) - 1))
    left = draw(st.integers(0, middle))
    right = draw(st.integers(middle, len(text) - 1))

    return (text, left, right)
