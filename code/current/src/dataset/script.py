import jsonlines
import sys

from expr_ast import *
from parser import *

dataset = '../../dataset/__exprs.jsonl'


def read_line(n):
    with jsonlines.open(dataset) as reader:
        for line, obj in enumerate(reader, 1):
            if line == n:
                return obj['text']
