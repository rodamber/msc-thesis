import sys

import jsonlines
import parsy

from parser import parse
from utils import LineError


def test_dataset():
    # Track how many recursion error we get
    recursion_errors_count = 0

    with jsonlines.open('dataset/__exprs.jsonl') as reader:
        for line, obj in enumerate(reader, 1):
            try:
                parse(obj['text'])
            except RecursionError:
                recursion_errors_count += 1
            except Exception as e:
                raise LineError(line) from e

    print(f'Got {recursion_errors_count} recursion errors', file=sys.stderr)
