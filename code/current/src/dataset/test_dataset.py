import jsonlines
import parsy

from parser import parse
from utils import LineError


def test_dataset():
    with jsonlines.open('dataset/__exprs.jsonl') as reader:
        for line, obj in enumerate(reader, 1):
            try:
                parse(obj['text'])
            except Exception as e:
                raise LineError(line) from e
