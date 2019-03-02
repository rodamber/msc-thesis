import jsonlines
import parsy
import pytest
import re

from parser import parse


def test_dataset():
    with jsonlines.open('dataset/exprs.jsonl') as reader:
        for line, obj in enumerate(reader, 1):
            if not re.search(r'\[.*\]', obj['text']):
                try:
                    parse(obj['text'])
                except parsy.ParseError:
                    pytest.fail(
                        f"Unexpected ParseError (line {line}): {obj['text']}")
