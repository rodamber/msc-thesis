import pytest

from src.synthesis.smt.lines.synth import synth

from .cases import (concat, index, length, replace, substr, substr_concat,
                    substr_index)
from .timewith import timewith

all_cases = concat.cases + index.cases + length.cases + replace.cases + \
    substr.cases + substr_concat.cases + substr_index.cases

@pytest.mark.parametrize('examples', all_cases)
def test_synth(examples):
    with timewith('synthesis test') as timer:
        is_ok, _ = synth(examples, timeout=1000)
        elapsed = timer.elapsed

    assert is_ok
    assert elapsed <= 60  # one minute


if __name__ == '__main__':
    test_all()
