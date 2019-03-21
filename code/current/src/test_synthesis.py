import pytest

from ..synthesis.synth import synth
from .test_cases import all_test_cases


@pytest.mark.parametrize('examples', all_test_cases())
def test_synth(examples):
    is_ok, _ = synth(examples, timeout=1000)
    assert is_ok


if __name__ == '__main__':
    test_synth()
