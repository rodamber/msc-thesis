from hypothesis import assume, given, note, strategies as st
from hypothesis.strategies import composite
from string import ascii_letters


@composite
def substr(draw, char_set=ascii_letters):
    text = draw(st.text(alphabet=char_set, min_size=1))
    middle = draw(st.integers(0, len(text) - 1))
    left = draw(st.integers(0, middle))
    right = draw(st.integers(middle, len(text) - 1))
    return (text, left, right)
