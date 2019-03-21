from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    # Try to find the index of '.'

    # One example doesn't work well if we don't explicitly say we're looking for
    # '.'
    (Example(inputs=('outsystems.com'), output=10)),

    # It works well with one example if we say explicitly we're looking for '.'
    (Example(inputs=('outsystems.com', '.'), output=10)),

    # But it works well if we give it two examples.
    (
        Example(inputs=('outsystems.com'), output=10),
        Example(inputs=('cmu.edu'), output=3),
    ),

    # Adding more '.' shouldn't confuse the synthesizer.
    (Example(inputs=('outsystems.com'), output=10),
     Example(inputs=('abc.gmail.com'), output=3)),
)
