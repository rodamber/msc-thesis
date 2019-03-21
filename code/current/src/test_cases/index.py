from synthesis.smt.lines.types import example

cases = (
    # Try to find the index of '.'

    # One example doesn't work well if we don't explicitly say we're looking for
    # '.'
    [example(('outsystems.com'), 10)],

    # It works well with one example if we say explicitly we're looking for '.'
    [example(('outsystems.com', '.'), 10)],

    # But it works well if we give it two examples.
    [example(('outsystems.com'), 10),
     example(('cmu.edu'), 3)],

    # Adding more '.' shouldn't confuse the synthesizer.
    [example(('outsystems.com'), 10),
     example(('abc.gmail.com'), 3)],
)
