from synthesis.types import example

cases = (
    [example(('outsystems.com',), 10)],

    [example(('outsystems.com', '.'), 10)],

    [example(('outsystems.com',), 10),
     example(('cmu.edu',), 3)],

    # Adding more '.' shouldn't confuse the synthesizer.
    [example(('outsystems.com',), 10),
     example(('abc.gmail.com',), 3)],
)
