from synthesis.types import example

cases = (
    [example(('abc',), 3)],
    [example(('abc',), 3), example(('rodrigo',), 7)],
    [example(('abc',), 3),
     example(('rodrigo',), 7),
     example(('pedro',), 5)],
)
