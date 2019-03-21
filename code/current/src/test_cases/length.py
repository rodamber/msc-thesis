from synthesis.types import example

cases = (
    # Try to find the length of a string

    # Bad: One example. Seems like index can be used to do some nasty stuff.
    [example(('abc'), 3)],

    # Bad: Two examples. Again, index is at fault.
    [example(('abc'), 3), example(('rodrigo'), 7)],

    # Good: Three examples. It seems like it's easier to just use length now.
    [example(('abc'), 3),
     example(('rodrigo'), 7),
     example(('pedro'), 5)],
)
