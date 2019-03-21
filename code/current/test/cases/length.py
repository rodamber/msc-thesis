from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    # Try to find the length of a string

    # Bad: One example. Seems like index can be used to do some nasty stuff.
    (Example(inputs=('abc'), output=3)),

    # Bad: Two examples. Again, index is at fault.
    (
        Example(inputs=('abc'), output=3),
        Example(inputs=('rodrigo'), output=7),
    ),

    # Good: Three examples. It seems like it's easier to just use length now.
    (Example(inputs=('abc'), output=3), Example(inputs=('rodrigo'), output=7),
     Example(inputs=('pedro'), output=5)),
)
