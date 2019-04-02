from simple.types import IO

cases = (
    [IO(('abc', ), 3)],
    [IO(('abc', ), 3), IO(('rodrigo', ), 7)],
    [IO(('abc', ), 3),
     IO(('rodrigo', ), 7),
     IO(('pedro', ), 5)],
)
