from simple.types import IO

cases = (
    [IO(('outsystems.com', ), 10)],
    [IO(('outsystems.com', '.'), 10)],
    [IO(('outsystems.com', ), 10),
     IO(('cmu.edu', ), 3)],

    # Adding more '.' shouldn't confuse the synthesizer.
    [IO(('outsystems.com', ), 10),
     IO(('abc.gmail.com', ), 3)],
)
