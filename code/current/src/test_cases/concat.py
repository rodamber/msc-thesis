from synthesis.smt.lines.types import example

cases = (
    # Size 2
    [example(('John', 'Doe'), 'John Doe')],

    # Size 2
    [example(('John', 'Doe'), 'John Doe'),
     example(('Anne', 'Smith'), 'Anne Smith')],

    # Size 3
    [example(('John', 'Doe', '-Odoi'), 'John Doe-Odoi'),
     example(('Anne', 'Smith', '-Sonian'), 'Anne Smith-Sonian')],

    # Size 3, learning the prefix
    [example(('John', 'Doe'), 'Dr. John Doe'),
     example(('Anne', 'Smith'), 'Dr. Anne Smith')],

    # Size 3, same as before
    [example(('John', 'Doe'), 'Dr. John Doe'),
     example(('Anne', 'Smith'), 'Dr. Anne Smith')],

    # Size 4
    [example(('John', 'Michael', 'Doe'), 'John Michael Doe'),
     example(('Anne', 'Marie', 'Smith'), 'Anne Marie Smith')],

    # Size 5, learning the prefix
    [example(('John', 'Michael', 'Doe'), 'Dr. John Michael Doe'),
     example(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith')],

    # Size 6
    [example(('John', 'Oliver', 'Michael', 'Doe'), 'John Oliver Michael Doe'),
     example(('Anne', 'Emily', 'Marie', 'Smith'), 'Anne Emily Marie Smith')],
)
