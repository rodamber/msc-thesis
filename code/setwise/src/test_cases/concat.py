from simple.types import IO

cases = (
    # 0: Size 2
    [IO(('John', 'Doe'), 'John Doe')],

    # 1: Size 2
    [
        IO(('John', 'Doe'), 'John Doe'),
        IO(('Anne', 'Smith'), 'Anne Smith'),
    ],

    # 2: Size 3
    [
        IO(('John', 'Doe', '-Odoi'), 'John Doe-Odoi'),
    ],

    # 3: Size 3
    [
        IO(('John', 'Doe', '-Odoi'), 'John Doe-Odoi'),
        IO(('Anne', 'Smith', '-Sonian'), 'Anne Smith-Sonian'),
    ],

    # 4: Size 3, learning the prefix
    [
        IO(('John', 'Doe'), 'Dr. John Doe'),
    ],

    # 5: Size 3, learning the prefix
    [
        IO(('John', 'Doe'), 'Dr. John Doe'),
        IO(('Anne', 'Smith'), 'Dr. Anne Smith'),
    ],

    # 6: Size 4
    [
        IO(('John', 'Michael', 'Doe'), 'John Michael Doe'),
    ],

    # 7: Size 4
    [
        IO(('John', 'Michael', 'Doe'), 'John Michael Doe'),
        IO(('Anne', 'Marie', 'Smith'), 'Anne Marie Smith')
    ],

    # 8: Size 4
    [
        IO(('John', 'Michael', 'Doe'), 'John Michael Doe'),
        IO(('Anne', 'Marie', 'Smith'), 'Anne Marie Smith'),
        IO(('Laura', 'Pinto', 'Wang'), 'Laura Pinto Wang')
    ],

    # 9: Size 5, learning the prefix
    [IO(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith')],

    # 10: Size 5, learning the prefix
    [
        IO(('John', 'Michael', 'Doe'), 'Dr. John Michael Doe'),
        IO(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith'),
    ],

    # 11: Size 5, learning the prefix
    [
        IO(('John', 'Michael', 'Doe'), 'Dr. John Michael Doe'),
        IO(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith'),
        IO(('Laura', 'Pinto', 'Wang'), 'Dr. Laura Pinto Wang')
    ],

    # 12: Size 6, no learning
    [
        IO(('John', 'Oliver', 'Michael', 'Doe', ' '),
           'John Oliver Michael Doe'),
    ],

    # 13: Size 6, no learning
    [
        IO(('John', 'Oliver', 'Michael', 'Doe', ' '),
           'John Oliver Michael Doe'),
        IO(('Anne', 'Emily', 'Marie', 'Smith', ' '), 'Anne Emily Marie Smith')
    ],

    # 14: Size 6, with learning
    [
        IO(('John', 'Oliver', 'Michael', 'Doe'), 'John Oliver Michael Doe'),
    ],

    # 15: Size 6, with learning
    [
        IO(('John', 'Oliver', 'Michael', 'Doe'), 'John Oliver Michael Doe'),
        IO(('Anne', 'Emily', 'Marie', 'Smith'), 'Anne Emily Marie Smith')
    ],
)
