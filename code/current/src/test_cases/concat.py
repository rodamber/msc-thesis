from synthesis.types import example

cases = (
    # 0: Size 2
    [example(('John', 'Doe'), 'John Doe')],

    # 1: Size 2
    [
        example(('John', 'Doe'), 'John Doe'),
        example(('Anne', 'Smith'), 'Anne Smith'),
    ],

    # 2: Size 3
    [
        example(('John', 'Doe', '-Odoi'), 'John Doe-Odoi'),
    ],

    # 3: Size 3
    [
        example(('John', 'Doe', '-Odoi'), 'John Doe-Odoi'),
        example(('Anne', 'Smith', '-Sonian'), 'Anne Smith-Sonian'),
    ],

    # 4: Size 3, learning the prefix
    [
        example(('John', 'Doe'), 'Dr. John Doe'),
    ],

    # 5: Size 3, learning the prefix
    [
        example(('John', 'Doe'), 'Dr. John Doe'),
        example(('Anne', 'Smith'), 'Dr. Anne Smith'),
    ],

    # 6: Size 4
    [
        example(('John', 'Michael', 'Doe'), 'John Michael Doe'),
    ],

    # 7: Size 4
    [
        example(('John', 'Michael', 'Doe'), 'John Michael Doe'),
        example(('Anne', 'Marie', 'Smith'), 'Anne Marie Smith')
    ],

    # 8: Size 4
    [
        example(('John', 'Michael', 'Doe'), 'John Michael Doe'),
        example(('Anne', 'Marie', 'Smith'), 'Anne Marie Smith'),
        example(('Laura', 'Pinto', 'Wang'), 'Laura Pinto Wang')
    ],

    # 9: Size 5, learning the prefix
    [example(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith')],

    # 10: Size 5, learning the prefix
    [
        example(('John', 'Michael', 'Doe'), 'Dr. John Michael Doe'),
        example(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith'),
    ],

    # 11: Size 5, learning the prefix
    [
        example(('John', 'Michael', 'Doe'), 'Dr. John Michael Doe'),
        example(('Anne', 'Marie', 'Smith'), 'Dr. Anne Marie Smith'),
        example(('Laura', 'Pinto', 'Wang'), 'Dr. Laura Pinto Wang')
    ],

    # 12: Size 6, no learning
    [
        example(('John', 'Oliver', 'Michael', 'Doe', ' '),
                'John Oliver Michael Doe'),
    ],

    # 13: Size 6, no learning
    [
        example(('John', 'Oliver', 'Michael', 'Doe', ' '),
                'John Oliver Michael Doe'),
        example(('Anne', 'Emily', 'Marie', 'Smith', ' '),
                'Anne Emily Marie Smith')
    ],

    # 14: Size 6, with learning
    [
        example(('John', 'Oliver', 'Michael', 'Doe'),
                'John Oliver Michael Doe'),
    ],

    # 15: Size 6, with learning
    [
        example(('John', 'Oliver', 'Michael', 'Doe'),
                'John Oliver Michael Doe'),
        example(('Anne', 'Emily', 'Marie', 'Smith'), 'Anne Emily Marie Smith')
    ],
)
