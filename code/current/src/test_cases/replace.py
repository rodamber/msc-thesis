from synthesis.types import example

cases = (
    # Simple replace test cases
    [example(('John Doe', ), 'John_Doe')],
    [
        example(('John Doe', ), 'John_Doe'),
        example(('Michael Scott', ), 'Michael_Scott')
    ],
    [example(('01/02/2000', ), '01-02-2000')],
    [ # 190
        example(('01/02/2000', '/', '-'), '01-02-2000'),
        example(('20/03/1999', '/', '-'), '20-03-1999')
    ],
    [ # 1479 sec
        example(('01/02/2000', '-'), '01-02-2000'),
        example(('20/03/1999', '-'), '20-03-1999')
    ],
    [ # 1801 sec
        example(('01/02/2000', ), '01-02-2000'),
        example(('02/03/1999', ), '02-03-1999')
    ])
