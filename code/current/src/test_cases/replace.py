from synthesis.types import example

cases = (
    # Simple replace test cases
    [example(('John Doe'), 'John_Doe')],
    [
        example(('John Doe'), 'John_Doe'),
        example(('Michael Scott'), 'Michael_Scott')
    ],
    [example(('01/01/2000'), '01-01-2000')],
    [
        example(('01/01/2000', '/', '-'), '01-01-2000'),
        example(('01/02/2000', '/', '-'), '01-02-2000')
    ],
    [
        example(('01/01/2000', '/'), '01-01-2000'),
        example(('01/02/2000', '/'), '01-02-2000')
    ],
    [
        example(('01/01/2000'), '01-01-2000'),
        example(('01/02/2000'), '01-02-2000')
    ])
