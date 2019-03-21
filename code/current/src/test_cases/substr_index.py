from synthesis.types import example

cases = (
    [example(('outsystems.com', ), 'outsystems')],
    [
        example(('outsystems.com', ), 'outsystems'),
        example(('cmu.edu', ), 'cmu')
    ],
    [
        example(('outsystems.com', ), 'outsystems'),
        example(('cmu.edu', ), 'cmu'),
        example(('tecnico.pt', ), 'tecnico')
    ],
    [
        example(('outsystems.com', '.'), 'outsystems'),
        example(('cmu.edu', '.'), 'cmu')
    ],
    [
        example(('www.outsystems.com', ), 'outsystems'),
        example(('www.cmu.edu', ), 'cmu'),
        example(('www.tecnico.pt', ), 'tecnico')
    ],
)
