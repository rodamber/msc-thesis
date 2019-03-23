from synthesis.types import example

cases = (
    # 00
    [example(('outsystems.com', ), 'outsystems')],
    # 01
    [
        example(('outsystems.com', ), 'outsystems'),
        example(('cmu.edu', ), 'cmu')
    ],
    # 02
    [
        example(('outsystems.com', ), 'outsystems'),
        example(('cmu.edu', ), 'cmu'),
        example(('tecnico.pt', ), 'tecnico')
    ],
    # 03
    [
        example(('outsystems.com', '.'), 'outsystems'),
        example(('cmu.edu', '.'), 'cmu')
    ],
    # 04
    [
        example(('www.outsystems.com', ), 'outsystems'),
        example(('www.cmu.edu', ), 'cmu'),
        example(('www.tecnico.pt', ), 'tecnico')
    ],
)
