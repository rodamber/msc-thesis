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
    # 05
    [
        example(('www.outsystems.com', ), 'outsystems'),
        example(('www.cmu.edu', ), 'cmu'),
        example(('www3.tecnico.pt', ), 'tecnico')
    ],
    # 06
    [
        example(('www.outsystems.com', ), 'outsystems'),
        example(('www.cmu.edu', ), 'cmu'),
        example(('www3.tecnico.pt', ), 'tecnico'),
        example(['https://www.tecnico.pt'], 'tecnico'),
    ],
)

# INFO:Started synthesis tests
# INFO:Examples:
# INFO:   ('www.outsystems.com',) --> 'outsystems'
# INFO:   ('www.cmu.edu',) --> 'cmu'
# INFO:   ('www3.tecnico.pt',) --> 'tecnico'
# INFO:   ('https://www.tecnico.pt',) --> 'tecnico'
# DEBUG:Library of components:
# DEBUG:  index
# DEBUG:  index3
# DEBUG:  substr
# DEBUG:  minus
# DEBUG:  add
# DEBUG:Min size: 5
# DEBUG:Max size: 5
# DEBUG:Z3 max_conflicts: 100000
# DEBUG:Solver result: SAT (177.490 seconds)
# INFO:Elapsed time: 177.873 seconds
# INFO:Program: (a) ↦ substr(a, add(1, index(a, '.')), minus(index3(a, '.',
# add(1, inde x(a, '.'))), add(1, index(a, '.'))))
# INFO:==================================================
# INFO:Finished synthesis tests
