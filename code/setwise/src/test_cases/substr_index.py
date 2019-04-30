from simple.types import IO

cases = (
    # 00
    [IO(('outsystems.com', ), 'outsystems')],
    # 01
    [IO(('outsystems.com', ), 'outsystems'),
     IO(('cmu.edu', ), 'cmu')],
    # 02
    [
        IO(('outsystems.com', ), 'outsystems'),
        IO(('cmu.edu', ), 'cmu'),
        IO(('tecnico.pt', ), 'tecnico')
    ],
    # 03
    [IO(('outsystems.com', '.'), 'outsystems'),
     IO(('cmu.edu', '.'), 'cmu')],
    # 04
    [
        IO(('www.outsystems.com', ), 'outsystems'),
        IO(('www.cmu.edu', ), 'cmu'),
        IO(('www.tecnico.pt', ), 'tecnico')
    ],
    # 05
    [
        IO(('www.outsystems.com', ), 'outsystems'),
        IO(('www.cmu.edu', ), 'cmu'),
        IO(('www3.tecnico.pt', ), 'tecnico')
    ],
    # 06
    [
        IO(('www.outsystems.com', ), 'outsystems'),
        IO(('www.cmu.edu', ), 'cmu'),
        IO(('www3.tecnico.pt', ), 'tecnico'),
        IO(['https://www.tecnico.pt'], 'tecnico'),
    ],
)

# INFO:Started synthesis tests
# INFO:IOs:
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
