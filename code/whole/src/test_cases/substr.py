from simple.types import IO

cases = (
    [
        IO(('Text longer than thirty characters.', ),
           'Text longer than thirty charac')
    ],
    [
        IO(('Text longer than thirty characters.', ),
           'Text longer than thirty charac'),
        IO(('Small text.', ), 'Small text.')
    ],
    [
        IO(('Text longer than thirty characters.', ),
           'Text longer than thirty charac'),
        IO(('Small text.', ), 'Small text.'),
        IO(('This text is also longer than thirty characters.', ),
           'This text is also longer than ')
    ],
    [IO(('01/04/2000', ), '01')],
    [IO(('01/04/2000', ), '01'),
     IO(('02/05/2000', ), '02')],
    [IO(('01/04/2000', ), '04')],
    [IO(('01/04/2000', ), '04'),
     IO(('02/05/2000', ), '05')],
    [IO(('01/04/2000', ), '2000')],
    [IO(('01/04/2000', ), '2000'),
     IO(('02/05/2001', ), '2001')],
    [IO(('#01-04-2000#', ), '2000')],
    [IO(('#01-04-2000#', ), '2000'),
     IO(('#02-05-2001#', ), '2001')],
)
