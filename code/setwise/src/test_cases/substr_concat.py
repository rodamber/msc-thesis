from simple.types import IO

cases = (
    [
        IO(('Text longer than thirty characters.', ),
           'Text longer than thirty charac...')
    ],
    [
        IO(('Text longer than thirty characters.', ),
           'Text longer than thirty charac...'),
        IO(('Small text.', ), 'Small text.')
    ],
    [
        IO(('Text longer than thirty characters.', ),
           'Text longer than thirty charac...'),
        IO(('Small text.', ), 'Small text.'),
        IO(('This text is also longer than thirty characters.', ),
           'This text is also longer than ...')
    ],
)
