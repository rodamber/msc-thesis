from synthesis.types import example

cases = (
    [
        example(('Text longer than thirty characters.'),
                'Text longer than thirty charac...')
    ],
    [
        example(('Text longer than thirty characters.'),
                'Text longer than thirty charac...'),
        example(('Small text.'), 'Small text.')
    ],
    [
        example(('Text longer than thirty characters.'),
                'Text longer than thirty charac...'),
        example(('Small text.'), 'Small text.'),
        example(('This text is also longer than thirty characters.'),
                'This text is also longer than ...')
    ],
)
