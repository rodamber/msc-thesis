from synthesis.types import example

cases = (
    [
        example(('Text longer than thirty characters.'),
                'Text longer than thirty charac')
    ],
    [
        example(('Text longer than thirty characters.'),
                'Text longer than thirty charac'),
        example(('Small text.'), 'Small text.')
    ],
    [
        example(('Text longer than thirty characters.'),
                'Text longer than thirty charac'),
        example(('Small text.'), 'Small text.'),
        example(('This text is also longer than thirty characters.'),
                'This text is also longer than ')
    ],
    [example(('01/04/2000'), '01')],
    [example(('01/04/2000'), '01'),
     example(('02/05/2000'), '02')],
    [example(('01/04/2000'), '04'),
     example(('02/05/2000'), '05')],
    [example(('01/04/2000'), '2000'),
     example(('02/05/2001'), '2001')],
    [example(('#01-04-2000#'), '2000'),
     example(('#02-05-2001#'), '2001')],
)
