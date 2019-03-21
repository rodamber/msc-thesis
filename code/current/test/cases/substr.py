from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    (Example(
        inputs=('Text longer than thirty characters.'),
        output='Text longer than thirty charac')),
    (Example(
        inputs=('Text longer than thirty characters.'),
        output='Text longer than thirty charac'),
     Example(inputs=('Small text.'), output='Small text.')),
    (Example(
        inputs=('Text longer than thirty characters.'),
        output='Text longer than thirty charac'),
     Example(inputs=('Small text.'), output='Small text.'),
     Example(
         inputs=('This text is also longer than thirty characters.'),
         output='This text is also longer than ')),
    (Example(inputs=('01/04/2000'), output='01')),
    (Example(inputs=('01/04/2000'), output='01'),
     Example(inputs=('02/05/2000'), output='02')),
    (Example(inputs=('01/04/2000'), output='04'),
     Example(inputs=('02/05/2000'), output='05')),
    (Example(inputs=('01/04/2000'), output='2000'),
     Example(inputs=('02/05/2001'), output='2001')),
    (Example(inputs=p.v('#01-04-2000#'), output='2000'),
     Example(inputs=p.v('#02-05-2001#'), output='2001')),
)
