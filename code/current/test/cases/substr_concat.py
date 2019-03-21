from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    (Example(
        inputs=('Text longer than thirty characters.'),
        output='Text longer than thirty charac...')),
    (Example(
        inputs=('Text longer than thirty characters.'),
        output='Text longer than thirty charac...'),
     Example(inputs=('Small text.'), output='Small text.')),
    (Example(
        inputs=('Text longer than thirty characters.'),
        output='Text longer than thirty charac...'),
     Example(inputs=('Small text.'), output='Small text.'),
     Example(
         inputs=('This text is also longer than thirty characters.'),
         output='This text is also longer than ...')),
)
