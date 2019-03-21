from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    # Simple replace test cases
    (Example(inputs=('John Doe'), output='John_Doe')),
    (Example(inputs=('John Doe'), output='John_Doe'),
     Example(inputs=('Michael Scott'), output='Michael_Scott')),
    (Example(inputs=('01/01/2000'), output='01-01-2000')),
    (Example(inputs=('01/01/2000', '/', '-'), output='01-01-2000'),
     Example(inputs=('01/02/2000', '/', '-'), output='01-02-2000')),
    (Example(inputs=('01/01/2000', '/'), output='01-01-2000'),
     Example(inputs=('01/02/2000', '/'), output='01-02-2000')),
    (Example(inputs=('01/01/2000'), output='01-01-2000'),
     Example(inputs=('01/02/2000'), output='01-02-2000')))
