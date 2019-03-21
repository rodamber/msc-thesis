from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    (Example(inputs=('outsystems.com'), output='outsystems')),
    (Example(inputs=('outsystems.com'), output='outsystems'),
     Example(inputs=('cmu.edu'), output='cmu')),
    (Example(inputs=('outsystems.com'), output='outsystems'),
     Example(inputs=('cmu.edu'), output='cmu'),
     Example(inputs=('tecnico.pt'), output='tecnico')),
    (Example(inputs=('outsystems.com', '.'), output='outsystems'),
     Example(inputs=('cmu.edu', '.'), output='cmu')),
    (Example(inputs=('www.outsystems.com'), output='outsystems'),
     Example(inputs=('www.cmu.edu'), output='cmu'),
     Example(inputs=('www.tecnico.pt'), output='tecnico')),
)
