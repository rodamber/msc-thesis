from synthesis.smt.enum_lines import *

e1 = Example(inputs=p.v('John', 'Doe'), output='John Doe')
e2 = Example(inputs=p.v('Jane', 'Done'), output='Jane Done')
e3 = Example(inputs=p.v('Andre', 'Moreira'), output='Andre Moreira')
examples = p.v(e1)

# library = p.v(concat)

res = synth(library, examples, program_size=2)

if res:
    prog, model, solver = res
    pretty_program(prog, model)
