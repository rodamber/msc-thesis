from synthesis.smt.enum_lines import *

e1 = Example(inputs=p.v('John', 'Doe'), output='John Doe')
e2 = Example(inputs=p.v('Jane', 'Done'), output='Jane Done')
examples = p.v(e1, e2)

program = generate_program(p.v(concat, concat), examples)
pretty_program(program, e1)

# library = p.v(concat)
print(synth(library, examples, program_size=2))
