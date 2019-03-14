import pdb

import pyrsistent as p
from z3 import *

from synthesis.smt.enum_lines import *

e1 = Example(inputs=p.v('John', 'Doe', ' '), output='John Doe')
e2 = Example(inputs=p.v('Jane', 'Done'), output='Jane Done')
e3 = Example(inputs=p.v('Andre', 'Moreira'), output='Andre Moreira')
examples = p.v(e1)

# library = p.v(concat)

res = synth(library, examples, program_size=2)

if res:
    prog, model, solver = res
    # print(model)
    pretty_program(prog, model)
    # print(solver)
else:
    print('Unable to synthesize :\'(')

# test
# program = generate_program(p.v(concat, concat), examples)

# consts = program.consts
# inputs = program.inputs
# outputs = p.pvector(l.output for l in program.lines)
# holes = p.pvector(h for l in program.lines for h in l.holes)

# const_count = len(consts)
# input_count = len(examples[0].inputs)
# component_count = len(program.lines)
# hole_count = sum(len(l.component.domain) for l in program.lines)

# b = list(gen_const_line_constraints(consts))
# c = list(gen_input_line_constraints(inputs, const_count))
# d = list(gen_output_line_constraints(outputs, const_count, input_count))
# e = list(gen_hole_line_constraints(program))
# f = list(gen_sort_line_constraints(inputs, holes, outputs))
# g = list(gen_well_formedness_constraints(holes, consts, inputs, outputs, examples))
# h = list(gen_output_soundness_constraints(program.lines, examples))
# i = list(gen_input_output_completeness_constraints(inputs, outputs, holes, examples))
# j = list(gen_correctness_constraints(hole_count, program.lines, examples))
# k = list(gen_input_value_constraints(inputs, examples))

# print('=============================')
# print(b, c, d, e, f, sep='\n')
# print('=============================')
# for x in g: print(x)
# print('=============================')
# print(h)
# print('=============================')
# for x in i: print(x)
# print('=============================')
# print(j, k, sep='\n')
# print('=============================')
