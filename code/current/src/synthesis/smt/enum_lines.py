import pyrsistent as p
import z3

'''
-----------
Definitions
-----------

H := set of all holes
I := set of all program inputs
O := set of all component outputs
X := H or I or O
C := set of all components
E := set of all examples
M := set of magic constants

S_e := S and e
l_x := line number where x is defined

holes(c)     := holes of component c
line(c)      := line (python int) of component c
output(c, e) := output (z3 constant) of component c on example e
last(cs)     := component that appears last in the program (highest line number)

component(h) := component of which hole h is part of

holes(e)   := holes of all components in example e
inputs(e)  := inputs of example e
outputs(e) := outputs of all components in example e

-----------
Constraints
-----------

We need to make sure that:

- output soundness
- aciclicity
- all program inputs are used on each example
- all component outputs are used on each example
- for every example, the output of the last component equals the output of the
  example

01. 1 <= l_m <= |M|                          for m in M
02. |M| + 1 <= l_i <= I                      for i in I
03. l_{output(c, e)} == line(c)              for c in C, e in E
04. 1 <= l_h <= line(c) + 1                  for c in C, h in holes(c)
05. l_x != l_y                               for x in X, y in X
                                               if sort(x) != sort(y)
06. l_x == l_y => x == y                     for e in E, x in holes(e),
                                               y in (inputs(e) or outputs(e))
                                               if sort(x) == sort(y)
07. (l_x == l_y and l_x <= |M|) => x == y    for x in H, y in H
                                               if sort(x) == sort(y)
08. output(c) == c(x1, x2, ..., xn)          for c in C,
                                               x1, x2, ..., xn in holes(c)
09. Or_{h in holes(e)}(l_h == l_i)           for i in I, e in E
                                               if sort(h) == sort(i)
10. Or_{h in {h in holes(e) | line(component(h) > line(component(o)))}(l_h == l_o)}
                                             for o in O, e in E
                                               if sort(h) == sort(o)
11. output(last(C), e) == output(e)          for e in E

In English:

01. Define the range for the lines of the magic constants
02. Define the range for the lines of the input constants
03. Define the range for the lines of the output constants on each example
04. Define the range for the lines of the hole constants
05. Two constants of the same sort cannot share their line.
06. In a given example, assert that if a hole is defined on the same line as an
input, or an output of some component, then its value must be equal to the value
of that input, or output, respectively. Do this for every example.
07. Two holes that share a line where a magic constant is defined must be equal
across all examples.
08. On a given example, the output of each component must be the result of
running that component with the values of its holes as inputs.
09. Every program input must be used on every example.
10. Every component output must be used on every example.
11. The output of the last component must equal the output of the example.


Constraint generation should be aborted if no constraints need to be generated
on points 09 and 10.

'''
