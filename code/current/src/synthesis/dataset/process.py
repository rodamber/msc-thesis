import itertools
import os
from typing import *

import jsonlines
import pyrsistent as p

from ..dsl.ast2component import ast2comp
from ..dsl.component import render, run
from ..dsl.input_gen import input_gen
from ..outsystems import expr_ast as ast
from ..outsystems import templatify as t
from ..outsystems.parser import parse
from ..utils import LineError

'''
 - [x] Simplify dataset by removing every json field apart from text or functions.
 - [ ] Templatify dataset (to a new file).
 - [ ] Rename operators to corresponding names and add them to the functions
   field. Will need to infer types.
 - [ ] Prune equal expressions.
 - [ ] Filter expressions that exclusively use supported constructs.
 - [ ] Split dataset into new files of expressions of different sizes.
 - [ ] Autogenerate inputs-output examples and save them.
'''

# ==============================================================================
# Templatify


def templatify(json: p.PVector):
    return ast_vec.transform(['text'], lambda x: t.templatify(parse(x)))


# # ==============================================================================
# # Select

# def select(infile, outfile, predicate, count=None, templates=False):
#     '''
#     Selects at most count expressions from infile that satisfy predicate, and
#     writes them to outfile.
#     '''
#     import jsonlines

#     def json():
#         with jsonlines.open(infile, 'r') as reader:
#             for line, elem in enumerate(reader, 1):
#                 try:
#                     if predicate(elem):
#                         if templates:
#                             elem['text'] = repr(
#                                 templatify(parse(elem['text'])))
#                         yield elem
#                 except Exception as e:
#                     raise LineError(line) from e

#     with jsonlines.open(outfile, 'w') as writer:
#         writer.write_all(itertools.islice(json(), count))

# # ==============================================================================
# # Predicates

# def short_pred(cutoff=300):
#     return lambda x: len(x['text']) < cutoff

# # FIXME XXX
# # Doesn't support '+' for concatenation yet
# def in_dsl(dsl):
#     def iter_(e):
#         from anytree import LevelOrderIter
#         return (node.name for node in LevelOrderIter(e.to_anytree()))

#     def pred(x):
#         functions = set(x['functions'])
#         text = x['text']

#         if functions and set(functions) <= set(dsl):
#             # print(f'Hey!\nfunctions: {functions}\ndsl: {dsl}')
#             template = templatify(parse(text))

#             # Filter unwanted operations

#             no_binops = not any(
#                 isinstance(x, ast.Binop) for x in iter_(template))
#             no_unops = not any(
#                 isinstance(x, ast.Unop) for x in iter_(template))
#             no_ternary_index = not any(
#                 isinstance(x, ast.Func) and x.name == 'Index'
#                 and len(x.parameters) > 2 for x in iter_(template))

#             return no_binops and no_unops and no_ternary_index
#         else:
#             return False

#     return pred

# def ast_size(size):
#     return lambda x: templatify(parse(x['text'])).size() == size

# # ==============================================================================
# # Main

# # FIXME Some programs become equal after templatification
# def process(n):
#     dataset = '../../dataset/exprs-short300.jsonl'
#     dsl = ['Length', 'Concat', 'Substr', 'Replace', 'Index']

#     def pred0(x):
#         return in_dsl(dsl)(x) and ast_size(n)(x)

#     infile = f'../../dataset/dsl01/exprs-short300-dsl01-size{n}.jsonl'
#     select(dataset, infile, pred0, count=10)

#     with jsonlines.open(infile, 'r') as reader:
#         for line, x in itertools.islice(enumerate(reader), None):
#             outfile = f'../../dataset/dsl01/size0{n}/{line}.benchmark'
#             os.makedirs(os.path.dirname(outfile), exist_ok=True)

#             with open(outfile, 'w+') as f:
#                 text = x['text']
#                 prog = ast2comp(templatify(parse(text)))

#                 envit = input_gen(prog, 5)
#                 examples = ((env, run(prog, env)) for env in envit)

#                 f.writelines(map(lambda x: str(x) + '\n', examples))

#                 f.write('\n=== Solution ===\n')
#                 f.write(render(prog) + '\n')

# # TODO
# # Assert that the benchmarks are correct
# # Number of files, number of lines, etc
