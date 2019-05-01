import json
import pyrsistent as p
from outsystems_lang import parse
from outsystems_lang import expr_ast as ast
import os
from collections import Counter


def collect_lits(tree):
    if ast.expr(tree) == ast.Expr.Lit:
        yield ast.val(tree)
    elif ast.expr(tree) == ast.Expr.Func:
        for c in ast.children(tree):
            yield from collect_lits(c)


def find_consts(directory: str):
    for f in os.listdir(directory):
        if f.startswith('examples'):
            with open(f'{directory}/{f}') as file:
                tree = parse(json.load(file)['text'])
                yield from collect_lits(tree)


# all_consts = Counter(find_consts('examples'))
# 67 constants
all_consts = Counter({
    0: 69,
    1: 36,
    " ": 16,
    "...": 10,
    5: 9,
    "/": 8,
    "": 8,
    10: 7,
    "-": 6,
    3: 5,
    ".": 5,
    7: 4,
    "0": 3,
    "@": 3,
    ",": 3,
    50: 2,
    16: 2,
    "(": 2,
    "http://": 2,
    "https://": 2,
    "_": 2,
    6: 2,
    100: 2,
    2: 2,
    "|": 2,
    ", ": 2,
    "\\": 2,
    9: 2,
    45: 1,
    "+": 1,
    ")": 1,
    "Prefix ": 1,
    "<": 1,
    ">": 1,
    "Sprint: ": 1,
    " At:": 1,
    "updated on ": 1,
    20: 1,
    "&nbsp;": 1,
    8: 1,
    ".com": 1,
    " â‚¬": 1,
    80: 1,
    "Enviado para ": 1,
    19: 1,
    "of": 1,
    "of<br />": 1,
    "Way": 1,
    "<br />Way": 1,
    99: 1,
    "weeks": 1,
    "wks": 1,
    40: 1,
    " | ": 1,
    "#": 1,
    70: 1,
    "Customer with ": 1,
    15: 1,
    "bed ": 1,
    "\n": 1,
    "    ": 1,
    300: 1,
    30: 1,
    "<span id=": 1,
    " > ": 1,
    "!@": 1,
    "Created on ": 1
})

# for x, y in all_consts.items():
#     if isinstance(x, str):
#         print(f'{repr(x)},{y}')
#     else:
#         print(f'{x},{y}')
