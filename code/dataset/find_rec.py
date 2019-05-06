import json
import pyrsistent as p
from outsystems_lang import parse
from outsystems_lang import expr_ast as ast
import os
import re
from collections import Counter

p = re.compile(r'examples-(\d\d).*')


def count_funs(directory: str):
    c = Counter()

    for f in os.listdir(directory):
        if f.startswith('examples'):
            with open(f'{directory}/{f}') as file:
                try:
                    fs = json.load(file)['functions']
                    if not any(x in fs for x in recs):
                        c += Counter(fs)
                except:
                    print(f'Error on {f}')
    return c


bs = count_funs('examples')

recs = ['ToLower', 'ToUpper', 'Trim', 'TrimStart', 'TrimEnd', 'Replace']


def count_recs(directory: str):
    for f in os.listdir(directory):
        if f.startswith('examples'):
            with open(f'{directory}/{f}') as file:
                try:
                    fs = json.load(file)['functions']
                    if any(x in fs for x in recs):
                        yield f
                except:
                    print(f'Error on {f}')


n = len(list(count_recs('examples')))


def find_rec(dpath):
    for basename in os.listdir(dpath):
        m = p.match(basename)
        if m:
            with open(f'{dpath}/{basename}') as f:
                fs = json.load(f)['functions']
                number = m.group(1)
                if any(x in fs for x in recs):
                    yield (number, 'TRUE')
                else:
                    yield (number, 'FALSE')
