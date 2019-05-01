import json
import pyrsistent as p
from outsystems_lang import parse
from outsystems_lang import expr_ast as ast
import os
from collections import Counter


def count_funs(directory: str):
    c = Counter()

    for f in os.listdir(directory):
        if f.startswith('examples'):
            with open(f'{directory}/{f}') as file:
                try:
                    fs = json.load(file)['functions']
                    c += Counter(fs)
                except:
                    print(f'Error on {f}')
    return c


bs = count_funs('examples')


def count_recs(directory: str):
    recs = ['ToLower', 'ToUpper', 'Trim', 'TrimStart', 'TrimEnd', 'Replace']

    for f in os.listdir(directory):
        if f.startswith('examples'):
            with open(f'{directory}/{f}') as file:
                try:
                    fs = json.load(file)['functions']
                    if any(x in fs for x in recs):
                        yield f
                except:
                    print(f'Error on {f}')
    return c


n = len(list(count_recs('examples')))


