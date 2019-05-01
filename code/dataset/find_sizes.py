import json
import pyrsistent as p
from outsystems_lang import parse
from outsystems_lang import expr_ast as ast
import os
from collections import Counter


def find_sizes(directory: str):
    for f in os.listdir(directory):
        if f.startswith('examples'):
            with open(f'{directory}/{f}') as file:
                try:
                    yield json.load(file)['size']
                except:
                    print(f'Error on {f}')


# size = Counter(find_sizes('examples'))
size = Counter({2: 31, 3: 22, 1: 16, 4: 10, 5: 10, 6: 5, 7: 1})
