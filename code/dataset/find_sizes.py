import json
import pyrsistent as p
from outsystems_lang import parse
from outsystems_lang import expr_ast as ast
import os
import re
from collections import Counter

p = re.compile(r'examples-(\d\d).*')
recs = ['ToLower', 'ToUpper', 'Trim', 'TrimStart', 'TrimEnd', 'Replace']

def find_sizes(directory: str):
    for f in os.listdir(directory):
        m = p.match(f)
        if m:
            with open(f'{directory}/{f}') as file:
                try:
                    jobj = json.load(file)
                    fs = jobj['functions']
                    if not any(x in fs for x in recs):
                        yield jobj['size']
                except:
                    print(f'Error on {f}')
                    raise


size = Counter(find_sizes('examples'))
# size = Counter({2: 31, 3: 22, 1: 16, 4: 10, 5: 10, 6: 5, 7: 1})
Counter({2: 19, 3: 12, 4: 8, 5: 5, 1: 5, 7: 1, 6: 1})
