import os
import sys
from contextlib import suppress
from typing import *

import jsonlines

from ..outsystems import expr_ast as ast
from ..outsystems.parser import parse
from ..outsystems.render import render


'''
 - [x] Simplify dataset by removing every json field apart from text or functions.
 - [ ] Rename operators to corresponding names and add them to the functions
   field. Will need to infer types. Don't worry about supporting anything else
   apart from the dsl.
 - [ ] Templatify dataset (to a new file).
 - [ ] Prune equal expressions.
 - [ ] Filter expressions that exclusively use supported constructs.
 - [ ] Split dataset into new files of expressions of different sizes.
 - [ ] Generate inputs-output examples, and save them.
'''


class reader_writer:
    def __init__(self, in_iter, out_iter):
        self.in_iter = in_iter
        self.out_iter = out_iter

    def __enter__(self):
        self.reader = jsonlines.Reader(self.in_iter)
        self.writer = jsonlines.Reader(self.out_iter)
        return self.reader, self.writer

    def __exit__(self, type, value, traceback):
        self.reader.close()
        self.writer.close()


def templatify(in_iter=sys.stdin, out_iter=sys.stdout):
    with reader_writer(in_iter, out_iter) as (reader, writer):
        print(reader, writer)
        for json in reader:
            with suppress(RecursionError):
                json['text'] = templatify(parse(json['text']))
                writer.write(json)
