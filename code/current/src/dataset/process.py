import itertools

import jsonlines

import expr_ast as ast
from parser import parse
from templatify import templatify
from utils import LineError


def select(infile, outfile, predicate, count=None):
    '''
    Selects at most count expressions from infile that satisfy predicate, and
    writes them to outfile.
    '''
    import jsonlines

    def json():
        with jsonlines.open(infile, 'r') as reader:
            for line, elem in enumerate(reader, 1):
                try:
                    if predicate(elem):
                        yield elem
                except Exception as e:
                    raise LineError(line) from e

    with jsonlines.open(outfile, 'w') as writer:
        writer.write_all(itertools.islice(json(), count))


def templates(infile, outfile, count=None):
    with jsonlines.open(infile) as reader:
        with open(outfile, 'w') as f:
            for x in itertools.islice(reader, count):
                template = templatify(parse(x['text']))
                f.write(f'{template}\n')


# Main


def short_pred(cutoff=300):
    return lambda x: len(x['text']) < cutoff


# FIXME XXX
# Doesn't support '+' for concatenation yet
def in_dsl(dsl):
    def iter_(e):
        from anytree import LevelOrderIter
        return (node.name for node in LevelOrderIter(e.to_anytree()))

    def pred(x):
        if x['functions'] and (set(x['functions']) <= set(dsl)):
            template = templatify(parse(x['text']))

            # Filter unwanted operations

            no_binops = not any(
                isinstance(x, ast.Binop) for x in iter_(template))
            if no_binops:
                no_unops = not any(
                    isinstance(x, ast.Unop) for x in iter_(template))
                return no_unops
        return False

    return pred


def ast_size(size):
    return lambda x: templatify(parse(x['text'])).size() == size
