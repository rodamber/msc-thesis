import itertools

from utils import LineError
from parser import parse


def select(infile, outfile, count, predicate):
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


def main(infile, outfile, cutoff=500, count=300, size=3):
    assert cutoff > 0 and size >= 0

    def predicate(x):
        text = x['text']
        template = parse(text).templatify()
        return len(text) < cutoff and template.size == size

    select(infile, outfile, count, predicate)


if __name__ == '__main__':
    # TODO import argparse
    import sys
    main(infile=sys.argv[1], outfile=sys.argv[2])
