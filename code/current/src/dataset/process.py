import jsonlines
import parser


def select_long_expressions(infile, outfile, cutoff):
    '''
    Selects each expression from infile whose text length is less than cutoff,
    and writes them to outfile.
    '''
    with jsonlines.open(infile, 'r') as reader:
        with jsonlines.open(outfile, 'w') as writer:
            for obj in reader:
                if len(obj['text']) < cutoff:
                    writer.write(obj)


def select_random(infile, outfile, p):
    '''
    Selects each expression from infile with probability p, and writes them to
    outfile.
    '''
    assert 0 <= p <= 1
    from random import random

    with jsonlines.open(infile, 'r') as reader:
        with jsonlines.open(outfile, 'w') as writer:
            for obj in reader:
                if random() <= p:
                    writer.write(obj)
