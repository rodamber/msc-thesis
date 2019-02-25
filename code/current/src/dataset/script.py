import collections
import jsonlines
import outsystems

allowed = set(['Concat', 'Lenght', 'Substr', 'Replace', 'Index'])


def write_():
    with jsonlines.open('../../dataset/exprs-01.jsonl') as reader:
        with jsonlines.open(
                '../../dataset/exprs-01-tmp.jsonl', mode='w') as writer:
            for obj in reader:
                if set(obj['functions']) <= allowed:
                    writer.write(obj)


def print_():
    with jsonlines.open('../../dataset/exprs-3-6.jsonl') as reader:
        for obj in reader:
            if set(obj['functions']) <= allowed:
                print(obj)
