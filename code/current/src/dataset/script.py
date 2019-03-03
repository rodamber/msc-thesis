import jsonlines
import sys

import parser

dataset = '../../dataset/exprs.jsonl'


def write():
    with jsonlines.open(dataset) as reader:
        outfile = '../../dataset/exprs-small.jsonl'
        fp = open(outfile, 'w')
        writer = jsonlines.Writer(fp)

        try:
            for line, obj in enumerate(reader, 1):
                if line % 500 == 0:
                    print(line)

                parser.parse(obj['text'])
                writer.write(obj)
        except Exception as err:
            print(
                f"Unexpected {type(err).__name__} (line {line}): {obj['text']}",
                file=sys.stderr)
        finally:
            writer.close()
            fp.close()


def read_line(n):
    with jsonlines.open(dataset) as reader:
        for line, obj in enumerate(reader, 1):
            if line == n:
                return obj['text']
