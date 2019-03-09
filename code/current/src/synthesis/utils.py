from dataclasses import dataclass
from collections import deque
from itertools import count


@dataclass
class LineError(Exception):
    line: int


# Obtain the number of elements of an iterator. This exhausts the iterator.
# https://stackoverflow.com/a/34404546/3854518
def ilen(it):
    # Make a stateful counting iterator
    cnt = count()

    # zip it with the input iterator, then drain until input exhausted at C level
    # cnt must be second zip arg to avoid advancing too far
    deque(zip(it, cnt), 0)

    # Since count 0 based, the next value is the count
    return next(cnt)


def fresh():
    for i in count():
        x = f'x{i}'
        yield x
