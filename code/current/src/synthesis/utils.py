from collections import deque
from dataclasses import dataclass
from itertools import count


@dataclass
class LineError(Exception):
    line: int


fresh_gen = lambda: (f'x{i}' for i in count())
