from dataclasses import dataclass


@dataclass
class LineError(Exception):
    line: int
