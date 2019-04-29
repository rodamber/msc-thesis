import json

from simple.types import IO
from typing import List, Dict, Union


def read_examples_from_file(filename: str) -> List[IO]:
    with open(filename) as file:
        jobj = json.load(file)
        examples = list(read_one_example(ex) for ex in jobj["examples"])
        return examples


def read_one_example(ex: Dict[str, Dict[str, str]]) -> IO:
    inputs = tuple(read_value(val) for val in ex["inputs"])
    output = read_value(ex["output"])
    return IO(inputs, output)


def read_value(val: Dict[str, str]) -> Union[str, int]:
    if "Left" in val:
        return val["Left"]
    elif "Right" in val:
        return int(val["Right"])
    else:
        return ValueError(str(val))
