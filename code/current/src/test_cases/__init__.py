from . import (add, concat, index, length, lower, newline, replace, sub,
               substr, substr_concat, substr_index, upper)


def all_test_cases():
    return concat.cases + index.cases + length.cases + replace.cases + \
        substr.cases + substr_concat.cases + substr_index.cases
