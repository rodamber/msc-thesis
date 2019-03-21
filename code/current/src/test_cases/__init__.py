from . import (concat, index, length, replace, substr, substr_concat,
               substr_index)

# from .. import synthesis


def all_test_cases():
    return concat.cases + index.cases + length.cases + replace.cases + \
        substr.cases + substr_concat.cases + substr_index.cases
