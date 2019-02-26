# Description of the language constructs needed for each set of expressions

## exprs-01.jsonl

No conditionals ('If' expressions). Working only with text functions.

- concat (happens basically everywhere)

The following constructs appear a lot together:

- length (even with no ifs, length comes often associated with substr)
- substr
- replace
- index (note that there are several variants, because of the optional args, but they're most often left as default)

Some interesting character constants to consider are:

- './-_@\n'

We need to consider basic arithmetic and integer constants:

-- +1, -1

This are nice, but maybe we'll leave them for later:

- tolower, toupper
- trim start, end, both


