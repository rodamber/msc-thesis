from simple.types import IO

cases = ([IO([0, 1], -1)], \
         [IO([0, 0], 0)],
         [IO([0, 0], 0), IO([1, -1], 2)],
         [IO([10**100, 10**100], 0)],
         [IO([10**100, 10**250], 10**100 - 10**250)],
         )
