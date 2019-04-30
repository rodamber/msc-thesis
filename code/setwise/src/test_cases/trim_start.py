from simple.types import IO

cases = (
    [IO([' abc'], 'abc')],
    [IO(['  abc'], 'abc')],
    [IO(['abc  '], 'abc  ')],
    [IO(['\tabc\t \n'], 'abc\t \n')],
    [IO(['   a b c   '], 'a b c   ')],
)
