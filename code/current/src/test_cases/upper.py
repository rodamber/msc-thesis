from simple.types import IO

cases = ( \
    [IO(['abc'], 'ABC')], \
    [IO(['ABC'], 'ABC')],
    [IO(['aBc'], 'ABC')],
    [IO(['aBC'], 'ABC')],
    [IO(['a B C'], 'A B C')],
)
