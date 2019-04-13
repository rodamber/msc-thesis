from simple.types import IO

cases = ([IO(['abc'], 'abc')], \
         [IO(['ABC'], 'abc')],
         [IO(['aBc'], 'abc')],
         [IO(['aBC'], 'abc')],
         [IO(['a B C'], 'a b c')],
         )
