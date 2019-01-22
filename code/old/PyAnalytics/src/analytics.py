import collections
import itertools

import outsystems

expressions = list(outsystems.expressions())


def how_many_funs(lower=0, upper=14, examples=False):
    cnt = collections.Counter()

    for e in expressions:
        if all(x in outsystems.builtin_funs for x in e.funs) \
           and e.type in outsystems.builtin_types:
            cnt[len(e.funs)] += 1

    def at_least(n):
        return sum(cnt[x] for x in range(n, upper + 1))

    for i in range(lower, upper + 1):
        fmt = 'There are {} expressions that use {} or more functions.'
        print(fmt.format(at_least(i), i))


def top(f):
    cnt = collections.Counter()

    for e in expressions:
        f(e, cnt)

    return cnt


def print_top(gen_top):
    for i, (x, c) in zip(itertools.count(start=1), gen_top):
        print('{}.\t{}: {}'.format(i, x, c))


def f(e, cnt):
    for fun in e.funs:
        if fun in outsystems.builtin_funs:
            cnt.update([fun])
