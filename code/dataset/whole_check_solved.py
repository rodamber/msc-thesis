import os
import re


def check(fpath: str):
    p = re.compile(r'(\d*.\d*)/(\d*.\d*)\s*=== Program')
    with open(fpath) as f:
        for line in f.readlines():
            m = re.match(p, line)
            if m:
                return m.group(2)


def check_dir(dpath: str):
    p = re.compile(r'examples-(\d\d).*')
    for f in os.listdir(dpath):
        m = p.match(f)
        if m:
            number = m.group(1)
            time = check(f'{dpath}/{f}')
            yield (number, time)


def display(dpath):
    res = list(check_dir(dpath))

    for number, time in sorted(res):
        if time:
            print(f'{number}\t{time}')
        else:
            print(f'{number}\t#N/A\t#N/A\t#N/A')

    total_solved = len(list(filter(lambda x: x[1], res)))
    print(f'Total solved: {total_solved}')
