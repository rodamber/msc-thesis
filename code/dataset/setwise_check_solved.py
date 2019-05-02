import os
import re


def check(fpath: str):
    with open(fpath) as f:
        lines = list(f)
        last = lines[-1]
        time_range, program = last.rstrip().split('\t', 1)
        upper_bound = time_range.split('/')[1].replace('.', ',')

        if not program.startswith('['):
            return upper_bound


p = re.compile(r'examples-(\d\d).*')


def check_dir(dpath: str):
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
