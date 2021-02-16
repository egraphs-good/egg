#!/usr/bin/env python3

import sys
import csv
from pathlib import Path

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def compute_cycles(args, d):
    ram = int(d["DLmr"]) + int(d["DLmw"]) + int(d["ILmr"])
    l3 = int(d["I1mr"]) + int(d["D1mw"]) + int(d["D1mr"]) - ram
    total = int(d["Ir"]) + int(d["Dr"]) + int(d["Dw"])
    l1 = total - l3 - ram
    assert total == l1 + l3 + ram
    return l1 * args.l1_hit + l3 * args.l3_hit + ram * args.ram_hit

def compare(args):
    baseline = {d['name']: d for d in csv.DictReader(args.baseline)}
    to_compare = {d['name']: d for d in csv.DictReader(args.to_compare)}

    names = set(baseline.keys()) | set(to_compare.keys())

    failures = []

    table = [['name', 'cycles 1', 'cycles 2', 'ratio', 'report']]
    for name in sorted(list(names)):
        row = [name]

        cycles1 = compute_cycles(args, baseline[name]) if name in baseline else '-'
        cycles2 = compute_cycles(args, to_compare[name]) if name in to_compare else '-'

        row.append(str(cycles1))
        row.append(str(cycles2))

        if type(cycles1) is int and type(cycles2) is int:
            delta = float(cycles2) / cycles1
            row.append(f'{delta:.3f}')
            if delta < args.low_threshold:
                failures.append(name)
                row.append(f'< {args.low_threshold:.3f}')
            elif delta > args.high_threshold:
                failures.append(name)
                row.append(f'> {args.high_threshold:.3f}')
            else:
                row.append('~')
        else:
            row.append('-')
            row.append('-')

        table.append(row)

    eprint(f'Thresholds are {args.low_threshold} and {args.high_threshold}')
    print_table(table, args.delimiter)

    if failures:
        eprint(f'\nFailed! {len(failures)} benchmarks are outside thresholds of {args.low_threshold} and {args.high_threshold}.')
        exit(1)

def print_table(table, delimiter):
    widths = [max(len(x) for x in col) for col in zip(*table)]
    for row in table:
        print("{:{}}".format(row[0] + delimiter, widths[0] + len(delimiter)), end='  ')
        sep = delimiter + "  "
        print(sep.join("{:>{}}".format(x, w)
                       for w, x in zip(widths[1:], row[1:])))

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Compare two benchmarks.')
    parser.add_argument('baseline', type=argparse.FileType('r'))
    parser.add_argument('to_compare', type=argparse.FileType('r'))
    parser.add_argument('--l1-hit', type=int, default = 1, help = 'cost in cycles')
    parser.add_argument('--l3-hit', type=int, default = 5, help = 'cost in cycles')
    parser.add_argument('--ram-hit', type=int, default = 35, help = 'cost in cycles')
    parser.add_argument('--low-threshold', type=float, default=.97)
    parser.add_argument('--high-threshold', type=float, default=1.03)
    parser.add_argument('--delimiter', type=str, default=' ')
    args = parser.parse_args()
    compare(args)
