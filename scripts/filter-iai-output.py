#!/usr/bin/env python3

import fileinput
import re
import statistics

BENCH_NAME = re.compile(r'(\w+)')
EST_CYCLES = re.compile(r' +Estimated Cycles: +(\d+) +\((.*)\)')

name = ''
printed_headers = False
ratios = []

for line in fileinput.input():
    if match := BENCH_NAME.match(line):
        name = match[1]
    if match := EST_CYCLES.match(line):
        if not printed_headers:
            printed_headers = True
            print(f'{"name":25} {"cycles":>10} {"diff":>10}')
        print(f'{name:25} {match[1]:>10} {match[2]:>10}')

        try:
            pct = float(match[2].rstrip('%'))
            ratios.append(1.0 + pct / 100.0)
        except ValueError:
            ratios.append(1.0)

if ratios:
    mean_ratio = statistics.harmonic_mean(ratios)
    pct = (mean_ratio - 1) * 100.0
    print(f'{pct:>+46.6f}% mean')
