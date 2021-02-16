#!/usr/bin/env python3

from pathlib import Path

import csv
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time

import multiprocessing.pool
pool = multiprocessing.pool.ThreadPool()

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def run(cmd):
    eprint(cmd)
    return subprocess.check_output(shlex.split(cmd), stderr=subprocess.STDOUT, text=True)

def gettime(tup):
    (tempdir, suite, binary, test) = tup
    start = time.monotonic()
    run(f'{binary} {test}')
    return time.monotonic() - start

def valgrind(tup):
    # inspired by https://github.com/pythonspeed/cachegrind-benchmarking/
    (tempdir, suite, binary, test) = tup
    outfile = f'{tempdir}/{suite}::{test}.out'
    valgrind = ' '.join([
        'setarch x86_64 --addr-no-randomize',
        'valgrind --tool=cachegrind',
        # haswell
        f'--I1={32 * 1<<10},8,64',
        f'--D1={32 * 1<<10},8,64',
        f'--LL={ 8 * 1<<20},16,64',
    ])
    run(f'{valgrind} --cachegrind-out-file={outfile} {binary} {test}')

    data = {'name': f'{suite}::{test}'}
    data.update(read_cachegrind(outfile))
    return data

def read_cachegrind(filename):
    s = Path(filename).read_text()
    events = re.search(r'events: (.*)', s)[1].strip().split()
    summary = re.search(r'summary: (.*)', s)[1].strip().split()
    return dict(zip(events, map(int, summary)))

def bench(args):
    start = time.monotonic()
    tuples = []
    tempdir = tempfile.mkdtemp(prefix='egg-bench-')

    os.environ['EGG_TIME_LIMIT'] = str(60 * 5)

    for suite in args.suites:
        cargolist = run('cargo test --target=x86_64-unknown-linux-musl'
                        f' --test {suite} --release -- --list')
        binary = re.search(r'Running (target/.*)', cargolist)[1]
        tests = re.findall(r'(.*): .*', cargolist)
        for test in tests:
            if 'fail' not in test:
                tuples.append((tempdir, suite, binary, test))

    # times_table = [pool.map(gettime, tuples) for i in range(args.n)]
    # times_min = list(map(min, zip(*times_table)))

    results = pool.map(valgrind, tuples)
    results.sort(key=lambda d: d['name'])

    w = csv.DictWriter(args.outfile, results[0].keys(), lineterminator='\n')
    w.writeheader()
    w.writerows(results)

    duration = time.monotonic() - start
    eprint(f'Ran {len(results)} benchmarks in {duration} seconds')

SUITES = ['math', 'lambda', 'prop']

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Benchmark with cachegrind.')
    parser.add_argument('outfile', type=argparse.FileType('w'))
    parser.add_argument('suites', type=str, nargs = '*')
    args = parser.parse_args()
    if not args.suites:
        fromenv = [s for s in os.environ.get('SUITES', '').split(',') if s]
        args.suites = fromenv or SUITES

    bench(args)
