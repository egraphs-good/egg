#!/usr/bin/env python3

import json
import glob
import numpy as np
import matplotlib
import matplotlib.pyplot as plt
import sys

from scipy.stats import linregress
from scipy.stats.mstats import spearmanr

matplotlib.rcParams.update({"font.size": 14})

def load(globbed):
    data = {}
    for filename in glob.glob(globbed):
        with open(filename) as f:
            # print('Loading {}...'.format(filename))
            j = json.load(f)
            data[j['name']] = j['data']
    return data

normal = load('data/normal/*.json')
upward = load('data/upward/*.json')
print('Loaded data!')

# assert list(normal.keys()) == list(upward.keys())
names = list(normal.keys())

# check out the data
for name in names:
    normal_iters = normal[name]
    upward_iters = upward[name]
    if len(normal_iters) != len(upward_iters):
        # print("difference: {} {} != {}".format(name, len(normal_iters), len(upward_iters)))
        pass

# extractors

def congr(point):
    return point['apply_time'] + point['rebuild_time']

def applied(point):
    return sum(point['applied'].values())

def total(point):
    return point['total_time']

def n_rebuilds(point):
    return point['n_rebuilds']

def sum_iters(func, dataset):
    return sum(func(p) for p in dataset)

def sub_sum_iters(func, dataset1, dataset2):
    return sum_iters(func, dataset1) - sum_iters(func, dataset2)

def div_sum_iters(func, dataset1, dataset2):
    return sum_iters(func, dataset1) / sum_iters(func, dataset2)

# plotting functions

def plot_times(filename=None, log=True):
    plt.clf()

    if log:
        plt.title("Congruence time (sec) - log scale")
        plt.xscale("log")
        plt.yscale("log")
    else:
        plt.title("Congruence time (sec) - linear scale")

    x = [sum_iters(congr, upward[name]) for name in names]
    y = [sum_iters(congr, normal[name]) for name in names]
    plt.scatter(x, y, alpha=0.7, edgecolor='black')

    add_xy_line()
    plt.xlabel("Rebuilding every merge")
    plt.ylabel("Rebuilding once per iteration")

    if filename:
        plt.tight_layout()
        plt.savefig(filename)
    else:
        plt.show()


def plot_iters(filename=None):
    plt.clf()
    def plot_name(name):
        x, y = [], []
        length = max(len(upward[name]), len(normal[name]))
        for i in range(length):
            ui, ni = upward[name][:i + 1], normal[name][:i + 1]
            x.append(sum_iters(applied, ni))
            y.append(div_sum_iters(congr, ui, ni))

        marker = 'o' # if normal[name][-1]['stop_reason'] == 'Saturated' else '^'
        plt.plot(x, y, alpha = 0.3)
        plt.scatter(
            x[-1], y[-1],
            marker = marker,
            edgecolor = 'black',
            zorder = 100,
        )

    for name in names:
        plot_name(name)

    plt.axhline(1, color='gray')
    plt.xscale("log")
    plt.yscale("log")
    plt.gca().yaxis.set_major_formatter(matplotlib.ticker.StrMethodFormatter('{x:g}×'))
    plt.yticks([0.3, 1, 3, 10, 30, 100, 300])

    plt.xlabel("Rewrites applied so far")
    plt.ylabel("Speedup (log scale)")

    if filename:
        plt.tight_layout()
        plt.savefig(filename)
    else:
        plt.show()

def plot_repairs(filename=None):
    plt.clf()

    plt.xscale("log")
    plt.yscale("log")

    xx = []
    yy = []
    sets = [
        (upward, "Rebuilding every merge"),
        (normal, "Rebuilding once per iteration"),
    ]
    for (dataset, label) in sets:
        x = [sum_iters(n_rebuilds, dataset[name]) for name in names]
        y = [sum_iters(congr, dataset[name]) for name in names]
        xx += x
        yy += y
        plt.scatter(x, y, alpha=0.7, edgecolor='black', label=label)

    # m, b, r, p, err = linregress(xx, yy)
    # print(m, b, r, p, err)
    # x = np.logspace(0, 6, 50)
    # plt.plot(x, m*x + b)

    spearman = spearmanr(xx, yy)
    print('Fig 7: spearman r =', spearman)

    # add_xy_line()
    plt.xlabel("Number of calls to repair")
    plt.ylabel("Time spent in congruence (sec)")

    plt.legend()

    if filename:
        plt.tight_layout()
        plt.savefig(filename)
    else:
        plt.show()

    return spearman


def add_xy_line():
    lims = [
        np.min([plt.xlim(), plt.ylim()]),  # min of both axes
        np.max([plt.xlim(), plt.ylim()]),  # max of both axes
    ]
    # now plot both limits against eachother
    plt.plot(lims, lims, 'k-', alpha=0.75, zorder=0)
    # ax.set_aspect('equal')
    plt.xlim(lims)
    plt.ylim(lims)


plot_times(filename='data/fig5a-speedup.pdf', log=False)
plot_times(filename='data/fig5b-speedup-log.pdf', log=True)
plot_iters(filename='data/fig6-speedup-iter.pdf')
corr = plot_repairs(filename='data/fig7-repairs.pdf')

def geomean(iterable):
    a = np.array(iterable)
    return a.prod() ** (1.0 / len(a))

def calculate_speedup(extractor):
    u = [sum_iters(extractor, upward[name]) for name in names]
    n = [sum_iters(extractor, normal[name]) for name in names]
    return sum(u) / sum(n)

congrup = calculate_speedup(congr)
print("Fig 5: Congruence speedup (geo mean)", congrup)
totalup = calculate_speedup(total)
print("Fig 5: Overall speedup (geo mean)", totalup)

n_tests = len(normal)
n_timeouts = len([t for t in normal.values() if len(t) >= 100])
# print('timeouts / tests', n_timeouts, n_tests)

with open("data/speedup-data.tex", "w") as f:
    f.write(
        "\\newcommand{\\CongrSpeedup}{\\ensuremath{%.2f\\times}\\xspace}\n"
        % congrup
    )
    f.write(
        "\\newcommand{\\TotalSpeedup}{\\ensuremath{%.2f\\times}\\xspace}\n"
        % totalup
    )
    f.write(
        "\\newcommand{\\RepairsR}{\\ensuremath{%.2f}\\xspace}\n"
        % corr.correlation
    )
    f.write(
        "\\newcommand{\\RepairsP}{%.2g\\xspace}\n"
        % corr.pvalue
    )
    f.write("\\newcommand{\\nEggTests}{%d\\xspace}\n" % n_tests)
    f.write("\\newcommand{\\nEggTimeouts}{%d\\xspace}\n" % n_timeouts)
