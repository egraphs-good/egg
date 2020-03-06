#!/usr/bin/env python3

import subprocess
import datetime
import shlex
import json
import os
import fcntl


def run(cmd, **kwargs):
    args = shlex.split(cmd)
    return subprocess.run(
        args, text=True, check=True, stdout=subprocess.PIPE, **kwargs
    ).stdout.strip()


def get_suites():
    suites = [f.rstrip(".rs") for f in os.listdir("tests/")]
    print("Found test suites", suites)
    return {s: [] for s in suites}


def sizeof_fmt(num, suffix="B"):
    for unit in ["", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi"]:
        if abs(num) < 1024.0:
            return "%3.1f%s%s" % (num, unit, suffix)
        num /= 1024.0
    return "%.1f%s%s" % (num, "Yi", suffix)


def mk_prelude(base_dir, now):
    data = {
        "date": now.isoformat(),
        "branch": run("git rev-parse --abbrev-ref HEAD"),
        "rev": run("git rev-parse HEAD"),
        "describe": run("git describe"),
        "suites": get_suites(),
        "dirty": {
            line[3:]: line[:2]
            for line in run(
                "git status --porcelain=v1 --untracked-files=no"
            ).splitlines()
        },
    }

    fname_date = data["date"].replace(":", "-").replace(".", "-")
    dirty_suffix = "-dirty" if data["dirty"] else ""
    fname = "{}_{rev}{}".format(fname_date, dirty_suffix, **data)
    data["directory"] = os.path.join(base_dir, fname)

    return data


if __name__ == "__main__":

    import argparse

    parser = argparse.ArgumentParser(description="Run the egg nightlies")
    parser.add_argument(
        "--base-dir",
        required=True,
        help="The base directory with all the nightly data",
    )
    args = parser.parse_args()

    now = datetime.datetime.now()
    data = mk_prelude(args.base_dir, now)
    run_dir = data["directory"]

    print(json.dumps(data, indent=2))

    os.mkdir(run_dir)
    env = os.environ.copy()
    env["EGG_BENCH"] = "1"

    for suite, result_files in data['suites'].items():
        suite_dir = os.path.join(run_dir, suite)
        os.mkdir(suite_dir)
        env["EGG_BENCH_DIR"] = suite_dir
        print("Running test suite", suite)
        run("cargo test --features 'reports' --release --test {} -- --nocapture".format(suite), env=env)
        # run("cargo test --features 'reports' --release --test {} -- --test-threads=1 --nocapture".format(suite), env=env)
        result_files.extend(os.listdir(suite_dir))

    total_data_size = sum(
        os.path.getsize(os.path.join(run_dir, suite, f))
        for suite, result_files in data["suites"].items()
        for f in result_files
    )
    data["total_data_size"] = total_data_size

    print(json.dumps(data, indent=2))

    index_file = os.path.join(args.base_dir, "index.json")

    try:
        with open(index_file, "x") as f:
            print("index.json did not exist, creating...")
            j = [data]
            json.dump(j, f, indent=2)
    except OSError:
        with open(index_file, "r+") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            j = json.load(f)
            print(
                "found an index.json with {} entries, going to append...".format(len(j))
            )
            j.append(data)

            f.seek(0)
            json.dump(j, f, indent=2)
            f.truncate()

    total_total = sizeof_fmt(sum(d["total_data_size"] for d in j))
    print("There are now {} entries with total size: {}".format(len(j), total_total))
