#!/usr/bin/env bash
#
# This script benchmarks egg in its default mode
# (which uses the rebuilding contribution of the POPL paper),
# versus an "upward merging" mode which emulates the traditional
# method of congruence maintenance.

function fail() {
    >&2 echo $@
    exit 1
}

# these parameters ensure that all of the tests have the same
# time/node/iterations limits
export EGG_TIME_LIMIT=3000
export EGG_NODE_LIMIT=1000000
export EGG_ITER_LIMIT=100

# change to the top-level egg directory
top=$(git rev-parse --show-toplevel)
echo "Base dir: $top"
cd $top


# create the data/ directory, if not already present
mkdir -p $top/data

# now make the two data subdirectories
# - data/normal will hold the data for normal execution of egg, which uses rebuilding
# - data/upward will hold the data for the upward-merging mode of egg
normal_dir=$top/data/normal/
upward_dir=$top/data/upward/

# if these directories are already present, they must be manually deleted to proceed
mkdir $normal_dir || fail "$normal_dir is already present, please delete it (or the whole 'data' folder) to proceed"
mkdir $upward_dir || fail "$upward_dir is already present, please delete it (or the whole 'data' folder) to proceed"

# first, benchmark egg in its normal mode
export EGG_BENCH_DIR=$normal_dir
cargo test --tests --features "reports"                --release -- --test-threads=1 --nocapture


# second, benchmark egg in the upward-merging mode
export EGG_BENCH_DIR=$upward_dir
cargo test --tests --features "reports,upward-merging" --release -- --test-threads=1 --nocapture
# some tests are ignored by default with the upward-merging feature, we have to enable them here
cargo test --tests --features "reports,upward-merging" --release -- --test-threads=1 --nocapture --ignored

echo 'Normal rebuild results are stored in' $normal_dir
echo 'Upward merging results are stored in' $upward_dir
