#!/usr/bin/env bash

# export EGG_TIME_LIMIT=3000
# export EGG_NODE_LIMIT=1000000
# export EGG_ITER_LIMIT=100

function fail() {
    >&2 echo $@
    exit 1
}

top=$(git rev-parse --show-toplevel)

echo "Base dir: $top"
cd $top

mkdir -p $top/data

normal_dir=$top/data/normal/
upward_dir=$top/data/upward/

mkdir $normal_dir || fail "$normal_dir is already present, please delete it (or the whole 'data' folder) to proceed"
mkdir $upward_dir || fail "$upward_dir is already present, please delete it (or the whole 'data' folder) to proceed"

export EGG_BENCH_DIR=$normal_dir
cargo test --tests --features "reports"                --release -- --test-threads=1 --nocapture
export EGG_BENCH_DIR=$upward_dir
cargo test --tests --features "reports,upward-merging" --release -- --test-threads=1 --nocapture
# some tests are ignored by default with the upward-merging feature, we have to enable them here
cargo test --tests --features "reports,upward-merging" --release -- --test-threads=1 --nocapture --ignored

echo 'Normal rebuild results are stored in' $normal_dir
echo 'Upward merging results are stored in' $upward_dir
