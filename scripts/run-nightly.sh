#!/usr/bin/env bash

function run() {
    echo $@
    $@
}

data_dir="$HOME/public/egg-nightlies/data"
test_dir="tests/"

rev=$(git describe --long --dirty --abbrev=1000)
if [[ "$rev" == *-dirty ]]; then
    # if we are dirty, use the current time
    now=$(date --iso-8601=seconds)
else
    # if clean, use the commit time
    now=$(git log -1 --format=%cI)
fi


# get the branch either from an environment variable or git
# and replace silly characters
branch=${NIGHTLY_BRANCH:-$(git rev-parse --abbrev-ref HEAD)}
branch=$(echo -n "$branch" | tr -c "[:alnum:]-_" "@")

run_dir="${data_dir}/${now}___${branch}___${rev}"

echo "Running nightly into ${run_dir}"
if [ -d "$run_dir" ]; then
    echo "Already exists: $run_dir"
    exit 0
else
    mkdir "$run_dir"
fi

suites=$(ls $test_dir)
echo -e "Found test suites in ${test_dir}\n${suites}"

EGG_BENCH=${EGG_BENCH:-10}
export EGG_BENCH

for suite in $suites; do
    suite=${suite/%.rs/}
    test_dir="$run_dir/$suite/"
    mkdir $test_dir
    cmd="cargo test --features reports --no-fail-fast --release \
         --test ${suite} -- --test-threads=1"
    EGG_BENCH_DIR=$test_dir run $cmd
done
