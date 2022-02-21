#!/bin/bash

rm -rf herbie
git clone git@github.com:uwplse/herbie

cd herbie
git checkout generate-proof-tests
make install
bash infra/generate-proof-examples.sh
cd ..

REPORTDIR=proof_report

if [ -d "$REPORTDIR" ]; then
    rm -r "$REPORTDIR"
fi

mkdir "$REPORTDIR"

cargo test herbie_benchmark --release --features reports -- --nocapture


racket eval-results.rkt "$REPORTDIR/herbie-bench-results.txt" "$REPORTDIR"
# racket eval-results.rkt "$REPORTDIR/herbie-bench-results.txt" "../egg-papers/2021-explanations/proof_report"
