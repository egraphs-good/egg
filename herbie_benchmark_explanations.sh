#!/bin/bash

rm -rf herbie
git clone git@github.com:uwplse/herbie

cd herbie
git checkout generate-proof-tests
make install
bash infra/generate-proof-examples.sh
cd ..

cargo test herbie_benchmark --release --features reports -- --nocapture

