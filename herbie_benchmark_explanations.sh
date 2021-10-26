#!/bin/bash

cd herbie
git checkout generate-proof-examples
bash infra/generate_proof_examples.sh
cd ..

cargo test herbie_benchmark --features reports -- --nocapture

