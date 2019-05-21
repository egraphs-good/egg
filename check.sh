#!/usr/bin/env bash

set -ex

set +x
echo
echo "+-----------------------------------------------+"
echo "|                  Testing egg                  |"
echo "+-----------------------------------------------+"
echo
set -x

pushd egg
cargo build ${CI+--verbose}
cargo test ${CI+--verbose}
cargo clippy --tests
cargo doc ${CI+--verbose}
cargo deadlinks --dir ../target/doc/egg
cargo fmt -- --check
popd

set +x
echo
echo "+-----------------------------------------------+"
echo "|               Testing web-demo                |"
echo "+-----------------------------------------------+"
echo
set -x

pushd web-demo
cargo web build
# cargo web test ${CI+--verbose}
cargo clippy
cargo fmt -- --check
popd
