#!/usr/bin/env bash

set -ev

cargo build ${CI+--verbose}
cargo test ${CI+--verbose}
cargo clippy --tests
cargo doc ${CI+--verbose}
cargo deadlinks
cargo fmt -- --check
