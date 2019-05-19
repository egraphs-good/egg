#!/usr/bin/env bash

set -ev

cargo build --all ${CI+--verbose}
cargo test --all ${CI+--verbose}
cargo clippy --all --tests
cargo doc --all ${CI+--verbose}
cargo deadlinks
cargo fmt --all -- --check
