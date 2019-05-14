#!/usr/bin/env bash

set -ev

cargo build ${CI+--verbose}
cargo test ${CI+--verbose}
cargo doc ${CI+--verbose}
cargo deadlinks
cargo fmt -- --check

