all: test nits bench

.PHONY: test
test:
	cargo build --release
	cargo test --release
	cargo test --release --features "upward-merging"

.PHONY: nits
nits:
	rustup component add rustfmt --toolchain `cat rust-toolchain`
	rustup component add clippy --toolchain `cat rust-toolchain`
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps
	cargo deadlinks

	cargo clippy --tests
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --features "reports"


.PHONY: bench
bench: bench-run bench-compare

.PHONY: bench-run
bench-run:
	rustup target add x86_64-unknown-linux-musl
	./scripts/benchmark.py scripts/data/current.csv

.PHONY: bench-compare
bench-compare:
	./scripts/compare.py scripts/data/baseline.csv scripts/data/current.csv

.PHONY: bench-accept
bench-accept:
	cp ./scripts/data/current.csv ./scripts/data/baseline.csv
