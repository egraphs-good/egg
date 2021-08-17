all: test nits bench

.PHONY: test
test:
	cargo build --release
	cargo test --release
	# don't run examples in proof-production mode
	cargo test --lib --bins --tests --benches --release --features "explanation-generation"

.PHONY: nits
nits:
	rustup component add rustfmt clippy
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps
	cargo deadlinks

	cargo clippy --tests
	cargo clippy --tests --features "explanation-generation"
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --features "reports"

.PHONY: bench
bench:
	cargo bench | ./scripts/filter-iai-output.py
