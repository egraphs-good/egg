all: test nits bench

.PHONY: test
test:
	cargo build --release
	cargo test --release
	cargo test --release --features "upward-merging"

.PHONY: nits
nits:
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps
	cargo deadlinks

	cargo clippy --tests
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --features "reports"

.PHONY: bench
bench:
	cargo bench | ./scripts/filter-iai-output.py
