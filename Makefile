all: test nits

.PHONY: test
test:
	cargo build --release
	cargo test --release
	# don't run examples in proof-production mode
	cargo test --release --features "test-explanations"
	

.PHONY: nits
nits:
	rustup component add rustfmt clippy
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps
	cargo deadlinks

	cargo clippy --tests
	cargo clippy --tests --features "test-explanations"
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --features "reports"