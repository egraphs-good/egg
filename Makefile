all: test nits

.PHONY: test
test:
	cargo test --release
	cargo test --release --features=lp
	# don't run examples in proof-production mode
	cargo test --release --features "test-explanations"
	

.PHONY: nits
nits:
	rustup component add rustfmt clippy
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps --all-features
	cargo deadlinks

	cargo clippy --tests
	cargo clippy --tests --features "test-explanations"
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --all-features

.PHONY: docs
docs:
	RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features --open