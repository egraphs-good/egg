all: test nits bench

.PHONY: test
test:
	cargo test --release
	cargo test --release --features=good_lp
	# don't run examples in proof-production mode
	EGG_TEST_EXPLANATIONS=true cargo test --lib --bins --tests --benches --release
	

.PHONY: nits
nits:
	rustup component add rustfmt clippy
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps
	cargo deadlinks

	cargo clippy --tests
	EGG_TEST_EXPLANATIONS=true cargo clippy --tests
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --features "reports"

.PHONY: bench
bench:
	cargo bench | ./scripts/filter-iai-output.py

.PHONY: bench_explanations
bench_explanations:
	EGG_TEST_EXPLANATIONS=true cargo bench | ./scripts/filter-iai-output.py