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



math.csv:
	EGG_BENCH_CSV=math.csv cargo test --test math --release -- --nocapture --test --test-threads=1

lambda.csv:
	EGG_BENCH_CSV=lambda.csv cargo test --test lambda --release -- --nocapture --test --test-threads=1

.PHONY: existing-bench
existing-bench: math.csv lambda.csv

.PHONY: clean-bench
clean-bench:
	rm math.csv lambda.csv profile.json

.PHONY: bench
bench:
	cargo build --profile test && cargo bench

profile.json:
	cargo build --profile test && samply record cargo bench

.PHONY: profile
profile: profile.json
