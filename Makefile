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
bench: bench-run bench-compare

.PHONY: bench-run
bench-run:
	./scripts/benchmark.py scripts/data/current.csv

.PHONY: bench-compare
bench-compare:
	./scripts/compare.py scripts/data/baseline.csv scripts/data/current.csv | tee scripts/data/compare.out

.PHONY: bench-accept
bench-accept:
	cp ./scripts/data/current.csv ./scripts/data/baseline.csv
