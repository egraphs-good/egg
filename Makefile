.PHONY:
test: test-egg
	cargo fmt -- --check
	cargo clean --doc
	cargo doc --no-deps
	cargo deadlinks

.PHONY: test-egg
test-egg:
	cargo build
	cargo test --release
	cargo test --release --features "upward-merging"

	cargo clippy --tests
	cargo clippy --tests --features "serde-1"
	cargo clippy --tests --features "reports"

.PHONY: deploy-nightlies
deploy-nightlies:
	rsync -ri --exclude=".*" scripts/nightly-static/ ~/public/egg-nightlies/

.PHONY: nightly
nightly:
	bash scripts/run-nightly.sh

# makefile hack to run my hacky benchmarks
bench:
	cargo test --features "reports" --release -- --test-threads=1 --nocapture
bench-%:
	cargo test --features "reports" --release -- --test-threads=1 --nocapture $*
