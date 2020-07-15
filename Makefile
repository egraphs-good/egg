.PHONY:
test: test-egg test-web
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


.PHONY: test-web
test-web:
	cd web-demo; cargo web build
	 # cargo web test ${CI+--verbose}
	cd web-demo; cargo clippy
	cd web-demo; cargo fmt -- --check

.PHONY: deploy-web-demo
deploy-web-demo:
	cd web-demo; cargo web deploy --release
	rsync -a target/deploy/ ~/src/site/stuff/egg/
	cd ~/src/site; make deploy

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
