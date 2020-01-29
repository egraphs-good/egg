.PHONY:
test: test-egg test-math test-web
	cargo fmt -- --check
	cargo doc --no-deps
	cargo deadlinks

.PHONY: test-egg
test-egg:
	cargo build
	cargo test
	cargo clippy --tests

	cargo build          --features "parent-pointers"
	cargo test           --features "parent-pointers"
	cargo clippy --tests --features "parent-pointers"

	cargo clippy --tests --features "serde-1"

.PHONY: test-math
test-math:
	cd egg-math; cargo clippy --tests --features "parent-pointers"
	cd egg-math; cargo test	          --features "parent-pointers"

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
