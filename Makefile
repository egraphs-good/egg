.PHONY:
test: test-egg test-math test-web
	cargo fmt -- --check
	cd egg; cargo doc --no-deps
	cd egg; cargo deadlinks --dir ../target/doc/egg

.PHONY: test-egg
test-egg:
	cd egg; cargo build
	cd egg; cargo test
	cd egg; cargo clippy --tests

	cd egg; cargo build          --features "parent-pointers"
	cd egg; cargo test           --features "parent-pointers"
	cd egg; cargo clippy --tests --features "parent-pointers"

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
	rsync -az target/deploy/ mwillsey.com:/var/www/stuff/egg/
