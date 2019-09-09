.PHONY:
test: test-egg test-math
	cargo fmt -- --check
	cd egg; cargo doc
	cd egg; cargo deadlinks --dir ../target/doc/egg

.PHONY: test-egg
test-egg:
	cd egg; cargo build
	cd egg; cargo test
	cd egg; cargo clippy --tests

.PHONY: test-math
test-math:
	cd egg-math; cargo clippy --tests
	cd egg-math; cargo test

.PHONY: deploy-web-demo
deploy-web-demo:
	cd web-demo; cargo web deploy --release
	rsync -az web-demo/target/deploy/ mwillsey.com:/var/www/stuff/egg/
