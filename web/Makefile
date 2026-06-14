# EndBASIC
# Copyright 2026 Julio Merino
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

# EndBASIC Service endpoint to connect to.
#
# Can be one of `prod`, `staging`, or `local`.  Refer to `package.json` for the
# authoritative list.
NODE_ENV = prod

# Launcher for webpack with the correct configuration.
WEBPACK = env NODE_ENV="$(NODE_ENV)" ./node_modules/.bin/webpack

node_modules/.stamp: package.json package-lock.json
	@if test "$${CI:-unset}" = unset; then \
	    echo "npm install"; \
	    npm install; \
    else \
	    echo "npm ci --verbose"; \
	    npm ci --verbose; \
	fi
	touch $@

.PHONY: build-debug
build-debug: node_modules/.stamp
	cargo build --target wasm32-unknown-unknown
	wasm-bindgen --target bundler --out-dir pkg --out-name index \
	    ../target/wasm32-unknown-unknown/debug/endbasic_web.wasm
	$(WEBPACK) --mode=development

.PHONY: build-release
build-release: node_modules/.stamp
	cargo build --target wasm32-unknown-unknown --release
	wasm-bindgen --target bundler --out-dir pkg --out-name index \
	    ../target/wasm32-unknown-unknown/release/endbasic_web.wasm
	wasm-opt -O3 -o pkg/index_bg.wasm pkg/index_bg.wasm
	$(WEBPACK) --mode=production

.PHONY: start-debug
start-debug: build-debug
	$(WEBPACK) serve --mode=development

.PHONY: start-release
start-release: build-release
	$(WEBPACK) serve --mode=production

.PHONY: test
test: node_modules/.stamp
	cargo test
	env \
	    GECKODRIVER=./node_modules/.bin/geckodriver \
	    CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUNNER=wasm-bindgen-test-runner \
	    cargo test --target wasm32-unknown-unknown

.PHONY: clean
clean:
	rm -rf dist pkg
