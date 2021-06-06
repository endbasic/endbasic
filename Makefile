# EndBASIC
# Copyright 2021 Julio Merino
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not
# use this file except in compliance with the License.  You may obtain a copy
# of the License at:
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
# License for the specific language governing permissions and limitations
# under the License.

sinclude config.mk

.PHONY: default
default:
	@echo "Must specify the 'test' target" 1>&2
	@false

# TODO(jmmv): Replace this target, and likely this file as well, once support
# for environment variables is in stable Cargo and we can have these stored
# in .cargo/config.toml.  See https://github.com/rust-lang/cargo/pull/9175.
.PHONY: test
test:
	@RUST_BACKTRACE=1 \
	    TEST_ACCOUNT_1_USERNAME="$(TEST_ACCOUNT_1_USERNAME)" \
	    TEST_ACCOUNT_1_PASSWORD="$(TEST_ACCOUNT_1_PASSWORD)" \
	    TEST_ACCOUNT_2_USERNAME="$(TEST_ACCOUNT_2_USERNAME)" \
	    TEST_ACCOUNT_2_PASSWORD="$(TEST_ACCOUNT_2_PASSWORD)" \
	    cargo test $(TEST_ARGS) -- --include-ignored
