#! /bin/sh
# EndBASIC
# Copyright 2020 Julio Merino
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

set -eux

# Runs code sanity checks.
do_lint() {
    cargo clippy --all-features --all-targets -- -D warnings
    cargo fmt -- --check
}

# Ensures that the package is ready for publication, which also ensures it
# builds in release mode.
do_package() {
    cargo publish --dry-run
}

# Builds and runs all binaries and tests in release mode.
do_release() {
    cargo test --all-features --verbose --release
}

# Builds and runs all binaries and tests in dev mode.
do_test() {
    cargo test --all-features --verbose
}

if [ "${DO-unset}" = unset ]; then
    echo "DO must be set in the environment" 1>&2
    exit 1
fi
case "${DO}" in
    lint|package|release|test)
        "do_${DO}"
        ;;

    *)
        echo "Unknown DO value" 1>&2
        exit 1
        ;;
esac
