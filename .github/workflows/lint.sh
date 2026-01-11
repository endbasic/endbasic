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

rustup component add clippy
rustup component add rustfmt

check_do_not_submit() {
    for f in .* *; do
        [ "${f}" != . ] || continue
        [ "${f}" != .. ] || continue
        [ "${f}" != .git ] || continue

        if grep -R '[D]O NOT SUBMIT' "${f}"; then
            echo "Submit blocked by" "DO" "NOT" "SUBMIT" 1>&2
            return 1
        fi
    done
}

check_cargo_toml_versions() {
    local core_version="$(grep ^version core/Cargo.toml \
        | head -n 1 | cut -d '"' -f 2)"
    for pkg in */Cargo.toml; do
        local other_version="$(grep ^version "${pkg}" \
            | head -n 1 | cut -d '"' -f 2)"
        if [ "${core_version}" != "${other_version}" ]; then
            echo "Inconsistent version number in ${pkg}" 1>&2
            return 1
        fi
    done
}

check_web_versions() {
    local web_version="$(grep ^version web/Cargo.toml \
        | head -n 1 | cut -d '"' -f 2)"
    local json_version="$(grep version web/package.json \
        | head -n 1 | cut -d '"' -f 4)"
    if [ "${web_version}" != "${json_version}" ]; then
        echo "Versions in Cargo.toml and package.json are inconsistent" 1>&2
        return 1
    fi
}

check_rust() {
    cargo clippy --all-targets -- -D warnings
    cargo clippy --all-targets --all -- -D warnings
    cargo clippy --all-targets --all-features -- -D warnings
    cargo clippy --all-targets --all-features --all -- -D warnings
    cargo fmt -- --check
}

check_do_not_submit
check_cargo_toml_versions
check_web_versions
# These checks must come last to avoid creating artifacts in the source
# directory.
check_rust
