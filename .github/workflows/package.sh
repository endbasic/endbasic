#! /bin/sh
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

# Verify that "cargo publish" has good chances of succeeding for all of our crates.
#
# This is very hard to do and is not well-documented, so to avoid pulling in very
# heavy dependencies, this tries to simulate the above by "just" packaging the
# crates (a la "cargo package") and adding them to a local-only index.
#
# WARNING: These checks are extremely expensive and only run at release time.
# WARNING: Make sure to follow the instructions in RELEASE.md for these to apply.

set -eux

cargo install cargo-index cargo-local-registry

# Build once to generate a Cargo.lock file.
cargo build --all-features
cargo clean

# Initialize a local registry based on the Cargo.lock file.
registry="$(pwd)/registry"
git config --global user.email "nobody@example.com"
git config --global user.name "Nobody"
cargo local-registry --sync . "${registry}"
(
    cd "${registry}/index"
    git init
    git add *
    git commit -a -m 'Initialize local registry'
)

# Configure Cargo overrides to use the local registry.
cat >.cargo/config <<EOF
[source.crates-io]
registry = 'https://github.com/rust-lang/crates.io-index'
replace-with = 'local-registry'

[source.local-registry]
local-registry = '${registry}'
EOF

# Package one crate at a time and add it to the local registry so that subsequent crates
# can pick them up.
for dir in core std repl client terminal sdl rpi cli; do
    cd "${dir}"
    cargo index add --index "${registry}/index" --index-url https://example.com
    cd -
    if [ "${dir}" != cli ]; then
        cp target/package/endbasic-"${dir}"-*.crate "${registry}"
    fi
done
