#! /bin/sh
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

set -eux

cargo clippy --all-targets -- -D warnings

# The --workspace and --all-features flags trigger the build/check of the
# "rpi" crate which only builds on Linux.
if [ "$(uname -s)" = Linux ]; then
    cargo clippy --all-targets --all-features -- -D warnings
    cargo clippy --workspace --all-targets -- -D warnings
    cargo clippy --workspace --all-targets --all-features -- -D warnings
fi

cargo fmt -- --check
