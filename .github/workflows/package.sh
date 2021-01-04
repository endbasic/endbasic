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

( cd core && cargo publish --dry-run )

# If we aren't yet ready to release a new version, all crates that depend
# on others in the workspace cannot be built in publish mode.  Skip them
# until we can test them.
if grep 'Changes in' NEWS.md | head -n 1 | fgrep 'X.Y.Z'; then
    echo "Skipping endbasic publish test in development version"
else
    ( cd std && cargo publish --dry-run )
    ( cd cli && cargo publish --dry-run )
fi
