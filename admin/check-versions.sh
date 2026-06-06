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

set -eu

core_version="$(grep ^version core/Cargo.toml | head -n 1 | cut -d '"' -f 2)"
for pkg in */Cargo.toml; do
    other_version="$(grep ^version "${pkg}" | head -n 1 | cut -d '"' -f 2)"
    if [ "${core_version}" != "${other_version}" ]; then
        echo "Inconsistent version number in ${pkg}" 1>&2
        exit 1
    fi
done

json_version="$(grep version web/package.json | head -n 1 | cut -d '"' -f 4)"
if [ "${core_version}" != "${json_version}" ]; then
    echo "Versions in Cargo.toml and package.json are inconsistent" 1>&2
    exit 1
fi
