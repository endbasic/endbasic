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

readonly PROGDIR="$(cd "$(dirname "${0}")" && pwd -P)"
readonly PROGNAME="${0##*/}"

err() {
    echo "${PROGNAME}: E: ${*}" 1>&2
    exit 1
}

main() {
    [ ${#} -eq 0 ] || err "Too many arguments"

    local tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/endbasic-bench.XXXXXX")"
    trap "rm -rf '${tmpdir}'" EXIT HUP INT TERM

    cd "${PROGDIR}/.." && cargo build --release

    "${PROGDIR}/compare.sh" \
        -b "${PROGDIR}/../target/release/endbasic" \
        -a "${PROGDIR}/../target/release/endbasic" \
        -o "${tmpdir}/results.csv" \
        -s smoke

    grep ^smoke.bas "${tmpdir}/results.csv" || err "Results validation failed"
}

main "${@}"
