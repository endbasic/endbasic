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

info() {
    echo "${PROGNAME}: I: ${*}" 1>&2
}

err() {
    echo "${PROGNAME}: E: ${*}" 1>&2
    exit 1
}

test_all_scenarios() {
    local tmpdir="${1}"; shift

    mkdir -p "${tmpdir}/scenarios"
    cp "${PROGDIR}/scenarios/smoke.bas" "${tmpdir}/scenarios/one.bas"
    cp "${PROGDIR}/scenarios/smoke.bas" "${tmpdir}/scenarios/two.bas"
    cp "${PROGDIR}/scenarios/smoke.bas" "${tmpdir}/scenarios/smoke.bas"

    "${PROGDIR}/compare.sh" \
        -b "${tmpdir}/endbasic" \
        -a "${tmpdir}/endbasic" \
        -o "${tmpdir}/results.csv"
    grep ^arithmetic.bas "${tmpdir}/results.csv" || err "Results validation failed"
    grep ^branches.bas "${tmpdir}/results.csv" || err "Results validation failed"
    ! grep ^smoke.bas "${tmpdir}/results.csv" || err "Results validation failed"
}

test_one_scenario() {
    local tmpdir="${1}"; shift

    "${PROGDIR}/compare.sh" \
        -b "${tmpdir}/endbasic" \
        -a "${tmpdir}/endbasic" \
        -o "${tmpdir}/results.csv" \
        -s smoke
    grep ^smoke.bas "${tmpdir}/results.csv" || err "Results validation failed"
}

main() {
    [ ${#} -eq 0 ] || err "Too many arguments"

    local tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/endbasic-bench.XXXXXX")"
    trap "rm -rf '${tmpdir}'" EXIT HUP INT TERM

    echo >"${tmpdir}/endbasic" <<EOF
#! /bin/sh
true
EOF
    chmod +x "${tmpdir}/endbasic"

    for t in \
        test_all_scenarios \
        test_one_scenario
    do
        info "Running ${t}"
        "${t}" "${tmpdir}"
    done
}

main "${@}"
