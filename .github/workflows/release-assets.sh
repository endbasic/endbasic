#! /bin/sh
# EndBASIC
# Copyright 2026 Julio Merino
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

set -eu

readonly PROGNAME="${0##*/}"

err() {
    echo "${PROGNAME}: ${*}" 1>&2
    exit 1
}

find_asset() {
    local directory="${1}"; shift

    [ -d "${directory}" ] || err "Missing artifact directory: ${directory}"

    local count=0
    local asset=
    for candidate in "${directory}"/*.zip; do
        [ -f "${candidate}" ] || continue
        count=$((count + 1))
        asset="${candidate}"
    done

    [ "${count}" -eq 1 ] || err "Expected exactly one ZIP in ${directory}"

    echo "${asset}"
}

main() {
    local errors=0
    local assets=
    for name in "${@}"; do
        local directory="artifacts/endbasic-${name}"
        local asset
        if asset="$(find_asset "${directory}")"; then
            if [ -z "${assets}" ]; then
                assets="${asset}"
            else
                assets="${assets},${asset}"
            fi
        else
            errors=$((errors + 1))
        fi
    done

    [ "${errors}" -eq 0 ] || err "Found ${errors} release asset issue(s)"

    echo "artifacts=${assets}"
}

main "${@}"
