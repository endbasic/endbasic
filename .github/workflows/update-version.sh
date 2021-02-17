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

set -e

readonly PROGNAME="${0##*/}"

err() {
    echo "${PROGNAME}: ${*}" 1>&2
    exit 1
}

replace() {
    local path="${1}"; shift
    sed "${@}" "${path}" >"${path}.new"
    mv "${path}.new" "${path}"
}

fix_package_lock() {
    local path="${1}"; shift
    local version="${1}"; shift

    POSIXLY_CORRECT=1 awk "
BEGIN { found = 0 }
/endbasic-www/ { found = 1 }
/version/ {
    if (found) {
        sub(/[0-9]+\\.[0-9]+\\.[0-9]+/, \"${version}\")
        found = 0
    }
}
{ print }
" "${path}" >"${path}.new"
    mv "${path}.new" "${path}"
}

main() {
    [ ${#} -eq 1 ] || err "Must specify the new version number"
    local version="${1}"; shift
    local date="$(date +%Y-%m-%d)"

    replace README.md -E "/latest version/s/[0-9]+\\.[0-9]+\\.[0-9]+/${version}/g"
    replace README.md -E "/released on/s/[0-9]{4}-[0-9]{2}-[0-9]{2}/${date}/g"

    replace NEWS.md -E "/Changes in.*X\\.Y\\.Z/s/[X0-9]+\\.[Y0-9]+\\.[Z0-9]+/${version}/g"
    replace NEWS.md -E "/STILL UNDER DEVELOPMENT/s/^.*$/**Released on ${date}.**/g"

    for f in */Cargo.toml; do
        replace "${f}" -E "/ENDBASIC-VERSION/s/[0-9]+\\.[0-9]+\\.[0-9]+/${version}/g"
    done

    replace web/package.json -E "/\"version\"/s/[0-9]+\\.[0-9]+\\.[0-9]+/${version}/g"
    fix_package_lock web/package-lock.json "${version}"

    replace .github/workflows/deploy-release.yml \
        -E "s/endbasic-[0-9]+\\.[0-9]+\\.[0-9]+/endbasic-${version}/g"
}

main "${@}"
