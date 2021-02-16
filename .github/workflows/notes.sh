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

set -eu

readonly PROGNAME="${0##*/}"

err() {
    echo "${PROGNAME}: ${*}" 1>&2
    exit 1
}

main() {
    local version=
    case "${GITHUB_REF-}" in
        refs/heads/endbasic-*|refs/tags/endbasic-*)
            version="${GITHUB_REF#*-}"
            ;;
    esac
    [ -n "${version}" ] || err "Not building a release"

    {
        while read line; do
            case "${line}" in
                "## Changes in version ${version}"*)
                    break
                    ;;
            esac
        done

        while read line; do
            [ -z "${line}" ] || break
        done
        echo "${line}"

        while read line; do
            case "${line}" in
                "## Changes in version "*)
                    break
                    ;;
                *)
                    echo "${line}"
                    ;;
            esac
        done
    } <NEWS.md
}

main
