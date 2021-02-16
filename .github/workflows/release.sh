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

set -eux

readonly PROGNAME="${0##*/}"

err() {
    echo "${PROGNAME}: ${*}" 1>&2
    exit 1
}

main() {
    [ "${#}" -eq 1 ] || err "Must provide a release configuration"
    local name="${1}"; shift

    local version=
    case "${GITHUB_REF-}" in
        refs/heads/endbasic-*|refs/tags/endbasic-*)
            version="${GITHUB_REF#*-}"

            local cargo_version="$(grep ^version core/Cargo.toml | head -n 1 | cut -d '"' -f 2)"
            [ "${version}" = "${cargo_version}" ] \
                || err "Cargo.toml version doesn't match branch name"
            ;;

        *)
            version="$(git rev-parse --short ${GITHUB_SHA})"
            ;;
    esac
    [ -n "${version}" ] || err "Cannot determine version number"

    local ext=
    local target=
    case "${name}" in
        linux-armv7-rpi)
            [ ! -f .cargo/config ] || err "Won't override existing .cargo/config"
            cp .cargo/config.rpi .cargo/config
            ( cd cli && cargo build --release --verbose --features=rpi )
            rm -f .cargo/config
            target=./target/armv7-unknown-linux-gnueabihf/release/endbasic
            ext=tgz
            ;;

        windows*)
            ( cd cli && cargo build --release --verbose )
            target=./target/release/endbasic.exe
            ext=zip
            ;;

        *)
            ( cd cli && cargo build --release --verbose )
            target=./target/release/endbasic
            ext=tgz
            ;;
    esac

    local distname="endbasic-${version}-${name}"
    local outdir="endbasic-${name}"
    mkdir -p "${distname}" "${outdir}"

    cp LICENSE NEWS.md NOTICE README.md "${target}" "${distname}"
    case "${ext}" in
        tgz)
            tar czvf "${outdir}/${distname}.${ext}" "${distname}"
            ;;
        zip)
            zip -r "${outdir}/${distname}.${ext}" "${distname}"
            ;;
    esac
    rm -rf "${distname}"
}

main "${@}"
