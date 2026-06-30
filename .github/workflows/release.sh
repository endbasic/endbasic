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

sanity_check() {
    local bin="${1}"; shift

    local ret=0
    echo "END 123" | "${bin}" || ret="${?}"
    [ "${ret}" -eq 123 ] || err "Packaged endbasic doesn't seem to work"
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

    local notices="$(echo NOTICE */NOTICE)"

    local distname="endbasic-${version}-${name}"
    local outdir="endbasic-${name}"
    mkdir -p "${distname}" "${outdir}"

    cp LICENSE NEWS.md README.md "${distname}"

    for f in ${notices}; do
        echo "# ${f}"
        echo
        cat "${f}"
        echo
    done >"${distname}/NOTICE"

    local target=
    case "${name}" in
        linux-aarch64-rpi-sdl)
            [ ! -f .cargo/config ] || err "Won't override existing .cargo/config"
            cp .cargo/config.rpi64 .cargo/config
            ( cd cli && cargo build --release --features=rpi,sdl-bundled )
            rm -f .cargo/config

            cp ./target/aarch64-unknown-linux-gnu/release/endbasic "${distname}"
            cp ./target/aarch64-unknown-linux-gnu/release/libSDL2.so* "${distname}"
            ;;

        linux-armv7-rpi-sdl)
            [ ! -f .cargo/config ] || err "Won't override existing .cargo/config"
            cp .cargo/config.rpi .cargo/config
            ( cd cli && cargo build --release --features=rpi,sdl-bundled )
            rm -f .cargo/config

            cp ./target/armv7-unknown-linux-gnueabihf/release/endbasic "${distname}"
            cp ./target/armv7-unknown-linux-gnueabihf/release/libSDL2.so* "${distname}"
            ;;

        macos*)
            brew install sdl2

            local brew="$(brew --prefix)"
            (
                cd cli
                export LIBRARY_PATH="${brew}/lib"
                cargo build --release --features=sdl
            )

            cp ./target/release/endbasic "${distname}/endbasic.bin"
            cp .github/workflows/macos-launcher.sh "${distname}/endbasic"

            # Bundle the necessary shared libraries as provided by Homebrew.
            cp "${brew}"/Cellar/sdl2-compat/*/lib/lib*.dylib "${distname}"
            cp "${brew}"/Cellar/sdl2-compat/*/LICENSE.txt "${distname}/LICENSE.sdl2-compat"
            cp "${brew}"/Cellar/sdl3/*/lib/lib*.dylib "${distname}"
            cp "${brew}"/Cellar/sdl3/*/LICENSE.txt "${distname}/LICENSE.sdl3"
            cp "${brew}"/Cellar/freetype/*/lib/libfreetype.*.dylib "${distname}"
            cp "${brew}"/Cellar/freetype/*/LICENSE.TXT "${distname}/LICENSE.freetype"
            cp "${brew}"/Cellar/libpng/*/lib/libpng16.*.dylib "${distname}"
            cp "${brew}"/Cellar/libpng/*/LICENSE "${distname}/LICENSE.libpng"

            brew uninstall --ignore-dependencies sdl2-compat sdl3 freetype libpng
            sanity_check "${distname}/endbasic"
            ;;

        windows*)
            ( cd cli && LIB="$(pwd)/libs" cargo build --release --features=sdl )

            cp ./target/release/endbasic.exe "${distname}"
            cp dlls/* "${distname}"

            sanity_check "${distname}/endbasic.exe"
            ;;

        *)
            ( cd cli && cargo build --release --features=sdl )

            cp ./target/release/endbasic "${distname}"

            sanity_check "${distname}/endbasic"
            ;;
    esac
    zip -r "${outdir}/${distname}.zip" "${distname}"
    rm -rf "${distname}"
}

main "${@}"
