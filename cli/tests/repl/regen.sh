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

# Regenerates the given .out files.

tmpdir="$(mktemp -d)"
trap "rm -f \"${tmpdir}\"/*; rmdir \"${tmpdir}\"" EXIT

run() {
    local local_drive="${1}"; shift

    rm -f "${tmpdir}"/*
    LINES=24 COLUMNS=80 cargo run -- --local-drive="${local_drive}" \
        --interactive "${@}"
}

date_re="[0-9]{4}-[0-9]{2}-[0-9]{2} [0-2][0-9]:[0-5][0-9]"
version_re="[0-9]+\\.[0-9]+\\.[0-9]+"

for outfile in "${@}"; do
    basfile="${outfile%.*}.bas"
    infile="${outfile%.*}.in"

    local_drive="file://${tmpdir}"
    case "${outfile}" in
        *dir.out) local_drive="memory://" ;;
        *storage.out) local_drive="file://${tmpdir}" ;;
    esac

    if [ -f "${basfile}" -a -f "${infile}" ]; then
        run "${local_drive}" "${basfile}" <"${infile}" >"${outfile}.new"
    elif [ -f "${basfile}" ]; then
        run "${local_drive}" "${basfile}" >"${outfile}.new"
    elif [ -f "${infile}" ]; then
        run "${local_drive}" <"${infile}" >"${outfile}.new"
    else
        echo "No input for ${outfile}?" 1>&2
        continue
    fi

    sed -E -e "s,${date_re},YYYY-MM-DD HH:MM,g" \
        -e "s,${version_re},X.Y.Z,g" \
        -e "s,${tmpdir},/PATH/TO/TMPDIR,g" \
        "${outfile}.new" >"${outfile}.tmp"
    mv "${outfile}.tmp" "${outfile}"
    rm -f "${outfile}.new" "${outfile}.tmp"
done
