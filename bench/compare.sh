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

info() {
    echo "${PROGNAME}: I: ${*}" 1>&2
}

run_scenario() {
    local before="${1}"; shift
    local after="${1}"; shift
    local scenario_file="${1}"; shift
    local output="${1}"; shift
    local tmpdir="${1}"; shift

    local scenario_name="${scenario_file##*/}"

    local tmpfile="${tmpdir}/${scenario_name}.csv"
    hyperfine \
        --warmup 1 \
        --export-csv "${tmpfile}" \
        "${before} ${scenario_file}" \
        "${after} ${scenario_file}"

    awk -F, -v scenario_name="${scenario_name}" '
        NR == 2 { before = $2 }
        NR == 3 { after = $2 }
        END {
            if (before == "" || after == "") {
                exit 1
            }
            printf "%s,%s,%s,%.6f\n", scenario_name, before, after, before / after
        }
    ' "${tmpfile}" >>"${output}" || err "Failed to extract results for ${scenario_file}"
}

main() {
    local after=endbasic-after
    local before=endbasic-before
    local output=results.csv
    local scenarios=
    local scenarios_dir="${PROGDIR}/scenarios"
    while getopts ':a:b:o:s:' arg "${@}"; do
        case "${arg}" in
            a)  # Path to the after binary.
                after="${OPTARG}"
                ;;

            b)  # Path to the before binary.
                before="${OPTARG}"
                ;;

            o)  # Output CSV file.
                output="${OPTARG}"
                ;;

            s)  # Name of a scenario to run; can be repeated.
                [ -e "${scenarios_dir}/${OPTARG}.bas" ] \
                    || err "Scenario ${OPTARG}.bas does not exist"
                scenarios="${scenarios} ${scenarios_dir}/${OPTARG}.bas"
                ;;

            :)
                err "Missing argument to option -${OPTARG}"
                ;;

            \?)
                err "Unknown option -${OPTARG}"
                ;;
        esac
    done
    shift $((${OPTIND} - 1))
    [ ${#} -eq 0 ] || err "Too many arguments"

    if [ -e "${output}" ]; then
        info "Backing up ${output} as ${output}~"
        mv "${output}" "${output}~"
    fi

    command -v hyperfine >/dev/null 2>&1 || err "hyperfine not found in PATH"

    case "${before}" in
        */*) ;;
        *) before="./${before}" ;;
    esac
    [ -x "${before}" ] || err "Before binary is missing or is not executable: ${before}"

    case "${after}" in
        */*) ;;
        *) after="./${after}" ;;
    esac
    [ -x "${after}" ] || err "After binary is missing or is not executable: ${after}"

    if [ -z "${scenarios}" ]; then
        for scenario in "${scenarios_dir}"/*.bas; do
            case "${scenario}" in
                */smoke.bas) continue ;;
            esac
            scenarios="${scenarios} ${scenario}"
        done
    fi

    local tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/endbasic-bench.XXXXXX")"
    trap "rm -rf '${tmpdir}'" EXIT HUP INT TERM

    printf 'scenario,before_mean_s,after_mean_s,speedup\n' >"${output}"

    for scenario in ${scenarios}; do
        run_scenario "${before}" "${after}" "${scenario}" "${output}" "${tmpdir}"
    done

    info "All done; results are in ${output}"
}

main "${@}"
