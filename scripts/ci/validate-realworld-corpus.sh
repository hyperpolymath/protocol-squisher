#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
jq_dir="${repo_root}/scripts/ci/jq"
protocol_squisher_bin="${PROTOCOL_SQUISHER_BIN:-${repo_root}/target/release/protocol-squisher}"
min_success=100
max_files=220
output_path=""
roots=()
strict_json_schema=true

usage() {
    cat <<USAGE
usage: $0 [options]

Validate real-world corpus coverage and invariant health by running
"protocol-squisher corpus-analyze" across discovered schema files.

Options:
  --bin <path>              protocol-squisher binary path
  --root <path>             Scan root (repeatable). Default: /var/mnt/eclipse/repos
  --min-success <n>         Minimum successful analyses required (default: 100)
  --max-files <n>           Max candidate files to attempt (default: 220)
  --output <path>           Write JSON report to path
  --no-strict-json-schema   Include all *.json files (default checks for schema metadata key)
  -h, --help                Show this help
USAGE
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --bin)
            protocol_squisher_bin="${2:-}"
            shift 2
            ;;
        --root)
            roots+=("${2:-}")
            shift 2
            ;;
        --min-success)
            min_success="${2:-}"
            shift 2
            ;;
        --max-files)
            max_files="${2:-}"
            shift 2
            ;;
        --output)
            output_path="${2:-}"
            shift 2
            ;;
        --no-strict-json-schema)
            strict_json_schema=false
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if [[ ${#roots[@]} -eq 0 ]]; then
    roots=(/var/mnt/eclipse/repos)
fi

if ! [[ "${min_success}" =~ ^[0-9]+$ ]]; then
    echo "error: --min-success must be an integer" >&2
    exit 2
fi
if ! [[ "${max_files}" =~ ^[0-9]+$ ]] || [[ "${max_files}" -le 0 ]]; then
    echo "error: --max-files must be a positive integer" >&2
    exit 2
fi

if [[ ! -x "${protocol_squisher_bin}" ]]; then
    if command -v protocol-squisher >/dev/null 2>&1; then
        protocol_squisher_bin="$(command -v protocol-squisher)"
    else
        cat >&2 <<ERR
error: protocol-squisher binary not found.
Expected executable at: ${protocol_squisher_bin}
Hint: cargo build -p protocol-squisher-cli --release
ERR
        exit 127
    fi
fi

if ! command -v jq >/dev/null 2>&1; then
    echo "error: jq is required." >&2
    exit 127
fi
if ! command -v rg >/dev/null 2>&1; then
    echo "error: rg is required." >&2
    exit 127
fi
if [[ ! -f "${jq_dir}/realworld-per-format-add.jq" || ! -f "${jq_dir}/realworld-report.jq" ]]; then
    echo "error: jq filters missing in ${jq_dir}" >&2
    exit 127
fi

tmp_dir="$(mktemp -d)"
cleanup() {
    rm -rf "${tmp_dir}"
}
trap cleanup EXIT

candidates_file="${tmp_dir}/candidates.tsv"
attempt_log="${tmp_dir}/attempts.tsv"
report_file="${tmp_dir}/report.json"
touch "${candidates_file}" "${attempt_log}"

append_lines_from_nul_stream() {
    local format="$1"
    while IFS= read -r -d '' file; do
        printf '%s\t%s\n' "${format}" "${file}" >>"${candidates_file}"
    done
}

for root in "${roots[@]}"; do
    if [[ ! -d "${root}" ]]; then
        continue
    fi

    # Rust files likely to be schema-bearing via serde derives.
    append_lines_from_nul_stream "rust" < <(
        rg -l --null \
            --glob '**/*.rs' \
            --glob '!**/.git/**' \
            --glob '!**/target/**' \
            --glob '!**/node_modules/**' \
            --glob '!**/deps/**' \
            --glob '!**/vendor/**' \
            --glob '!**/_build/**' \
            --glob '!**/.venv/**' \
            --glob '!**/.zig-cache/**' \
            '#\[derive\([^]]*(Serialize|Deserialize)' \
            "${root}" || true
    )

    append_lines_from_nul_stream "protobuf" < <(
        find "${root}" \
            \( -type d \( -name .git -o -name target -o -name node_modules -o -name deps -o -name vendor -o -name _build -o -name .venv -o -name .zig-cache \) -prune \) -o \
            \( -type f -name '*.proto' -print0 \) 2>/dev/null
    )
    append_lines_from_nul_stream "thrift" < <(
        find "${root}" \
            \( -type d \( -name .git -o -name target -o -name node_modules -o -name deps -o -name vendor -o -name _build -o -name .venv -o -name .zig-cache \) -prune \) -o \
            \( -type f -name '*.thrift' -print0 \) 2>/dev/null
    )
    append_lines_from_nul_stream "avro" < <(
        find "${root}" \
            \( -type d \( -name .git -o -name target -o -name node_modules -o -name deps -o -name vendor -o -name _build -o -name .venv -o -name .zig-cache \) -prune \) -o \
            \( -type f \( -name '*.avsc' -o -name '*.avdl' \) -print0 \) 2>/dev/null
    )
    append_lines_from_nul_stream "capnproto" < <(
        find "${root}" \
            \( -type d \( -name .git -o -name target -o -name node_modules -o -name deps -o -name vendor -o -name _build -o -name .venv -o -name .zig-cache \) -prune \) -o \
            \( -type f -name '*.capnp' -print0 \) 2>/dev/null
    )
    append_lines_from_nul_stream "flatbuffers" < <(
        find "${root}" \
            \( -type d \( -name .git -o -name target -o -name node_modules -o -name deps -o -name vendor -o -name _build -o -name .venv -o -name .zig-cache \) -prune \) -o \
            \( -type f -name '*.fbs' -print0 \) 2>/dev/null
    )

    if [[ "${strict_json_schema}" == true ]]; then
        append_lines_from_nul_stream "json-schema" < <(
            rg -l --null \
                --glob '**/*.json' \
                --glob '!**/.git/**' \
                --glob '!**/target/**' \
                --glob '!**/node_modules/**' \
                --glob '!**/deps/**' \
                --glob '!**/vendor/**' \
                --glob '!**/_build/**' \
                --glob '!**/.venv/**' \
                --glob '!**/.zig-cache/**' \
                '"\$schema"\s*:' \
                "${root}" || true
        )
    else
        append_lines_from_nul_stream "json-schema" < <(
            find "${root}" \
                \( -type d \( -name .git -o -name target -o -name node_modules -o -name deps -o -name vendor -o -name _build -o -name .venv -o -name .zig-cache \) -prune \) -o \
                \( -type f -name '*.json' -print0 \) 2>/dev/null
        )
    fi
done

if [[ ! -s "${candidates_file}" ]]; then
    echo "error: no corpus candidates discovered under configured roots." >&2
    exit 1
fi

# Deduplicate while preserving discovery order.
awk -F'\t' '!seen[$0]++' "${candidates_file}" >"${candidates_file}.dedup"
mv "${candidates_file}.dedup" "${candidates_file}"

total_candidates="$(wc -l <"${candidates_file}" | tr -d ' ')"
attempted=0
successful=0
parse_failures=0
invariant_violations=0

declare -A attempted_by_format=()
declare -A successful_by_format=()
declare -A parse_failures_by_format=()
declare -A violations_by_format=()

json_tmp="${tmp_dir}/analysis.json"
err_tmp="${tmp_dir}/analysis.err"

validate_invariants() {
    jq -e '
        .schema and
        .squishability and
        (.transport_classes | type == "array") and
        (.squishability.confidence >= 0 and .squishability.confidence <= 1) and
        (.squishability.predicted_speedup > 0) and
        (
            (.squishability.best_achievable_class | IN("Concorde","Business","Economy","Wheelbarrow")) and
            ((.transport_classes | all(IN("Concorde","Business","Economy","Wheelbarrow"))))
        )
    ' "${json_tmp}" >/dev/null
}

while IFS=$'\t' read -r format file_path; do
    if (( attempted >= max_files )); then
        break
    fi

    ((attempted += 1))
    attempted_by_format["${format}"]=$(( ${attempted_by_format["${format}"]:-0} + 1 ))

    if "${protocol_squisher_bin}" corpus-analyze --input "${file_path}" --format "${format}" >"${json_tmp}" 2>"${err_tmp}"; then
        ((successful += 1))
        successful_by_format["${format}"]=$(( ${successful_by_format["${format}"]:-0} + 1 ))

        if validate_invariants; then
            printf 'ok\t%s\t%s\n' "${format}" "${file_path}" >>"${attempt_log}"
        else
            ((invariant_violations += 1))
            violations_by_format["${format}"]=$(( ${violations_by_format["${format}"]:-0} + 1 ))
            printf 'invariant_violation\t%s\t%s\n' "${format}" "${file_path}" >>"${attempt_log}"
        fi
    else
        ((parse_failures += 1))
        parse_failures_by_format["${format}"]=$(( ${parse_failures_by_format["${format}"]:-0} + 1 ))
        printf 'parse_failure\t%s\t%s\n' "${format}" "${file_path}" >>"${attempt_log}"
    fi
done <"${candidates_file}"

formats=()
while IFS=$'\t' read -r format _; do
    formats+=("${format}")
done <"${candidates_file}"
IFS=$'\n' formats=($(printf '%s\n' "${formats[@]}" | sort -u))

per_format_json='{}'
for format in "${formats[@]}"; do
    per_format_json="$(
        jq -c \
            --arg format "${format}" \
            --argjson attempted "${attempted_by_format["${format}"]:-0}" \
            --argjson successful "${successful_by_format["${format}"]:-0}" \
            --argjson parse_failures "${parse_failures_by_format["${format}"]:-0}" \
            --argjson invariant_violations "${violations_by_format["${format}"]:-0}" \
            -f "${jq_dir}/realworld-per-format-add.jq" \
            <<<"${per_format_json}"
    )"
done

generated_at="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
roots_json="$(printf '%s\n' "${roots[@]}" | jq -R . | jq -s .)"

jq -n \
    --arg generated_at "${generated_at}" \
    --arg bin "${protocol_squisher_bin}" \
    --argjson roots "${roots_json}" \
    --argjson strict_json_schema "$( [[ "${strict_json_schema}" == true ]] && echo true || echo false )" \
    --argjson min_success "${min_success}" \
    --argjson max_files "${max_files}" \
    --argjson total_candidates "${total_candidates}" \
    --argjson attempted "${attempted}" \
    --argjson successful "${successful}" \
    --argjson parse_failures "${parse_failures}" \
    --argjson invariant_violations "${invariant_violations}" \
    --argjson per_format "${per_format_json}" \
    -f "${jq_dir}/realworld-report.jq" >"${report_file}"

if [[ -n "${output_path}" ]]; then
    mkdir -p "$(dirname "${output_path}")"
    cp "${report_file}" "${output_path}"
fi

cat "${report_file}"

if (( successful < min_success || invariant_violations > 0 )); then
    exit 1
fi
