#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
panic_attack_bin="${PANIC_ATTACK_BIN:-panic-attack}"
baseline_file="${1:-${repo_root}/scripts/ci/panic-assail-baseline.json}"

if ! command -v "${panic_attack_bin}" >/dev/null 2>&1; then
    echo "error: panic-attack binary not found (set PANIC_ATTACK_BIN or add panic-attack to PATH)." >&2
    exit 127
fi

if ! command -v jq >/dev/null 2>&1; then
    echo "error: jq is required for panic-assail regression checks." >&2
    exit 127
fi

if [[ ! -f "${baseline_file}" ]]; then
    echo "error: baseline file not found: ${baseline_file}" >&2
    exit 2
fi

tmp_dir="$(mktemp -d)"
cleanup() {
    rm -rf "${tmp_dir}"
}
trap cleanup EXIT

source_tree="${tmp_dir}/source"
report_file="${tmp_dir}/assail.json"

"${repo_root}/scripts/ci/build-panic-assail-source.sh" "${source_tree}" >/dev/null
if ! "${panic_attack_bin}" assail "${source_tree}" --output "${report_file}" >/dev/null 2>"${tmp_dir}/panic-assail.stderr"; then
    cat "${tmp_dir}/panic-assail.stderr" >&2
    exit 1
fi

baseline_weak_points="$(jq -r '.metrics.weak_points' "${baseline_file}")"
baseline_unwrap_calls="$(jq -r '.metrics.unwrap_calls' "${baseline_file}")"

current_weak_points="$(jq -r '.weak_points | length' "${report_file}")"
current_unwrap_calls="$(jq -r '.statistics.unwrap_calls' "${report_file}")"
current_panic_sites="$(jq -r '.statistics.panic_sites' "${report_file}")"

echo "panic-assail regression metrics"
echo "  weak_points : ${current_weak_points} (baseline: ${baseline_weak_points})"
echo "  unwrap_calls: ${current_unwrap_calls} (baseline: ${baseline_unwrap_calls})"
echo "  panic_sites : ${current_panic_sites} (tracked)"

status=0

if (( current_weak_points > baseline_weak_points )); then
    echo "error: weak_points increased from ${baseline_weak_points} to ${current_weak_points}" >&2
    status=1
fi

if (( current_unwrap_calls > baseline_unwrap_calls )); then
    echo "error: unwrap_calls increased from ${baseline_unwrap_calls} to ${current_unwrap_calls}" >&2
    status=1
fi

exit "${status}"
