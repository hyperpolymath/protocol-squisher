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
    echo "error: jq is required for baseline generation." >&2
    exit 127
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

weak_points="$(jq -r '.weak_points | length' "${report_file}")"
unwrap_calls="$(jq -r '.statistics.unwrap_calls' "${report_file}")"
panic_sites="$(jq -r '.statistics.panic_sites' "${report_file}")"
today="$(date -u +%F)"

cat > "${baseline_file}" <<EOF
{
  "tool": "panic-attack",
  "generated_on": "${today}",
  "scope": "production-source-only (src + crate src + ephapax-ir + ffi/zig + scripts/ci; excludes tests/examples/benches and test-only crates)",
  "metrics": {
    "weak_points": ${weak_points},
    "unwrap_calls": ${unwrap_calls},
    "panic_sites": ${panic_sites}
  }
}
EOF

echo "updated ${baseline_file}"
