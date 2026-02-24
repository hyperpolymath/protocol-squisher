#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
output_path="${1:-${repo_root}/docs/launch/METRICS.md}"

tmp_output="$(mktemp)"
cleanup() {
    rm -f "${tmp_output}"
}
trap cleanup EXIT

cd "${repo_root}"

echo "running cargo test --all (this may take a while)..."
cargo test --all 2>&1 | tee "${tmp_output}" >/dev/null

read -r passed failed ignored < <(
    awk '
        /test result:/ {
            gsub(";", "", $5);
            gsub(";", "", $7);
            gsub(";", "", $9);
            p += $4;
            f += $6;
            i += $8;
        }
        END {
            print p, f, i;
        }
    ' "${tmp_output}"
)

generated_at_utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
git_commit="$(git rev-parse HEAD)"

cat >"${output_path}" <<EOF
# Launch Metrics

- Generated at (UTC): ${generated_at_utc}
- Git commit: \`${git_commit}\`
- Command: \`cargo test --all\`
- Result: ${passed} passed, ${ignored} ignored, ${failed} failed

## Notes

- Regenerate before posting announcements:
  \`./scripts/ci/refresh-launch-metrics.sh\`
- This file is intended as the single source of truth for launch copy metrics.
EOF

echo "wrote ${output_path}"
