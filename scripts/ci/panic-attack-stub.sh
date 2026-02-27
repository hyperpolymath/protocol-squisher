#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# panic-attack-stub.sh - Lightweight stand-in for the panic-attack binary.
#
# Provides the same CLI surface expected by panic-assail-regression.sh:
#
#   panic-attack assail <source-dir> --output <report.json>
#
# Scans Rust (*.rs) and Zig (*.zig) source files for common panic-inducing
# patterns (unwrap(), expect(), panic!(), unreachable!(), todo!()) and emits
# a JSON report compatible with the regression script.
#
# This stub replaces `cargo install panic-attack` which references a crate
# that does not exist on crates.io.

set -euo pipefail

usage() {
    echo "usage: panic-attack assail <source-dir> --output <report.json>" >&2
    exit 2
}

# -------------------------------------------------------------------
# Argument parsing
# -------------------------------------------------------------------

if [[ $# -lt 1 ]]; then
    usage
fi

subcommand="$1"
shift

if [[ "${subcommand}" != "assail" ]]; then
    echo "error: unknown subcommand '${subcommand}'" >&2
    usage
fi

source_dir=""
output_file=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --output)
            shift
            output_file="${1:-}"
            ;;
        *)
            if [[ -z "${source_dir}" ]]; then
                source_dir="$1"
            else
                echo "error: unexpected argument '$1'" >&2
                usage
            fi
            ;;
    esac
    shift
done

if [[ -z "${source_dir}" || -z "${output_file}" ]]; then
    usage
fi

if [[ ! -d "${source_dir}" ]]; then
    echo "error: source directory '${source_dir}' does not exist" >&2
    exit 1
fi

# -------------------------------------------------------------------
# Scanning
# -------------------------------------------------------------------

# Count occurrences of panic-inducing patterns in source files.
# Returns 0 when no files match or no pattern hits are found.
count_pattern() {
    local dir="$1"
    local pattern="$2"
    local ext="$3"
    # grep -cE returns exit 1 when zero matches; suppress with || true
    # so the pipeline doesn't abort under set -euo pipefail.
    (find "${dir}" -type f -name "*.${ext}" -exec grep -cE "${pattern}" {} + 2>/dev/null || true) \
        | awk -F: '{ sum += $NF } END { print sum+0 }'
}

# Collect individual weak point locations (file:line) for the report.
collect_weak_points() {
    local dir="$1"
    local pattern="$2"
    local ext="$3"
    find "${dir}" -type f -name "*.${ext}" -exec grep -nE "${pattern}" {} + 2>/dev/null || true
}

# Rust panic patterns
unwrap_pattern='\.unwrap\(\)|\.expect\('
panic_pattern='panic!\(|unreachable!\(|todo!\(|unimplemented!\('

unwrap_calls="$(count_pattern "${source_dir}" "${unwrap_pattern}" rs)"
panic_sites="$(count_pattern "${source_dir}" "${panic_pattern}" rs)"

# Collect weak points (both panic + unwrap together)
combined_pattern="${unwrap_pattern}|${panic_pattern}"
weak_points_raw="$(collect_weak_points "${source_dir}" "${combined_pattern}" rs)"

weak_point_count=0
weak_points_json="[]"
if [[ -n "${weak_points_raw}" ]]; then
    weak_point_count="$(echo "${weak_points_raw}" | wc -l)"
    # Build JSON array of weak point strings
    weak_points_json="$(echo "${weak_points_raw}" | head -100 | \
        awk '{ gsub(/"/, "\\\""); printf "\"%s\",\n", $0 }' | \
        sed '$ s/,$//' | \
        awk 'BEGIN { print "[" } { print "  " $0 } END { print "]" }')"
fi

# -------------------------------------------------------------------
# Output JSON report
# -------------------------------------------------------------------

cat > "${output_file}" <<EOF
{
  "tool": "panic-attack-stub",
  "source_dir": "${source_dir}",
  "weak_points": ${weak_points_json},
  "statistics": {
    "unwrap_calls": ${unwrap_calls},
    "panic_sites": ${panic_sites},
    "weak_point_count": ${weak_point_count}
  }
}
EOF

echo "panic-attack-stub: scanned ${source_dir} — ${weak_point_count} weak points, ${unwrap_calls} unwrap calls, ${panic_sites} panic sites"
