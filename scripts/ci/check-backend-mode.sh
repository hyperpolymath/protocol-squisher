#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

mode="${1:-}"
if [[ "${mode}" != "stub" && "${mode}" != "verified" ]]; then
    echo "usage: $0 <stub|verified>" >&2
    exit 2
fi

EXPECT_EPHAPAX_MODE="${mode}" \
cargo test -p protocol-squisher-transport-primitives tests::backend_mode_matches_expectation -- --exact
