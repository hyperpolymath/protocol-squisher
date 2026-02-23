#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

if [[ "${1:-}" == "--version" ]]; then
    echo "mock-ephapax-cli 0.1.0"
    exit 0
fi

if [[ "${1:-}" != "compile" ]]; then
    echo "mock-ephapax-cli: expected 'compile' command" >&2
    exit 64
fi

if [[ $# -lt 4 ]]; then
    echo "mock-ephapax-cli: usage: compile <input.eph> -o <output.wasm>" >&2
    exit 64
fi

input="${2}"
flag="${3}"
output="${4}"

if [[ "${flag}" != "-o" ]]; then
    echo "mock-ephapax-cli: expected '-o' flag, got '${flag}'" >&2
    exit 64
fi

mkdir -p "$(dirname "${output}")"
printf "mock wasm artifact for %s\n" "${input}" > "${output}"
