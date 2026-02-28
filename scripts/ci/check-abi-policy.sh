#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# check-abi-policy.sh - Enforces Idris2 ABI + Zig FFI bridge policy.
#
# Ensures:
#   1. Idris2 ABI definition (ephapax-ir/idris2/FFI.idr) contains required
#      C-exported symbols.
#   2. Zig FFI bridge (ffi/zig/src/main.zig) contains required export fns.
#   3. Rust production crates do NOT expose raw C ABI (extern "C" /
#      #[no_mangle]) — all C ABI must go through the Zig bridge.
#   4. Rust production crates do NOT declare cdylib crate-type.
#
# Uses grep/find instead of ripgrep for CI portability (rg is not
# pre-installed on GitHub Actions ubuntu-latest runners).

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${repo_root}"

tmp_dir="$(mktemp -d)"
cleanup() {
    rm -rf "${tmp_dir}"
}
trap cleanup EXIT

rust_abi_violations="${tmp_dir}/rust-abi-violations.txt"
rust_cdylib_violations="${tmp_dir}/rust-cdylib-violations.txt"

# require_match PATTERN FILE MESSAGE
# Asserts that PATTERN (grep -qE) matches somewhere in FILE.
require_match() {
    local pattern="$1"
    local file="$2"
    local message="$3"
    if ! grep -qF "${pattern}" "${file}" 2>/dev/null; then
        echo "::error::${message}" >&2
        exit 1
    fi
}

# require_match_regex PATTERN FILE MESSAGE
# Like require_match but uses extended regex (grep -qE).
require_match_regex() {
    local pattern="$1"
    local file="$2"
    local message="$3"
    if ! grep -qE "${pattern}" "${file}" 2>/dev/null; then
        echo "::error::${message}" >&2
        exit 1
    fi
}

# ------------------------------------------------------------------
# File existence checks
# ------------------------------------------------------------------

if [[ ! -f ephapax-ir/idris2/FFI.idr ]]; then
    echo "::error::Missing Idris2 ABI definition file: ephapax-ir/idris2/FFI.idr" >&2
    exit 1
fi

if [[ ! -f ffi/zig/src/main.zig ]]; then
    echo "::error::Missing Zig ABI bridge file: ffi/zig/src/main.zig" >&2
    exit 1
fi

# ------------------------------------------------------------------
# Idris2 owns the proof-backed ABI contract.
# ------------------------------------------------------------------

require_match '%export "C:ephapax_analyze_primitive_compat"' ephapax-ir/idris2/FFI.idr \
    "Idris2 ABI export 'ephapax_analyze_primitive_compat' is missing."
require_match '%export "C:ephapax_get_fidelity"' ephapax-ir/idris2/FFI.idr \
    "Idris2 ABI export 'ephapax_get_fidelity' is missing."
require_match '%export "C:ephapax_get_overhead"' ephapax-ir/idris2/FFI.idr \
    "Idris2 ABI export 'ephapax_get_overhead' is missing."

# ------------------------------------------------------------------
# Zig owns the C ABI surface for protocol-squisher.
# Word boundary is approximated with [^a-zA-Z0-9_] or end-of-line.
# ------------------------------------------------------------------

require_match_regex 'export fn squisher_init($|[^a-zA-Z0-9_])' ffi/zig/src/main.zig \
    "Zig ABI export 'squisher_init' is missing."
require_match_regex 'export fn squisher_analyze_compatibility($|[^a-zA-Z0-9_])' ffi/zig/src/main.zig \
    "Zig ABI export 'squisher_analyze_compatibility' is missing."
require_match_regex 'export fn squisher_generate_adapter($|[^a-zA-Z0-9_])' ffi/zig/src/main.zig \
    "Zig ABI export 'squisher_generate_adapter' is missing."

# ------------------------------------------------------------------
# Rust crates should not expose raw C ABI directly.
# Scan *.rs files under crates/, src/, ephapax-ir/ for extern "C" or
# #[no_mangle]. Excludes test/ directories.
# ------------------------------------------------------------------

if find crates src ephapax-ir -name '*.rs' -not -path '*/test/*' -not -path '*/tests/*' \
       -exec grep -nH 'extern "C"\|#\[no_mangle\]' {} + >"${rust_abi_violations}" 2>/dev/null; then
    echo "::error::Rust C ABI exports detected. Route C ABI through Zig bridge instead." >&2
    cat "${rust_abi_violations}" >&2
    exit 1
fi

# ------------------------------------------------------------------
# Restrict cdylib check to production crates. Integration
# tests/examples may intentionally emit Python extension modules for
# local validation.
# ------------------------------------------------------------------

if find crates ephapax-ir -name 'Cargo.toml' \
       -exec grep -nHE 'crate-type\s*=\s*\[[^]]*cdylib' {} + >"${rust_cdylib_violations}" 2>/dev/null; then
    echo "::error::Rust cdylib crate-type detected in core crates. Use Zig for exported ABI artifacts." >&2
    cat "${rust_cdylib_violations}" >&2
    exit 1
fi

echo "ABI/FFI policy check passed (Idris2 ABI + Zig FFI bridge)."
