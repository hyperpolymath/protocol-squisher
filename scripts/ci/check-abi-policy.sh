#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

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

require_match() {
    local pattern="$1"
    local file="$2"
    local message="$3"
    if ! rg -q "${pattern}" "${file}"; then
        echo "::error::${message}" >&2
        exit 1
    fi
}

if [[ ! -f ephapax-ir/idris2/FFI.idr ]]; then
    echo "::error::Missing Idris2 ABI definition file: ephapax-ir/idris2/FFI.idr" >&2
    exit 1
fi

if [[ ! -f ffi/zig/src/main.zig ]]; then
    echo "::error::Missing Zig ABI bridge file: ffi/zig/src/main.zig" >&2
    exit 1
fi

# Idris2 owns the proof-backed ABI contract.
require_match '%export "C:ephapax_analyze_primitive_compat"' ephapax-ir/idris2/FFI.idr \
    "Idris2 ABI export 'ephapax_analyze_primitive_compat' is missing."
require_match '%export "C:ephapax_get_fidelity"' ephapax-ir/idris2/FFI.idr \
    "Idris2 ABI export 'ephapax_get_fidelity' is missing."
require_match '%export "C:ephapax_get_overhead"' ephapax-ir/idris2/FFI.idr \
    "Idris2 ABI export 'ephapax_get_overhead' is missing."

# Zig owns the C ABI surface for protocol-squisher.
require_match 'export fn squisher_init\b' ffi/zig/src/main.zig \
    "Zig ABI export 'squisher_init' is missing."
require_match 'export fn squisher_analyze_compatibility\b' ffi/zig/src/main.zig \
    "Zig ABI export 'squisher_analyze_compatibility' is missing."
require_match 'export fn squisher_generate_adapter\b' ffi/zig/src/main.zig \
    "Zig ABI export 'squisher_generate_adapter' is missing."

# Rust crates should not expose raw C ABI directly.
if rg -n --glob '*.rs' 'extern "C"|#\[no_mangle\]' crates src ephapax-ir >"${rust_abi_violations}"; then
    echo "::error::Rust C ABI exports detected. Route C ABI through Zig bridge instead." >&2
    cat "${rust_abi_violations}" >&2
    exit 1
fi

# Restrict this check to production crates. Integration tests/examples may
# intentionally emit Python extension modules for local validation.
if rg -n --glob 'Cargo.toml' 'crate-type\s*=\s*\[[^]]*cdylib' crates ephapax-ir >"${rust_cdylib_violations}"; then
    echo "::error::Rust cdylib crate-type detected in core crates. Use Zig for exported ABI artifacts." >&2
    cat "${rust_cdylib_violations}" >&2
    exit 1
fi

echo "ABI/FFI policy check passed (Idris2 ABI + Zig FFI bridge)."
