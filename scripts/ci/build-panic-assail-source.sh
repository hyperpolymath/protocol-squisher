#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

usage() {
    echo "usage: $0 <output-dir>" >&2
}

if [[ $# -ne 1 ]]; then
    usage
    exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
out_dir="$1"

rm -rf "${out_dir}"
mkdir -p "${out_dir}"

copy_dir() {
    local rel="$1"
    local src="${repo_root}/${rel}"
    local dst="${out_dir}/${rel}"
    if [[ -d "${src}" ]]; then
        mkdir -p "${dst}"
        rsync -a \
            --exclude "target/" \
            --exclude "tests/" \
            --exclude "test/" \
            --exclude "benches/" \
            --exclude "examples/" \
            --exclude "build/" \
            --exclude "build-ffi/" \
            --exclude "__pycache__/" \
            "${src}/" "${dst}/"
    fi
}

# Inline Rust unit tests live in production source files (`src/*.rs`) behind
# `#[cfg(test)]`. Strip those tails so panic-assail metrics match the declared
# production-only scope.
sanitize_rust_sources() {
    local root="$1"
    local file
    while IFS= read -r -d '' file; do
        if rg -q '^[[:space:]]*#\[cfg\(test\)\]' "${file}"; then
            awk '
                /^[[:space:]]*#\[cfg\(test\)\]/ { exit }
                { print }
            ' "${file}" >"${file}.tmp"
            mv "${file}.tmp" "${file}"
        fi
        # Remove line comments so rustdoc/example snippets do not skew panic
        # metrics for executable production paths.
        awk '
            /^[[:space:]]*\/\// { next }
            { print }
        ' "${file}" >"${file}.tmp"
        mv "${file}.tmp" "${file}"
    done < <(find "${root}" -type f -name '*.rs' -print0)
}

# Zig `test` blocks live in `src/main.zig` alongside exports. They are not part
# of production runtime, so trim from the first test declaration onward.
sanitize_zig_sources() {
    local root="$1"
    local file
    while IFS= read -r -d '' file; do
        if rg -q '^[[:space:]]*test[[:space:]]+"' "${file}"; then
            awk '
                /^[[:space:]]*test[[:space:]]+"/ { exit }
                { print }
            ' "${file}" >"${file}.tmp"
            mv "${file}.tmp" "${file}"
        fi
    done < <(find "${root}" -type f -name '*.zig' -print0)
}

# Core production surfaces.
copy_dir "src"
copy_dir "ephapax-ir/src"
copy_dir "ephapax-ir/idris2"
copy_dir "ffi/zig/src"
copy_dir "scripts/ci"

# Workspace crates, excluding test-only crates.
for crate_src in "${repo_root}"/crates/*/src; do
    [[ -d "${crate_src}" ]] || continue
    crate_name="$(basename "$(dirname "${crate_src}")")"
    case "${crate_name}" in
        protocol-squisher-integration-tests|protocol-squisher-property-tests)
            continue
            ;;
    esac

    rel="crates/${crate_name}/src"
    mkdir -p "${out_dir}/${rel}"
    rsync -a "${crate_src}/" "${out_dir}/${rel}/"
done

sanitize_rust_sources "${out_dir}"
sanitize_zig_sources "${out_dir}"

echo "${out_dir}"
