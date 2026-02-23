#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
install_path="${1:-${repo_root}/tools/ephapax-cli}"

# Pinned to a concrete commit for reproducibility.
ephapax_repo="${EPHAPAX_REPO_URL:-https://github.com/hyperpolymath/ephapax.git}"
ephapax_commit="${EPHAPAX_COMMIT:-74c7235f7861419c43dce9133341ba66e15f41b2}"

if ! command -v git >/dev/null 2>&1; then
    echo "error: git is required to install ephapax-cli." >&2
    exit 127
fi
if ! command -v cargo >/dev/null 2>&1; then
    echo "error: cargo is required to build ephapax-cli." >&2
    exit 127
fi

tmp_dir="$(mktemp -d)"
cleanup() {
    rm -rf "${tmp_dir}"
}
trap cleanup EXIT

src_dir="${tmp_dir}/ephapax"
mkdir -p "${src_dir}"

echo "Fetching ephapax from ${ephapax_repo} at ${ephapax_commit}..."
git -C "${src_dir}" init -q
git -C "${src_dir}" remote add origin "${ephapax_repo}"
git -C "${src_dir}" fetch --depth 1 origin "${ephapax_commit}"
git -C "${src_dir}" checkout --detach -q FETCH_HEAD

checked_out_commit="$(git -C "${src_dir}" rev-parse HEAD)"
if [[ "${checked_out_commit}" != "${ephapax_commit}" ]]; then
    echo "error: expected commit ${ephapax_commit}, got ${checked_out_commit}" >&2
    exit 1
fi

build_toolchain="${EPHAPAX_BUILD_TOOLCHAIN:-1.89.0}"
cargo_cmd=(cargo)
if command -v rustup >/dev/null 2>&1; then
    echo "Ensuring Rust toolchain ${build_toolchain} is available..."
    rustup toolchain install "${build_toolchain}" --profile minimal >/dev/null
    cargo_cmd=(cargo "+${build_toolchain}")
fi

echo "Building ephapax-cli (locked) ..."
(
    cd "${src_dir}"
    "${cargo_cmd[@]}" build --release -p ephapax-cli --locked
)

mkdir -p "$(dirname "${install_path}")"
cp "${src_dir}/target/release/ephapax" "${install_path}"
chmod 0755 "${install_path}"

echo "Installed ephapax-cli wrapper binary to ${install_path}"
"${install_path}" --version || true
