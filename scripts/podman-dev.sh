#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

# Avoid strict shell options here: podman-compose's shell wrapper can misbehave
# when inherited `SHELLOPTS` enables strict flags.

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${PROJECT_ROOT}"

COMPOSE_FILE="${COMPOSE_FILE:-podman-compose.yml}"

if ! command -v podman >/dev/null 2>&1; then
    echo "error: podman not found in PATH" >&2
    exit 127
fi

if [[ -n "${PODMAN_COMPOSE_BIN:-}" ]]; then
    if ! command -v "${PODMAN_COMPOSE_BIN}" >/dev/null 2>&1; then
        echo "error: ${PODMAN_COMPOSE_BIN} not found in PATH" >&2
        exit 127
    fi
    COMPOSE_CMD=("${PODMAN_COMPOSE_BIN}")
elif podman compose version >/dev/null 2>&1; then
    COMPOSE_CMD=("podman" "compose")
elif command -v podman-compose >/dev/null 2>&1; then
    COMPOSE_CMD=("podman-compose")
else
    echo "error: neither 'podman compose' nor 'podman-compose' is available" >&2
    exit 127
fi

run_compose() {
    "${COMPOSE_CMD[@]}" -f "${COMPOSE_FILE}" "$@"
}

usage() {
    cat <<'EOF'
Usage: scripts/podman-dev.sh <command>

Commands:
  build          Build dev image
  up             Start background dev service
  shell          Open interactive shell inside dev service
  test           Run full workspace tests in container
  bench          Run benchmark dry-run in container
  install-ephapax-cli
                 Build/install pinned real ephapax-cli to /workspace/tools/ephapax-cli
  backend-stub   Verify stub backend mode in container
  backend-verified-sim
                 Verify simulated verified backend mode in container
  backend-verified-real
                 Verify real verified backend mode (requires mounted ephapax-cli)
  compile-smoke  Run CLI compile smoke test in container
  compile-smoke-verified-sim
                 Run compile smoke test in simulated verified mode
  compile-smoke-verified-real
                 Run compile smoke test in real verified mode (requires mounted ephapax-cli)
  down           Stop and remove compose services

Environment:
  EPHAPAX_COMMIT
      Override pinned ephapax commit for install-ephapax-cli
  EPHAPAX_BUILD_TOOLCHAIN
      Rust toolchain used to build ephapax-cli (default: 1.89.0)
  EPHAPAX_REPO_URL
      Override ephapax repository URL for install-ephapax-cli
  EPHAPAX_CLI_CONTAINER_PATH
      Path inside container to real ephapax-cli
      Default: /workspace/tools/ephapax-cli
EOF
}

cmd="${1:-}"
case "${cmd}" in
    build)
        run_compose build dev
        ;;
    up)
        run_compose up -d dev
        ;;
    shell)
        run_compose exec dev bash
        ;;
    test)
        run_compose run --rm dev cargo test --all --no-fail-fast
        ;;
    bench)
        run_compose run --rm dev cargo bench --no-run
        ;;
    install-ephapax-cli)
        run_compose run --rm \
            -e EPHAPAX_COMMIT="${EPHAPAX_COMMIT:-74c7235f7861419c43dce9133341ba66e15f41b2}" \
            -e EPHAPAX_BUILD_TOOLCHAIN="${EPHAPAX_BUILD_TOOLCHAIN:-1.89.0}" \
            -e EPHAPAX_REPO_URL="${EPHAPAX_REPO_URL:-https://github.com/hyperpolymath/ephapax.git}" \
            dev ./scripts/ci/install-ephapax-cli.sh /workspace/tools/ephapax-cli
        ;;
    backend-stub)
        run_compose run --rm dev ./scripts/ci/check-backend-mode.sh stub
        ;;
    backend-verified-sim)
        run_compose run --rm -e EPHAPAX_CLI=/workspace/scripts/ci/mock-ephapax-cli.sh \
            dev ./scripts/ci/check-backend-mode.sh verified
        ;;
    backend-verified-real)
        ephapax_cli_path="${EPHAPAX_CLI_CONTAINER_PATH:-/workspace/tools/ephapax-cli}"
        run_compose run --rm dev sh -c \
            "if [ ! -x \"${ephapax_cli_path}\" ]; then echo \"error: ephapax-cli not found or not executable at ${ephapax_cli_path}\" >&2; exit 127; fi" || exit $?
        run_compose run --rm -e EPHAPAX_CLI="${ephapax_cli_path}" \
            dev ./scripts/ci/check-backend-mode.sh verified
        ;;
    compile-smoke)
        run_compose run --rm dev cargo run -p protocol-squisher-cli -- compile \
            --from rust \
            --to protobuf \
            --input examples/zero-copy-demo/src/lib.rs \
            --output /tmp/protocol-squisher-compile-smoke
        ;;
    compile-smoke-verified-sim)
        run_compose run --rm -e EPHAPAX_CLI=/workspace/scripts/ci/mock-ephapax-cli.sh \
            dev cargo run -p protocol-squisher-cli -- compile \
            --from rust \
            --to protobuf \
            --input examples/zero-copy-demo/src/lib.rs \
            --output /tmp/protocol-squisher-compile-smoke-verified-sim
        ;;
    compile-smoke-verified-real)
        ephapax_cli_path="${EPHAPAX_CLI_CONTAINER_PATH:-/workspace/tools/ephapax-cli}"
        run_compose run --rm dev sh -c \
            "if [ ! -x \"${ephapax_cli_path}\" ]; then echo \"error: ephapax-cli not found or not executable at ${ephapax_cli_path}\" >&2; exit 127; fi" || exit $?
        run_compose run --rm -e EPHAPAX_CLI="${ephapax_cli_path}" \
            dev cargo run -p protocol-squisher-cli -- compile \
            --from rust \
            --to protobuf \
            --input examples/zero-copy-demo/src/lib.rs \
            --output /tmp/protocol-squisher-compile-smoke-verified-real
        ;;
    down)
        run_compose down --remove-orphans
        ;;
    *)
        usage
        exit 1
        ;;
esac
