# SPDX-License-Identifier: PMPL-1.0
# protocol-squisher - Justfile
# https://just.systems/man/en/

set shell := ["bash", "-uc"]
set dotenv-load := true
set positional-arguments := true

# Project metadata
project := "protocol-squisher"
version := "0.1.0"

# ═══════════════════════════════════════════════════════════════════════════════
# DEFAULT & HELP
# ═══════════════════════════════════════════════════════════════════════════════

# Show all available recipes
default:
    @just --list --unsorted

# Show project info
info:
    @echo "Project: {{project}}"
    @echo "Version: {{version}}"

# ═══════════════════════════════════════════════════════════════════════════════
# BUILD
# ═══════════════════════════════════════════════════════════════════════════════

# Build ephapax IR (compile .eph to WASM)
build-ephapax-ir:
    @echo "Building ephapax IR..."
    @cli="${EPHAPAX_CLI:-ephapax-cli}"; \
    if command -v "${cli}" >/dev/null 2>&1 || [ -x "${cli}" ]; then \
        mkdir -p ephapax-ir/target; \
        "${cli}" compile ephapax-ir/src/types.eph -o ephapax-ir/target/types.wasm; \
        "${cli}" compile ephapax-ir/src/compat.eph -o ephapax-ir/target/compat.wasm; \
        echo "Compiled ephapax IR via ${cli}"; \
    else \
        echo "ephapax-cli not found; build scripts will use stub fallback"; \
        echo "Tip: ./scripts/podman-dev.sh install-ephapax-cli"; \
    fi

# Build the project (ephapax IR + Rust crates)
build: build-ephapax-ir
    @echo "Building {{project}}..."
    cargo build --workspace

# Build release
build-release: build-ephapax-ir
    cargo build --workspace --release

# Clean build artifacts
clean:
    @echo "Cleaning..."
    cargo clean
    rm -rf ephapax-ir/target/*.wasm

# ═══════════════════════════════════════════════════════════════════════════════
# TEST & QUALITY
# ═══════════════════════════════════════════════════════════════════════════════

# Run tests
test: build-ephapax-ir
    @echo "Running tests..."
    cargo test --workspace

# Run property-based tests (longer running)
test-prop: build-ephapax-ir
    cargo test --workspace --release -- --ignored

# Run linter
lint:
    @echo "Linting..."
    cargo clippy --workspace -- -D warnings

# Format code
fmt:
    @echo "Formatting..."
    cargo fmt --all
    @echo "Note: ephapax formatting not yet available"

# Run all quality checks
quality: fmt lint test

# ═══════════════════════════════════════════════════════════════════════════════
# VALIDATION
# ═══════════════════════════════════════════════════════════════════════════════

# Validate RSR compliance
validate-rsr:
    @echo "Validating RSR compliance..."
    @test -f .gitignore || (echo "Missing .gitignore" && exit 1)
    @test -f .gitattributes || (echo "Missing .gitattributes" && exit 1)
    @test -f .editorconfig || (echo "Missing .editorconfig" && exit 1)
    @test -f .tool-versions || (echo "Missing .tool-versions" && exit 1)
    @test -f META.scm || (echo "Missing META.scm" && exit 1)
    @test -f STATE.scm || (echo "Missing STATE.scm" && exit 1)
    @test -f ECOSYSTEM.scm || (echo "Missing ECOSYSTEM.scm" && exit 1)
    @test -f PLAYBOOK.scm || (echo "Missing PLAYBOOK.scm" && exit 1)
    @test -f AGENTIC.scm || (echo "Missing AGENTIC.scm" && exit 1)
    @test -f NEUROSYM.scm || (echo "Missing NEUROSYM.scm" && exit 1)
    @test ! -f Makefile || (echo "Makefile forbidden - use justfile" && exit 1)
    @echo "RSR validation passed!"

# Validate STATE.scm syntax
validate-state:
    @echo "Validating STATE.scm..."
    @test -f STATE.scm && echo "STATE.scm exists" || echo "STATE.scm missing"

# Update STATE.scm timestamp
state-touch:
    @echo "Updating STATE.scm timestamp..."
    @[ -f STATE.scm ] && sed -i 's/(updated . "[^"]*")/(updated . "'$(date +%Y-%m-%d)'")/' STATE.scm || true

# ═══════════════════════════════════════════════════════════════════════════════
# CI
# ═══════════════════════════════════════════════════════════════════════════════

# Run full CI pipeline locally
ci: quality validate-rsr
    @echo "CI pipeline passed!"

# Run corrective-maintenance gates (ABI/FFI policy + panic-assail + real verified backend)
maint-corrective:
    ./scripts/ci/check-abi-policy.sh
    @panic_bin="${PANIC_ATTACK_BIN:-}"; [ -n "${panic_bin}" ] || [ ! -x /var/mnt/eclipse/repos/panic-attacker/target/release/panic-attack ] || panic_bin=/var/mnt/eclipse/repos/panic-attacker/target/release/panic-attack; PANIC_ATTACK_BIN="${panic_bin}" ./scripts/ci/panic-assail-regression.sh
    ./scripts/podman-dev.sh install-ephapax-cli
    ./scripts/podman-dev.sh backend-verified-real
    ./scripts/podman-dev.sh compile-smoke-verified-real

# Capture maintenance metrics snapshot (JSON in /tmp by default)
maint-metrics:
    ./scripts/ci/capture-maintenance-metrics.sh

# Capture maintenance metrics including timed podman checks
maint-metrics-podman:
    ./scripts/ci/capture-maintenance-metrics.sh --with-podman

# ═══════════════════════════════════════════════════════════════════════════════
# CONTAINER (PODMAN)
# ═══════════════════════════════════════════════════════════════════════════════

# Build Podman dev image
container-build:
    ./scripts/podman-dev.sh build

# Start Podman dev service
container-up:
    ./scripts/podman-dev.sh up

# Open shell in Podman dev service
container-shell:
    ./scripts/podman-dev.sh shell

# Run full tests in Podman dev container
container-test:
    ./scripts/podman-dev.sh test

# Run full tests in Podman with real verified ephapax-cli
container-test-verified-real:
    ./scripts/podman-dev.sh test-verified-real

# Run benchmark dry-run in Podman dev container
container-bench:
    ./scripts/podman-dev.sh bench

# Run benchmark dry-run in Podman with real verified ephapax-cli
container-bench-verified-real:
    ./scripts/podman-dev.sh bench-verified-real

# Install pinned real ephapax-cli in Podman dev container
container-install-ephapax-cli:
    ./scripts/podman-dev.sh install-ephapax-cli

# Verify real verified backend mode in Podman dev container
container-backend-verified-real:
    ./scripts/podman-dev.sh backend-verified-real

# Stop Podman dev service
container-down:
    ./scripts/podman-dev.sh down
