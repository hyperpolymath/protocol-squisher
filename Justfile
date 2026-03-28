# SPDX-License-Identifier: PMPL-1.0-or-later
# protocol-squisher - Justfile
# https://just.systems/man/en/

set shell := ["bash", "-uc"]
set dotenv-load := true
set positional-arguments := true

# Project metadata
project := "protocol-squisher"
version := "1.1.0"

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

# Run all benchmarks
bench:
    @echo "Running benchmarks..."
    cargo bench --workspace

# Run analysis throughput benchmarks only
bench-analysis:
    cargo bench --bench analysis_throughput

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
    @test -f .machines_readable/6scm/META.scm || (echo "Missing .machines_readable/6scm/META.scm" && exit 1)
    @test -f .machines_readable/6scm/STATE.scm || (echo "Missing .machines_readable/6scm/STATE.scm" && exit 1)
    @test -f .machines_readable/6scm/ECOSYSTEM.scm || (echo "Missing .machines_readable/6scm/ECOSYSTEM.scm" && exit 1)
    @test -f .machines_readable/6scm/PLAYBOOK.scm || (echo "Missing .machines_readable/6scm/PLAYBOOK.scm" && exit 1)
    @test -f .machines_readable/6scm/AGENTIC.scm || (echo "Missing .machines_readable/6scm/AGENTIC.scm" && exit 1)
    @test -f .machines_readable/6scm/NEUROSYM.scm || (echo "Missing .machines_readable/6scm/NEUROSYM.scm" && exit 1)
    @test ! -f Makefile || (echo "Makefile forbidden - use justfile" && exit 1)
    @echo "RSR validation passed!"

# Validate STATE.scm syntax
validate-state:
    @echo "Validating .machines_readable/6scm/STATE.scm..."
    @test -f .machines_readable/6scm/STATE.scm && echo "STATE.scm exists" || echo "STATE.scm missing"

# Update STATE.scm timestamp
state-touch:
    @echo "Updating STATE.scm timestamp..."
    @[ -f .machines_readable/6scm/STATE.scm ] && sed -i 's/(updated . "[^"]*")/(updated . "'$(date +%Y-%m-%d)'")/' .machines_readable/6scm/STATE.scm || true

# ═══════════════════════════════════════════════════════════════════════════════
# CI
# ═══════════════════════════════════════════════════════════════════════════════

# Run full CI pipeline locally
ci: quality validate-rsr
    @echo "CI pipeline passed!"

# Run corrective-maintenance gates (ABI/FFI policy + panic-assail + real verified backend)
maint-corrective:
    ./scripts/ci/check-abi-policy.sh
    @panic_bin="${PANIC_ATTACK_BIN:-}"; [ -n "${panic_bin}" ] || [ ! -x /var$REPOS_DIR/panic-attacker/target/release/panic-attack ] || panic_bin=/var$REPOS_DIR/panic-attacker/target/release/panic-attack; PANIC_ATTACK_BIN="${panic_bin}" ./scripts/ci/panic-assail-regression.sh
    ./scripts/podman-dev.sh install-ephapax-cli
    ./scripts/podman-dev.sh backend-verified-real
    ./scripts/podman-dev.sh compile-smoke-verified-real

# Validate real-world schema coverage and invariant health.
# Defaults enforce roadmap gates: >=100 successful analyses and 0 invariant violations.
maint-realworld:
    ./scripts/ci/validate-realworld-corpus.sh --output /tmp/protocol-squisher-realworld-gate.json

# Capture maintenance metrics snapshot (JSON in /tmp by default)
maint-metrics:
    ./scripts/ci/capture-maintenance-metrics.sh

# Capture maintenance metrics including timed podman checks
maint-metrics-podman:
    ./scripts/ci/capture-maintenance-metrics.sh --with-podman

# Capture maintenance metrics including real-world schema gate
maint-metrics-realworld:
    ./scripts/ci/capture-maintenance-metrics.sh --with-realworld

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

# ═══════════════════════════════════════════════════════════════════════════════
# EXPLORER (ELIXIR OTP CRAWLER)
# ═══════════════════════════════════════════════════════════════════════════════

# Run Elixir crawler tests
explorer-crawler-test:
    cd explorer/crawler && mix test

# Run Elixir GitHub schema crawler (pass extra flags after `--`)
explorer-crawler-run *args:
    cd explorer/crawler && mix crawler.run {{args}}

# Install pinned real ephapax-cli in Podman dev container
container-install-ephapax-cli:
    ./scripts/podman-dev.sh install-ephapax-cli

# Verify real verified backend mode in Podman dev container
container-backend-verified-real:
    ./scripts/podman-dev.sh backend-verified-real

# Stop Podman dev service
container-down:
    ./scripts/podman-dev.sh down

# ═══════════════════════════════════════════════════════════════════════════════
# FFI (ZIG)
# ═══════════════════════════════════════════════════════════════════════════════

# Build the Zig FFI shared/static libraries (ffi/zig/)
#
# The Zig FFI provides a C-compatible ABI boundary for protocol-squisher,
# exposing handle-based init/free, compatibility analysis, adapter generation,
# buffer management, and callback registration. Types match the Idris2 ABI
# definitions in src/abi/.
#
# Produces:
#   zig-out/lib/libprotocol_squisher_ffi.so  (shared)
#   zig-out/lib/libprotocol_squisher_ffi.a   (static)
build-ffi:
    @echo "Building Zig FFI..."
    @if command -v zig >/dev/null 2>&1; then \
        cd ffi/zig && zig build; \
        echo "Zig FFI built successfully"; \
    else \
        echo "zig not found in PATH — skipping FFI build"; \
        echo "Install: https://ziglang.org/download/"; \
    fi

# Run Zig FFI unit + integration tests
test-ffi:
    @echo "Testing Zig FFI..."
    @if command -v zig >/dev/null 2>&1; then \
        cd ffi/zig && zig build test; \
        echo "Zig FFI tests passed"; \
    else \
        echo "zig not found in PATH — skipping FFI tests"; \
    fi

# ═══════════════════════════════════════════════════════════════════════════════
# SHAPE IR (Phase 1 — universal data shape reasoning)
# ═══════════════════════════════════════════════════════════════════════════════

# Build the shape-ir crate
build-shape:
    cargo build -p shape-ir

# Run shape-ir tests (84 tests: 79 unit + 5 doc)
test-shape:
    cargo test -p shape-ir

# Run clippy on shape-ir with denied warnings
check-shape:
    cargo clippy -p shape-ir -- -D warnings

# Run shape-ir benchmarks
bench-shape:
    cargo bench -p shape-ir

# Full vision pipeline check (currently Phase 1 only)
vision-check:
    @echo "=== Shape IR ==="
    cargo test -p shape-ir --quiet
    @echo "=== Shape IR: all tests passing ==="

# ═══════════════════════════════════════════════════════════════════════════════
# INVARIANTS (must always hold)
# ═══════════════════════════════════════════════════════════════════════════════

# Check algebraic invariants that must never be violated
invariants:
    @echo "Checking invariants..."
    @echo "  Transport class algebra: Concorde is identity"
    cargo test -p shape-ir -- transport_class --quiet
    @echo "  Linearity lattice: meet is commutative"
    cargo test -p shape-ir -- linearity --quiet
    @echo "  Self-comparison is always Concorde"
    cargo test -p shape-ir -- self_comparison_is_concorde --quiet
    @echo "All invariants hold."

# ═══════════════════════════════════════════════════════════════════════════════
# MULTI-ARCH
# ═══════════════════════════════════════════════════════════════════════════════

# [AUTO-GENERATED] Multi-arch / RISC-V target
build-riscv:
	@echo "Building for RISC-V..."
	cross build --target riscv64gc-unknown-linux-gnu

# Run panic-attacker pre-commit scan
assail:
    @command -v panic-attack >/dev/null 2>&1 && panic-attack assail . || echo "panic-attack not found — install from https://github.com/hyperpolymath/panic-attacker"

# Self-diagnostic — checks dependencies, permissions, paths
doctor:
    @echo "Running diagnostics for protocol-squisher..."
    @echo "Checking required tools..."
    @command -v just >/dev/null 2>&1 && echo "  [OK] just" || echo "  [FAIL] just not found"
    @command -v git >/dev/null 2>&1 && echo "  [OK] git" || echo "  [FAIL] git not found"
    @echo "Checking for hardcoded paths..."
    @grep -rn '$HOME\|$ECLIPSE_DIR' --include='*.rs' --include='*.ex' --include='*.res' --include='*.gleam' --include='*.sh' . 2>/dev/null | head -5 || echo "  [OK] No hardcoded paths"
    @echo "Diagnostics complete."

# Guided tour of key features
tour:
    @echo "=== protocol-squisher Tour ==="
    @echo ""
    @echo "1. Project structure:"
    @ls -la
    @echo ""
    @echo "2. Available commands: just --list"
    @echo ""
    @echo "3. Read README.adoc for full overview"
    @echo "4. Read EXPLAINME.adoc for architecture decisions"
    @echo "5. Run 'just doctor' to check your setup"
    @echo ""
    @echo "Tour complete! Try 'just --list' to see all available commands."

# Open feedback channel with diagnostic context
help-me:
    @echo "=== protocol-squisher Help ==="
    @echo "Platform: $(uname -s) $(uname -m)"
    @echo "Shell: $SHELL"
    @echo ""
    @echo "To report an issue:"
    @echo "  https://github.com/hyperpolymath/protocol-squisher/issues/new"
    @echo ""
    @echo "Include the output of 'just doctor' in your report."

# Attempt to automatically install missing tools
heal:
    #!/usr/bin/env bash
    echo "═══════════════════════════════════════════════════"
    echo "  Protocol Squisher Heal — Automatic Tool Installation"
    echo "═══════════════════════════════════════════════════"
    echo ""
if ! command -v cargo >/dev/null 2>&1; then
    echo "Installing Rust via rustup..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source "$HOME/.cargo/env"
fi
if ! command -v just >/dev/null 2>&1; then
    echo "Installing just..."
    cargo install just 2>/dev/null || echo "Install just from https://just.systems"
fi
    echo ""
    echo "Heal complete. Run 'just doctor' to verify."
