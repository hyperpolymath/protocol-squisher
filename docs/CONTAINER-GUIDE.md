# Container Guide (Podman)

Protocol Squisher now includes a Podman-native developer container for reproducible builds, tests, and benchmark dry-runs.

## Prerequisites

- Podman
- either `podman-compose` or `podman compose` plugin

## Quick Start

```bash
# Build image and start service
./scripts/podman-dev.sh build
./scripts/podman-dev.sh up

# Open shell in container
./scripts/podman-dev.sh shell
```

## Reproducible Workflows

```bash
# Run full test suite
./scripts/podman-dev.sh test

# Validate benchmarks compile
./scripts/podman-dev.sh bench

# Run tests/bench with real ephapax-cli backend (after install)
./scripts/podman-dev.sh test-verified-real
./scripts/podman-dev.sh bench-verified-real

# Compile smoke test (Rust -> Protobuf)
./scripts/podman-dev.sh compile-smoke

# Backend mode checks
./scripts/podman-dev.sh backend-stub
./scripts/podman-dev.sh backend-verified-sim
```

## Direct compose commands

```bash
podman-compose -f podman-compose.yml run --rm dev cargo test --all --no-fail-fast
podman-compose -f podman-compose.yml run --rm dev cargo bench --no-run
# equivalent with podman compose:
podman compose -f podman-compose.yml run --rm dev cargo test --all --no-fail-fast
```

## Verified Backend in Podman

### Simulated verified mode (CI parity)

Use the bundled mock CLI to exercise the verified backend path:

```bash
./scripts/podman-dev.sh backend-verified-sim
./scripts/podman-dev.sh compile-smoke-verified-sim
```

### Real verified mode

1. Install pinned `ephapax-cli` into the repo:

```bash
./scripts/podman-dev.sh install-ephapax-cli
```

The installer is cached. Re-running the same pinned commit/toolchain is a no-op unless
`EPHAPAX_INSTALL_FORCE=1` is set.

2. Run verified checks in container:

```bash
./scripts/podman-dev.sh test-verified-real
./scripts/podman-dev.sh bench-verified-real
./scripts/podman-dev.sh backend-verified-real
./scripts/podman-dev.sh compile-smoke-verified-real
```

If your binary is in a different in-container location, set:

```bash
EPHAPAX_CLI_CONTAINER_PATH=/workspace/your/path/ephapax-cli ./scripts/podman-dev.sh backend-verified-real
```

To override installer source (advanced):

```bash
EPHAPAX_COMMIT=<commit> EPHAPAX_REPO_URL=<repo-url> ./scripts/podman-dev.sh install-ephapax-cli
```

To override installer build toolchain:

```bash
EPHAPAX_BUILD_TOOLCHAIN=1.89.0 ./scripts/podman-dev.sh install-ephapax-cli
```

To force reinstall even when cache metadata matches:

```bash
EPHAPAX_INSTALL_FORCE=1 ./scripts/podman-dev.sh install-ephapax-cli
```

## Notes

- The image installs `python3` and `pydantic` so Python analyzer paths work consistently.
- Stub mode remains the default until an `EPHAPAX_CLI` path is provided and functional.
- Persistent volumes cache Rustup toolchains, Cargo registry/git, and `target/` to improve repeat run times.
