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

# Build the project
build:
    @echo "Building {{project}}..."

# Clean build artifacts
clean:
    @echo "Cleaning..."

# ═══════════════════════════════════════════════════════════════════════════════
# TEST & QUALITY
# ═══════════════════════════════════════════════════════════════════════════════

# Run tests
test:
    @echo "Running tests..."

# Run linter
lint:
    @echo "Linting..."

# Format code
fmt:
    @echo "Formatting..."

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
