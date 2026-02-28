#!/bin/bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

# Run PyO3 integration tests
# This script builds the Python extension and runs pytest

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║         PyO3 Integration Test Runner                         ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo

# Check for required tools
echo "Checking dependencies..."

if ! command -v python3 &> /dev/null; then
    echo "Error: python3 not found"
    exit 1
fi

if ! command -v maturin &> /dev/null; then
    echo "maturin not found, installing..."
    pip install maturin
fi

if ! python3 -c "import pytest" &> /dev/null; then
    echo "pytest not found, installing..."
    pip install pytest
fi

echo "✓ Dependencies OK"
echo

# Create/activate virtual environment
if [ ! -d ".venv" ]; then
    echo "Creating virtual environment..."
    python3 -m venv .venv
fi

echo "Activating virtual environment..."
source .venv/bin/activate

# Install pytest in venv
if ! python3 -c "import pytest" &> /dev/null; then
    echo "Installing pytest in venv..."
    pip install pytest
fi

# Build the extension
echo "Building Python extension with maturin..."
maturin develop

echo
echo "✓ Build complete"
echo

# Run tests
echo "Running pytest..."
echo "────────────────────────────────────────────────────────────────"
python3 -m pytest python/tests -v

echo
echo "════════════════════════════════════════════════════════════════"
echo "✓ All integration tests passed!"
echo "════════════════════════════════════════════════════════════════"
