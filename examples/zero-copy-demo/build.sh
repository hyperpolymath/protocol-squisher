#!/bin/bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Build the zero-copy-demo PyO3 library

set -e

echo "Building zero-copy-demo..."

# Check if maturin is installed
if ! command -v maturin &> /dev/null; then
    echo "ERROR: maturin not found!"
    echo "Install with: pip install maturin"
    exit 1
fi

# Build with maturin
echo "Running maturin develop..."
maturin develop --release

echo ""
echo "✓ Build complete!"
echo ""
echo "Run the demo with:"
echo "  python test.py"
echo ""
echo "Or analyze with protocol-squisher:"
echo "  cargo run -p protocol-squisher-cli -- analyze --rust src/lib.rs"
