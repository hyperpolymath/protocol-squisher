#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

set -euo pipefail

echo "Building mixed-transport example..."
maturin develop

echo ""
echo "Build complete! You can now run:"
echo "  python test.py"
