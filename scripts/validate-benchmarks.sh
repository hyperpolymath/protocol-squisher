#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

# Quick validation script for benchmark suite

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"

GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo "==================================================="
echo "Protocol Squisher Benchmark Suite Validation"
echo "==================================================="
echo ""

# Check files exist
echo "Checking files..."
FILES=(
    "benches/transport_classes.rs"
    "benches/container_operations.rs"
    "benches/generated_vs_handwritten.rs"
    "benches/optimizer_bench.rs"
    "benches/README.md"
    "docs/BENCHMARK-QUICKSTART.md"
    "docs/BENCHMARK-RESULTS.md"
    "scripts/run-benchmarks.sh"
    "BENCHMARK-SUITE-SUMMARY.md"
)

for file in "${FILES[@]}"; do
    if [[ -f "$file" ]]; then
        echo -e "${GREEN}✓${NC} $file"
    else
        echo -e "${RED}✗${NC} $file (MISSING)"
        exit 1
    fi
done

echo ""
echo "Checking Cargo.toml..."
if grep -q "transport_classes" Cargo.toml && \
   grep -q "container_operations" Cargo.toml && \
   grep -q "generated_vs_handwritten" Cargo.toml; then
    echo -e "${GREEN}✓${NC} Benchmark entries in Cargo.toml"
else
    echo -e "${RED}✗${NC} Missing benchmark entries in Cargo.toml"
    exit 1
fi

echo ""
echo "Checking script permissions..."
if [[ -x "scripts/run-benchmarks.sh" ]]; then
    echo -e "${GREEN}✓${NC} run-benchmarks.sh is executable"
else
    echo -e "${YELLOW}⚠${NC} run-benchmarks.sh not executable (fixing...)"
    chmod +x scripts/run-benchmarks.sh
fi

echo ""
echo "Testing compilation..."
echo "(This may take a few minutes on first run)"
echo ""

if cargo bench --no-run 2>&1 | tail -5; then
    echo ""
    echo -e "${GREEN}✓${NC} All benchmarks compile successfully"
else
    echo ""
    echo -e "${RED}✗${NC} Compilation failed"
    exit 1
fi

echo ""
echo "==================================================="
echo -e "${GREEN}Validation Complete!${NC}"
echo "==================================================="
echo ""
echo "Benchmark suite is ready to use."
echo ""
echo "Next steps:"
echo "  1. Run quick test:  cargo bench --bench transport_classes Concorde"
echo "  2. Run all tests:   cargo bench"
echo "  3. Use script:      ./scripts/run-benchmarks.sh --all"
echo "  4. Read docs:       cat docs/BENCHMARK-QUICKSTART.md"
echo ""
echo "HTML reports will be in: target/criterion/report/index.html"
echo ""
