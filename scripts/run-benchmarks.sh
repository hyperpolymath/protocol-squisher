#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

# Run protocol-squisher benchmarks with comprehensive reporting

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${PROJECT_ROOT}"

CRITERION_DIR="target/criterion"
REPORT_DIR="benchmark-reports"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

print_header() {
    echo -e "${BLUE}===================================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}===================================================${NC}"
}

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

show_usage() {
    cat <<'EOF'
Usage: scripts/run-benchmarks.sh [OPTIONS]

Run protocol-squisher performance benchmarks.

OPTIONS:
    -h, --help              Show this help message
    -a, --all               Run all benchmarks (default)
    -t, --transport         Run transport class benchmarks only
    -c, --containers        Run container operation benchmarks only
    -g, --generated         Run generated vs handwritten comparison only
    -o, --optimizer         Run optimizer benchmarks only
    -q, --quick             Quick mode (reduced sample size)
    -s, --summary           Generate summary report
    -v, --view              View HTML reports in browser
    --baseline NAME         Save results as baseline NAME
    --compare BASELINE      Compare against baseline

EXAMPLES:
    # Run all benchmarks
    scripts/run-benchmarks.sh --all

    # Run only transport class benchmarks
    scripts/run-benchmarks.sh --transport

    # Quick run for development
    scripts/run-benchmarks.sh --quick --transport

    # Create baseline for comparison
    scripts/run-benchmarks.sh --all --baseline main

    # Compare against baseline
    scripts/run-benchmarks.sh --all --compare main

    # Run and view results
    scripts/run-benchmarks.sh --all --view
EOF
}

# Parse arguments
RUN_ALL=true
RUN_TRANSPORT=false
RUN_CONTAINERS=false
RUN_GENERATED=false
RUN_OPTIMIZER=false
QUICK_MODE=false
GENERATE_SUMMARY=false
VIEW_REPORTS=false
BASELINE_NAME=""
COMPARE_BASELINE=""

while [[ $# -gt 0 ]]; do
    case "${1}" in
        -h|--help)
            show_usage
            exit 0
            ;;
        -a|--all)
            RUN_ALL=true
            shift
            ;;
        -t|--transport)
            RUN_ALL=false
            RUN_TRANSPORT=true
            shift
            ;;
        -c|--containers)
            RUN_ALL=false
            RUN_CONTAINERS=true
            shift
            ;;
        -g|--generated)
            RUN_ALL=false
            RUN_GENERATED=true
            shift
            ;;
        -o|--optimizer)
            RUN_ALL=false
            RUN_OPTIMIZER=true
            shift
            ;;
        -q|--quick)
            QUICK_MODE=true
            shift
            ;;
        -s|--summary)
            GENERATE_SUMMARY=true
            shift
            ;;
        -v|--view)
            VIEW_REPORTS=true
            shift
            ;;
        --baseline)
            if [[ $# -lt 2 ]]; then
                print_error "--baseline requires a value"
                exit 1
            fi
            BASELINE_NAME="$2"
            shift 2
            ;;
        --compare)
            if [[ $# -lt 2 ]]; then
                print_error "--compare requires a value"
                exit 1
            fi
            COMPARE_BASELINE="$2"
            shift 2
            ;;
        *)
            print_error "Unknown option: ${1}"
            show_usage
            exit 1
            ;;
    esac
done

# Determine which benchmarks to run
if [[ "${RUN_ALL}" == true ]]; then
    RUN_TRANSPORT=true
    RUN_CONTAINERS=true
    RUN_GENERATED=true
    RUN_OPTIMIZER=true
fi

print_header "Protocol Squisher Benchmarks"

# Check for release mode
print_info "Building in release mode..."
cargo build --release

# Configure criterion
BENCH_ARGS=()
if [[ -n "${BASELINE_NAME}" ]]; then
    BENCH_ARGS+=(--save-baseline "${BASELINE_NAME}")
    print_info "Saving baseline: ${BASELINE_NAME}"
fi

if [[ -n "${COMPARE_BASELINE}" ]]; then
    BENCH_ARGS+=(--baseline "${COMPARE_BASELINE}")
    print_info "Comparing against baseline: ${COMPARE_BASELINE}"
fi

# Quick mode: reduce samples
if [[ "${QUICK_MODE}" == true ]]; then
    print_warn "Quick mode enabled - results may be less precise"
    export CARGO_CRITERION_OPTS="--warm-up-time 1 --measurement-time 3 --sample-size 10"
fi

# Run benchmarks
if [[ "${RUN_TRANSPORT}" == true ]]; then
    print_header "Transport Class Benchmarks"
    print_info "Running Concorde, Business, Economy, and Wheelbarrow tests..."
    cargo bench --bench transport_classes "${BENCH_ARGS[@]}" || {
        print_error "Transport class benchmarks failed"
        exit 1
    }
fi

if [[ "${RUN_CONTAINERS}" == true ]]; then
    print_header "Container Operations Benchmarks"
    print_info "Running Vec, Option, HashMap, and nested container tests..."
    cargo bench --bench container_operations "${BENCH_ARGS[@]}" || {
        print_error "Container operations benchmarks failed"
        exit 1
    }
fi

if [[ "${RUN_GENERATED}" == true ]]; then
    print_header "Generated vs Handwritten Comparison"
    print_info "Comparing generated code against handwritten FFI and raw Rust..."
    cargo bench --bench generated_vs_handwritten "${BENCH_ARGS[@]}" || {
        print_error "Generated vs handwritten benchmarks failed"
        exit 1
    }
fi

if [[ "${RUN_OPTIMIZER}" == true ]]; then
    print_header "Optimizer Benchmarks"
    print_info "Running optimizer comparison tests..."
    cargo bench --bench optimizer_bench "${BENCH_ARGS[@]}" || {
        print_error "Optimizer benchmarks failed"
        exit 1
    }
fi

# Generate summary report
if [[ "${GENERATE_SUMMARY}" == true ]]; then
    print_header "Generating Summary Report"

    mkdir -p "${REPORT_DIR}"
    SUMMARY_FILE="${REPORT_DIR}/summary-$(date +%Y%m%d-%H%M%S).txt"

    {
        echo "Protocol Squisher Benchmark Summary"
        echo "Generated: $(date)"
        echo "========================================"
        echo ""

        if [[ -d "${CRITERION_DIR}" ]]; then
            echo "Benchmark Results Location:"
            echo "  ${CRITERION_DIR}"
            echo ""

            echo "Available Reports:"
            find "${CRITERION_DIR}" -name "index.html" -type f | while IFS= read -r report; do
                rel_path="${report#"${CRITERION_DIR}"/}"
                echo "  - ${rel_path}"
            done
            echo ""

            echo "Performance Targets:"
            echo "  Concorde:       1-2ns    (zero-copy)"
            echo "  Business Class: 10-20ns  (safe widening)"
            echo "  Economy:        50-100ns (allocation)"
            echo "  Wheelbarrow:    100-1000ns (JSON fallback)"
            echo ""
        fi
    } | tee "${SUMMARY_FILE}"

    print_info "Summary saved to: ${SUMMARY_FILE}"
fi

# View reports
if [[ "${VIEW_REPORTS}" == true ]]; then
    print_header "Opening HTML Reports"

    if [[ -f "${CRITERION_DIR}/report/index.html" ]]; then
        print_info "Opening main report in browser..."

        # Detect browser
        if command -v xdg-open &> /dev/null; then
            xdg-open "${CRITERION_DIR}/report/index.html"
        elif command -v open &> /dev/null; then
            open "${CRITERION_DIR}/report/index.html"
        elif command -v firefox &> /dev/null; then
            firefox "${CRITERION_DIR}/report/index.html"
        else
            print_warn "Could not detect browser. Open manually:"
            echo "  file://${PROJECT_ROOT}/${CRITERION_DIR}/report/index.html"
        fi
    else
        print_error "No HTML reports found. Run benchmarks first."
        exit 1
    fi
fi

print_header "Benchmark Complete"
print_info "Results available at: ${CRITERION_DIR}/report/index.html"

# Show quick summary if available
if [[ -f "${CRITERION_DIR}/report/index.html" ]]; then
    echo ""
    echo "Quick Access Links:"
    echo "  Main Report:     file://${PROJECT_ROOT}/${CRITERION_DIR}/report/index.html"
    [[ "${RUN_TRANSPORT}" == true ]] && echo "  Transport Class: file://${PROJECT_ROOT}/${CRITERION_DIR}/Concorde/report/index.html"
    [[ "${RUN_CONTAINERS}" == true ]] && echo "  Containers:      file://${PROJECT_ROOT}/${CRITERION_DIR}/Vec/report/index.html"
    [[ "${RUN_GENERATED}" == true ]] && echo "  Comparison:      file://${PROJECT_ROOT}/${CRITERION_DIR}/Point/report/index.html"
fi

exit 0
