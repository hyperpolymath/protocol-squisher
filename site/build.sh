#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# build.sh — Build the protocol-squisher.net site using ddraig-ssg
#
# Prerequisites:
#   - Idris 2 >= 0.8.0 installed (via pack or system package)
#   - ddraig-ssg compiled: idris2 Ddraig.idr -o ddraig
#
# Usage:
#   ./build.sh                    # Build using default ddraig location
#   DDRAIG=/path/to/ddraig ./build.sh  # Build with custom ddraig path
#
# The script looks for ddraig-ssg in these locations (in order):
#   1. $DDRAIG environment variable
#   2. ../ssg-collection/stubs/ddraig/build/exec/ddraig (sibling repo)
#   3. ddraig on $PATH

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONTENT_DIR="${SCRIPT_DIR}/content"
OUTPUT_DIR="${SCRIPT_DIR}/output"
TEMPLATE_FILE="${SCRIPT_DIR}/templates/main.html"

# Locate ddraig-ssg binary
find_ddraig() {
    if [[ -n "${DDRAIG:-}" ]] && [[ -x "${DDRAIG}" ]]; then
        echo "${DDRAIG}"
        return 0
    fi

    # Check sibling repo (standard hyperpolymath layout)
    local sibling
    sibling="$(cd "${SCRIPT_DIR}/../.." && pwd)/ssg-collection/stubs/ddraig/build/exec/ddraig"
    if [[ -x "${sibling}" ]]; then
        echo "${sibling}"
        return 0
    fi

    # Check PATH
    if command -v ddraig &>/dev/null; then
        command -v ddraig
        return 0
    fi

    return 1
}

DDRAIG_BIN="$(find_ddraig)" || {
    echo "Error: ddraig-ssg not found."
    echo ""
    echo "To build ddraig-ssg:"
    echo "  cd /path/to/ssg-collection/stubs/ddraig"
    echo "  idris2 Ddraig.idr -o ddraig"
    echo ""
    echo "Or set DDRAIG=/path/to/ddraig and re-run this script."
    exit 1
}

echo "protocol-squisher.net site builder"
echo "==================================="
echo "  ddraig:   ${DDRAIG_BIN}"
echo "  content:  ${CONTENT_DIR}"
echo "  output:   ${OUTPUT_DIR}"
echo "  template: ${TEMPLATE_FILE}"
echo ""

# Clean previous output
rm -rf "${OUTPUT_DIR}"
mkdir -p "${OUTPUT_DIR}"

# Build the site
"${DDRAIG_BIN}" build "${CONTENT_DIR}" "${OUTPUT_DIR}" "${TEMPLATE_FILE}"

echo ""
echo "Done. Site written to ${OUTPUT_DIR}/"
echo "To preview: python3 -m http.server 8000 -d ${OUTPUT_DIR}"
