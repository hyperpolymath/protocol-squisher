# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

# Coq proof compilation for Protocol Squisher.
#
# Usage:
#   make check    — Compile all proofs (verifies they type-check)
#   make clean    — Remove compiled artefacts

COQC := coqc
COQFLAGS := -Q . ProtocolSquisher

SOURCES := Types.v ConcordeSafety.v CarriesInvariant.v
OBJECTS := $(SOURCES:.v=.vo)

.PHONY: check clean

check: $(OBJECTS)
	@echo "All Coq proofs verified."

Types.vo: Types.v
	$(COQC) $(COQFLAGS) $<

ConcordeSafety.vo: ConcordeSafety.v Types.vo
	$(COQC) $(COQFLAGS) $<

CarriesInvariant.vo: CarriesInvariant.v Types.vo
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
