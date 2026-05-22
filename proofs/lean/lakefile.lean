-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

import Lake
open Lake DSL

package «protocol-squisher-proofs» where
  version := v!"1.1.0"

lean_lib Proofs where
  roots := #[`concorde_safety]
