-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Trustfile - cryptographic, provenance, and algebraic invariant verification
-- protocol-squisher
-- Author: Jonathan D.A. Jewell

module Trustfile where

import Control.Monad (forM)
import System.Directory (doesFileExist)
import System.Environment (lookupEnv)
import System.Exit (exitFailure, exitSuccess)
import System.Process (readProcessWithExitCode)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CRYPTOGRAPHIC & PROVENANCE VERIFICATION (existing)
-- ═══════════════════════════════════════════════════════════════════════════════

policyPath :: FilePath
policyPath = "policy/policy.ncl"

policyHashPath :: FilePath
policyHashPath = "policy/policy.ncl.sha256"

schemaPath :: FilePath
schemaPath = "schema/schema.json"

schemaSigPath :: FilePath
schemaSigPath = "schema/schema.sig"

schemaPubPath :: FilePath
schemaPubPath = "schema/schema.pub"

driverPaths :: [FilePath]
driverPaths = ["drivers/gateway-driver.bin"]

migrationsPath :: FilePath
migrationsPath = "migrations/provenance.json"

migrationsSigPath :: FilePath
migrationsSigPath = "migrations/provenance.sig"

migrationsPubPath :: FilePath
migrationsPubPath = "migrations/provenance.pub"

runCmd :: String -> [String] -> IO Bool
runCmd cmd args = do
  (code, _out, _err) <- readProcessWithExitCode cmd args ""
  pure (code == mempty)

readFirstWord :: FilePath -> IO (Maybe String)
readFirstWord path = do
  exists <- doesFileExist path
  if not exists
    then pure Nothing
    else do
      content <- readFile path
      pure (case words content of
        [] -> Nothing
        (w:_) -> Just w)

verifyPolicyHash :: IO Bool
verifyPolicyHash = do
  expected <- readFirstWord policyHashPath
  case expected of
    Nothing -> pure False
    Just hash -> do
      (code, out, _err) <- readProcessWithExitCode "sha256sum" [policyPath] ""
      if code /= mempty
        then pure False
        else do
          let actual = case words out of
                [] -> ""
                (w:_) -> w
          pure (actual == hash)

verifySchemaSignature :: IO Bool
verifySchemaSignature = do
  filesOk <- and <$> mapM doesFileExist [schemaPath, schemaSigPath, schemaPubPath]
  if not filesOk
    then pure False
    else runCmd "openssl" ["dgst", "-sha256", "-verify", schemaPubPath, "-signature", schemaSigPath, schemaPath]

verifyKyber1024Signatures :: IO Bool
verifyKyber1024Signatures = do
  cmd <- lookupEnv "KYBER_VERIFY_CMD"
  let kyberCmd = maybe "kyber-verify" id cmd
  results <- forM driverPaths $ \path -> do
    let sig = path <> ".sig"
    let pub = path <> ".pub"
    filesOk <- and <$> mapM doesFileExist [path, sig, pub]
    if not filesOk
      then pure False
      else runCmd kyberCmd ["--pub", pub, "--sig", sig, "--file", path]
  pure (and results)

verifyMigrationProvenance :: IO Bool
verifyMigrationProvenance = do
  filesOk <- and <$> mapM doesFileExist [migrationsPath, migrationsSigPath, migrationsPubPath]
  if not filesOk
    then pure False
    else runCmd "openssl" ["dgst", "-sha256", "-verify", migrationsPubPath, "-signature", migrationsSigPath, migrationsPath]

-- ═══════════════════════════════════════════════════════════════════════════════
-- VISION COMMITMENT (18-month plan)
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- This project is committed to a 6-phase, 18-month transformation from
-- format converter to universal data shape reasoning engine.
--
-- Source of truth: VISION-18-MONTHS.md
--
-- Phase 1 (Months 1-3):  Shape IR with dependent types, linearity, information metrics
-- Phase 2 (Months 4-6):  Algebra — category structure, adapter composition, pathfinding
-- Phase 3 (Months 7-9):  Eat the World — databases, APIs, type systems, memory layouts
-- Phase 4 (Months 10-12): Temporal dimension — schema evolution, compatibility forecasting
-- Phase 5 (Months 13-15): Visual language — TUI explorer, PanLL integration, web interface
-- Phase 6 (Months 16-18): Paper (POPL/ICFP) + release (CLI, crates.io, server)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SHAPE IR INVARIANTS (must always hold)
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- These are algebraic properties that the shape-ir crate must satisfy at all
-- times. Breaking any of these is a release-blocking defect.
--
-- 1. Transport Class Algebra
--    - TransportClass forms a bounded join-semilattice
--    - Concorde is the identity element (bottom): compose(Concorde, x) = x
--    - Wheelbarrow is the top element: compose(x, Wheelbarrow) = Wheelbarrow
--    - Composition is commutative: compose(a, b) = compose(b, a)
--    - Composition is associative: compose(compose(a, b), c) = compose(a, compose(b, c))
--    - Ordering: Concorde < Business < Economy < Wheelbarrow
--    - Compose = max in the ordering
--
-- 2. Linearity Lattice
--    - Linearity forms a four-point lattice from (can_copy, can_drop) boolean pair
--    - Unrestricted = (true, true), Linear = (false, false)
--    - Affine = (false, true), Relevant = (true, false)
--    - Meet is commutative: meet(a, b) = meet(b, a)
--    - Meet is associative: meet(meet(a, b), c) = meet(a, meet(b, c))
--    - Linear is the bottom (most restrictive)
--    - Unrestricted is the top (least restrictive)
--
-- 3. Self-Comparison
--    - Comparing any Shape to itself always yields Concorde transport class
--    - This is the reflexivity property of the comparison relation
--
-- 4. Information Content
--    - InformationContent separates min_bits/max_bits/fixed_size/cardinality
--    - min_bits <= max_bits (always)
--    - fixed_size implies min_bits == max_bits
--    - Enables precise morphism classification (isomorphism, embedding, projection)

-- Verify shape-ir algebraic invariants via cargo test
verifyShapeIrInvariants :: IO Bool
verifyShapeIrInvariants = do
  transportOk <- runCmd "cargo" ["test", "-p", "shape-ir", "--", "transport_class", "--quiet"]
  linearityOk <- runCmd "cargo" ["test", "-p", "shape-ir", "--", "linearity", "--quiet"]
  selfCompareOk <- runCmd "cargo" ["test", "-p", "shape-ir", "--", "self_comparison_is_concorde", "--quiet"]
  pure (and [transportOk, linearityOk, selfCompareOk])

-- ═══════════════════════════════════════════════════════════════════════════════
-- PHASE QUALITY GATES
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- Each phase has quality gates that must pass before the phase is considered complete.
--
-- Phase 1 Gates:
--   ✓ All 11 Shape constructors implemented (Unit, Atom, Product, Sum, Dependent, Recursive, Ref, Sequence, Optional, Map, Annotated)
--   ✓ Transport class algebra: all semilattice laws hold (property tests)
--   ✓ Linearity lattice: all lattice laws hold (property tests)
--   ✓ Self-comparison reflexivity: proven for all constructors (property test)
--   ✓ Information content: min <= max, fixed_size consistency (property tests)
--   ✓ Comparison engine: alpha-equivalence for recursive types
--   ✓ Shape extraction: Canonical IR → Shape IR bridge
--   ✓ MorphismMetrics: quantitative morphism classification
--   ✓ CLI integration: `shape extract` and `shape compare` commands
--   ✓ Criterion benchmarks established
--   ✓ Zero clippy warnings on shape-ir
--   ✓ All existing 937 tests still pass + 165 new shape-ir tests (no regressions)
--   ✓ Documentation pass: #![warn(missing_docs)], all public APIs documented
--   ✓ Property tests expanded: 36 property tests covering extraction, category laws, pathfinding
--
-- Phase 2 Gates:
--   ✓ Category laws: identity, associativity of composition (unit + property tested)
--   ✓ Adapter composition: A->B + B->C = A->C (compose_arrows, compose_path)
--   ✓ Roundtrip property: roundtrip_class verifies Concorde/Economy classification
--   ✓ Pathfinding: Dijkstra minimax finds minimum-cost adapter chain
--   ✓ All Phase 1 invariants still hold (165 tests, clippy clean, 0 doc warnings)
--   ✓ Symmetric monoidal structure: Product (tensor) + Coproduct (sum) + Unit
--   ✓ CLI `shape graph` subcommand wired and working
--   - Remaining: Formal Idris2 verification, functor/natural transformation abstractions
--
-- Phase 3 Gates:
--   - Each new domain (DB, API, types, memory, config) has a Shape extractor
--   - Each extractor produces valid Shapes (passes invariant checks)
--   - Existing 13 format analyzers still work via Shape extraction
--   - All Phase 1+2 invariants still hold
--
-- Phase 4 Gates:
--   - Temporal morphisms compose correctly
--   - Version classification matches semver semantics
--   - Evolution pathfinder produces valid migration sequences
--   - All Phase 1+2+3 invariants still hold
--
-- Phase 5 Gates:
--   - TUI renders all Shape constructors
--   - PanLL Panel-L/N/W integration working
--   - Visual notation is unambiguous (no two shapes render identically)
--   - All Phase 1-4 invariants still hold
--
-- Phase 6 Gates:
--   - Paper accepted or submitted to POPL/ICFP
--   - CLI `shape` command handles all documented operations
--   - crates.io publication successful
--   - All Phase 1-5 invariants still hold

-- Verify phase 1 quality gates
verifyPhase1Gates :: IO Bool
verifyPhase1Gates = do
  invariantsOk <- verifyShapeIrInvariants
  allTests <- runCmd "cargo" ["test", "-p", "shape-ir", "--quiet"]
  clippyOk <- runCmd "cargo" ["clippy", "-p", "shape-ir", "--", "-D", "warnings"]
  noRegressions <- runCmd "cargo" ["test", "--workspace", "--quiet"]
  pure (and [invariantsOk, allTests, clippyOk, noRegressions])

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAIN
-- ═══════════════════════════════════════════════════════════════════════════════

main :: IO ()
main = do
  -- Cryptographic verification
  policyOk <- verifyPolicyHash
  schemaOk <- verifySchemaSignature
  driversOk <- verifyKyber1024Signatures
  migrationsOk <- verifyMigrationProvenance
  -- Algebraic invariants
  shapeOk <- verifyShapeIrInvariants
  if and [policyOk, schemaOk, driversOk, migrationsOk, shapeOk]
    then exitSuccess
    else exitFailure
