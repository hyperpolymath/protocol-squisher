;; SPDX-License-Identifier: PMPL-1.0-or-later
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

;; Ephapax Cryptographic Security Standards
;; These standards apply to all cryptographic operations in ephapax-ir,
;; including WASM codegen, any future network protocols, and build artifacts.

(define user-security-requirements
  '(
    ;; Category, Algorithm/Standard, NIST/FIPS Standard, Notes
    (PasswordHashing "Argon2id (512 MiB, 8 iter, 4 lanes)" "—" "Max memory/iterations for GPU/ASIC resistance; aligns with proactive security stance.")
    (GeneralHashing "SHAKE3-512 (512-bit output)" "FIPS 202" "Post-quantum; use for provenance, key derivation, and long-term storage.")
    (PQSignatures "Dilithium5-AES (hybrid)" "ML-DSA-87 (FIPS 204)" "Hybrid with AES-256 for belt-and-suspenders security. SPHINCS+ as conservative backup.")
    (PQKeyExchange "Kyber-1024 + SHAKE256-KDF" "ML-KEM-1024 (FIPS 203)" "Kyber-1024 for KEM, SHAKE256 for key derivation. SPHINCS+ as backup.")
    (ClassicalSigs "Ed448 + Dilithium5 (hybrid)" "—" "Ed448 for classical compatibility; Dilithium5 for PQ. SPHINCS+ as backup. Terminate Ed25519/SHA-1 immediately.")
    (Symmetric "XChaCha20-Poly1305 (256-bit key)" "—" "Larger nonce space; 256-bit keys for quantum margin.")
    (KeyDerivation "HKDF-SHAKE512" "FIPS 202" "Post-quantum KDF; use with all secret key material.")
    (RNG "ChaCha20-DRBG (512-bit seed)" "SP 800-90Ar1" "CSPRNG for deterministic, high-entropy needs.")
    (UserFriendlyHashNames "Base32(SHAKE256(hash)) → Wordlist" "—" "Memorable, deterministic mapping (e.g., \"Gigantic-Giraffe-7\" for drivers).")
    (DatabaseHashing "BLAKE3 (512-bit) + SHAKE3-512" "—" "BLAKE3 for speed, SHAKE3-512 for long-term storage (semantic XML/ARIA tags).")
    (SemanticXMLGraphQL "Virtuoso (VOS) + SPARQL 1.2" "—" "Supports WCAG 2.3 AAA, ARIA, and formal verification for accessibility/compliance.")
    (VMExecution "GraalVM (with formal verification)" "—" "Aligns with preference for introspective, reversible design.")
    (ProtocolStack "QUIC + HTTP/3 + IPv6 (IPv4 disabled)" "—" "Terminate HTTP/1.1, IPv4, and SHA-1 per \"danger zone\" policy.")
    (Accessibility "WCAG 2.3 AAA + ARIA + Semantic XML" "—" "CSS-first, HTML-second; full compliance with accessibility requirements.")
    (Fallback "SPHINCS+" "—" "Conservative PQ backup for all hybrid classical+PQ systems; use if primary PQ algorithm is ever compromised.")
    (FormalVerification "Coq/Isabelle (for crypto primitives)" "—" "Proactive attestation and transparent logic per system design principles.")
  )
)

;; Application to Ephapax Compiler/IR:
;;
;; 1. WASM Codegen Security:
;;    - All hash functions in generated WASM: BLAKE3 or SHAKE3-512
;;    - No SHA-1, SHA-256, or other legacy hashes
;;    - Cryptographic imports follow XChaCha20-Poly1305 for symmetric ops
;;
;; 2. Build Artifacts:
;;    - Binary hashes: SHAKE3-512 (512-bit)
;;    - Provenance attestation: Dilithium5-AES signatures
;;    - SBOM generation: signed with Ed448 + Dilithium5 hybrid
;;
;; 3. Linear Type System Security:
;;    - Linear types enforce single-use semantics for secrets
;;    - Prevents accidental key material duplication
;;    - Formal verification via Idris2 ABI layer
;;
;; 4. Future Network Protocols (if added):
;;    - QUIC + HTTP/3 only (no HTTP/1.1, no HTTP/2 fallback)
;;    - IPv6 only (IPv4 disabled)
;;    - Kyber-1024 for key exchange
;;    - Dilithium5-AES for signatures
;;
;; 5. RNG in Compiler:
;;    - Use ChaCha20-DRBG for any deterministic randomness
;;    - Example: generating unique symbol names, WASM section IDs
;;
;; 6. Documentation Hashes:
;;    - Source file integrity: SHAKE3-512
;;    - User-facing hashes: Base32(SHAKE256) → wordlist for readability

;; Immediate Action Items:
;; - Audit existing crates for SHA-1, SHA-256, MD5 usage → replace with BLAKE3/SHAKE3-512
;; - Ensure no Ed25519 usage (upgrade to Ed448)
;; - Add formal verification step for any crypto primitives added to stdlib
;; - Document in SECURITY.md that SHA-1 is prohibited

;; Media Type: application/vnd.hyperpolymath.security-standards+scm
