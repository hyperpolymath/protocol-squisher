;; SPDX-License-Identifier: PMPL-1.0-or-later
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
;; Security Requirements and Cryptographic Standards for protocol-squisher

(define-module (protocol_squisher security_requirements)
  #:export (cryptographic-standards
            password-hashing
            symmetric-encryption
            asymmetric-encryption
            digital-signatures
            key-derivation
            secure-hashing
            random-number-generation
            post-quantum-cryptography
            applicability-matrix))

;;; Cryptographic Standards
;;; These standards apply to future security-sensitive features

(define cryptographic-standards
  '((version . "1.1.0")
    (updated . "2026-02-04")
    (compliance . ("NIST-SP-800-series" "FIPS-140-3" "Post-Quantum-Cryptography-NIST"))
    (note . "protocol-squisher is currently a code generation tool. Security requirements apply to future features.")))

;;; Password Hashing
;;; Applies to: future schema registry authentication, user management

(define password-hashing
  '((algorithm . "Argon2id")
    (version . "1.3")
    (parameters
      ((memory-cost . 65536)         ;; 64 MiB (65536 KiB)
       (time-cost . 3)                ;; 3 iterations
       (parallelism . 4)              ;; 4 parallel threads
       (output-length . 32)           ;; 32 bytes (256 bits)
       (salt-length . 16)))           ;; 16 bytes (128 bits) random salt
    (rationale . "Argon2id provides resistance to GPU/ASIC attacks and side-channel attacks")
    (applies-to
      "Schema registry user authentication"
      "API key derivation"
      "Developer credential storage")))

;;; Symmetric Encryption
;;; Applies to: encrypted schema storage, secure schema transmission

(define symmetric-encryption
  '((algorithm . "ChaCha20-Poly1305")
    (key-size . 256)                  ;; 256-bit keys
    (nonce-size . 96)                 ;; 96-bit nonce (never reuse with same key)
    (tag-size . 128)                  ;; 128-bit authentication tag
    (mode . "AEAD")                   ;; Authenticated Encryption with Associated Data
    (rationale . "ChaCha20-Poly1305 is constant-time, fast on all platforms, NIST-approved")
    (applies-to
      "Encrypted schema storage"
      "Secure schema transmission over untrusted channels"
      "Encrypted cache files")))

;;; Asymmetric Encryption (Post-Quantum)
;;; Applies to: future public key infrastructure for schema signing

(define asymmetric-encryption
  '((algorithm . "Kyber-1024")
    (security-level . "NIST-Level-5")  ;; ~256-bit classical security
    (key-size
      ((public-key . 1568)             ;; bytes
       (secret-key . 3168)             ;; bytes
       (ciphertext . 1568)))           ;; bytes
    (rationale . "Kyber-1024 provides post-quantum security against quantum attacks")
    (fallback . "X25519")              ;; Hybrid mode: Kyber-1024 + X25519 for transition period
    (applies-to
      "Schema encryption for public distribution"
      "Secure schema exchange between parties"
      "Future PKI infrastructure")))

;;; Digital Signatures (Post-Quantum)
;;; Applies to: schema integrity verification, signed releases

(define digital-signatures
  '((algorithm . "Dilithium5-AES")
    (security-level . "NIST-Level-5")  ;; ~256-bit classical security
    (key-size
      ((public-key . 2592)             ;; bytes
       (secret-key . 4864)             ;; bytes
       (signature . 4627)))            ;; bytes (average)
    (rationale . "Dilithium5-AES provides post-quantum signature security with AES acceleration")
    (fallback . "Ed25519")             ;; Hybrid mode: Dilithium5 + Ed25519 for transition period
    (applies-to
      "Schema file signatures (.schema.sig)"
      "Release artifact signing"
      "Compatibility report signatures"
      "Code generation attestations")))

;;; Key Derivation
;;; Applies to: deriving encryption keys from passwords or master keys

(define key-derivation
  '((algorithm . "BLAKE3-KDF")
    (output-length . "arbitrary")      ;; Can derive any length key
    (context-string . "required")      ;; Domain separation via context string
    (key-material . "required")        ;; Input key material
    (rationale . "BLAKE3-KDF is faster than HKDF, provides domain separation")
    (alternative . "HKDF-SHA512")      ;; If BLAKE3 not available
    (applies-to
      "Deriving encryption keys from master key"
      "Deriving MAC keys"
      "Session key generation"
      "Subkey derivation for different purposes")))

;;; Secure Hashing
;;; Applies to: content-addressable storage, integrity verification

(define secure-hashing
  '((algorithm . "SHAKE3-512")
    (output-length . 512)              ;; 512 bits (64 bytes)
    (collision-resistance . "256-bit") ;; Security level
    (alternative . "BLAKE3")           ;; Faster, equally secure, not NIST-standardized
    (rationale . "SHAKE3-512 provides post-quantum security, extendable output")
    (applies-to
      "Schema content addressing (CAS)"
      "File integrity verification"
      "Merkle tree construction"
      "Commitment schemes"
      "Hash-based data structures")))

;;; Random Number Generation
;;; Applies to: generating salts, nonces, IVs, keys

(define random-number-generation
  '((source . "OS-CSPRNG")
    (implementations
      ((linux . "/dev/urandom")
       (freebsd . "/dev/urandom")
       (macos . "SecRandomCopyBytes")
       (windows . "BCryptGenRandom")
       (rust . "getrandom crate")))
    (minimum-entropy . 256)            ;; bits
    (never-use
      "rand()" "random()" "PRNG" "Mersenne-Twister" "/dev/random")
    (rationale . "OS CSPRNG is cryptographically secure, automatically reseeded")
    (applies-to
      "Salt generation for Argon2id"
      "Nonce generation for ChaCha20-Poly1305"
      "IV generation"
      "Session token generation"
      "Key generation")))

;;; Post-Quantum Cryptography Standards
;;; Overall PQC requirements and migration strategy

(define post-quantum-cryptography
  '((readiness . "required")
    (algorithms
      ((signatures . "Dilithium5-AES")
       (encryption . "Kyber-1024")
       (hashing . "SHAKE3-512")))
    (hybrid-mode . "recommended")      ;; Use both PQC and classical for transition
    (classical-fallbacks
      ((signatures . "Ed25519")
       (encryption . "X25519")
       (hashing . "BLAKE3")))
    (rationale . "Preparing for quantum computing threats")
    (migration-timeline
      ((phase-1 . "Add PQC algorithms as optional")
       (phase-2 . "Enable hybrid mode (PQC + classical)")
       (phase-3 . "Make PQC default")
       (phase-4 . "Deprecate classical-only mode")))))

;;; Applicability Matrix
;;; Which requirements apply to which features

(define applicability-matrix
  '((current-features
      ((schema-analysis . ("secure-hashing" "integrity-verification"))
       (code-generation . ("secure-hashing" "deterministic-output"))
       (cli-tool . ("random-generation" "temporary-file-security"))))
    (future-features
      ((schema-registry
         ("password-hashing" "symmetric-encryption" "secure-hashing" "random-generation"))
       (signed-schemas
         ("digital-signatures" "secure-hashing"))
       (encrypted-schemas
         ("asymmetric-encryption" "symmetric-encryption" "key-derivation"))
       (schema-crawler
         ("password-hashing" "secure-hashing" "random-generation"))
       (compatibility-database
         ("secure-hashing" "integrity-verification" "backup-encryption"))))
    (infrastructure
      ((ci-cd-secrets . ("symmetric-encryption"))
       (artifact-signing . ("digital-signatures"))
       (secure-distribution . ("asymmetric-encryption"))))))

;;; Implementation Notes
;;;
;;; 1. **Rust Crates to Use:**
;;;    - argon2 = "0.5" (password hashing)
;;;    - chacha20poly1305 = "0.10" (AEAD encryption)
;;;    - blake3 = "1.5" (hashing, KDF)
;;;    - pqcrypto = "0.18" (post-quantum: Dilithium, Kyber)
;;;    - getrandom = "0.2" (CSPRNG)
;;;    - sha3 = "0.10" (SHAKE3)
;;;
;;; 2. **Key Management:**
;;;    - Never hardcode keys in source code
;;;    - Use environment variables or secure key stores
;;;    - Rotate keys periodically
;;;    - Use different keys for different purposes
;;;
;;; 3. **Timing Attacks:**
;;;    - Use constant-time comparison for secrets
;;;    - Avoid branching on secret data
;;;    - Use constant-time libraries
;;;
;;; 4. **Memory Safety:**
;;;    - Clear sensitive data after use (zeroize crate)
;;;    - Avoid logging sensitive data
;;;    - Use secure memory allocation if available
;;;
;;; 5. **Hybrid Cryptography:**
;;;    - During transition, use both PQC and classical
;;;    - Signature: Dilithium5 + Ed25519
;;;    - Encryption: Kyber-1024 + X25519
;;;    - Only accept if BOTH signatures valid
;;;
;;; 6. **Protocol Versioning:**
;;;    - Include cryptographic protocol version in all messages
;;;    - Support multiple versions during transition
;;;    - Reject deprecated versions after sunset period

;;; Security Audit Checklist
;;;
;;; [ ] All password hashing uses Argon2id with specified parameters
;;; [ ] All symmetric encryption uses ChaCha20-Poly1305 AEAD
;;; [ ] All signatures use Dilithium5-AES (+ Ed25519 in hybrid mode)
;;; [ ] All encryption uses Kyber-1024 (+ X25519 in hybrid mode)
;;; [ ] All hashing uses SHAKE3-512 or BLAKE3
;;; [ ] All random generation uses OS CSPRNG (getrandom crate)
;;; [ ] No hardcoded keys, salts, or secrets
;;; [ ] Sensitive data zeroized after use
;;; [ ] Constant-time comparison for secrets
;;; [ ] Cryptographic protocol version included in messages
;;; [ ] Key rotation policy documented and implemented
;;; [ ] Security audit performed before production release
