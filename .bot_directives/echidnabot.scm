;; SPDX-License-Identifier: PMPL-1.0-or-later
(bot-directive
  (bot "echidnabot")
  (scope "formal verification, fuzzing, and protocol analysis validation")
  (languages ("Rust" "Idris2"))
  (targets
    ("crates/" "Rust workspace crates")
    ("crates/protocol-squisher-echidna-bridge/" "ECHIDNA integration bridge")
    ("crates/protocol-squisher-constraints/" "Constraint solver")
    ("crates/protocol-squisher-minikanren/" "MiniKanren logic engine")
    ("ephapax-ir/" "Ephapax IR integration"))
  (allow ("analysis" "fuzzing" "proof checks" "property testing" "unsafe auditing"))
  (deny ("write to core modules" "write to bindings" "modify Cargo.lock"))
  (scanning-rules
    (rust
      (ban ("unsafe" "transmute") (unless "// SAFETY: comment present"))
      (flag ("unwrap" "expect") (severity "medium"))
      (flag ("todo!" "unimplemented!") (severity "low")))
    (idris2
      (ban ("believe_me" "assert_total" "assert_smaller") (severity "critical"))))
  (notes "May open findings; code changes require explicit approval. Protocol analyzer crates are safety-critical."))
