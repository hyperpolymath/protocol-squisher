---
title: Governance & Help
slug: governance
order: 5
date: 2026-02-28
tags: [governance, help, license, security, privacy]
---

# Information Governance & Help

## License

protocol-squisher is released under the **Palimpsest License (PMPL-1.0-or-later)**, a free and open-source software license. You may use, modify, and redistribute the software under the terms of this license.

- Full license text: `LICENSE` in the repository root
- SPDX identifier: `PMPL-1.0-or-later`

Third-party dependencies retain their original licenses (MIT, Apache-2.0, BSD, etc.). protocol-squisher does not relicense any third-party code.

## Security

### Reporting Vulnerabilities

If you discover a security vulnerability in protocol-squisher, please report it responsibly:

- **Email:** j.d.a.jewell@open.ac.uk
- **Subject line:** `[SECURITY] protocol-squisher: <brief description>`

Please do not open a public issue for security vulnerabilities. We aim to acknowledge reports within 48 hours and provide a fix or mitigation within 7 days for critical issues.

### Security Practices

protocol-squisher follows these security practices:

- **cargo audit** runs in CI — 0 known vulnerabilities across 275 dependencies
- **No MD5 or SHA1** for any security purpose (SHA-256 minimum)
- **HTTPS only** — no HTTP URLs anywhere in the codebase
- **No hardcoded secrets** — all credentials are environment-based
- **SHA-pinned dependencies** in CI workflows
- **Hypatia neurosymbolic scanning** for automated security analysis
- **TruffleHog secret scanning** in CI
- **OpenSSF Scorecard** for supply chain security

### panic-attack Security Suite

protocol-squisher is regularly tested with the panic-attack security suite, which includes:

- **assail** — Static analysis for security weak points
- **amuck** — Mutation testing to verify test coverage catches regressions
- **abduct** — Dependency isolation testing
- **adjudicate** — Verdict engine aggregating all results

The most recent run achieved a **PASS** verdict with zero crashes, zero critical weak points, and zero failed attacks.

## Data Handling

protocol-squisher processes schema files locally. It does not:

- Send schema data to any external service
- Collect telemetry or usage statistics
- Phone home or check for updates
- Require network access for core functionality

ECHIDNA cross-prover integration and VeriSimDB storage are optional features that can operate entirely offline via local fallback modes.

## Accessibility

This website is built with ddraig-ssg, a static site generator written in Idris 2. The site is designed with accessibility in mind:

- Semantic HTML5 structure
- High-contrast text (WCAG AA compliant)
- Keyboard-navigable tab interface
- System font stack (no web font downloads)
- Responsive layout for mobile and desktop
- Print-friendly stylesheet
- No JavaScript required

## Mirrors

protocol-squisher source code is available from three independent forges:

- **GitHub:** github.com/hyperpolymath/protocol-squisher (primary)
- **GitLab:** gitlab.com/hyperpolymath/protocol-squisher (mirror)
- **Bitbucket:** bitbucket.org/hyperpolymath/protocol-squisher (mirror)

Mirrors are synchronised automatically via CI.

## Formal Proofs

All formal proofs are machine-checked and reproducible:

- **Agda proofs** require Agda 2.6.4+ with standard library
- **Coq proofs** require Coq 8.18+
- **Lean 4 proofs** require Lean 4 toolchain (leanprover/lean4)
- **Isabelle proofs** require Isabelle 2024+
- **Z3 proofs** require Z3 4.12+

Proof source files are in `proofs/` and can be independently verified without building protocol-squisher itself.

## Getting Help

### Common Questions

**Q: Which protocol format should I use for a new project?**
Run `protocol-squisher squishability` on candidate schemas. The squishability report ranks formats by interoperability potential and highlights trade-offs.

**Q: Can protocol-squisher translate between any two formats?**
It can analyse and compare any pair of the 13 supported formats. Whether a useful translation exists depends on the specific schemas involved. The transport class system tells you exactly how much fidelity to expect.

**Q: Do I need the formal proofs?**
No. The proofs verify the correctness of the core algorithms. You benefit from their guarantees whether or not you inspect them. They are included for transparency and for researchers who wish to build on the work.

**Q: How do I add support for a new protocol format?**
Implement the `SchemaAnalyzer` trait from `protocol-squisher-ir`. The trait requires four methods: `analyzer_name`, `supported_extensions`, `analyze_file`, and `analyze_str`. See any of the 13 existing analysers for reference.

### Support Channels

- **Documentation:** In-repository docs (`README.adoc`, `docs/`)
- **Issues:** github.com/hyperpolymath/protocol-squisher/issues
- **Discussions:** github.com/hyperpolymath/protocol-squisher/discussions
- **Email:** j.d.a.jewell@open.ac.uk

## Acknowledgements

protocol-squisher builds on the work of many open-source projects and research communities. The formal verification approach was inspired by decades of work in type theory, and the practical implementation benefits from the Rust ecosystem's focus on safety and correctness.

This site was generated by **ddraig-ssg**, a dependently typed static site generator written in Idris 2 by the same author.
