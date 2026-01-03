# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 0.1.x   | :white_check_mark: |

## Reporting a Vulnerability

**DO NOT** create a public issue for security vulnerabilities.

### Report via Secure Channels

- **Email**: security@hyperpolymath.dev
- **GitHub Security Advisory**: [Create advisory](https://github.com/hyperpolymath/protocol-squisher/security/advisories/new)

### Include

- Description of the vulnerability
- Steps to reproduce
- Potential impact
- Suggested fix (if available)

### Response Timeline

- **Acknowledge** receipt within 48 hours
- **Assess** severity within 7 days
- **Release fix** within 30 days for critical issues

## Security Model

Protocol Squisher is designed with security as a foundational principle:

1. **Sandboxed Parsing**: Schema analyzers have recursion limits and timeouts
2. **No Arbitrary Code Execution**: Schemas cannot execute code
3. **Generated Code Safety**: All generated adapters are memory-safe (no `unsafe`)
4. **Type Safety**: Rust's ownership model prevents memory vulnerabilities

## Security.txt

See [.well-known/security.txt](.well-known/security.txt) for RFC 9116 compliance.
