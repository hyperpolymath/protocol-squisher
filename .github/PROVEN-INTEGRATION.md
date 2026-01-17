# proven Integration Plan

This document outlines the recommended [proven](https://github.com/hyperpolymath/proven) modules for Protocol Squisher.

## Recommended Modules

| Module | Purpose | Priority |
|--------|---------|----------|
| SafeSchema | Schema migration with compatibility proofs for protocol transformations | High |
| SafeJson | Safe JSON parsing for protocol data interchange | High |

## Integration Notes

Protocol Squisher as a universal protocol interoperability tool through automatic adapter synthesis requires:

- **SafeSchema** is essential for protocol transformations. When converting between protocol versions or different protocols entirely, formal compatibility guarantees ensure data is not lost or corrupted. The `isBackwardCompatible` and `isForwardCompatible` checks verify adapters preserve semantics.

- **SafeJson** handles JSON-based protocols safely. Many modern protocols use JSON for data interchange, and SafeJson's typed extraction (`get_int`, `get_path`) ensures protocol messages are parsed correctly without runtime exceptions.

The combination ensures protocol adapters are mathematically correct - data that goes in one side comes out correctly on the other, with formal proofs of the transformation's validity.

## Related

- [proven library](https://github.com/hyperpolymath/proven)
- [Idris 2 documentation](https://idris2.readthedocs.io/)
