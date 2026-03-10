<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Format Specification Versions

Tracks which specification version each protocol-squisher analyzer targets.
Updated: 2026-03-10.

## Analyzer Spec Matrix

| Format | Analyzer Crate | Spec Version(s) Supported | Notes |
|--------|---------------|---------------------------|-------|
| **Protobuf** | `protocol-squisher-protobuf-analyzer` | proto2, proto3 (Language Guide rev 2024) | Regex-based parser; detects `syntax = "proto2"` / `"proto3"`. No Editions (2023+) support yet. |
| **Avro** | `protocol-squisher-avro-analyzer` | Apache Avro 1.11.x schema spec | JSON-based schema parsing; supports record, enum, fixed, union, array, map. |
| **Thrift** | `protocol-squisher-thrift-analyzer` | Apache Thrift IDL (v0.21.x compatible) | Regex-based parser; structs, enums, exceptions, typedefs. Field modifiers: required/optional/default. |
| **FlatBuffers** | `protocol-squisher-flatbuffers-analyzer` | FlatBuffers schema (flatc 24.x compatible) | Tables, structs (zero-copy), enums, unions. Supports `root_type` declaration. |
| **Cap'n Proto** | `protocol-squisher-capnproto-analyzer` | Cap'n Proto encoding spec (capnpc 1.x) | Structs with `@N` field numbering, enums, inline unions. Data types only (no RPC interfaces). |
| **MessagePack** | `protocol-squisher-messagepack-analyzer` | MessagePack spec (2013 revision, msgpack.org) | Schema-less format; accepts JSON Schema as proxy for type information. All types map to Wheelbarrow class. |
| **GraphQL** | `protocol-squisher-graphql-analyzer` | GraphQL SDL (October 2021 spec) | Object types, inputs, interfaces, enums, unions, scalars. `Int` is 32-bit, `Float` is f64. |
| **TOML** | `protocol-squisher-toml-analyzer` | TOML v1.1.0 (via `toml` crate 1.0.6+spec-1.1.0) | Type inference from documents; tables, arrays, date-time, inline tables. |
| **JSON Schema** | `protocol-squisher-json-schema-analyzer` | draft-04, draft-06, draft-07, draft-2019-09, draft-2020-12 | Auto-detects version from `$schema` URI. Supports `$ref`, `allOf`/`anyOf`/`oneOf`, `prefixItems` (2020-12). |
| **Bebop** | `protocol-squisher-bebop-analyzer` | Bebop schema spec (bebop 3.x compatible) | Structs (unversioned), messages (versioned with field numbers), enums. Maps and arrays supported. |
| **ReScript** | `protocol-squisher-rescript-analyzer` | ReScript type syntax (v11/v12 compatible) | Regex-based parser for ReScript type definitions and record types. |

## Spec Upgrade Tracking

### Not Yet Supported

| Format | Missing Spec Feature | Priority |
|--------|---------------------|----------|
| Protobuf | Editions (2023+) | Medium — new Google protobuf feature, not yet widely adopted |
| Avro | Schema fingerprints (CRC-64-AVRO) | Low |
| Cap'n Proto | Generic types `Pair(K,V)` | Low |
| Cap'n Proto | RPC interface definitions | Low — currently data-types-only |
| FlatBuffers | FlexBuffers (schema-less variant) | Low |
| JSON Schema | Vocabulary system (2019-09+) | Low |
| GraphQL | `@specifiedBy` directive (scalars) | Low |

### Spec Version Sources

- Protobuf: https://protobuf.dev/programming-guides/proto3/
- Avro: https://avro.apache.org/docs/current/specification/
- Thrift: https://thrift.apache.org/docs/idl
- FlatBuffers: https://flatbuffers.dev/flatbuffers_guide_writing_schema.html
- Cap'n Proto: https://capnproto.org/encoding.html
- MessagePack: https://github.com/msgpack/msgpack/blob/master/spec.md
- GraphQL: https://spec.graphql.org/October2021/
- TOML: https://toml.io/en/v1.1.0
- JSON Schema: https://json-schema.org/specification
- Bebop: https://bebop.sh/reference/
