-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Protocol Squisher ABI Type Definitions
--
-- Defines C-compatible types for the protocol-squisher FFI layer.
-- These types are used by the Zig FFI implementation to provide
-- a stable C ABI for external consumers.

module ProtocolSquisher.ABI.Types

-- | Transport class classification for protocol compatibility
-- Matches the Rust enum in ephapax-ir/src/lib.rs
public export
data TransportClass
    = Concorde     -- Zero-copy, 100% fidelity
    | Business     -- Minor overhead, 98% fidelity
    | Economy      -- Moderate overhead, 80% fidelity
    | Wheelbarrow  -- High overhead, 50% fidelity (JSON fallback)

-- | Supported protocol formats
public export
data ProtocolFormat
    = Protobuf
    | Avro
    | Thrift
    | CapnProto
    | Bebop
    | FlatBuffers
    | MessagePack
    | JsonSchema
    | ReScript
    | Python

-- | IR primitive types matching Rust PrimitiveType enum
public export
data IRPrimitive
    = I8 | I16 | I32 | I64 | I128
    | U8 | U16 | U32 | U64 | U128
    | F32 | F64
    | PrimBool | PrimChar | PrimStr | PrimUnit

-- | Compatibility analysis result for FFI (C-compatible layout)
public export
record CompatResultFFI where
    constructor MkCompatResultFFI
    sourceFormat   : Bits8   -- ProtocolFormat enum value (0-9)
    targetFormat   : Bits8   -- ProtocolFormat enum value (0-9)
    transportClass : Bits8   -- TransportClass enum value (0-3)
    fidelity       : Bits32  -- Fidelity percentage * 100 (0-10000)

-- | Field mapping between source and target protocols
public export
record FieldMappingFFI where
    constructor MkFieldMappingFFI
    sourceFieldIdx : Bits32  -- Index into source schema fields
    targetFieldIdx : Bits32  -- Index into target schema fields
    transportClass : Bits8   -- TransportClass for this field pair
    fidelity       : Bits32  -- Field-level fidelity * 100

-- | Adapter result for FFI
public export
record AdapterFFI where
    constructor MkAdapterFFI
    sourceFormat   : Bits8   -- Source ProtocolFormat
    targetFormat   : Bits8   -- Target ProtocolFormat
    mappingCount   : Bits32  -- Number of field mappings
    overallClass   : Bits8   -- Overall TransportClass

-- Size proofs for FFI struct layout verification
export
compatResultFFISize : CompatResultFFI -> Nat
compatResultFFISize _ = 7  -- 1+1+1+4 bytes

export
fieldMappingFFISize : FieldMappingFFI -> Nat
fieldMappingFFISize _ = 13  -- 4+4+1+4 bytes

export
adapterFFISize : AdapterFFI -> Nat
adapterFFISize _ = 7  -- 1+1+4+1 bytes
