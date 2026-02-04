-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Protocol Squisher - FFI Exports for Rust

module FFI

import Types
import Compat

%default total

-- Export transport class as integer for C FFI
export
transportClassToInt : TransportClass -> Int
transportClassToInt Concorde    = 100
transportClassToInt Business    = 101
transportClassToInt Economy     = 102
transportClassToInt Wheelbarrow = 103

-- Export primitive type as integer for C FFI
export
primitiveTypeToInt : PrimitiveType -> Int
primitiveTypeToInt I8       = 0
primitiveTypeToInt I16      = 1
primitiveTypeToInt I32      = 2
primitiveTypeToInt I64      = 3
primitiveTypeToInt U8       = 4
primitiveTypeToInt U16      = 5
primitiveTypeToInt U32      = 6
primitiveTypeToInt U64      = 7
primitiveTypeToInt F32      = 8
primitiveTypeToInt F64      = 9
primitiveTypeToInt Bool_    = 10
primitiveTypeToInt Char_    = 11
primitiveTypeToInt Str      = 12
primitiveTypeToInt UnitType = 13

-- Inverse: integer to primitive type
export
intToPrimitiveType : Int -> Maybe PrimitiveType
intToPrimitiveType 0  = Just I8
intToPrimitiveType 1  = Just I16
intToPrimitiveType 2  = Just I32
intToPrimitiveType 3  = Just I64
intToPrimitiveType 4  = Just U8
intToPrimitiveType 5  = Just U16
intToPrimitiveType 6  = Just U32
intToPrimitiveType 7  = Just U64
intToPrimitiveType 8  = Just F32
intToPrimitiveType 9  = Just F64
intToPrimitiveType 10 = Just Bool_
intToPrimitiveType 11 = Just Char_
intToPrimitiveType 12 = Just Str
intToPrimitiveType 13 = Just UnitType
intToPrimitiveType _  = Nothing

-- FFI-friendly function: analyze primitive compatibility
-- Returns transport class as integer
export
%export "C:ephapax_analyze_primitive_compat"
analyzePrimitiveCompatFFI : Int -> Int -> Int
analyzePrimitiveCompatFFI sourceInt targetInt =
  case (intToPrimitiveType sourceInt, intToPrimitiveType targetInt) of
    (Just source, Just target) =>
      transportClassToInt (analyzePrimitiveCompat source target)
    _ => transportClassToInt Wheelbarrow  -- Invalid types → worst case

-- FFI-friendly function: get fidelity percentage
export
%export "C:ephapax_get_fidelity"
getFidelityFFI : Int -> Int
getFidelityFFI classInt =
  case classInt of
    100 => cast (getFidelity Concorde)
    101 => cast (getFidelity Business)
    102 => cast (getFidelity Economy)
    103 => cast (getFidelity Wheelbarrow)
    _   => 0

-- FFI-friendly function: get overhead percentage
export
%export "C:ephapax_get_overhead"
getOverheadFFI : Int -> Int
getOverheadFFI classInt =
  case classInt of
    100 => cast (getOverhead Concorde)
    101 => cast (getOverhead Business)
    102 => cast (getOverhead Economy)
    103 => cast (getOverhead Wheelbarrow)
    _   => 100
