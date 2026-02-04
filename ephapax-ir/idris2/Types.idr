-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Protocol Squisher - Canonical IR Type System (Idris2)
--
-- This module encodes IR types using dependent types, demonstrating
-- linear type guarantees for protocol-squisher's IR operations.

module Types

%default total

-- ============================================================================
-- Primitive Type Tags
-- ============================================================================

public export
data PrimitiveType = I8 | I16 | I32 | I64 | I128
                   | U8 | U16 | U32 | U64 | U128
                   | F32 | F64
                   | Bool_ | Char_ | Str | UnitType

public export
Eq PrimitiveType where
  I8 == I8 = True
  I16 == I16 = True
  I32 == I32 = True
  I64 == I64 = True
  I128 == I128 = True
  U8 == U8 = True
  U16 == U16 = True
  U32 == U32 = True
  U64 == U64 = True
  U128 == U128 = True
  F32 == F32 = True
  F64 == F64 = True
  Bool_ == Bool_ = True
  Char_ == Char_ = True
  Str == Str = True
  UnitType == UnitType = True
  _ == _ = False

-- ============================================================================
-- Container Type Tags
-- ============================================================================

public export
data ContainerType = Array | Vec | Map | Set | Optional

public export
Eq ContainerType where
  Array == Array = True
  Vec == Vec = True
  Map == Map = True
  Set == Set = True
  Optional == Optional = True
  _ == _ = False

-- ============================================================================
-- Composite Type Tags
-- ============================================================================

public export
data CompositeType = Struct | Enum | Tuple

public export
Eq CompositeType where
  Struct == Struct = True
  Enum == Enum = True
  Tuple == Tuple = True
  _ == _ = False

-- ============================================================================
-- Unified Type System
-- ============================================================================

public export
data IRType = Prim PrimitiveType
            | Container ContainerType IRType
            | Composite CompositeType (List IRType)

-- ============================================================================
-- Type Compatibility Checking
-- ============================================================================

-- Check if numeric widening is allowed
public export
primitivesCompatible : PrimitiveType -> PrimitiveType -> Bool
primitivesCompatible a b = a == b ||
  case (a, b) of
    -- Signed integer widening
    (I8, I16)   => True
    (I8, I32)   => True
    (I8, I64)   => True
    (I8, I128)  => True
    (I16, I32)  => True
    (I16, I64)  => True
    (I16, I128) => True
    (I32, I64)  => True
    (I32, I128) => True
    (I64, I128) => True
    -- Unsigned integer widening
    (U8, U16)   => True
    (U8, U32)   => True
    (U8, U64)   => True
    (U8, U128)  => True
    (U16, U32)  => True
    (U16, U64)  => True
    (U16, U128) => True
    (U32, U64)  => True
    (U32, U128) => True
    (U64, U128) => True
    -- Float widening
    (F32, F64) => True
    _ => False

-- ============================================================================
-- Type Size Calculation (for memory layout)
-- ============================================================================

public export
typeSize : PrimitiveType -> Nat
typeSize I8       = 1
typeSize I16      = 2
typeSize I32      = 4
typeSize I64      = 8
typeSize I128     = 16
typeSize U8       = 1
typeSize U16      = 2
typeSize U32      = 4
typeSize U64      = 8
typeSize U128     = 16
typeSize F32      = 4
typeSize F64      = 8
typeSize Bool_    = 1
typeSize Char_    = 4
typeSize Str      = 8
typeSize UnitType = 0

-- ============================================================================
-- Type Validation
-- ============================================================================

public export
isNumeric : PrimitiveType -> Bool
isNumeric I8   = True
isNumeric I16  = True
isNumeric I32  = True
isNumeric I64  = True
isNumeric I128 = True
isNumeric U8   = True
isNumeric U16  = True
isNumeric U32  = True
isNumeric U64  = True
isNumeric U128 = True
isNumeric F32  = True
isNumeric F64  = True
isNumeric _    = False

public export
isInteger : PrimitiveType -> Bool
isInteger I8   = True
isInteger I16  = True
isInteger I32  = True
isInteger I64  = True
isInteger I128 = True
isInteger U8   = True
isInteger U16  = True
isInteger U32  = True
isInteger U64  = True
isInteger U128 = True
isInteger _    = False

public export
isFloat : PrimitiveType -> Bool
isFloat F32 = True
isFloat F64 = True
isFloat _   = False

-- ============================================================================
-- Show Instances
-- ============================================================================

public export
Show PrimitiveType where
  show I8       = "i8"
  show I16      = "i16"
  show I32      = "i32"
  show I64      = "i64"
  show I128     = "i128"
  show U8       = "u8"
  show U16      = "u16"
  show U32      = "u32"
  show U64      = "u64"
  show U128     = "u128"
  show F32      = "f32"
  show F64      = "f64"
  show Bool_    = "bool"
  show Char_    = "char"
  show Str      = "string"
  show UnitType = "unit"

public export
Show ContainerType where
  show Array    = "array"
  show Vec      = "vec"
  show Map      = "map"
  show Set      = "set"
  show Optional = "optional"

public export
Show CompositeType where
  show Struct = "struct"
  show Enum   = "enum"
  show Tuple  = "tuple"

public export
Show IRType where
  show (Prim p) = show p
  show (Container c t) = show c ++ "<" ++ show t ++ ">"
  show (Composite c ts) = show c ++ "(" ++ showList ts ++ ")"
    where
      showList : List IRType -> String
      showList [] = ""
      showList [x] = show x
      showList (x :: xs) = show x ++ ", " ++ showList xs
