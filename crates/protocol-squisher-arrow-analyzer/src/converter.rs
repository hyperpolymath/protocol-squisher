// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Apache Arrow → Protocol Squisher IR converter.
//!
//! Maps Arrow columnar data types to IR types. Arrow schemas are flat
//! (a list of typed fields), so each schema produces a single IR struct.
//!
//! ## Type Mappings
//!
//! | Arrow DataType          | IR Type         | Notes                       |
//! |-------------------------|-----------------|-----------------------------|
//! | Boolean                 | Bool            | 1-bit boolean               |
//! | Int8 / UInt8            | I8 / U8         | 8-bit integer               |
//! | Int16 / UInt16          | I16 / U16       | 16-bit integer              |
//! | Int32 / UInt32          | I32 / U32       | 32-bit integer              |
//! | Int64 / UInt64          | I64 / U64       | 64-bit integer              |
//! | Float16 / Float32       | F32             | Single precision            |
//! | Float64                 | F64             | Double precision            |
//! | Utf8 / LargeUtf8        | String          | Variable-length text        |
//! | Binary / LargeBinary    | Bytes           | Variable-length binary      |
//! | FixedSizeBinary(n)      | Bytes           | Fixed-size binary           |
//! | Date32 / Date64         | Date            | Calendar date               |
//! | Timestamp               | DateTime        | Date + time                 |
//! | Time32 / Time64         | Time            | Time of day                 |
//! | Duration                | Duration        | Time interval               |
//! | Decimal128 / Decimal256 | Decimal         | Arbitrary precision         |
//! | List / LargeList        | Vec<T>          | Variable-length sequence    |
//! | FixedSizeList(n)        | Array<T, n>     | Fixed-length array          |
//! | Struct                  | Struct           | Named fields                |
//! | Map                     | Map<K, V>       | Key-value mapping           |
//! | Union                   | Union            | Variant types               |
//!
//! ## Nullability
//!
//! Nullable Arrow fields become `Optional<T>` in the IR.

use crate::parser::{ParsedArrowField, ParsedArrowSchema};
use crate::AnalyzerError;
use arrow_schema::DataType;
use protocol_squisher_ir::*;

/// The Arrow → IR converter.
#[derive(Debug, Default)]
pub struct ArrowConverter;

impl ArrowConverter {
    /// Convert a parsed Arrow schema to an IR schema.
    pub fn convert(&self, parsed: &ParsedArrowSchema) -> Result<IrSchema, AnalyzerError> {
        let mut schema = IrSchema::new(&parsed.name, "arrow-ipc");

        let fields: Vec<FieldDef> = parsed
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        let mut metadata = TypeMetadata::default();
        for (k, v) in &parsed.metadata {
            metadata.extra.insert(k.clone(), v.clone());
        }

        let struct_def = TypeDef::Struct(StructDef {
            name: parsed.name.clone(),
            fields,
            metadata,
        });

        schema.add_type(parsed.name.clone(), struct_def);
        schema.add_root(parsed.name.clone());

        Ok(schema)
    }

    /// Convert a single Arrow field to an IR field.
    fn convert_field(&self, field: &ParsedArrowField) -> Result<FieldDef, AnalyzerError> {
        let base_type = self.convert_data_type(&field.data_type)?;

        // Nullable fields become Optional<T>
        let ty = if field.nullable {
            IrType::Container(ContainerType::Option(Box::new(base_type)))
        } else {
            base_type
        };

        let mut constraints = Vec::new();
        if !field.nullable {
            constraints.push(Constraint::NonEmpty);
        }

        let mut field_metadata = FieldMetadata::default();
        for (k, v) in &field.metadata {
            field_metadata.serde_hints.insert(k.clone(), v.clone());
        }

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional: field.nullable,
            constraints,
            metadata: field_metadata,
        })
    }

    /// Convert an Arrow `DataType` to an IR type.
    #[allow(clippy::only_used_in_recursion)]
    fn convert_data_type(&self, dt: &DataType) -> Result<IrType, AnalyzerError> {
        let ir = match dt {
            // Boolean
            DataType::Boolean => IrType::Primitive(PrimitiveType::Bool),

            // Signed integers
            DataType::Int8 => IrType::Primitive(PrimitiveType::I8),
            DataType::Int16 => IrType::Primitive(PrimitiveType::I16),
            DataType::Int32 => IrType::Primitive(PrimitiveType::I32),
            DataType::Int64 => IrType::Primitive(PrimitiveType::I64),

            // Unsigned integers
            DataType::UInt8 => IrType::Primitive(PrimitiveType::U8),
            DataType::UInt16 => IrType::Primitive(PrimitiveType::U16),
            DataType::UInt32 => IrType::Primitive(PrimitiveType::U32),
            DataType::UInt64 => IrType::Primitive(PrimitiveType::U64),

            // Floating point
            DataType::Float16 | DataType::Float32 => IrType::Primitive(PrimitiveType::F32),
            DataType::Float64 => IrType::Primitive(PrimitiveType::F64),

            // Decimal
            DataType::Decimal32(_, _)
            | DataType::Decimal64(_, _)
            | DataType::Decimal128(_, _)
            | DataType::Decimal256(_, _) => IrType::Primitive(PrimitiveType::Decimal),

            // Text
            DataType::Utf8 | DataType::LargeUtf8 | DataType::Utf8View => {
                IrType::Primitive(PrimitiveType::String)
            }

            // Binary
            DataType::Binary
            | DataType::LargeBinary
            | DataType::BinaryView
            | DataType::FixedSizeBinary(_) => IrType::Primitive(PrimitiveType::Bytes),

            // Temporal
            DataType::Date32 | DataType::Date64 => IrType::Primitive(PrimitiveType::Date),
            DataType::Timestamp(_, _) => IrType::Primitive(PrimitiveType::DateTime),
            DataType::Time32(_) | DataType::Time64(_) => IrType::Primitive(PrimitiveType::Time),
            DataType::Duration(_) => IrType::Primitive(PrimitiveType::Duration),
            DataType::Interval(_) => IrType::Primitive(PrimitiveType::Duration),

            // Lists → Vec<T>
            DataType::List(inner) | DataType::LargeList(inner) | DataType::ListView(inner) | DataType::LargeListView(inner) => {
                let inner_type = self.convert_data_type(inner.data_type())?;
                IrType::Container(ContainerType::Vec(Box::new(inner_type)))
            }

            // Fixed-size list → Array<T, n>
            DataType::FixedSizeList(inner, n) => {
                let inner_type = self.convert_data_type(inner.data_type())?;
                IrType::Container(ContainerType::Array(Box::new(inner_type), *n as usize))
            }

            // Struct → inline struct (we flatten to fields)
            DataType::Struct(fields) => {
                let ir_fields: Vec<FieldDef> = fields
                    .iter()
                    .map(|f| {
                        self.convert_field(&ParsedArrowField {
                            name: f.name().clone(),
                            data_type: f.data_type().clone(),
                            nullable: f.is_nullable(),
                            metadata: f
                                .metadata()
                                .iter()
                                .map(|(k, v)| (k.clone(), v.clone()))
                                .collect(),
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                // For nested structs, we return a Reference and register the type separately.
                // But since Arrow schemas are flat and nested structs are inline,
                // we use Special(Opaque) with a hint. In practice, callers should
                // handle this by creating nested struct types.
                // For simplicity, we convert to a struct-like representation using Tuple.
                // Actually, the cleanest approach is to just use the field types inline.
                // Let's return a Tuple of the field types — the shape extractor
                // will produce a Product shape from this.
                if ir_fields.is_empty() {
                    IrType::Special(SpecialType::Unit)
                } else {
                    IrType::Container(ContainerType::Tuple(
                        ir_fields.into_iter().map(|f| f.ty).collect(),
                    ))
                }
            }

            // Map → Map<K, V>
            DataType::Map(entries_field, _sorted) => {
                // Arrow maps are stored as List<Struct<key, value>>
                if let DataType::Struct(kv_fields) = entries_field.data_type() {
                    if kv_fields.len() >= 2 {
                        let key_type = self.convert_data_type(kv_fields[0].data_type())?;
                        let val_type = self.convert_data_type(kv_fields[1].data_type())?;
                        IrType::Container(ContainerType::Map(
                            Box::new(key_type),
                            Box::new(val_type),
                        ))
                    } else {
                        IrType::Special(SpecialType::Any)
                    }
                } else {
                    IrType::Special(SpecialType::Any)
                }
            }

            // Union → Union
            DataType::Union(union_fields, _mode) => {
                let variants: Vec<IrType> = union_fields
                    .iter()
                    .map(|(_, f)| self.convert_data_type(f.data_type()))
                    .collect::<Result<Vec<_>, _>>()?;
                if variants.is_empty() {
                    IrType::Special(SpecialType::Unit)
                } else {
                    IrType::Special(SpecialType::Any) // Unions are complex; simplify
                }
            }

            // Dictionary → the value type (the dictionary encoding is a transport detail)
            DataType::Dictionary(_, value_type) => self.convert_data_type(value_type)?,

            // RunEndEncoded → the value type
            DataType::RunEndEncoded(_, value_field) => {
                self.convert_data_type(value_field.data_type())?
            }

            // Null type
            DataType::Null => IrType::Special(SpecialType::Unit),
        };

        Ok(ir)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ArrowParser;
    use arrow_schema::{Field, Schema, TimeUnit};

    fn convert_schema(fields: Vec<Field>) -> IrSchema {
        let schema = Schema::new(fields);
        let parser = ArrowParser;
        let parsed = parser.from_arrow_schema(&schema, "test");
        ArrowConverter.convert(&parsed).expect("conversion should succeed")
    }

    #[test]
    fn integer_types() {
        let ir = convert_schema(vec![
            Field::new("a", DataType::Int8, false),
            Field::new("b", DataType::Int16, false),
            Field::new("c", DataType::Int32, false),
            Field::new("d", DataType::Int64, false),
            Field::new("e", DataType::UInt32, false),
        ]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::I8)));
                assert!(matches!(s.fields[1].ty, IrType::Primitive(PrimitiveType::I16)));
                assert!(matches!(s.fields[2].ty, IrType::Primitive(PrimitiveType::I32)));
                assert!(matches!(s.fields[3].ty, IrType::Primitive(PrimitiveType::I64)));
                assert!(matches!(s.fields[4].ty, IrType::Primitive(PrimitiveType::U32)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn float_types() {
        let ir = convert_schema(vec![
            Field::new("f32", DataType::Float32, false),
            Field::new("f64", DataType::Float64, false),
        ]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::F32)));
                assert!(matches!(s.fields[1].ty, IrType::Primitive(PrimitiveType::F64)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn text_and_binary() {
        let ir = convert_schema(vec![
            Field::new("text", DataType::Utf8, false),
            Field::new("blob", DataType::Binary, false),
        ]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::String)));
                assert!(matches!(s.fields[1].ty, IrType::Primitive(PrimitiveType::Bytes)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn temporal_types() {
        let ir = convert_schema(vec![
            Field::new("ts", DataType::Timestamp(TimeUnit::Microsecond, None), false),
            Field::new("date", DataType::Date32, false),
            Field::new("time", DataType::Time64(TimeUnit::Nanosecond), false),
            Field::new("dur", DataType::Duration(TimeUnit::Second), false),
        ]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::DateTime)));
                assert!(matches!(s.fields[1].ty, IrType::Primitive(PrimitiveType::Date)));
                assert!(matches!(s.fields[2].ty, IrType::Primitive(PrimitiveType::Time)));
                assert!(matches!(s.fields[3].ty, IrType::Primitive(PrimitiveType::Duration)));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn nullable_becomes_optional() {
        let ir = convert_schema(vec![
            Field::new("required", DataType::Int32, false),
            Field::new("nullable", DataType::Int32, true),
        ]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(!s.fields[0].optional);
                assert!(matches!(s.fields[0].ty, IrType::Primitive(PrimitiveType::I32)));
                assert!(s.fields[1].optional);
                assert!(matches!(
                    s.fields[1].ty,
                    IrType::Container(ContainerType::Option(_))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn list_type() {
        let inner = Field::new("item", DataType::Utf8, false);
        let ir = convert_schema(vec![Field::new(
            "tags",
            DataType::List(Box::new(inner).into()),
            false,
        )]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Container(ContainerType::Vec(_))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn fixed_size_list_type() {
        let inner = Field::new("item", DataType::Float32, false);
        let ir = convert_schema(vec![Field::new(
            "coords",
            DataType::FixedSizeList(Box::new(inner).into(), 3),
            false,
        )]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Container(ContainerType::Array(_, 3))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn map_type() {
        let ir = convert_schema(vec![Field::new(
            "labels",
            DataType::Map(
                Box::new(Field::new(
                    "entries",
                    DataType::Struct(
                        vec![
                            Field::new("key", DataType::Utf8, false),
                            Field::new("value", DataType::Int64, true),
                        ]
                        .into(),
                    ),
                    false,
                ))
                .into(),
                false,
            ),
            false,
        )]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Container(ContainerType::Map(_, _))
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn decimal_type() {
        let ir = convert_schema(vec![Field::new(
            "price",
            DataType::Decimal128(10, 2),
            false,
        )]);
        match &ir.types["test"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::Decimal)
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn source_format_is_arrow_ipc() {
        let ir = convert_schema(vec![Field::new("x", DataType::Int32, false)]);
        assert_eq!(ir.source_format, "arrow-ipc");
    }
}
