// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Conversion from Python/Pydantic types to IR types

use crate::types::{
    FieldConstraints, IntrospectionResult, PydanticEnum, PydanticField, PydanticModel,
    PydanticType, PythonType,
};
use crate::AnalyzerError;
use protocol_squisher_ir::{
    Constraint, ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, NumberValue,
    PrimitiveType, SpecialType, StructDef, TagStyle, TypeDef, TypeMetadata, VariantDef,
    VariantMetadata,
};

/// Convert an introspection result to an IR schema
pub fn convert_introspection(result: &IntrospectionResult) -> Result<IrSchema, AnalyzerError> {
    if let Some(ref error) = result.error {
        return Err(AnalyzerError::IntrospectionError(error.clone()));
    }

    let mut schema = IrSchema::new(&result.module, "pydantic");

    for pydantic_type in &result.types {
        match pydantic_type {
            PydanticType::Model(model) => {
                let type_def = convert_model(model)?;
                schema.add_type(model.name.clone(), type_def);
                schema.add_root(model.name.clone());
            },
            PydanticType::Enum(enum_def) => {
                let type_def = convert_enum(enum_def)?;
                schema.add_type(enum_def.name.clone(), type_def);
                schema.add_root(enum_def.name.clone());
            },
            PydanticType::Error { name, error } => {
                return Err(AnalyzerError::IntrospectionError(format!(
                    "Failed to extract {name}: {error}"
                )));
            },
        }
    }

    Ok(schema)
}

/// Convert a Pydantic model to an IR struct
fn convert_model(model: &PydanticModel) -> Result<TypeDef, AnalyzerError> {
    let mut fields = Vec::new();

    for field in &model.fields {
        fields.push(convert_field(field)?);
    }

    let mut serde_hints = std::collections::BTreeMap::new();

    // Extract relevant config options
    if let Some(extra) = model.config.get("extra") {
        if let Some(s) = extra.as_str() {
            serde_hints.insert("extra".to_string(), s.to_string());
        }
    }
    if let Some(frozen) = model.config.get("frozen") {
        if frozen.as_bool() == Some(true) {
            serde_hints.insert("frozen".to_string(), "true".to_string());
        }
    }

    Ok(TypeDef::Struct(StructDef {
        name: model.name.clone(),
        fields,
        metadata: TypeMetadata {
            doc: model.doc.clone(),
            serde_hints,
            ..Default::default()
        },
    }))
}

/// Convert a Pydantic field to an IR field
fn convert_field(field: &PydanticField) -> Result<FieldDef, AnalyzerError> {
    let ty = convert_python_type(&field.field_type)?;
    let constraints = convert_constraints(&field.constraints);

    let mut serde_hints = std::collections::BTreeMap::new();
    if let Some(ref alias) = field.alias {
        serde_hints.insert("alias".to_string(), alias.clone());
    }

    Ok(FieldDef {
        name: field.alias.clone().unwrap_or_else(|| field.name.clone()),
        ty,
        optional: field.optional,
        constraints,
        metadata: FieldMetadata {
            doc: field.description.clone(),
            default: field.default.clone(),
            aliases: field.alias.iter().cloned().collect(),
            flatten: false,
            skip: false,
            serde_hints,
        },
    })
}

/// Convert a Python type annotation to an IR type
pub fn convert_python_type(py_type: &PythonType) -> Result<IrType, AnalyzerError> {
    match py_type {
        PythonType::Primitive { prim_type } => {
            Ok(IrType::Primitive(match prim_type.as_str() {
                "string" | "str" => PrimitiveType::String,
                "int" => PrimitiveType::I64, // Python ints are arbitrary precision, map to i64
                "float" => PrimitiveType::F64,
                "bool" => PrimitiveType::Bool,
                "bytes" => PrimitiveType::Bytes,
                "datetime" => PrimitiveType::DateTime,
                "date" => PrimitiveType::Date,
                "time" => PrimitiveType::Time,
                "duration" | "timedelta" => PrimitiveType::Duration,
                "decimal" => PrimitiveType::Decimal,
                "uuid" => PrimitiveType::Uuid,
                other => {
                    return Err(AnalyzerError::UnsupportedType(format!(
                        "Unknown primitive type: {other}"
                    )));
                },
            }))
        },

        PythonType::None => Ok(IrType::Special(SpecialType::Unit)),

        PythonType::Any => Ok(IrType::Special(SpecialType::Json)),

        PythonType::Optional { inner } => {
            let inner_type = convert_python_type(inner)?;
            Ok(IrType::Container(ContainerType::Option(Box::new(
                inner_type,
            ))))
        },

        PythonType::Union { variants } => {
            // Check if this is effectively Optional (Union with None)
            let non_none: Vec<_> = variants
                .iter()
                .filter(|v| !matches!(v, PythonType::None))
                .collect();

            if non_none.len() == 1 && variants.iter().any(|v| matches!(v, PythonType::None)) {
                // This is Optional[T]
                let inner = convert_python_type(non_none[0])?;
                return Ok(IrType::Container(ContainerType::Option(Box::new(inner))));
            }

            // True union - convert to IR union (stored as tuple of variants)
            // Note: This is a simplification; full union support would need IR extension
            let variant_types: Result<Vec<_>, _> =
                variants.iter().map(convert_python_type).collect();
            Ok(IrType::Container(ContainerType::Tuple(variant_types?)))
        },

        PythonType::List { inner } => {
            let inner_type = convert_python_type(inner)?;
            Ok(IrType::Container(ContainerType::Vec(Box::new(inner_type))))
        },

        PythonType::Set { inner } => {
            let inner_type = convert_python_type(inner)?;
            Ok(IrType::Container(ContainerType::Set(Box::new(inner_type))))
        },

        PythonType::Map { key, value } => {
            let key_type = convert_python_type(key)?;
            let value_type = convert_python_type(value)?;
            Ok(IrType::Container(ContainerType::Map(
                Box::new(key_type),
                Box::new(value_type),
            )))
        },

        PythonType::Tuple { elements } => {
            let element_types: Result<Vec<_>, _> =
                elements.iter().map(convert_python_type).collect();
            Ok(IrType::Container(ContainerType::Tuple(element_types?)))
        },

        PythonType::Enum { name, .. } => Ok(IrType::Reference(name.clone())),

        PythonType::Reference { name, .. } => Ok(IrType::Reference(name.clone())),

        PythonType::Unknown { repr } => Err(AnalyzerError::UnsupportedType(format!(
            "Unknown Python type: {}",
            repr.as_deref().unwrap_or("?")
        ))),
    }
}

/// Convert a Python enum to an IR enum
fn convert_enum(enum_def: &PydanticEnum) -> Result<TypeDef, AnalyzerError> {
    let variants: Vec<VariantDef> = enum_def
        .variants
        .iter()
        .map(|v| VariantDef {
            name: v.name.clone(),
            payload: None, // Python enums are typically unit variants with values
            metadata: VariantMetadata {
                doc: None,
                aliases: vec![],
                serde_hints: std::collections::BTreeMap::new(),
            },
        })
        .collect();

    Ok(TypeDef::Enum(EnumDef {
        name: enum_def.name.clone(),
        variants,
        tag_style: TagStyle::External, // Python enums serialize to their value
        metadata: TypeMetadata {
            doc: enum_def.doc.clone(),
            ..Default::default()
        },
    }))
}

/// Convert Pydantic field constraints to IR constraints
fn convert_constraints(constraints: &FieldConstraints) -> Vec<Constraint> {
    let mut result = Vec::new();

    // Numeric constraints
    // Note: Python's gt/lt are exclusive, ge/le are inclusive
    // IR's Min/Max are inclusive, so we use GreaterThan/LessThan for exclusive
    if let Some(gt) = constraints.gt {
        // gt means > value (exclusive), we'll use a custom constraint for now
        // or approximate with Min(value + epsilon) for floats
        result.push(Constraint::GreaterThan(format!("{gt}")));
    }
    if let Some(ge) = constraints.ge {
        result.push(Constraint::Min(f64_to_number_value(ge)));
    }
    if let Some(lt) = constraints.lt {
        // lt means < value (exclusive)
        result.push(Constraint::LessThan(format!("{lt}")));
    }
    if let Some(le) = constraints.le {
        result.push(Constraint::Max(f64_to_number_value(le)));
    }
    if let Some(multiple_of) = constraints.multiple_of {
        result.push(Constraint::MultipleOf(f64_to_number_value(multiple_of)));
    }

    // String/collection constraints
    if let Some(min_len) = constraints.min_length {
        result.push(Constraint::MinLength(min_len));
    }
    if let Some(max_len) = constraints.max_length {
        result.push(Constraint::MaxLength(max_len));
    }
    if let Some(ref pattern) = constraints.pattern {
        result.push(Constraint::Pattern(pattern.clone()));
    }

    result
}

/// Convert an f64 to a NumberValue, preferring integer if possible
fn f64_to_number_value(value: f64) -> NumberValue {
    if value.fract() == 0.0 && value >= i64::MIN as f64 && value <= i64::MAX as f64 {
        NumberValue::Integer(value as i64)
    } else {
        NumberValue::Float(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_primitive() {
        let py_type = PythonType::Primitive {
            prim_type: "string".to_string(),
        };
        let ir_type = convert_python_type(&py_type).unwrap();
        assert!(matches!(ir_type, IrType::Primitive(PrimitiveType::String)));
    }

    #[test]
    fn test_convert_optional() {
        let py_type = PythonType::Optional {
            inner: Box::new(PythonType::Primitive {
                prim_type: "int".to_string(),
            }),
        };
        let ir_type = convert_python_type(&py_type).unwrap();
        let IrType::Container(ContainerType::Option(inner)) = ir_type else {
            unreachable!("optional python type should map to Option");
        };
        assert!(matches!(*inner, IrType::Primitive(PrimitiveType::I64)));
    }

    #[test]
    fn test_convert_list() {
        let py_type = PythonType::List {
            inner: Box::new(PythonType::Primitive {
                prim_type: "string".to_string(),
            }),
        };
        let ir_type = convert_python_type(&py_type).unwrap();
        let IrType::Container(ContainerType::Vec(inner)) = ir_type else {
            unreachable!("list python type should map to Vec");
        };
        assert!(matches!(*inner, IrType::Primitive(PrimitiveType::String)));
    }

    #[test]
    fn test_convert_map() {
        let py_type = PythonType::Map {
            key: Box::new(PythonType::Primitive {
                prim_type: "string".to_string(),
            }),
            value: Box::new(PythonType::Primitive {
                prim_type: "int".to_string(),
            }),
        };
        let ir_type = convert_python_type(&py_type).unwrap();
        let IrType::Container(ContainerType::Map(key, value)) = ir_type else {
            unreachable!("dict python type should map to Map");
        };
        assert!(matches!(*key, IrType::Primitive(PrimitiveType::String)));
        assert!(matches!(*value, IrType::Primitive(PrimitiveType::I64)));
    }

    #[test]
    fn test_convert_constraints() {
        let constraints = FieldConstraints {
            ge: Some(0.0),
            le: Some(100.0),
            min_length: Some(1),
            pattern: Some(r"^\w+$".to_string()),
            ..Default::default()
        };
        let ir_constraints = convert_constraints(&constraints);
        assert_eq!(ir_constraints.len(), 4);
    }
}
