// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Converter from parsed ReScript to protocol-squisher IR

use crate::parser::{
    ParsedReScript, ReScriptConstructor, ReScriptField, ReScriptRecord, ReScriptTypeAlias,
    ReScriptVariant,
};
use crate::AnalyzerError;
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef,
    TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata, VariantPayload,
};
use std::collections::BTreeMap;

/// Converter from parsed ReScript to IR
#[derive(Debug, Default)]
pub struct ReScriptConverter {}

impl ReScriptConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed ReScript to IR schema
    pub fn convert(&self, parsed: &ParsedReScript, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut ir = IrSchema::new(name, "rescript");
        let mut types = BTreeMap::new();

        // Convert type aliases
        for alias in &parsed.type_aliases {
            let typedef = self.convert_type_alias(alias)?;
            types.insert(alias.name.clone(), typedef);
        }

        // Convert records
        for record in &parsed.records {
            let struct_def = self.convert_record(record)?;
            types.insert(struct_def.name.clone(), TypeDef::Struct(struct_def));
        }

        // Convert variants
        for variant in &parsed.variants {
            let enum_def = self.convert_variant(variant)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert a type alias to IR typedef
    fn convert_type_alias(&self, alias: &ReScriptTypeAlias) -> Result<TypeDef, AnalyzerError> {
        // Type aliases map to their target types
        let target_type = self.rescript_type_to_ir(&alias.target)?;

        // For now, we'll create a struct with a single field wrapping the alias
        // This preserves the semantic distinction in the IR
        Ok(TypeDef::Struct(StructDef {
            name: alias.name.clone(),
            fields: vec![FieldDef {
                name: "value".to_string(),
                ty: target_type,
                optional: false,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            }],
            metadata: TypeMetadata::default(),
        }))
    }

    /// Convert a ReScript record to IR struct
    fn convert_record(&self, record: &ReScriptRecord) -> Result<StructDef, AnalyzerError> {
        let fields = record
            .fields
            .iter()
            .map(|f| self.convert_field(f))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(StructDef {
            name: record.name.clone(),
            fields,
            metadata: TypeMetadata::default(),
        })
    }

    /// Convert a ReScript field to IR field
    fn convert_field(&self, field: &ReScriptField) -> Result<FieldDef, AnalyzerError> {
        let ty = self.rescript_type_to_ir(&field.field_type)?;

        let mut aliases = vec![];
        if let Some(js_name) = &field.js_name {
            aliases.push(js_name.clone());
        }

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional: field.optional,
            constraints: vec![],
            metadata: FieldMetadata {
                doc: None,
                default: None,
                aliases,
                flatten: false,
                skip: false,
                serde_hints: BTreeMap::new(),
            },
        })
    }

    /// Convert a ReScript type string to IR type
    #[allow(clippy::only_used_in_recursion)]
    fn rescript_type_to_ir(&self, type_str: &str) -> Result<IrType, AnalyzerError> {
        let type_str = type_str.trim();

        // Handle primitive types
        match type_str {
            "int" => return Ok(IrType::Primitive(PrimitiveType::I64)),
            "float" => return Ok(IrType::Primitive(PrimitiveType::F64)),
            "string" => return Ok(IrType::Primitive(PrimitiveType::String)),
            "bool" => return Ok(IrType::Primitive(PrimitiveType::Bool)),
            "unit" => return Ok(IrType::Special(protocol_squisher_ir::SpecialType::Unit)),
            "char" => return Ok(IrType::Primitive(PrimitiveType::Char)),
            _ => {},
        }

        // Handle option<T>
        if type_str.starts_with("option<") && type_str.ends_with('>') {
            let inner = &type_str[7..type_str.len() - 1];
            let inner_type = self.rescript_type_to_ir(inner)?;
            return Ok(IrType::Container(ContainerType::Option(Box::new(
                inner_type,
            ))));
        }

        // Handle array<T>
        if type_str.starts_with("array<") && type_str.ends_with('>') {
            let inner = &type_str[6..type_str.len() - 1];
            let inner_type = self.rescript_type_to_ir(inner)?;
            return Ok(IrType::Container(ContainerType::Vec(Box::new(inner_type))));
        }

        // Handle Js.Dict.t<T>
        if type_str.starts_with("Js.Dict.t<") && type_str.ends_with('>') {
            let value_type = &type_str[10..type_str.len() - 1];
            let value_ir = self.rescript_type_to_ir(value_type)?;
            return Ok(IrType::Container(ContainerType::Map(
                Box::new(IrType::Primitive(PrimitiveType::String)),
                Box::new(value_ir),
            )));
        }

        // Handle tuples: (T1, T2, ...)
        if type_str.starts_with('(') && type_str.ends_with(')') {
            let inner = &type_str[1..type_str.len() - 1];
            let elements = split_by_comma(inner);
            let mut element_types = Vec::new();

            for elem in elements {
                let elem_type = self.rescript_type_to_ir(&elem)?;
                element_types.push(elem_type);
            }

            return Ok(IrType::Container(ContainerType::Tuple(element_types)));
        }

        // Handle type parameters (polymorphic types like 'a, 'b)
        if type_str.starts_with('\'') {
            // Represent as a generic placeholder
            return Ok(IrType::Reference(type_str.to_string()));
        }

        // User-defined types (references to other types)
        Ok(IrType::Reference(type_str.to_string()))
    }

    /// Convert a ReScript variant to IR enum
    fn convert_variant(&self, variant: &ReScriptVariant) -> Result<EnumDef, AnalyzerError> {
        let variants: Vec<VariantDef> = variant
            .constructors
            .iter()
            .map(|c| self.convert_constructor(c))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(EnumDef {
            name: variant.name.clone(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        })
    }

    /// Convert a ReScript constructor to IR variant
    fn convert_constructor(
        &self,
        constructor: &ReScriptConstructor,
    ) -> Result<VariantDef, AnalyzerError> {
        let payload = if let Some(payload_str) = &constructor.payload {
            let payload_type = self.rescript_type_to_ir(payload_str)?;
            // ReScript variant payloads are always tuple-style (single value)
            Some(VariantPayload::Tuple(vec![payload_type]))
        } else {
            None
        };

        Ok(VariantDef {
            name: constructor.name.clone(),
            payload,
            metadata: VariantMetadata::default(),
        })
    }
}

/// Split by comma, respecting nested angle brackets and parentheses
fn split_by_comma(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for c in s.chars() {
        match c {
            '<' | '(' => {
                depth += 1;
                current.push(c);
            },
            '>' | ')' => {
                depth -= 1;
                current.push(c);
            },
            ',' if depth == 0 => {
                parts.push(current.trim().to_string());
                current.clear();
            },
            _ => current.push(c),
        }
    }

    if !current.trim().is_empty() {
        parts.push(current.trim().to_string());
    }

    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rescript_type_to_ir() {
        let converter = ReScriptConverter::new();

        assert!(matches!(
            converter.rescript_type_to_ir("string").unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            converter.rescript_type_to_ir("int").unwrap(),
            IrType::Primitive(PrimitiveType::I64)
        ));
        assert!(matches!(
            converter.rescript_type_to_ir("float").unwrap(),
            IrType::Primitive(PrimitiveType::F64)
        ));
        assert!(matches!(
            converter.rescript_type_to_ir("bool").unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
    }

    #[test]
    fn test_option_type_conversion() {
        let converter = ReScriptConverter::new();
        let result = converter.rescript_type_to_ir("option<string>").unwrap();

        let IrType::Container(ContainerType::Option(inner)) = result else {
            unreachable!("option<string> should map to Option");
        };
        assert!(matches!(*inner, IrType::Primitive(PrimitiveType::String)));
    }

    #[test]
    fn test_array_type_conversion() {
        let converter = ReScriptConverter::new();
        let result = converter.rescript_type_to_ir("array<int>").unwrap();

        let IrType::Container(ContainerType::Vec(inner)) = result else {
            unreachable!("array<int> should map to Vec");
        };
        assert!(matches!(*inner, IrType::Primitive(PrimitiveType::I64)));
    }

    #[test]
    fn test_js_dict_conversion() {
        let converter = ReScriptConverter::new();
        let result = converter.rescript_type_to_ir("Js.Dict.t<string>").unwrap();

        let IrType::Container(ContainerType::Map(key, value)) = result else {
            unreachable!("Js.Dict.t<T> should map to Map");
        };
        assert!(matches!(*key, IrType::Primitive(PrimitiveType::String)));
        assert!(matches!(*value, IrType::Primitive(PrimitiveType::String)));
    }

    #[test]
    fn test_tuple_conversion() {
        let converter = ReScriptConverter::new();
        let result = converter.rescript_type_to_ir("(int, string)").unwrap();

        let IrType::Container(ContainerType::Tuple(elements)) = result else {
            unreachable!("tuple should map to Tuple container");
        };
        assert_eq!(elements.len(), 2);
        assert!(matches!(elements[0], IrType::Primitive(PrimitiveType::I64)));
        assert!(matches!(
            elements[1],
            IrType::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_reference_type() {
        let converter = ReScriptConverter::new();
        let result = converter.rescript_type_to_ir("CustomType").unwrap();

        let IrType::Reference(name) = result else {
            unreachable!("CustomType should map to reference");
        };
        assert_eq!(name, "CustomType");
    }

    #[test]
    fn test_type_parameter() {
        let converter = ReScriptConverter::new();
        let result = converter.rescript_type_to_ir("'a").unwrap();

        let IrType::Reference(name) = result else {
            unreachable!("type parameter should map to reference");
        };
        assert_eq!(name, "'a");
    }

    #[test]
    fn test_split_by_comma() {
        let parts = split_by_comma("int, string, option<array<float>>");
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0], "int");
        assert_eq!(parts[1], "string");
        assert_eq!(parts[2], "option<array<float>>");
    }

    #[test]
    fn test_nested_containers() {
        let converter = ReScriptConverter::new();
        let result = converter
            .rescript_type_to_ir("option<array<string>>")
            .unwrap();

        let IrType::Container(ContainerType::Option(inner)) = result else {
            unreachable!("outer type should be Option");
        };
        let IrType::Container(ContainerType::Vec(inner2)) = *inner else {
            unreachable!("inner option type should be Vec");
        };
        assert!(matches!(*inner2, IrType::Primitive(PrimitiveType::String)));
    }

    #[test]
    fn test_convert_simple_record() {
        use crate::parser::{ReScriptField, ReScriptRecord};

        let converter = ReScriptConverter::new();

        let record = ReScriptRecord {
            name: "person".to_string(),
            type_params: vec![],
            fields: vec![
                ReScriptField {
                    name: "name".to_string(),
                    field_type: "string".to_string(),
                    optional: false,
                    js_name: None,
                },
                ReScriptField {
                    name: "age".to_string(),
                    field_type: "int".to_string(),
                    optional: false,
                    js_name: None,
                },
            ],
        };

        let result = converter.convert_record(&record);
        assert!(result.is_ok());

        let struct_def = result.unwrap();
        assert_eq!(struct_def.name, "person");
        assert_eq!(struct_def.fields.len(), 2);
    }

    #[test]
    fn test_convert_variant() {
        use crate::parser::{ReScriptConstructor, ReScriptVariant};

        let converter = ReScriptConverter::new();

        let variant = ReScriptVariant {
            name: "status".to_string(),
            type_params: vec![],
            constructors: vec![
                ReScriptConstructor {
                    name: "Active".to_string(),
                    payload: None,
                },
                ReScriptConstructor {
                    name: "Inactive".to_string(),
                    payload: None,
                },
            ],
        };

        let result = converter.convert_variant(&variant);
        assert!(result.is_ok());

        let enum_def = result.unwrap();
        assert_eq!(enum_def.name, "status");
        assert_eq!(enum_def.variants.len(), 2);
    }

    #[test]
    fn test_field_with_js_alias() {
        let converter = ReScriptConverter::new();

        let field = ReScriptField {
            name: "id".to_string(),
            field_type: "int".to_string(),
            optional: false,
            js_name: Some("user_id".to_string()),
        };

        let result = converter.convert_field(&field);
        assert!(result.is_ok());

        let field_def = result.unwrap();
        assert_eq!(field_def.name, "id");
        assert_eq!(field_def.metadata.aliases.len(), 1);
        assert_eq!(field_def.metadata.aliases[0], "user_id");
    }
}
