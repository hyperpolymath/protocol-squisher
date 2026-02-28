// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Convert parsed TOML into Protocol Squisher IR.
//!
//! TOML type inference mappings:
//! - Tables → `StructDef` (each key becomes a field)
//! - Arrays → `ContainerType::Vec` of the inferred element type
//! - String → `PrimitiveType::String`
//! - Integer → `PrimitiveType::I64` (TOML integers are 64-bit)
//! - Float → `PrimitiveType::F64`
//! - Boolean → `PrimitiveType::Bool`
//! - DateTime → `PrimitiveType::DateTime`
//! - Array of tables → `Vec<StructDef>`

use crate::parser::*;
use crate::AnalyzerError;
use protocol_squisher_ir::*;

/// Converter from parsed TOML to IR.
#[derive(Debug, Default)]
pub struct TomlConverter {}

impl TomlConverter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed TOML document into an `IrSchema`.
    pub fn convert(&self, parsed: &ParsedToml, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut schema = IrSchema::new(name, "toml");

        // The root table becomes the root struct.
        let root_name = to_pascal_case(name);
        let root_struct = self.convert_table_entries(&parsed.entries, &root_name, &mut schema);
        schema.add_type(root_name.clone(), TypeDef::Struct(root_struct));
        schema.add_root(root_name);

        Ok(schema)
    }

    /// Convert a list of TOML entries into an IR struct definition.
    fn convert_table_entries(
        &self,
        entries: &[TomlEntry],
        parent_name: &str,
        schema: &mut IrSchema,
    ) -> StructDef {
        let fields = entries
            .iter()
            .map(|entry| {
                let ty = self.convert_value(&entry.value, &entry.key, parent_name, schema);
                FieldDef {
                    name: entry.key.clone(),
                    ty,
                    optional: false, // TOML keys are always present.
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }
            })
            .collect();

        StructDef {
            name: parent_name.to_string(),
            fields,
            metadata: TypeMetadata {
                doc: Some(format!("TOML table {parent_name}")),
                ..Default::default()
            },
        }
    }

    /// Convert a TOML value to an IR type.
    fn convert_value(
        &self,
        value: &TomlValue,
        key: &str,
        parent_name: &str,
        schema: &mut IrSchema,
    ) -> IrType {
        match value {
            TomlValue::String(_) => IrType::Primitive(PrimitiveType::String),
            TomlValue::Integer(_) => IrType::Primitive(PrimitiveType::I64),
            TomlValue::Float(_) => IrType::Primitive(PrimitiveType::F64),
            TomlValue::Boolean(_) => IrType::Primitive(PrimitiveType::Bool),
            TomlValue::DateTime(_) => IrType::Primitive(PrimitiveType::DateTime),
            TomlValue::Table(entries) => {
                let struct_name = format!("{parent_name}_{}", to_pascal_case(key));
                let struct_def = self.convert_table_entries(entries, &struct_name, schema);
                schema.add_type(struct_name.clone(), TypeDef::Struct(struct_def));
                IrType::Reference(struct_name)
            },
            TomlValue::Array(elements) => {
                if elements.is_empty() {
                    // Empty array — default to Vec<String>.
                    IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
                        PrimitiveType::String,
                    ))))
                } else {
                    // Infer type from first element.
                    let elem_ty = self.convert_value(&elements[0], key, parent_name, schema);
                    IrType::Container(ContainerType::Vec(Box::new(elem_ty)))
                }
            },
        }
    }
}

/// Convert a snake_case or kebab-case string to PascalCase.
fn to_pascal_case(s: &str) -> String {
    s.split(['_', '-', '.'])
        .filter(|part| !part.is_empty())
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(first) => {
                    let mut result = first.to_uppercase().to_string();
                    result.extend(chars.flat_map(|c| c.to_lowercase()));
                    result
                },
                None => String::new(),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_pascal_case_works() {
        assert_eq!(to_pascal_case("hello_world"), "HelloWorld");
        assert_eq!(to_pascal_case("my-config"), "MyConfig");
        assert_eq!(to_pascal_case("simple"), "Simple");
        assert_eq!(to_pascal_case("a.b.c"), "ABC");
    }

    #[test]
    fn converts_basic_types() {
        let converter = TomlConverter::new();
        let mut schema = IrSchema::new("test", "toml");

        let entries = vec![
            TomlEntry {
                key: "name".to_string(),
                value: TomlValue::String("test".to_string()),
            },
            TomlEntry {
                key: "count".to_string(),
                value: TomlValue::Integer(42),
            },
            TomlEntry {
                key: "ratio".to_string(),
                value: TomlValue::Float(3.14),
            },
            TomlEntry {
                key: "debug".to_string(),
                value: TomlValue::Boolean(true),
            },
        ];

        let struct_def = converter.convert_table_entries(&entries, "Root", &mut schema);
        assert_eq!(struct_def.fields.len(), 4);
        assert!(matches!(
            struct_def.fields[0].ty,
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            struct_def.fields[1].ty,
            IrType::Primitive(PrimitiveType::I64)
        ));
    }
}
