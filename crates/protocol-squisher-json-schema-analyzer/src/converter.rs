// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from JSON Schema to protocol-squisher IR

use crate::{AnalyzerError, JsonSchema, SchemaType, SingleType};
use protocol_squisher_ir::{
    Constraint, ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, NumberValue,
    PrimitiveType, StructDef, TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata,
    VariantPayload,
};
use std::collections::{BTreeMap, HashSet};

/// Converter from JSON Schema to IR
#[derive(Debug, Default)]
pub struct SchemaConverter {
    /// Counter for generating anonymous type names
    type_counter: std::cell::Cell<usize>,
}

impl SchemaConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed JSON Schema to IR
    pub fn convert(&self, schema: &JsonSchema, name: &str) -> Result<IrSchema, AnalyzerError> {
        self.type_counter.set(0);

        let mut ir = IrSchema::new(name, "json-schema");
        let mut collected_types = BTreeMap::new();

        // First, collect all definitions
        for (def_name, def_schema) in &schema.definitions {
            self.collect_type(def_name, def_schema, &mut collected_types)?;
        }
        for (def_name, def_schema) in &schema.defs {
            self.collect_type(def_name, def_schema, &mut collected_types)?;
        }

        // Convert the root schema
        let root_name = schema.title.as_deref().unwrap_or(name);
        self.collect_type(root_name, schema, &mut collected_types)?;

        // Add all collected types to the IR
        for (type_name, type_def) in collected_types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Collect a type definition from a schema
    fn collect_type(
        &self,
        name: &str,
        schema: &JsonSchema,
        types: &mut BTreeMap<String, TypeDef>,
    ) -> Result<(), AnalyzerError> {
        // Handle $ref
        if schema.ref_uri.is_some() {
            // References are resolved at conversion time, not collected
            return Ok(());
        }

        // Handle enum
        if let Some(enum_values) = &schema.enum_values {
            let enum_def = self.convert_enum(name, enum_values, schema)?;
            types.insert(name.to_string(), TypeDef::Enum(enum_def));
            return Ok(());
        }

        // Handle oneOf as tagged union
        if let Some(one_of) = &schema.one_of {
            let enum_def = self.convert_oneof(name, one_of, types)?;
            types.insert(name.to_string(), TypeDef::Enum(enum_def));
            return Ok(());
        }

        // Handle object type
        if matches!(
            &schema.schema_type,
            Some(SchemaType::Single(SingleType::Object))
        ) || !schema.properties.is_empty()
        {
            let struct_def = self.convert_object(name, schema, types)?;
            types.insert(name.to_string(), TypeDef::Struct(struct_def));
            return Ok(());
        }

        // Handle primitive types at root level (rare but possible)
        if let Some(schema_type) = &schema.schema_type {
            match schema_type {
                SchemaType::Single(single) => {
                    // For non-object primitives at root, create a wrapper struct
                    if *single != SingleType::Object {
                        let struct_def = StructDef {
                            name: name.to_string(),
                            fields: vec![FieldDef {
                                name: "value".to_string(),
                                ty: self.convert_single_type(single, schema)?,
                                optional: false,
                                constraints: self.extract_constraints(schema),
                                metadata: FieldMetadata::default(),
                            }],
                            metadata: TypeMetadata {
                                doc: schema.description.clone(),
                                ..Default::default()
                            },
                        };
                        types.insert(name.to_string(), TypeDef::Struct(struct_def));
                    }
                },
                SchemaType::Multiple(_) => {
                    // Multi-type schemas become unions
                    // For now, treat as Any
                },
            }
        }

        Ok(())
    }

    /// Convert a JSON Schema object to an IR struct
    fn convert_object(
        &self,
        name: &str,
        schema: &JsonSchema,
        types: &mut BTreeMap<String, TypeDef>,
    ) -> Result<StructDef, AnalyzerError> {
        let required_set: HashSet<&str> = schema.required.iter().map(|s| s.as_str()).collect();
        let mut fields = Vec::new();

        for (field_name, field_schema) in &schema.properties {
            let is_required = required_set.contains(field_name.as_str());
            let field_type = self.convert_schema_type(field_name, field_schema, types)?;

            let ty = if is_required {
                field_type
            } else {
                IrType::Container(ContainerType::Option(Box::new(field_type)))
            };

            let constraints = self.extract_constraints(field_schema);

            let metadata = FieldMetadata {
                doc: field_schema.description.clone(),
                default: field_schema.default.clone(),
                ..Default::default()
            };

            fields.push(FieldDef {
                name: field_name.clone(),
                ty,
                optional: !is_required,
                constraints,
                metadata,
            });
        }

        Ok(StructDef {
            name: name.to_string(),
            fields,
            metadata: TypeMetadata {
                doc: schema.description.clone(),
                ..Default::default()
            },
        })
    }

    /// Convert a schema to an IR type
    fn convert_schema_type(
        &self,
        context_name: &str,
        schema: &JsonSchema,
        types: &mut BTreeMap<String, TypeDef>,
    ) -> Result<IrType, AnalyzerError> {
        // Handle $ref
        if let Some(ref_uri) = &schema.ref_uri {
            let ref_name = self.extract_ref_name(ref_uri)?;
            return Ok(IrType::Reference(ref_name));
        }

        // Handle enum
        if let Some(enum_values) = &schema.enum_values {
            // Check if it's a simple string enum
            if enum_values.iter().all(|v| v.is_string()) {
                let enum_name = format!("{}Enum", self.to_pascal_case(context_name));
                if !types.contains_key(&enum_name) {
                    let enum_def = self.convert_enum(&enum_name, enum_values, schema)?;
                    types.insert(enum_name.clone(), TypeDef::Enum(enum_def));
                }
                return Ok(IrType::Reference(enum_name));
            }
        }

        // Handle oneOf
        if let Some(one_of) = &schema.one_of {
            let union_name = format!("{}Union", self.to_pascal_case(context_name));
            if !types.contains_key(&union_name) {
                let enum_def = self.convert_oneof(&union_name, one_of, types)?;
                types.insert(union_name.clone(), TypeDef::Enum(enum_def));
            }
            return Ok(IrType::Reference(union_name));
        }

        // Handle nested objects
        if matches!(
            &schema.schema_type,
            Some(SchemaType::Single(SingleType::Object))
        ) || !schema.properties.is_empty()
        {
            let nested_name = schema
                .title
                .clone()
                .unwrap_or_else(|| format!("{}Nested", self.to_pascal_case(context_name)));

            if !types.contains_key(&nested_name) {
                let struct_def = self.convert_object(&nested_name, schema, types)?;
                types.insert(nested_name.clone(), TypeDef::Struct(struct_def));
            }
            return Ok(IrType::Reference(nested_name));
        }

        // Handle typed schemas
        if let Some(schema_type) = &schema.schema_type {
            return self.convert_type(schema_type, schema, context_name, types);
        }

        // Default to Any
        Ok(IrType::Special(protocol_squisher_ir::SpecialType::Any))
    }

    /// Convert a schema type to IR type
    fn convert_type(
        &self,
        schema_type: &SchemaType,
        schema: &JsonSchema,
        _context_name: &str,
        _types: &mut BTreeMap<String, TypeDef>,
    ) -> Result<IrType, AnalyzerError> {
        match schema_type {
            SchemaType::Single(single) => self.convert_single_type(single, schema),
            SchemaType::Multiple(multi) => {
                // Handle nullable types (e.g., ["string", "null"])
                if multi.len() == 2 && multi.contains(&SingleType::Null) {
                    let non_null: Vec<_> =
                        multi.iter().filter(|t| **t != SingleType::Null).collect();
                    if non_null.len() == 1 {
                        let inner = self.convert_single_type(non_null[0], schema)?;
                        return Ok(IrType::Container(ContainerType::Option(Box::new(inner))));
                    }
                }

                // For other multi-types, use Any for now
                // (proper union support would require creating a Union type definition)
                Ok(IrType::Special(protocol_squisher_ir::SpecialType::Any))
            },
        }
    }

    /// Convert a single JSON Schema type to IR type
    fn convert_single_type(
        &self,
        single: &SingleType,
        schema: &JsonSchema,
    ) -> Result<IrType, AnalyzerError> {
        match single {
            SingleType::String => {
                // Check format hints
                if let Some(format) = &schema.format {
                    match format.as_str() {
                        "date-time" => return Ok(IrType::Primitive(PrimitiveType::DateTime)),
                        "date" => return Ok(IrType::Primitive(PrimitiveType::Date)),
                        "time" => return Ok(IrType::Primitive(PrimitiveType::Time)),
                        "uuid" => return Ok(IrType::Primitive(PrimitiveType::Uuid)),
                        "byte" => return Ok(IrType::Primitive(PrimitiveType::Bytes)),
                        "uri" | "uri-reference" => {
                            // URI is represented as String with format constraint
                            return Ok(IrType::Primitive(PrimitiveType::String));
                        },
                        _ => {},
                    }
                }
                Ok(IrType::Primitive(PrimitiveType::String))
            },
            SingleType::Number => Ok(IrType::Primitive(PrimitiveType::F64)),
            SingleType::Integer => Ok(IrType::Primitive(PrimitiveType::I64)),
            SingleType::Boolean => Ok(IrType::Primitive(PrimitiveType::Bool)),
            SingleType::Null => Ok(IrType::Special(protocol_squisher_ir::SpecialType::Unit)),
            SingleType::Array => {
                if let Some(items) = &schema.items {
                    let item_type =
                        self.convert_schema_type("Item", items, &mut BTreeMap::new())?;
                    Ok(IrType::Container(ContainerType::Vec(Box::new(item_type))))
                } else {
                    // Array with no item type - use Any
                    Ok(IrType::Container(ContainerType::Vec(Box::new(
                        IrType::Special(protocol_squisher_ir::SpecialType::Any),
                    ))))
                }
            },
            SingleType::Object => {
                // Generic object without properties - use Map<String, Any>
                Ok(IrType::Container(ContainerType::Map(
                    Box::new(IrType::Primitive(PrimitiveType::String)),
                    Box::new(IrType::Special(protocol_squisher_ir::SpecialType::Any)),
                )))
            },
        }
    }

    /// Convert enum values to IR enum
    fn convert_enum(
        &self,
        name: &str,
        values: &[serde_json::Value],
        schema: &JsonSchema,
    ) -> Result<EnumDef, AnalyzerError> {
        let variants: Vec<VariantDef> = values
            .iter()
            .filter_map(|v| match v {
                serde_json::Value::String(s) => Some(VariantDef {
                    name: self.to_pascal_case(s),
                    payload: None, // Unit variant
                    metadata: VariantMetadata {
                        doc: None,
                        aliases: vec![s.clone()],
                        serde_hints: Default::default(),
                    },
                }),
                serde_json::Value::Number(n) => Some(VariantDef {
                    name: format!("Value{}", n),
                    payload: None, // Unit variant
                    metadata: Default::default(),
                }),
                _ => None,
            })
            .collect();

        Ok(EnumDef {
            name: name.to_string(),
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata {
                doc: schema.description.clone(),
                ..Default::default()
            },
        })
    }

    /// Convert oneOf to IR enum (tagged union)
    fn convert_oneof(
        &self,
        name: &str,
        schemas: &[JsonSchema],
        types: &mut BTreeMap<String, TypeDef>,
    ) -> Result<EnumDef, AnalyzerError> {
        let mut variants = Vec::new();

        for (i, variant_schema) in schemas.iter().enumerate() {
            let variant_name = variant_schema
                .title
                .clone()
                .unwrap_or_else(|| format!("Variant{}", i));

            // Determine payload type
            let payload = if variant_schema.properties.is_empty()
                && variant_schema.schema_type.is_none()
            {
                None // Unit variant
            } else if !variant_schema.properties.is_empty() {
                // Create nested struct for this variant
                let struct_name = format!("{}{}", name, variant_name);
                let struct_def = self.convert_object(&struct_name, variant_schema, types)?;
                types.insert(struct_name.clone(), TypeDef::Struct(struct_def));
                // Struct variant with named fields
                Some(VariantPayload::Struct(vec![FieldDef {
                    name: "data".to_string(),
                    ty: IrType::Reference(struct_name),
                    optional: false,
                    constraints: vec![],
                    metadata: Default::default(),
                }]))
            } else if let Some(schema_type) = &variant_schema.schema_type {
                let ty = self.convert_type(schema_type, variant_schema, &variant_name, types)?;
                Some(VariantPayload::Tuple(vec![ty]))
            } else {
                None // Unit variant
            };

            variants.push(VariantDef {
                name: self.to_pascal_case(&variant_name),
                payload,
                metadata: VariantMetadata {
                    doc: variant_schema.description.clone(),
                    ..Default::default()
                },
            });
        }

        Ok(EnumDef {
            name: name.to_string(),
            variants,
            tag_style: TagStyle::External,
            metadata: Default::default(),
        })
    }

    /// Extract constraints from a schema
    fn extract_constraints(&self, schema: &JsonSchema) -> Vec<Constraint> {
        let mut constraints = Vec::new();

        // Numeric constraints - use Min/Max with NumberValue
        if let Some(min) = schema.minimum {
            constraints.push(Constraint::Min(NumberValue::Float(min)));
        }
        if let Some(max) = schema.maximum {
            constraints.push(Constraint::Max(NumberValue::Float(max)));
        }

        // Handle exclusive constraints - convert to regular Min/Max with adjustment
        if let Some(ex_min) = &schema.exclusive_minimum {
            if let Some(n) = ex_min.as_f64() {
                // For exclusive minimum, we can use Min with the value
                // (the semantic difference is handled at validation time)
                constraints.push(Constraint::Min(NumberValue::Float(n)));
            }
            // draft-04 style: exclusiveMinimum: true with minimum is handled by minimum above
        }
        if let Some(ex_max) = &schema.exclusive_maximum {
            if let Some(n) = ex_max.as_f64() {
                constraints.push(Constraint::Max(NumberValue::Float(n)));
            }
            // draft-04 style handled by maximum above
        }

        if let Some(mult) = schema.multiple_of {
            constraints.push(Constraint::MultipleOf(NumberValue::Float(mult)));
        }

        // String constraints
        if let Some(min) = schema.min_length {
            constraints.push(Constraint::MinLength(min as usize));
        }
        if let Some(max) = schema.max_length {
            constraints.push(Constraint::MaxLength(max as usize));
        }
        if let Some(pattern) = &schema.pattern {
            constraints.push(Constraint::Pattern(pattern.clone()));
        }

        // Array constraints
        if let Some(min) = schema.min_items {
            constraints.push(Constraint::MinItems(min as usize));
        }
        if let Some(max) = schema.max_items {
            constraints.push(Constraint::MaxItems(max as usize));
        }
        if schema.unique_items == Some(true) {
            constraints.push(Constraint::UniqueItems);
        }

        constraints
    }

    /// Extract reference name from a $ref URI
    fn extract_ref_name(&self, ref_uri: &str) -> Result<String, AnalyzerError> {
        // Handle local references like "#/$defs/Address" or "#/definitions/Address"
        if let Some(rest) = ref_uri.strip_prefix("#/") {
            let parts: Vec<&str> = rest.split('/').collect();
            if parts.len() >= 2 {
                if let Some(name) = parts.last() {
                    return Ok((*name).to_string());
                }
            }
        }

        // Handle simple anchor refs like "#Address"
        if let Some(name) = ref_uri.strip_prefix('#') {
            return Ok(name.to_string());
        }

        Err(AnalyzerError::ReferenceError(format!(
            "Unsupported reference format: {}",
            ref_uri
        )))
    }

    /// Convert string to PascalCase
    fn to_pascal_case(&self, s: &str) -> String {
        let mut result = String::new();
        let mut capitalize_next = true;

        for c in s.chars() {
            if c == '_' || c == '-' || c == ' ' {
                capitalize_next = true;
            } else if capitalize_next {
                result.extend(c.to_uppercase());
                capitalize_next = false;
            } else {
                result.push(c);
            }
        }

        result
    }

    /// Generate a unique anonymous type name
    #[allow(dead_code)]
    fn generate_type_name(&self, prefix: &str) -> String {
        let counter = self.type_counter.get();
        self.type_counter.set(counter + 1);
        format!("{}{}", prefix, counter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_and_convert(json: &str, name: &str) -> Result<IrSchema, AnalyzerError> {
        let schema: JsonSchema = serde_json::from_str(json).unwrap();
        let converter = SchemaConverter::new();
        converter.convert(&schema, name)
    }

    #[test]
    fn test_simple_object() {
        let json = r#"{
            "type": "object",
            "properties": {
                "name": { "type": "string" },
                "age": { "type": "integer" }
            },
            "required": ["name"]
        }"#;

        let ir = parse_and_convert(json, "Person").unwrap();
        assert!(ir.types.contains_key("Person"));

        let TypeDef::Struct(s) = &ir.types["Person"] else {
            unreachable!("Person should convert to struct");
        };
        assert_eq!(s.fields.len(), 2);

        let name_field = s.fields.iter().find(|f| f.name == "name").unwrap();
        assert!(!name_field.optional);

        let age_field = s.fields.iter().find(|f| f.name == "age").unwrap();
        assert!(age_field.optional);
    }

    #[test]
    fn test_string_enum() {
        let json = r#"{
            "type": "object",
            "properties": {
                "status": {
                    "type": "string",
                    "enum": ["pending", "active", "done"]
                }
            }
        }"#;

        let ir = parse_and_convert(json, "Task").unwrap();
        assert!(ir.types.contains_key("StatusEnum"));

        let TypeDef::Enum(e) = &ir.types["StatusEnum"] else {
            unreachable!("StatusEnum should convert to enum");
        };
        assert_eq!(e.variants.len(), 3);
    }

    #[test]
    fn test_constraints() {
        let json = r#"{
            "type": "object",
            "properties": {
                "count": {
                    "type": "integer",
                    "minimum": 0,
                    "maximum": 100
                },
                "name": {
                    "type": "string",
                    "minLength": 1,
                    "maxLength": 50
                }
            }
        }"#;

        let ir = parse_and_convert(json, "Constrained").unwrap();

        if let TypeDef::Struct(s) = &ir.types["Constrained"] {
            let count = s.fields.iter().find(|f| f.name == "count").unwrap();
            assert!(count
                .constraints
                .iter()
                .any(|c| matches!(c, Constraint::Min(NumberValue::Float(v)) if *v == 0.0)));
            assert!(count
                .constraints
                .iter()
                .any(|c| matches!(c, Constraint::Max(NumberValue::Float(v)) if *v == 100.0)));

            let name = s.fields.iter().find(|f| f.name == "name").unwrap();
            assert!(name
                .constraints
                .iter()
                .any(|c| matches!(c, Constraint::MinLength(1))));
            assert!(name
                .constraints
                .iter()
                .any(|c| matches!(c, Constraint::MaxLength(50))));
        }
    }

    #[test]
    fn test_refs() {
        let json = r##"{
            "$defs": {
                "Address": {
                    "type": "object",
                    "properties": {
                        "street": { "type": "string" }
                    }
                }
            },
            "type": "object",
            "properties": {
                "home": { "$ref": "#/$defs/Address" }
            }
        }"##;

        let ir = parse_and_convert(json, "Customer").unwrap();
        assert!(ir.types.contains_key("Address"));

        if let TypeDef::Struct(s) = &ir.types["Customer"] {
            let home = s.fields.iter().find(|f| f.name == "home").unwrap();
            // The type should be an Option since it's not required
            if let IrType::Container(ContainerType::Option(inner)) = &home.ty {
                assert!(matches!(inner.as_ref(), IrType::Reference(name) if name == "Address"));
            }
        }
    }

    #[test]
    fn test_array_type() {
        let json = r#"{
            "type": "object",
            "properties": {
                "tags": {
                    "type": "array",
                    "items": { "type": "string" }
                }
            }
        }"#;

        let ir = parse_and_convert(json, "Tagged").unwrap();

        if let TypeDef::Struct(s) = &ir.types["Tagged"] {
            let tags = s.fields.iter().find(|f| f.name == "tags").unwrap();
            // Optional Vec<String>
            if let IrType::Container(ContainerType::Option(inner)) = &tags.ty {
                assert!(matches!(
                    inner.as_ref(),
                    IrType::Container(ContainerType::Vec(_))
                ));
            }
        }
    }

    #[test]
    fn test_nullable_type() {
        let json = r#"{
            "type": "object",
            "properties": {
                "nickname": {
                    "type": ["string", "null"]
                }
            }
        }"#;

        let ir = parse_and_convert(json, "User").unwrap();

        if let TypeDef::Struct(s) = &ir.types["User"] {
            let nickname = s.fields.iter().find(|f| f.name == "nickname").unwrap();
            // Should be Option<Option<String>> due to being both nullable type and not required
            assert!(matches!(
                &nickname.ty,
                IrType::Container(ContainerType::Option(_))
            ));
        }
    }

    #[test]
    fn test_pascal_case() {
        let converter = SchemaConverter::new();
        assert_eq!(converter.to_pascal_case("hello_world"), "HelloWorld");
        assert_eq!(converter.to_pascal_case("hello-world"), "HelloWorld");
        assert_eq!(converter.to_pascal_case("hello world"), "HelloWorld");
        assert_eq!(converter.to_pascal_case("pending"), "Pending");
    }
}
