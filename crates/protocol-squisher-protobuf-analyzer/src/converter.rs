// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Converter from parsed Protobuf to protocol-squisher IR

use crate::parser::{FieldLabel, ParsedProto, ProtoEnum, ProtoField, ProtoMessage, ProtoOneof};
use crate::{AnalyzerError, ProtoSyntax};
use protocol_squisher_ir::{
    ContainerType, EnumDef, FieldDef, FieldMetadata, IrSchema, IrType, PrimitiveType, StructDef,
    TagStyle, TypeDef, TypeMetadata, VariantDef, VariantMetadata, VariantPayload,
};
use std::collections::BTreeMap;

/// Converter from parsed protobuf to IR
#[derive(Debug, Default)]
pub struct ProtoConverter {}

impl ProtoConverter {
    /// Create a new converter
    pub fn new() -> Self {
        Self::default()
    }

    /// Convert a parsed protobuf to IR schema
    pub fn convert(&self, parsed: &ParsedProto, name: &str) -> Result<IrSchema, AnalyzerError> {
        let mut ir = IrSchema::new(name, "protobuf");
        let mut types = BTreeMap::new();

        let syntax = parsed.syntax;

        // Convert top-level enums
        for proto_enum in &parsed.enums {
            let enum_def = self.convert_enum(proto_enum, "")?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert top-level messages
        for message in &parsed.messages {
            self.convert_message(message, "", syntax, &mut types)?;
        }

        // Add all types to IR
        for (type_name, type_def) in types {
            ir.add_type(type_name, type_def);
        }

        Ok(ir)
    }

    /// Convert a protobuf message to IR struct
    fn convert_message(
        &self,
        message: &ProtoMessage,
        prefix: &str,
        syntax: ProtoSyntax,
        types: &mut BTreeMap<String, TypeDef>,
    ) -> Result<String, AnalyzerError> {
        let full_name = if prefix.is_empty() {
            message.name.clone()
        } else {
            format!("{}_{}", prefix, message.name)
        };

        // Convert nested enums first
        for nested_enum in &message.nested_enums {
            let enum_def = self.convert_enum(nested_enum, &full_name)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert nested messages
        for nested_message in &message.nested_messages {
            self.convert_message(nested_message, &full_name, syntax, types)?;
        }

        // Convert oneof groups to enum types
        for oneof in &message.oneofs {
            let enum_def = self.convert_oneof(&full_name, oneof)?;
            types.insert(enum_def.name.clone(), TypeDef::Enum(enum_def));
        }

        // Convert fields
        let mut fields = Vec::new();

        // Add oneof fields as optional enum references
        for oneof in &message.oneofs {
            let oneof_type_name = format!("{}_{}", full_name, to_pascal_case(&oneof.name));
            fields.push(FieldDef {
                name: oneof.name.clone(),
                ty: IrType::Container(ContainerType::Option(Box::new(IrType::Reference(
                    oneof_type_name,
                )))),
                optional: true,
                constraints: vec![],
                metadata: FieldMetadata::default(),
            });
        }

        // Convert regular fields
        for field in &message.fields {
            let field_def = self.convert_field(field, syntax, &full_name)?;
            fields.push(field_def);
        }

        let struct_def = StructDef {
            name: full_name.clone(),
            fields,
            metadata: TypeMetadata::default(),
        };

        types.insert(full_name.clone(), TypeDef::Struct(struct_def));
        Ok(full_name)
    }

    /// Convert a protobuf field to IR field
    fn convert_field(
        &self,
        field: &ProtoField,
        syntax: ProtoSyntax,
        _message_prefix: &str,
    ) -> Result<FieldDef, AnalyzerError> {
        let field_type = self.convert_field_type(field)?;

        // Determine if field is optional
        let is_repeated = field.label == FieldLabel::Repeated;
        let is_optional = match syntax {
            ProtoSyntax::Proto2 => field.label == FieldLabel::Optional,
            ProtoSyntax::Proto3 => {
                // In proto3, all scalar fields have implicit defaults
                // We treat them as non-optional unless explicitly marked
                field.label == FieldLabel::Optional
            }
        };

        let ty = if is_repeated {
            // Check if this is a map field
            if field.field_type == "map" {
                self.convert_map_type(field)?
            } else {
                IrType::Container(ContainerType::Vec(Box::new(field_type)))
            }
        } else if is_optional {
            IrType::Container(ContainerType::Option(Box::new(field_type)))
        } else {
            field_type
        };

        Ok(FieldDef {
            name: field.name.clone(),
            ty,
            optional: is_optional || is_repeated,
            constraints: vec![],
            metadata: FieldMetadata {
                doc: None,
                default: None,
                aliases: vec![],
                flatten: false,
                skip: false,
                serde_hints: BTreeMap::new(),
            },
        })
    }

    /// Convert a protobuf field type string to IR type
    fn convert_field_type(&self, field: &ProtoField) -> Result<IrType, AnalyzerError> {
        match field.field_type.as_str() {
            "double" => Ok(IrType::Primitive(PrimitiveType::F64)),
            "float" => Ok(IrType::Primitive(PrimitiveType::F32)),
            "int64" | "sint64" | "sfixed64" => Ok(IrType::Primitive(PrimitiveType::I64)),
            "uint64" | "fixed64" => Ok(IrType::Primitive(PrimitiveType::U64)),
            "int32" | "sint32" | "sfixed32" => Ok(IrType::Primitive(PrimitiveType::I32)),
            "uint32" | "fixed32" => Ok(IrType::Primitive(PrimitiveType::U32)),
            "bool" => Ok(IrType::Primitive(PrimitiveType::Bool)),
            "string" => Ok(IrType::Primitive(PrimitiveType::String)),
            "bytes" => Ok(IrType::Primitive(PrimitiveType::Bytes)),
            "map" => {
                // Map types are handled separately in convert_map_type
                Ok(IrType::Special(protocol_squisher_ir::SpecialType::Any))
            }
            type_name => {
                // Reference to another message or enum
                let ref_name = normalize_type_name(type_name);
                Ok(IrType::Reference(ref_name))
            }
        }
    }

    /// Convert a map field to IR type
    fn convert_map_type(&self, field: &ProtoField) -> Result<IrType, AnalyzerError> {
        let key_type = field
            .map_key_type
            .as_ref()
            .map(|k| self.proto_type_to_ir(k))
            .unwrap_or_else(|| IrType::Primitive(PrimitiveType::String));

        let value_type = field
            .map_value_type
            .as_ref()
            .map(|v| self.proto_type_to_ir(v))
            .unwrap_or_else(|| IrType::Special(protocol_squisher_ir::SpecialType::Any));

        Ok(IrType::Container(ContainerType::Map(
            Box::new(key_type),
            Box::new(value_type),
        )))
    }

    /// Convert a protobuf type string to IR type
    fn proto_type_to_ir(&self, type_str: &str) -> IrType {
        match type_str {
            "double" => IrType::Primitive(PrimitiveType::F64),
            "float" => IrType::Primitive(PrimitiveType::F32),
            "int64" | "sint64" | "sfixed64" => IrType::Primitive(PrimitiveType::I64),
            "uint64" | "fixed64" => IrType::Primitive(PrimitiveType::U64),
            "int32" | "sint32" | "sfixed32" => IrType::Primitive(PrimitiveType::I32),
            "uint32" | "fixed32" => IrType::Primitive(PrimitiveType::U32),
            "bool" => IrType::Primitive(PrimitiveType::Bool),
            "string" => IrType::Primitive(PrimitiveType::String),
            "bytes" => IrType::Primitive(PrimitiveType::Bytes),
            type_name => IrType::Reference(normalize_type_name(type_name)),
        }
    }

    /// Convert a protobuf enum to IR enum
    fn convert_enum(&self, proto_enum: &ProtoEnum, prefix: &str) -> Result<EnumDef, AnalyzerError> {
        let full_name = if prefix.is_empty() {
            proto_enum.name.clone()
        } else {
            format!("{}_{}", prefix, proto_enum.name)
        };

        let variants: Vec<VariantDef> = proto_enum
            .values
            .iter()
            .map(|v| VariantDef {
                name: to_pascal_case(&v.name),
                payload: None, // Protobuf enums don't have payloads
                metadata: VariantMetadata {
                    doc: None,
                    aliases: vec![v.name.clone()],
                    serde_hints: BTreeMap::new(),
                },
            })
            .collect();

        Ok(EnumDef {
            name: full_name,
            variants,
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        })
    }

    /// Convert a oneof to IR enum
    fn convert_oneof(&self, message_name: &str, oneof: &ProtoOneof) -> Result<EnumDef, AnalyzerError> {
        let full_name = format!("{}_{}", message_name, to_pascal_case(&oneof.name));

        let variants: Result<Vec<VariantDef>, AnalyzerError> = oneof
            .fields
            .iter()
            .map(|field| {
                let field_type = self.convert_field_type(field)?;

                Ok(VariantDef {
                    name: to_pascal_case(&field.name),
                    payload: Some(VariantPayload::Tuple(vec![field_type])),
                    metadata: VariantMetadata {
                        doc: None,
                        aliases: vec![field.name.clone()],
                        serde_hints: BTreeMap::new(),
                    },
                })
            })
            .collect();

        Ok(EnumDef {
            name: full_name,
            variants: variants?,
            tag_style: TagStyle::External,
            metadata: TypeMetadata::default(),
        })
    }
}

/// Convert snake_case or SCREAMING_CASE to PascalCase
fn to_pascal_case(s: &str) -> String {
    let mut result = String::new();
    let mut capitalize_next = true;

    for c in s.chars() {
        if c == '_' {
            capitalize_next = true;
        } else if capitalize_next {
            result.extend(c.to_uppercase());
            capitalize_next = false;
        } else {
            result.push(c.to_ascii_lowercase());
        }
    }

    result
}

/// Normalize a protobuf type name to a simple reference name
fn normalize_type_name(type_name: &str) -> String {
    // Type names in protobuf can be like ".package.Message" or "Message"
    // We want just the simple name, with nested messages using underscore
    let name = type_name.trim_start_matches('.');

    // Replace dots with underscores for nested types
    name.replace('.', "_")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("hello_world"), "HelloWorld");
        assert_eq!(to_pascal_case("ACTIVE"), "Active");
        assert_eq!(to_pascal_case("user_name"), "UserName");
        assert_eq!(to_pascal_case("STATUS_UNKNOWN"), "StatusUnknown");
    }

    #[test]
    fn test_normalize_type_name() {
        assert_eq!(normalize_type_name(".Person"), "Person");
        assert_eq!(normalize_type_name("Person"), "Person");
        assert_eq!(normalize_type_name(".package.Person"), "package_Person");
        assert_eq!(normalize_type_name("Person.Address"), "Person_Address");
    }

    #[test]
    fn test_proto_type_to_ir() {
        let converter = ProtoConverter::new();

        assert!(matches!(
            converter.proto_type_to_ir("string"),
            IrType::Primitive(PrimitiveType::String)
        ));
        assert!(matches!(
            converter.proto_type_to_ir("int32"),
            IrType::Primitive(PrimitiveType::I32)
        ));
        assert!(matches!(
            converter.proto_type_to_ir("bool"),
            IrType::Primitive(PrimitiveType::Bool)
        ));
        assert!(matches!(
            converter.proto_type_to_ir("MyMessage"),
            IrType::Reference(_)
        ));
    }
}
