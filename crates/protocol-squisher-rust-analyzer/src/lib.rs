// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! # Protocol Squisher Rust Analyzer
//!
//! Analyzes Rust source files to extract serde-compatible type definitions
//! and convert them to the canonical IR.
//!
//! ## Supported Patterns
//!
//! - `#[derive(Serialize, Deserialize)]` structs and enums
//! - Common serde attributes (`#[serde(rename = "...")]`, etc.)
//! - Standard library types (Option, Vec, HashMap, etc.)
//! - Custom newtypes and type aliases
//!
//! ## Usage
//!
//! ```rust,ignore
//! use protocol_squisher_rust_analyzer::RustAnalyzer;
//!
//! let source = r#"
//!     #[derive(Serialize, Deserialize)]
//!     struct User {
//!         id: u64,
//!         name: String,
//!     }
//! "#;
//!
//! let analyzer = RustAnalyzer::new();
//! let schema = analyzer.analyze_source(source)?;
//! ```

use protocol_squisher_ir::{
    Constraint, EnumDef, FieldDef, FieldMetadata, IrSchema, StringFormat, StructDef, TagStyle,
    TypeDef, TypeMetadata, VariantDef, VariantPayload,
};

mod attributes;
mod converter;
mod ephapax_bridge;
mod parser;

pub use attributes::*;
pub use converter::*;
pub use ephapax_bridge::*;
pub use parser::*;

/// Errors that can occur during Rust analysis
#[derive(Debug, Clone)]
pub enum AnalyzerError {
    /// Failed to parse Rust source
    ParseError(String),
    /// Unsupported Rust construct
    UnsupportedConstruct(String),
    /// Missing required derive
    MissingDerive(String),
    /// Invalid serde attribute
    InvalidAttribute(String),
}

impl std::fmt::Display for AnalyzerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnalyzerError::ParseError(msg) => write!(f, "Parse error: {msg}"),
            AnalyzerError::UnsupportedConstruct(msg) => write!(f, "Unsupported: {msg}"),
            AnalyzerError::MissingDerive(msg) => write!(f, "Missing derive: {msg}"),
            AnalyzerError::InvalidAttribute(msg) => write!(f, "Invalid attribute: {msg}"),
        }
    }
}

impl std::error::Error for AnalyzerError {}

/// Rust source analyzer
pub struct RustAnalyzer {
    /// Whether to require serde derives
    require_serde: bool,
    /// Whether to include private fields
    include_private: bool,
}

impl Default for RustAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl RustAnalyzer {
    /// Create a new analyzer with default settings
    pub fn new() -> Self {
        Self {
            require_serde: true,
            include_private: false,
        }
    }

    /// Set whether to require serde derives
    pub fn require_serde(mut self, require: bool) -> Self {
        self.require_serde = require;
        self
    }

    /// Set whether to include private fields
    pub fn include_private(mut self, include: bool) -> Self {
        self.include_private = include;
        self
    }

    /// Analyze Rust source code and extract schema
    pub fn analyze_source(&self, source: &str) -> Result<IrSchema, AnalyzerError> {
        let file = syn::parse_file(source).map_err(|e| AnalyzerError::ParseError(e.to_string()))?;

        let mut schema = IrSchema::new("rust-schema", "rust-serde");

        for item in &file.items {
            match item {
                syn::Item::Struct(item_struct) => {
                    if let Some(type_def) = self.analyze_struct(item_struct)? {
                        let name = item_struct.ident.to_string();
                        schema.add_type(name.clone(), type_def);
                        schema.add_root(name);
                    }
                },
                syn::Item::Enum(item_enum) => {
                    if let Some(type_def) = self.analyze_enum(item_enum)? {
                        let name = item_enum.ident.to_string();
                        schema.add_type(name.clone(), type_def);
                        schema.add_root(name);
                    }
                },
                syn::Item::Type(item_type) => {
                    if let Some(type_def) = self.analyze_type_alias(item_type)? {
                        let name = item_type.ident.to_string();
                        schema.add_type(name, type_def);
                    }
                },
                _ => {}, // Skip other items
            }
        }

        Ok(schema)
    }

    /// Analyze a struct definition
    fn analyze_struct(&self, item: &syn::ItemStruct) -> Result<Option<TypeDef>, AnalyzerError> {
        let attrs = SerdeAttributes::from_attrs(&item.attrs);

        // Check for serde derives if required
        if self.require_serde && !has_serde_derive(&item.attrs) {
            return Ok(None);
        }

        let fields = match &item.fields {
            syn::Fields::Named(named) => self.analyze_named_fields(&named.named, &attrs)?,
            syn::Fields::Unnamed(unnamed) => {
                // Tuple struct - convert to newtype if single field
                if unnamed.unnamed.len() == 1 {
                    let Some(field) = unnamed.unnamed.first() else {
                        return Err(AnalyzerError::UnsupportedConstruct(
                            "Tuple struct declared with one field but no field was found"
                                .to_string(),
                        ));
                    };
                    let inner_type = convert_type(&field.ty)?;
                    return Ok(Some(TypeDef::Newtype(protocol_squisher_ir::NewtypeDef {
                        name: item.ident.to_string(),
                        inner: inner_type,
                        constraints: vec![],
                        metadata: TypeMetadata {
                            doc: extract_doc_comment(&item.attrs),
                            ..Default::default()
                        },
                    })));
                }
                return Err(AnalyzerError::UnsupportedConstruct(
                    "Tuple structs with multiple fields not yet supported".to_string(),
                ));
            },
            syn::Fields::Unit => {
                // Unit struct
                vec![]
            },
        };

        Ok(Some(TypeDef::Struct(StructDef {
            name: item.ident.to_string(),
            fields,
            metadata: TypeMetadata {
                doc: extract_doc_comment(&item.attrs),
                serde_hints: attrs.to_hints(),
                ..Default::default()
            },
        })))
    }

    /// Analyze named fields
    fn analyze_named_fields(
        &self,
        fields: &syn::punctuated::Punctuated<syn::Field, syn::token::Comma>,
        _parent_attrs: &SerdeAttributes,
    ) -> Result<Vec<FieldDef>, AnalyzerError> {
        let mut result = Vec::new();

        for field in fields {
            // Skip private fields if not including them
            if !self.include_private {
                if let syn::Visibility::Inherited = field.vis {
                    // Private field, but we'll include it anyway for serde
                    // (serde serializes private fields by default)
                }
            }

            let field_attrs = SerdeAttributes::from_attrs(&field.attrs);

            // Skip fields marked with #[serde(skip)]
            if field_attrs.skip {
                continue;
            }

            let name = field
                .ident
                .as_ref()
                .map(|i| i.to_string())
                .unwrap_or_default();

            let ty = convert_type(&field.ty)?;
            let optional = is_option_type(&field.ty) || field_attrs.default;

            result.push(FieldDef {
                name: field_attrs.rename.clone().unwrap_or(name),
                ty,
                optional,
                constraints: extract_field_constraints(&field.attrs),
                metadata: FieldMetadata {
                    doc: extract_doc_comment(&field.attrs),
                    default: field_attrs.default_value.clone(),
                    aliases: field_attrs.aliases.clone(),
                    flatten: field_attrs.flatten,
                    skip: field_attrs.skip,
                    serde_hints: field_attrs.to_hints(),
                },
            });
        }

        Ok(result)
    }

    /// Analyze an enum definition
    fn analyze_enum(&self, item: &syn::ItemEnum) -> Result<Option<TypeDef>, AnalyzerError> {
        let attrs = SerdeAttributes::from_attrs(&item.attrs);

        if self.require_serde && !has_serde_derive(&item.attrs) {
            return Ok(None);
        }

        let mut variants = Vec::new();

        for variant in &item.variants {
            let variant_attrs = SerdeAttributes::from_attrs(&variant.attrs);

            let payload = match &variant.fields {
                syn::Fields::Named(named) => {
                    let fields = self.analyze_named_fields(&named.named, &attrs)?;
                    Some(VariantPayload::Struct(fields))
                },
                syn::Fields::Unnamed(unnamed) => {
                    let types: Result<Vec<_>, _> = unnamed
                        .unnamed
                        .iter()
                        .map(|f| convert_type(&f.ty))
                        .collect();
                    Some(VariantPayload::Tuple(types?))
                },
                syn::Fields::Unit => None,
            };

            variants.push(VariantDef {
                name: variant_attrs
                    .rename
                    .clone()
                    .unwrap_or_else(|| variant.ident.to_string()),
                payload,
                metadata: protocol_squisher_ir::VariantMetadata {
                    doc: extract_doc_comment(&variant.attrs),
                    aliases: variant_attrs.aliases.clone(),
                    serde_hints: variant_attrs.to_hints(),
                },
            });
        }

        let tag_style = determine_tag_style(&attrs);

        Ok(Some(TypeDef::Enum(EnumDef {
            name: item.ident.to_string(),
            variants,
            tag_style,
            metadata: TypeMetadata {
                doc: extract_doc_comment(&item.attrs),
                serde_hints: attrs.to_hints(),
                ..Default::default()
            },
        })))
    }

    /// Analyze a type alias
    fn analyze_type_alias(&self, item: &syn::ItemType) -> Result<Option<TypeDef>, AnalyzerError> {
        let target = convert_type(&item.ty)?;

        Ok(Some(TypeDef::Alias(protocol_squisher_ir::AliasDef {
            name: item.ident.to_string(),
            target,
            metadata: TypeMetadata {
                doc: extract_doc_comment(&item.attrs),
                ..Default::default()
            },
        })))
    }
}

/// Check if a type has serde derive macros
fn has_serde_derive(attrs: &[syn::Attribute]) -> bool {
    for attr in attrs {
        if attr.path().is_ident("derive") {
            if let Ok(nested) = attr.parse_args_with(
                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
            ) {
                for path in nested {
                    let ident = path
                        .segments
                        .last()
                        .map(|s| s.ident.to_string())
                        .unwrap_or_default();
                    if ident == "Serialize" || ident == "Deserialize" {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Extract doc comments from attributes
fn extract_doc_comment(attrs: &[syn::Attribute]) -> Option<String> {
    let docs: Vec<String> = attrs
        .iter()
        .filter_map(|attr| {
            if attr.path().is_ident("doc") {
                if let syn::Meta::NameValue(nv) = &attr.meta {
                    if let syn::Expr::Lit(syn::ExprLit {
                        lit: syn::Lit::Str(s),
                        ..
                    }) = &nv.value
                    {
                        return Some(s.value().trim().to_string());
                    }
                }
            }
            None
        })
        .collect();

    if docs.is_empty() {
        None
    } else {
        Some(docs.join("\n"))
    }
}

/// Check if a type is Option<T>
fn is_option_type(ty: &syn::Type) -> bool {
    if let syn::Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            return segment.ident == "Option";
        }
    }
    false
}

/// Extract field constraints from attributes (e.g., validator crate)
fn extract_field_constraints(attrs: &[syn::Attribute]) -> Vec<Constraint> {
    let mut constraints = Vec::new();

    for attr in attrs {
        if !attr.path().is_ident("validate") {
            continue;
        }

        let _ = attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("length") {
                let mut min_len: Option<usize> = None;
                let mut max_len: Option<usize> = None;
                let mut exact_len: Option<usize> = None;

                meta.parse_nested_meta(|nested| {
                    if nested.path.is_ident("min") {
                        let lit: syn::LitInt = nested.value()?.parse()?;
                        min_len = lit.base10_parse::<usize>().ok();
                    } else if nested.path.is_ident("max") {
                        let lit: syn::LitInt = nested.value()?.parse()?;
                        max_len = lit.base10_parse::<usize>().ok();
                    } else if nested.path.is_ident("equal") {
                        let lit: syn::LitInt = nested.value()?.parse()?;
                        exact_len = lit.base10_parse::<usize>().ok();
                    }
                    Ok(())
                })?;

                if let Some(v) = min_len {
                    constraints.push(Constraint::MinLength(v));
                    if v > 0 {
                        constraints.push(Constraint::NonEmpty);
                    }
                }
                if let Some(v) = max_len {
                    constraints.push(Constraint::MaxLength(v));
                }
                if let Some(v) = exact_len {
                    constraints.push(Constraint::ExactLength(v));
                }
                return Ok(());
            }

            if meta.path.is_ident("email") {
                constraints.push(Constraint::Format(StringFormat::Email));
                return Ok(());
            }

            if meta.path.is_ident("url") {
                constraints.push(Constraint::Format(StringFormat::Uri));
                return Ok(());
            }

            if meta.path.is_ident("uuid") {
                constraints.push(Constraint::Format(StringFormat::Uuid));
                return Ok(());
            }

            if meta.path.is_ident("regex") {
                let mut pattern: Option<String> = None;
                meta.parse_nested_meta(|nested| {
                    if nested.path.is_ident("path") {
                        let lit: syn::LitStr = nested.value()?.parse()?;
                        pattern = Some(lit.value());
                    }
                    Ok(())
                })?;
                if let Some(value) = pattern {
                    constraints.push(Constraint::Pattern(value));
                }
                return Ok(());
            }

            Ok(())
        });
    }

    constraints
}

/// Determine tag style from serde attributes
fn determine_tag_style(attrs: &SerdeAttributes) -> TagStyle {
    if attrs.untagged {
        TagStyle::Untagged
    } else if let Some(ref tag) = attrs.tag {
        if let Some(ref content) = attrs.content {
            TagStyle::Adjacent {
                tag_field: tag.clone(),
                content_field: content.clone(),
            }
        } else {
            TagStyle::Internal {
                tag_field: tag.clone(),
            }
        }
    } else {
        TagStyle::External
    }
}

impl protocol_squisher_ir::SchemaAnalyzer for RustAnalyzer {
    type Error = AnalyzerError;

    fn analyzer_name(&self) -> &str {
        "rust"
    }

    fn supported_extensions(&self) -> &[&str] {
        &["rs"]
    }

    fn analyze_file(&self, path: &std::path::Path) -> Result<IrSchema, Self::Error> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| AnalyzerError::ParseError(format!("IO error: {e}")))?;
        self.analyze_source(&content)
    }

    fn analyze_str(&self, content: &str, _name: &str) -> Result<IrSchema, Self::Error> {
        self.analyze_source(content)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_schema_analyzer_trait() {
        use protocol_squisher_ir::SchemaAnalyzer;
        let analyzer = RustAnalyzer::new();
        assert_eq!(analyzer.analyzer_name(), "rust");
        assert!(analyzer.supported_extensions().contains(&"rs"));
        let source = r#"
            #[derive(Serialize, Deserialize)]
            struct Point { x: f64, y: f64 }
        "#;
        let schema = SchemaAnalyzer::analyze_str(&analyzer, source, "point").unwrap();
        assert!(schema.types.contains_key("Point"));
    }

    #[test]
    fn test_simple_struct() {
        let source = r#"
            #[derive(Serialize, Deserialize)]
            struct User {
                id: u64,
                name: String,
            }
        "#;

        let analyzer = RustAnalyzer::new();
        let schema = analyzer.analyze_source(source).unwrap();

        assert_eq!(schema.types.len(), 1);
        assert!(schema.types.contains_key("User"));
    }

    #[test]
    fn test_optional_field() {
        let source = r#"
            #[derive(Serialize, Deserialize)]
            struct Config {
                required: String,
                optional: Option<i32>,
            }
        "#;

        let analyzer = RustAnalyzer::new();
        let schema = analyzer.analyze_source(source).unwrap();

        let config = schema.types.get("Config");
        assert!(
            matches!(config, Some(TypeDef::Struct(_))),
            "Expected struct Config"
        );
        let Some(TypeDef::Struct(s)) = config else {
            unreachable!("asserted struct Config");
        };
        assert_eq!(s.fields.len(), 2);
        assert!(!s.fields[0].optional);
        assert!(s.fields[1].optional);
    }

    #[test]
    fn test_enum_variants() {
        let source = r#"
            #[derive(Serialize, Deserialize)]
            enum Status {
                Active,
                Inactive,
                Pending { reason: String },
            }
        "#;

        let analyzer = RustAnalyzer::new();
        let schema = analyzer.analyze_source(source).unwrap();

        let status = schema.types.get("Status");
        assert!(
            matches!(status, Some(TypeDef::Enum(_))),
            "Expected enum Status"
        );
        let Some(TypeDef::Enum(e)) = status else {
            unreachable!("asserted enum Status");
        };
        assert_eq!(e.variants.len(), 3);
        assert!(e.variants[0].payload.is_none()); // Unit variant
        assert!(e.variants[2].payload.is_some()); // Struct variant
    }

    #[test]
    fn test_skip_non_serde() {
        let source = r#"
            struct NotSerde {
                field: i32,
            }

            #[derive(Serialize, Deserialize)]
            struct IsSerde {
                field: i32,
            }
        "#;

        let analyzer = RustAnalyzer::new();
        let schema = analyzer.analyze_source(source).unwrap();

        assert_eq!(schema.types.len(), 1);
        assert!(schema.types.contains_key("IsSerde"));
        assert!(!schema.types.contains_key("NotSerde"));
    }

    #[test]
    fn test_extract_validator_constraints() {
        let source = r#"
            #[derive(Serialize, Deserialize)]
            struct User {
                #[validate(length(min = 1, max = 64), email)]
                email: String,
            }
        "#;

        let analyzer = RustAnalyzer::new();
        let schema = analyzer.analyze_source(source).unwrap();

        let user = schema.types.get("User");
        assert!(
            matches!(user, Some(TypeDef::Struct(_))),
            "Expected struct User"
        );
        let Some(TypeDef::Struct(user)) = user else {
            unreachable!("asserted struct User");
        };
        let constraints = &user.fields[0].constraints;

        assert!(constraints.contains(&Constraint::MinLength(1)));
        assert!(constraints.contains(&Constraint::MaxLength(64)));
        assert!(constraints.contains(&Constraint::NonEmpty));
        assert!(constraints.contains(&Constraint::Format(StringFormat::Email)));
    }
}
