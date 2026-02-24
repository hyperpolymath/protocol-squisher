// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Type conversion from Rust types to IR types

use crate::AnalyzerError;
use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType, SpecialType};

/// Convert a Rust type to an IR type
pub fn convert_type(ty: &syn::Type) -> Result<IrType, AnalyzerError> {
    match ty {
        syn::Type::Path(type_path) => convert_path_type(type_path),
        syn::Type::Reference(type_ref) => {
            // References are transparent for serialization
            convert_type(&type_ref.elem)
        },
        syn::Type::Tuple(type_tuple) => {
            if type_tuple.elems.is_empty() {
                Ok(IrType::Special(SpecialType::Unit))
            } else {
                let types: Result<Vec<_>, _> = type_tuple.elems.iter().map(convert_type).collect();
                Ok(IrType::Container(ContainerType::Tuple(types?)))
            }
        },
        syn::Type::Array(type_array) => {
            let inner = convert_type(&type_array.elem)?;
            // Try to extract array length
            let len = extract_array_len(&type_array.len).unwrap_or(0);
            Ok(IrType::Container(ContainerType::Array(
                Box::new(inner),
                len,
            )))
        },
        syn::Type::Slice(type_slice) => {
            let inner = convert_type(&type_slice.elem)?;
            Ok(IrType::Container(ContainerType::Vec(Box::new(inner))))
        },
        syn::Type::Paren(type_paren) => convert_type(&type_paren.elem),
        syn::Type::Group(type_group) => convert_type(&type_group.elem),
        syn::Type::Never(_) => Ok(IrType::Special(SpecialType::Never)),
        _ => Err(AnalyzerError::UnsupportedConstruct(
            "Unsupported type construct".to_string(),
        )),
    }
}

/// Convert a path type (e.g., `String`, `Vec<T>`, `Option<T>`)
fn convert_path_type(type_path: &syn::TypePath) -> Result<IrType, AnalyzerError> {
    let path = &type_path.path;

    // Get the last segment (the actual type name)
    let segment = path
        .segments
        .last()
        .ok_or_else(|| AnalyzerError::ParseError("Empty type path".to_string()))?;

    let ident = segment.ident.to_string();

    // Check for generic arguments
    let generic_args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(args) => args
            .args
            .iter()
            .filter_map(|arg| {
                if let syn::GenericArgument::Type(ty) = arg {
                    Some(ty.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>(),
        _ => vec![],
    };

    // Match primitives
    if let Some(prim) = match_primitive(&ident) {
        return Ok(IrType::Primitive(prim));
    }

    // Match container types
    match ident.as_str() {
        // Option
        "Option" => {
            let inner = generic_args.first().ok_or_else(|| {
                AnalyzerError::ParseError("Option requires type argument".to_string())
            })?;
            Ok(IrType::Container(ContainerType::Option(Box::new(
                convert_type(inner)?,
            ))))
        },

        // Vec / vectors
        "Vec" | "VecDeque" => {
            let inner = generic_args.first().ok_or_else(|| {
                AnalyzerError::ParseError("Vec requires type argument".to_string())
            })?;
            Ok(IrType::Container(ContainerType::Vec(Box::new(
                convert_type(inner)?,
            ))))
        },

        // Sets
        "HashSet" | "BTreeSet" | "IndexSet" => {
            let inner = generic_args.first().ok_or_else(|| {
                AnalyzerError::ParseError("Set requires type argument".to_string())
            })?;
            Ok(IrType::Container(ContainerType::Set(Box::new(
                convert_type(inner)?,
            ))))
        },

        // Maps
        "HashMap" | "BTreeMap" | "IndexMap" => {
            if generic_args.len() < 2 {
                return Err(AnalyzerError::ParseError(
                    "Map requires key and value type arguments".to_string(),
                ));
            }
            let key = convert_type(&generic_args[0])?;
            let value = convert_type(&generic_args[1])?;
            Ok(IrType::Container(ContainerType::Map(
                Box::new(key),
                Box::new(value),
            )))
        },

        // Result
        "Result" => {
            if generic_args.len() < 2 {
                return Err(AnalyzerError::ParseError(
                    "Result requires Ok and Err type arguments".to_string(),
                ));
            }
            let ok = convert_type(&generic_args[0])?;
            let err = convert_type(&generic_args[1])?;
            Ok(IrType::Container(ContainerType::Result(
                Box::new(ok),
                Box::new(err),
            )))
        },

        // Box is transparent for serialization
        "Box" | "Rc" | "Arc" | "Cow" => {
            let inner = generic_args.first().ok_or_else(|| {
                AnalyzerError::ParseError("Smart pointer requires type argument".to_string())
            })?;
            convert_type(inner)
        },

        // Cell types are transparent
        "Cell" | "RefCell" | "Mutex" | "RwLock" => {
            let inner = generic_args.first().ok_or_else(|| {
                AnalyzerError::ParseError("Cell type requires type argument".to_string())
            })?;
            convert_type(inner)
        },

        // JSON value
        "Value" if is_serde_json_path(path) => Ok(IrType::Special(SpecialType::Json)),

        // Any type (when using serde_json::Value or similar)
        "Value" => Ok(IrType::Special(SpecialType::Json)),

        // Unknown types are references to user-defined types
        _ => {
            // Build the full type path for the reference
            let full_path = path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect::<Vec<_>>()
                .join("::");
            Ok(IrType::Reference(full_path))
        },
    }
}

/// Match primitive type names to IR primitives
fn match_primitive(name: &str) -> Option<PrimitiveType> {
    match name {
        // Booleans
        "bool" => Some(PrimitiveType::Bool),

        // Signed integers
        "i8" => Some(PrimitiveType::I8),
        "i16" => Some(PrimitiveType::I16),
        "i32" => Some(PrimitiveType::I32),
        "i64" => Some(PrimitiveType::I64),
        "i128" => Some(PrimitiveType::I128),
        "isize" => Some(PrimitiveType::I64), // Platform-dependent, treat as i64

        // Unsigned integers
        "u8" => Some(PrimitiveType::U8),
        "u16" => Some(PrimitiveType::U16),
        "u32" => Some(PrimitiveType::U32),
        "u64" => Some(PrimitiveType::U64),
        "u128" => Some(PrimitiveType::U128),
        "usize" => Some(PrimitiveType::U64), // Platform-dependent, treat as u64

        // Floating point
        "f32" => Some(PrimitiveType::F32),
        "f64" => Some(PrimitiveType::F64),

        // Text
        "String" | "str" => Some(PrimitiveType::String),
        "char" => Some(PrimitiveType::Char),

        // Binary
        "Bytes" => Some(PrimitiveType::Bytes),

        // Common external types
        "Uuid" => Some(PrimitiveType::Uuid),
        "DateTime" | "NaiveDateTime" => Some(PrimitiveType::DateTime),
        "NaiveDate" | "Date" => Some(PrimitiveType::Date),
        "NaiveTime" | "Time" => Some(PrimitiveType::Time),
        "Duration" => Some(PrimitiveType::Duration),
        "Decimal" | "BigDecimal" => Some(PrimitiveType::Decimal),
        "BigInt" | "BigUint" => Some(PrimitiveType::BigInt),

        _ => None,
    }
}

/// Check if path is serde_json::Value
fn is_serde_json_path(path: &syn::Path) -> bool {
    let segments: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();

    match segments.as_slice() {
        [a, b] if a == "serde_json" && b == "Value" => true,
        [a] if a == "Value" => true,
        _ => false,
    }
}

/// Extract array length from expression
fn extract_array_len(expr: &syn::Expr) -> Option<usize> {
    if let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Int(lit_int),
        ..
    }) = expr
    {
        lit_int.base10_parse().ok()
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    fn parse_type(tokens: proc_macro2::TokenStream) -> syn::Type {
        syn::parse2(tokens).unwrap()
    }

    #[test]
    fn test_primitive_types() {
        assert!(matches!(
            convert_type(&parse_type(quote!(i32))).unwrap(),
            IrType::Primitive(PrimitiveType::I32)
        ));

        assert!(matches!(
            convert_type(&parse_type(quote!(String))).unwrap(),
            IrType::Primitive(PrimitiveType::String)
        ));

        assert!(matches!(
            convert_type(&parse_type(quote!(bool))).unwrap(),
            IrType::Primitive(PrimitiveType::Bool)
        ));
    }

    #[test]
    fn test_option_type() {
        let ty = convert_type(&parse_type(quote!(Option<i32>))).unwrap();
        assert!(
            matches!(
                &ty,
                IrType::Container(ContainerType::Option(inner))
                    if matches!(inner.as_ref(), IrType::Primitive(PrimitiveType::I32))
            ),
            "Expected Option<i32> container"
        );
    }

    #[test]
    fn test_vec_type() {
        let ty = convert_type(&parse_type(quote!(Vec<String>))).unwrap();
        assert!(
            matches!(
                &ty,
                IrType::Container(ContainerType::Vec(inner))
                    if matches!(inner.as_ref(), IrType::Primitive(PrimitiveType::String))
            ),
            "Expected Vec<String> container"
        );
    }

    #[test]
    fn test_hashmap_type() {
        let ty = convert_type(&parse_type(quote!(HashMap<String, i32>))).unwrap();
        assert!(
            matches!(
                &ty,
                IrType::Container(ContainerType::Map(key, value))
                    if matches!(key.as_ref(), IrType::Primitive(PrimitiveType::String))
                        && matches!(value.as_ref(), IrType::Primitive(PrimitiveType::I32))
            ),
            "Expected Map<String, i32> container"
        );
    }

    #[test]
    fn test_nested_types() {
        let ty = convert_type(&parse_type(quote!(Option<Vec<String>>))).unwrap();
        assert!(
            matches!(
                &ty,
                IrType::Container(ContainerType::Option(inner))
                    if matches!(
                        inner.as_ref(),
                        IrType::Container(ContainerType::Vec(inner2))
                            if matches!(inner2.as_ref(), IrType::Primitive(PrimitiveType::String))
                    )
            ),
            "Expected Option<Vec<String>> container"
        );
    }

    #[test]
    fn test_reference_type() {
        let ty = convert_type(&parse_type(quote!(MyCustomType))).unwrap();
        assert!(matches!(ty, IrType::Reference(ref name) if name == "MyCustomType"));
    }

    #[test]
    fn test_box_transparent() {
        let ty = convert_type(&parse_type(quote!(Box<i32>))).unwrap();
        assert!(matches!(ty, IrType::Primitive(PrimitiveType::I32)));
    }

    #[test]
    fn test_tuple_type() {
        let ty = convert_type(&parse_type(quote!((i32, String)))).unwrap();
        assert!(
            matches!(&ty, IrType::Container(ContainerType::Tuple(types)) if types.len() == 2),
            "Expected tuple container with 2 elements"
        );
    }

    #[test]
    fn test_unit_type() {
        let ty = convert_type(&parse_type(quote!(()))).unwrap();
        assert!(matches!(ty, IrType::Special(SpecialType::Unit)));
    }
}
