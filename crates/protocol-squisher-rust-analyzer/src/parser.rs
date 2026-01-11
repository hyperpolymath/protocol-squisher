// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Rust source file parsing utilities

use crate::AnalyzerError;
use std::fs;
use std::path::Path;

/// Parse a Rust source file from the filesystem
pub fn parse_file(path: impl AsRef<Path>) -> Result<syn::File, AnalyzerError> {
    let path = path.as_ref();
    let source = fs::read_to_string(path)
        .map_err(|e| AnalyzerError::ParseError(format!("Failed to read file: {e}")))?;

    syn::parse_file(&source)
        .map_err(|e| AnalyzerError::ParseError(format!("Failed to parse: {e}")))
}

/// Extract all struct names from a parsed file
pub fn extract_struct_names(file: &syn::File) -> Vec<String> {
    file.items.iter()
        .filter_map(|item| {
            if let syn::Item::Struct(item_struct) = item {
                Some(item_struct.ident.to_string())
            } else {
                None
            }
        })
        .collect()
}

/// Extract all enum names from a parsed file
pub fn extract_enum_names(file: &syn::File) -> Vec<String> {
    file.items.iter()
        .filter_map(|item| {
            if let syn::Item::Enum(item_enum) = item {
                Some(item_enum.ident.to_string())
            } else {
                None
            }
        })
        .collect()
}

/// Extract all type alias names from a parsed file
pub fn extract_type_alias_names(file: &syn::File) -> Vec<String> {
    file.items.iter()
        .filter_map(|item| {
            if let syn::Item::Type(item_type) = item {
                Some(item_type.ident.to_string())
            } else {
                None
            }
        })
        .collect()
}

/// Find all items with a specific derive macro
pub fn find_items_with_derive(file: &syn::File, derive_name: &str) -> Vec<String> {
    let mut results = Vec::new();

    for item in &file.items {
        let (name, attrs) = match item {
            syn::Item::Struct(s) => (s.ident.to_string(), &s.attrs),
            syn::Item::Enum(e) => (e.ident.to_string(), &e.attrs),
            _ => continue,
        };

        for attr in attrs {
            if attr.path().is_ident("derive") {
                if let Ok(nested) = attr.parse_args_with(
                    syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated
                ) {
                    for path in nested {
                        if let Some(ident) = path.segments.last() {
                            if ident.ident == derive_name {
                                results.push(name.clone());
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_struct_names() {
        let source = r#"
            struct Foo {}
            struct Bar {}
            enum Baz {}
        "#;
        let file = syn::parse_file(source).unwrap();
        let names = extract_struct_names(&file);
        assert_eq!(names, vec!["Foo", "Bar"]);
    }

    #[test]
    fn test_extract_enum_names() {
        let source = r#"
            struct Foo {}
            enum Bar {}
            enum Baz {}
        "#;
        let file = syn::parse_file(source).unwrap();
        let names = extract_enum_names(&file);
        assert_eq!(names, vec!["Bar", "Baz"]);
    }

    #[test]
    fn test_find_items_with_derive() {
        let source = r#"
            #[derive(Debug)]
            struct NotSerde {}

            #[derive(Debug, Serialize, Deserialize)]
            struct IsSerde {}

            #[derive(Serialize)]
            enum AlsoSerde {}
        "#;
        let file = syn::parse_file(source).unwrap();

        let serialize = find_items_with_derive(&file, "Serialize");
        assert_eq!(serialize, vec!["IsSerde", "AlsoSerde"]);

        let deserialize = find_items_with_derive(&file, "Deserialize");
        assert_eq!(deserialize, vec!["IsSerde"]);
    }
}
