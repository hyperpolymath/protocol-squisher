// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Serde attribute parsing
//!
//! Parses serde attributes like `#[serde(rename = "...")]` from Rust source.

use std::collections::BTreeMap;

/// Parsed serde attributes
#[derive(Debug, Default, Clone)]
pub struct SerdeAttributes {
    /// Rename the field/variant
    pub rename: Option<String>,
    /// Rename all fields/variants (for containers)
    pub rename_all: Option<String>,
    /// Alternative names for deserialization
    pub aliases: Vec<String>,
    /// Skip this field
    pub skip: bool,
    /// Skip serializing this field
    pub skip_serializing: bool,
    /// Skip deserializing this field
    pub skip_deserializing: bool,
    /// Skip if condition
    pub skip_serializing_if: Option<String>,
    /// Use default value
    pub default: bool,
    /// Default value expression
    pub default_value: Option<serde_json::Value>,
    /// Flatten this field
    pub flatten: bool,
    /// Tag field name (for enums)
    pub tag: Option<String>,
    /// Content field name (for adjacently tagged enums)
    pub content: Option<String>,
    /// Untagged enum
    pub untagged: bool,
    /// Deny unknown fields
    pub deny_unknown_fields: bool,
    /// Transparent newtype
    pub transparent: bool,
    /// Custom serialize function
    pub serialize_with: Option<String>,
    /// Custom deserialize function
    pub deserialize_with: Option<String>,
    /// Bound for generics
    pub bound: Option<String>,
}

impl SerdeAttributes {
    /// Parse serde attributes from syn attributes
    pub fn from_attrs(attrs: &[syn::Attribute]) -> Self {
        let mut result = Self::default();

        for attr in attrs {
            if !attr.path().is_ident("serde") {
                continue;
            }

            let _ = attr.parse_nested_meta(|meta| {
                let ident = meta
                    .path
                    .get_ident()
                    .map(|i| i.to_string())
                    .unwrap_or_default();

                match ident.as_str() {
                    "rename" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.rename = Some(lit.value());
                            }
                        }
                    },
                    "rename_all" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.rename_all = Some(lit.value());
                            }
                        }
                    },
                    "alias" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.aliases.push(lit.value());
                            }
                        }
                    },
                    "skip" => {
                        result.skip = true;
                    },
                    "skip_serializing" => {
                        result.skip_serializing = true;
                    },
                    "skip_deserializing" => {
                        result.skip_deserializing = true;
                    },
                    "skip_serializing_if" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.skip_serializing_if = Some(lit.value());
                            }
                        }
                    },
                    "default" => {
                        result.default = true;
                        // Try to get default value if specified
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.default_value = Some(serde_json::Value::String(lit.value()));
                            }
                        }
                    },
                    "flatten" => {
                        result.flatten = true;
                    },
                    "tag" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.tag = Some(lit.value());
                            }
                        }
                    },
                    "content" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.content = Some(lit.value());
                            }
                        }
                    },
                    "untagged" => {
                        result.untagged = true;
                    },
                    "deny_unknown_fields" => {
                        result.deny_unknown_fields = true;
                    },
                    "transparent" => {
                        result.transparent = true;
                    },
                    "serialize_with" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.serialize_with = Some(lit.value());
                            }
                        }
                    },
                    "deserialize_with" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.deserialize_with = Some(lit.value());
                            }
                        }
                    },
                    "bound" => {
                        if let Ok(value) = meta.value() {
                            if let Ok(lit) = value.parse::<syn::LitStr>() {
                                result.bound = Some(lit.value());
                            }
                        }
                    },
                    _ => {},
                }

                Ok(())
            });
        }

        result
    }

    /// Convert to serde hints map for IR metadata
    pub fn to_hints(&self) -> BTreeMap<String, String> {
        let mut hints = BTreeMap::new();

        if let Some(ref rename) = self.rename {
            hints.insert("rename".to_string(), rename.clone());
        }
        if let Some(ref rename_all) = self.rename_all {
            hints.insert("rename_all".to_string(), rename_all.clone());
        }
        if self.skip {
            hints.insert("skip".to_string(), "true".to_string());
        }
        if self.flatten {
            hints.insert("flatten".to_string(), "true".to_string());
        }
        if let Some(ref tag) = self.tag {
            hints.insert("tag".to_string(), tag.clone());
        }
        if let Some(ref content) = self.content {
            hints.insert("content".to_string(), content.clone());
        }
        if self.untagged {
            hints.insert("untagged".to_string(), "true".to_string());
        }
        if self.deny_unknown_fields {
            hints.insert("deny_unknown_fields".to_string(), "true".to_string());
        }
        if self.transparent {
            hints.insert("transparent".to_string(), "true".to_string());
        }

        hints
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    fn parse_attrs(tokens: proc_macro2::TokenStream) -> Vec<syn::Attribute> {
        let item: syn::ItemStruct = syn::parse2(quote! {
            #tokens
            struct Dummy {}
        })
        .unwrap();
        item.attrs
    }

    #[test]
    fn test_parse_rename() {
        let attrs = parse_attrs(quote! {
            #[serde(rename = "other_name")]
        });
        let parsed = SerdeAttributes::from_attrs(&attrs);
        assert_eq!(parsed.rename, Some("other_name".to_string()));
    }

    #[test]
    fn test_parse_skip() {
        let attrs = parse_attrs(quote! {
            #[serde(skip)]
        });
        let parsed = SerdeAttributes::from_attrs(&attrs);
        assert!(parsed.skip);
    }

    #[test]
    fn test_parse_tag_content() {
        let attrs = parse_attrs(quote! {
            #[serde(tag = "type", content = "data")]
        });
        let parsed = SerdeAttributes::from_attrs(&attrs);
        assert_eq!(parsed.tag, Some("type".to_string()));
        assert_eq!(parsed.content, Some("data".to_string()));
    }

    #[test]
    fn test_to_hints() {
        let attrs = SerdeAttributes {
            rename: Some("new_name".to_string()),
            flatten: true,
            ..Default::default()
        };

        let hints = attrs.to_hints();
        assert_eq!(hints.get("rename"), Some(&"new_name".to_string()));
        assert_eq!(hints.get("flatten"), Some(&"true".to_string()));
    }
}
