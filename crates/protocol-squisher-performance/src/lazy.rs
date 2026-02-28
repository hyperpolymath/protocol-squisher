// SPDX-License-Identifier: PMPL-1.0-or-later

use once_cell::unsync::OnceCell;
use serde::de::DeserializeOwned;

/// Lazily-deserialized JSON payload.
pub struct LazyJson<T> {
    raw: String,
    decoded: OnceCell<T>,
}

impl<T> LazyJson<T> {
    pub fn new(raw: impl Into<String>) -> Self {
        Self {
            raw: raw.into(),
            decoded: OnceCell::new(),
        }
    }

    pub fn raw(&self) -> &str {
        &self.raw
    }
}

impl<T> LazyJson<T>
where
    T: DeserializeOwned,
{
    pub fn decode(&self) -> Result<&T, serde_json::Error> {
        self.decoded
            .get_or_try_init(|| serde_json::from_str(&self.raw))
    }
}

/// A lazy wrapper for IR schema JSON that defers parsing until first field access.
pub struct LazySchema {
    raw: String,
    parsed: OnceCell<protocol_squisher_ir::IrSchema>,
}

impl LazySchema {
    /// Create a lazy schema from raw JSON text.
    pub fn new(raw: impl Into<String>) -> Self {
        Self {
            raw: raw.into(),
            parsed: OnceCell::new(),
        }
    }

    /// Return the raw JSON without parsing.
    pub fn raw(&self) -> &str {
        &self.raw
    }

    /// Check whether the schema has been materialized (parsed) yet.
    pub fn is_materialized(&self) -> bool {
        self.parsed.get().is_some()
    }

    /// Materialize (parse) the schema on first call; return cached reference thereafter.
    pub fn get(&self) -> Result<&protocol_squisher_ir::IrSchema, serde_json::Error> {
        self.parsed
            .get_or_try_init(|| serde_json::from_str(&self.raw))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct Payload {
        id: u32,
        name: String,
    }

    #[test]
    fn lazy_decode_parses_on_demand() {
        let lazy = LazyJson::<Payload>::new(r#"{"id":42,"name":"hello"}"#);
        assert_eq!(lazy.raw(), r#"{"id":42,"name":"hello"}"#);

        let first = lazy.decode().expect("first decode");
        assert_eq!(
            first,
            &Payload {
                id: 42,
                name: "hello".to_string()
            }
        );

        let second = lazy.decode().expect("second decode");
        assert!(std::ptr::eq(first, second));
    }

    #[test]
    fn lazy_schema_defers_parsing() {
        let schema = protocol_squisher_ir::IrSchema::new("test-schema", "test");
        let json = serde_json::to_string(&schema).expect("serialize");

        let lazy = LazySchema::new(json);
        assert!(!lazy.is_materialized());

        let parsed = lazy.get().expect("parse schema");
        assert!(lazy.is_materialized());
        assert_eq!(parsed.name, "test-schema");

        // Second access returns same reference.
        let parsed2 = lazy.get().expect("parse schema again");
        assert!(std::ptr::eq(parsed, parsed2));
    }

    #[test]
    fn lazy_schema_raw_access_no_parse() {
        let lazy = LazySchema::new(r#"{"not": "valid schema"}"#);
        assert_eq!(lazy.raw(), r#"{"not": "valid schema"}"#);
        assert!(!lazy.is_materialized());
    }
}
