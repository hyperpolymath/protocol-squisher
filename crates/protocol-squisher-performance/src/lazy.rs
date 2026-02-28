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
}
