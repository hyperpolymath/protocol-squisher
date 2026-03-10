// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Labels and Field Paths
//!
//! Labels attach human-readable names to shape nodes. Every product field and
//! sum variant carries a label. Labels also track provenance: which source format
//! the name came from, because the same logical field might be called `user_id`
//! in SQL, `userId` in JSON, and `user_id` in Protobuf.
//!
//! Field paths address locations within a nested shape, enabling morphism steps
//! to precisely describe where a transformation applies.

use serde::{Deserialize, Serialize};
use std::fmt;

/// A label attached to a field, variant, or shape node.
///
/// Labels carry both the structural name and metadata about its origin.
/// Two labels with the same `name` but different `source_format` values
/// represent the same logical field as seen through different format lenses.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Label {
    /// The canonical name of this field or variant.
    pub name: String,

    /// Optional documentation string describing the purpose of this field.
    pub doc: Option<String>,

    /// The serialization format this label was extracted from, if known.
    /// Examples: "protobuf", "avro", "json-schema", "sql", "rust"
    pub source_format: Option<String>,
}

impl Label {
    /// Create a new label with just a name.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            doc: None,
            source_format: None,
        }
    }

    /// Create a label with a name and documentation.
    pub fn with_doc(name: impl Into<String>, doc: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            doc: Some(doc.into()),
            source_format: None,
        }
    }

    /// Create a label with full provenance information.
    pub fn with_provenance(
        name: impl Into<String>,
        doc: Option<String>,
        source_format: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            doc,
            source_format: Some(source_format.into()),
        }
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl From<&str> for Label {
    fn from(s: &str) -> Self {
        Label::new(s)
    }
}

impl From<String> for Label {
    fn from(s: String) -> Self {
        Label::new(s)
    }
}

/// A path addressing a specific location within a nested shape.
///
/// Field paths are used by [`crate::morphism::MorphismStep`] to describe exactly
/// where a transformation applies. A path like `["user", "address", "city"]`
/// addresses the `city` field inside the `address` field inside `user`.
///
/// An empty path refers to the root shape itself.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FieldPath {
    /// The sequence of field names from root to the target location.
    pub segments: Vec<String>,
}

impl FieldPath {
    /// Create a path addressing the root shape.
    pub fn root() -> Self {
        Self {
            segments: Vec::new(),
        }
    }

    /// Create a path from a single field name.
    pub fn field(name: impl Into<String>) -> Self {
        Self {
            segments: vec![name.into()],
        }
    }

    /// Create a path from a sequence of field names.
    pub fn from_segments(segments: Vec<String>) -> Self {
        Self { segments }
    }

    /// Append a segment to this path, returning a new deeper path.
    pub fn join(&self, segment: impl Into<String>) -> Self {
        let mut segments = self.segments.clone();
        segments.push(segment.into());
        Self { segments }
    }

    /// Returns true if this path addresses the root shape.
    pub fn is_root(&self) -> bool {
        self.segments.is_empty()
    }

    /// Returns the depth of this path (number of segments).
    pub fn depth(&self) -> usize {
        self.segments.len()
    }
}

impl fmt::Display for FieldPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.segments.is_empty() {
            write!(f, ".")
        } else {
            write!(f, "{}", self.segments.join("."))
        }
    }
}
