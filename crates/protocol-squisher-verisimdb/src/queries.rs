// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! VQL (VeriSimDB Query Language) query builders.
//!
//! These functions construct VQL strings for the common query patterns used
//! by protocol-squisher: temporal history, vector similarity, provenance
//! tracking, and graph traversal of type relationships.

/// Build a temporal query for analysis records within a time range.
///
/// Returns all analysis records for a `(source, target)` pair between
/// `from` and `to` timestamps, ordered chronologically.
pub fn build_temporal_query(
    source_type: &str,
    target_type: &str,
    from: &str,
    to: &str,
) -> String {
    format!(
        "SELECT * FROM analyses \
         WHERE source_type = '{source_type}' \
         AND target_type = '{target_type}' \
         TEMPORAL BETWEEN '{from}' AND '{to}' \
         ORDER BY timestamp ASC"
    )
}

/// Build a vector similarity query for finding similar type pairs.
///
/// Searches the analysis collection for records whose embeddings are
/// closest to the provided vector, returning the top `limit` results.
pub fn build_vector_query(embedding: &[f64], limit: usize) -> String {
    let embedding_str: Vec<String> = embedding.iter().map(|v| format!("{v}")).collect();
    format!(
        "SELECT * FROM analyses \
         VECTOR NEAREST([{embedding}], {limit})",
        embedding = embedding_str.join(", "),
    )
}

/// Build a provenance query filtering by analyzer version.
///
/// Returns all analysis records produced by a specific analyzer version,
/// optionally filtered by format.
pub fn build_provenance_query(
    analyzer_version: &str,
    format: Option<&str>,
) -> String {
    let base = format!(
        "SELECT * FROM analyses \
         PROVENANCE analyzer_version = '{analyzer_version}'"
    );

    if let Some(fmt) = format {
        format!("{base} AND format = '{fmt}'")
    } else {
        base
    }
}

/// Build a graph query for type compatibility relationships.
///
/// Traverses the RDF-style graph to find all types connected to `type_name`
/// by compatibility edges, up to `depth` hops.
pub fn build_graph_query(type_name: &str, depth: usize) -> String {
    format!(
        "SELECT * FROM type_graph \
         GRAPH TRAVERSE '{type_name}' \
         DEPTH {depth} \
         EDGE compatible_with"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vql_temporal_builder() {
        let query = build_temporal_query(
            "User.id",
            "UserDTO.id",
            "2026-01-01",
            "2026-02-28",
        );
        assert!(query.contains("TEMPORAL BETWEEN"));
        assert!(query.contains("User.id"));
        assert!(query.contains("2026-01-01"));
        assert!(query.contains("ORDER BY timestamp ASC"));
    }

    #[test]
    fn vql_vector_builder() {
        let embedding = vec![0.1, 0.2, 0.3];
        let query = build_vector_query(&embedding, 5);
        assert!(query.contains("VECTOR NEAREST"));
        assert!(query.contains("0.1"));
        assert!(query.contains("5"));
    }

    #[test]
    fn vql_provenance_builder() {
        let query = build_provenance_query("1.0.0", Some("protobuf"));
        assert!(query.contains("PROVENANCE"));
        assert!(query.contains("1.0.0"));
        assert!(query.contains("protobuf"));
    }

    #[test]
    fn vql_provenance_no_format() {
        let query = build_provenance_query("2.0.0", None);
        assert!(query.contains("PROVENANCE"));
        assert!(!query.contains("format"));
    }

    #[test]
    fn vql_graph_builder() {
        let query = build_graph_query("User", 3);
        assert!(query.contains("GRAPH TRAVERSE"));
        assert!(query.contains("User"));
        assert!(query.contains("DEPTH 3"));
    }
}
