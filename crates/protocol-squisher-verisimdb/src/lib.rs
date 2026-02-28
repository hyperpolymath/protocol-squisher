// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # VeriSimDB Integration for Protocol Squisher
//!
//! Persistent storage layer for analysis results, proof certificates, schema
//! history, and optimizer suggestions. Uses VeriSimDB's multi-modal data engine
//! (graph, vector, document, temporal, provenance, semantic) to store and query
//! protocol compatibility data.
//!
//! ## Architecture
//!
//! ```text
//! Analyzer  →  AnalysisRecord  →  AnalysisStore::store_analysis()
//!                                       ↓
//!                              VeriSimDBStore (HTTP)  or  InMemoryStore (fallback)
//!                                       ↓
//!                              VQL queries for trends, provenance, similarity
//! ```
//!
//! ## Modality Mapping
//!
//! | VeriSimDB Modality | Protocol-Squisher Use |
//! |--------------------|-----------------------|
//! | Graph              | Type compatibility relationships (RDF triples) |
//! | Vector             | Embedding similarity search on type pairs |
//! | Document           | Full-text search on analysis reports |
//! | Temporal           | Version history of transport class assignments |
//! | Provenance         | Which analyzer version produced which result |
//! | Semantic           | ECHIDNA proof certificates (CBOR) |

pub mod client;
pub mod error;
pub mod models;
pub mod queries;
pub mod store;

pub use client::VeriSimDBClient;
pub use error::VeriSimError;
pub use models::{AnalysisRecord, SchemaVersionEntry, SuggestionLogEntry};
pub use queries::{
    build_graph_query, build_provenance_query, build_temporal_query, build_vector_query,
};
pub use store::{AnalysisStore, InMemoryStore, VeriSimDBStore};
