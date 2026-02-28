// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Error types for VeriSimDB integration.

use thiserror::Error;

/// Errors from VeriSimDB operations.
#[derive(Debug, Error)]
pub enum VeriSimError {
    /// HTTP transport error communicating with VeriSimDB.
    #[error("HTTP error: {0}")]
    HttpError(String),

    /// VeriSimDB API returned a non-success status code.
    #[error("VeriSimDB API error ({status}): {message}")]
    ApiError { status: u16, message: String },

    /// VeriSimDB service is not reachable.
    #[error("VeriSimDB unavailable at {url}")]
    Unavailable { url: String },

    /// VQL query syntax or execution error.
    #[error("VQL query error: {0}")]
    QueryError(String),

    /// Requested entity was not found.
    #[error("entity not found: {0}")]
    NotFound(String),

    /// Serialization or deserialization error.
    #[error("serialization error: {0}")]
    SerializationError(String),
}
