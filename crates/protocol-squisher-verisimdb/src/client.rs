// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! HTTP client for VeriSimDB's REST API.
//!
//! `VeriSimDBClient` provides typed access to VeriSimDB's core operations:
//! health checks, VQL queries, entity CRUD, and vector similarity search.

use crate::error::VeriSimError;
use serde_json::Value;

/// HTTP client for communicating with a VeriSimDB instance.
pub struct VeriSimDBClient {
    /// Base URL of the VeriSimDB API (e.g., `http://localhost:8080`).
    base_url: String,
}

impl VeriSimDBClient {
    /// Create a client pointing at `base_url`.
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            base_url: base_url.into(),
        }
    }

    /// Return the base URL.
    pub fn base_url(&self) -> &str {
        &self.base_url
    }

    /// Check whether the VeriSimDB instance is reachable and healthy.
    pub fn health(&self) -> Result<bool, VeriSimError> {
        let url = format!("{}/health", self.base_url);
        let response = reqwest::blocking::Client::new()
            .get(&url)
            .timeout(std::time::Duration::from_secs(3))
            .send()
            .map_err(|_| VeriSimError::Unavailable {
                url: url.clone(),
            })?;
        Ok(response.status().is_success())
    }

    /// Execute a VQL (VeriSimDB Query Language) query.
    pub fn vql_query(&self, vql: &str) -> Result<Value, VeriSimError> {
        let url = format!("{}/api/v1/vql", self.base_url);
        let body = serde_json::json!({ "query": vql });

        let response = reqwest::blocking::Client::new()
            .post(&url)
            .json(&body)
            .send()
            .map_err(|_| VeriSimError::Unavailable {
                url: url.clone(),
            })?;

        if !response.status().is_success() {
            return Err(VeriSimError::ApiError {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    /// Create a new entity in VeriSimDB.
    pub fn create_entity(
        &self,
        collection: &str,
        entity: &Value,
    ) -> Result<Value, VeriSimError> {
        let url = format!("{}/api/v1/entities/{}", self.base_url, collection);

        let response = reqwest::blocking::Client::new()
            .post(&url)
            .json(entity)
            .send()
            .map_err(|_| VeriSimError::Unavailable {
                url: url.clone(),
            })?;

        if !response.status().is_success() {
            return Err(VeriSimError::ApiError {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    /// Retrieve an entity by collection and ID.
    pub fn get_entity(
        &self,
        collection: &str,
        id: &str,
    ) -> Result<Value, VeriSimError> {
        let url = format!("{}/api/v1/entities/{}/{}", self.base_url, collection, id);

        let response = reqwest::blocking::Client::new()
            .get(&url)
            .send()
            .map_err(|_| VeriSimError::Unavailable {
                url: url.clone(),
            })?;

        if response.status() == reqwest::StatusCode::NOT_FOUND {
            return Err(VeriSimError::NotFound(format!("{collection}/{id}")));
        }

        if !response.status().is_success() {
            return Err(VeriSimError::ApiError {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }

    /// Perform a vector similarity search.
    pub fn vector_search(
        &self,
        collection: &str,
        embedding: &[f64],
        limit: usize,
    ) -> Result<Vec<Value>, VeriSimError> {
        let url = format!("{}/api/v1/vector/{}/search", self.base_url, collection);
        let body = serde_json::json!({
            "embedding": embedding,
            "limit": limit,
        });

        let response = reqwest::blocking::Client::new()
            .post(&url)
            .json(&body)
            .send()
            .map_err(|_| VeriSimError::Unavailable {
                url: url.clone(),
            })?;

        if !response.status().is_success() {
            return Err(VeriSimError::ApiError {
                status: response.status().as_u16(),
                message: response.text().unwrap_or_default(),
            });
        }

        response
            .json()
            .map_err(|e| VeriSimError::SerializationError(e.to_string()))
    }
}
