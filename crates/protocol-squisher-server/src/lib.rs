// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Protocol Squisher HTTP Server
//!
//! An `axum`-based HTTP/JSON API for remote and distributed protocol analysis.
//! Designed for PanLL's Tauri HTTP proxy pattern and standalone CI/CD deployment.
//!
//! ## Endpoints
//!
//! | Method | Path              | Purpose                                       |
//! |--------|-------------------|-----------------------------------------------|
//! | GET    | `/health`         | Liveness check                                |
//! | GET    | `/formats`        | List supported analyzer formats                |
//! | POST   | `/analyze`        | Analyze a schema, return IR + transport class  |
//! | POST   | `/compare`        | Bidirectional comparison of two schemas         |
//! | POST   | `/constraints`    | Evaluate constraints against a schema           |
//!
//! ## Usage
//!
//! ```rust,ignore
//! use protocol_squisher_server::build_router;
//!
//! #[tokio::main]
//! async fn main() {
//!     let app = build_router();
//!     let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
//!     axum::serve(listener, app).await.unwrap();
//! }
//! ```

use axum::{
    extract::Json,
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Router,
};
use protocol_squisher_compat::{bidirectional_compare, BidirectionalResult};
use protocol_squisher_constraints::{
    evaluate as evaluate_constraints, ConstraintReport, ConstraintSet,
};
use protocol_squisher_ir::IrSchema;
use serde::{Deserialize, Serialize};

// ─── Router ─────────────────────────────────────────────────────────────────

/// Build the axum router with all protocol-squisher API routes.
pub fn build_router() -> Router {
    Router::new()
        .route("/health", get(health))
        .route("/formats", get(formats))
        .route("/analyze", post(analyze))
        .route("/compare", post(compare))
        .route("/constraints", post(constraints))
}

// ─── Health ─────────────────────────────────────────────────────────────────

/// Health check response.
#[derive(Debug, Serialize)]
pub struct HealthResponse {
    /// Service status.
    pub status: String,
    /// Service version.
    pub version: String,
}

/// `GET /health` — liveness check.
async fn health() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

// ─── Formats ────────────────────────────────────────────────────────────────

/// Description of a supported format.
#[derive(Debug, Serialize, Deserialize)]
pub struct FormatInfo {
    /// Short name (e.g. "protobuf", "json-schema").
    pub name: String,
    /// File extensions handled.
    pub extensions: Vec<String>,
}

/// `GET /formats` — list supported analyzer formats.
///
/// Returns a static list matching the 13 analyzers in the main crate.
async fn formats() -> Json<Vec<FormatInfo>> {
    let fmts = vec![
        FormatInfo {
            name: "rust".into(),
            extensions: vec!["rs".into()],
        },
        FormatInfo {
            name: "python".into(),
            extensions: vec!["py".into(), "pyi".into()],
        },
        FormatInfo {
            name: "json-schema".into(),
            extensions: vec!["json".into()],
        },
        FormatInfo {
            name: "protobuf".into(),
            extensions: vec!["proto".into()],
        },
        FormatInfo {
            name: "avro".into(),
            extensions: vec!["avsc".into()],
        },
        FormatInfo {
            name: "thrift".into(),
            extensions: vec!["thrift".into()],
        },
        FormatInfo {
            name: "bebop".into(),
            extensions: vec!["bop".into()],
        },
        FormatInfo {
            name: "capnproto".into(),
            extensions: vec!["capnp".into()],
        },
        FormatInfo {
            name: "flatbuffers".into(),
            extensions: vec!["fbs".into()],
        },
        FormatInfo {
            name: "messagepack".into(),
            extensions: vec!["msgpack".into()],
        },
        FormatInfo {
            name: "rescript".into(),
            extensions: vec!["res".into(), "resi".into()],
        },
        FormatInfo {
            name: "graphql".into(),
            extensions: vec!["graphql".into(), "gql".into()],
        },
        FormatInfo {
            name: "toml".into(),
            extensions: vec!["toml".into()],
        },
    ];
    Json(fmts)
}

// ─── Analyze ────────────────────────────────────────────────────────────────

/// Request body for `POST /analyze`.
#[derive(Debug, Deserialize)]
pub struct AnalyzeRequest {
    /// Raw schema text.
    pub schema: String,
    /// Schema name/identifier.
    pub name: String,
    /// Source format hint (e.g. "protobuf"). Optional.
    pub format: Option<String>,
}

/// Response for `POST /analyze`.
#[derive(Debug, Serialize, Deserialize)]
pub struct AnalyzeResponse {
    /// The parsed IR schema (if successful).
    pub ir: Option<IrSchema>,
    /// Error message (if parsing failed).
    pub error: Option<String>,
    /// Suggested transport class hint based on format.
    pub format_hint: Option<String>,
}

/// `POST /analyze` — accepts schema text, returns IR.
///
/// This is currently a stub that returns the schema text as-is in a
/// minimal IR wrapper. Full implementation requires wiring up the 13
/// analyzers, which depends on the root `protocol-squisher` crate.
async fn analyze(Json(req): Json<AnalyzeRequest>) -> impl IntoResponse {
    // Stub: create a minimal IR schema from the request metadata.
    // A full implementation would select an analyzer based on `format`
    // and call `analyzer.analyze_str(&req.schema, &req.name)`.
    let source_format = req.format.clone().unwrap_or_else(|| "unknown".to_string());
    let ir = IrSchema::new(&req.name, &source_format);

    (
        StatusCode::OK,
        Json(AnalyzeResponse {
            ir: Some(ir),
            error: None,
            format_hint: req.format,
        }),
    )
}

// ─── Compare ────────────────────────────────────────────────────────────────

/// Request body for `POST /compare`.
#[derive(Debug, Deserialize)]
pub struct CompareRequest {
    /// First schema (source).
    pub schema_a: IrSchema,
    /// Second schema (target).
    pub schema_b: IrSchema,
}

/// Response for `POST /compare`.
#[derive(Debug, Serialize)]
pub struct CompareResponse {
    /// Bidirectional comparison report.
    pub report: BidirectionalResult,
}

/// `POST /compare` — accepts two IR schemas, returns bidirectional report.
async fn compare(Json(req): Json<CompareRequest>) -> impl IntoResponse {
    let report = bidirectional_compare(&req.schema_a, &req.schema_b);
    (StatusCode::OK, Json(CompareResponse { report }))
}

// ─── Constraints ────────────────────────────────────────────────────────────

/// Request body for `POST /constraints`.
#[derive(Debug, Deserialize)]
pub struct ConstraintsRequest {
    /// Schema to evaluate against.
    pub schema: IrSchema,
    /// Constraints to check.
    pub constraints: ConstraintSet,
}

/// Response for `POST /constraints`.
#[derive(Debug, Serialize)]
pub struct ConstraintsResponse {
    /// Constraint evaluation report.
    pub report: ConstraintReport,
}

/// `POST /constraints` — accepts schema + constraints, returns evaluation report.
async fn constraints(Json(req): Json<ConstraintsRequest>) -> impl IntoResponse {
    let report = evaluate_constraints(&req.schema, &req.constraints);
    (StatusCode::OK, Json(ConstraintsResponse { report }))
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use tower::ServiceExt;

    #[tokio::test]
    async fn test_health_endpoint() {
        let app = build_router();
        let response = app
            .oneshot(
                Request::builder()
                    .uri("/health")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_formats_endpoint() {
        let app = build_router();
        let response = app
            .oneshot(
                Request::builder()
                    .uri("/formats")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let formats: Vec<FormatInfo> = serde_json::from_slice(&body).unwrap();
        assert_eq!(formats.len(), 13);
    }

    #[tokio::test]
    async fn test_analyze_endpoint() {
        let app = build_router();
        let req_body = serde_json::json!({
            "schema": "message User { string name = 1; }",
            "name": "user",
            "format": "protobuf"
        });
        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/analyze")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&req_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let resp: AnalyzeResponse = serde_json::from_slice(&body).unwrap();
        assert!(resp.ir.is_some());
        assert!(resp.error.is_none());
    }

    #[tokio::test]
    async fn test_compare_endpoint() {
        let app = build_router();
        let schema_a = IrSchema::new("a", "test");
        let schema_b = IrSchema::new("b", "test");
        let req_body = serde_json::json!({
            "schema_a": schema_a,
            "schema_b": schema_b,
        });
        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/compare")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&req_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_constraints_endpoint() {
        let app = build_router();
        let schema = IrSchema::new("test", "test");
        let constraints = ConstraintSet::new();
        let req_body = serde_json::json!({
            "schema": schema,
            "constraints": constraints,
        });
        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/constraints")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&req_body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
    }
}
