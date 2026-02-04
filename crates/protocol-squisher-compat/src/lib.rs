// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # Protocol Squisher Compatibility Engine
//!
//! Analyzes IR schemas to determine compatibility and classify conversions.
//!
//! ## Transport Classes
//!
//! Conversions are classified into "transport classes" (like airline classes):
//!
//! - **Concorde**: Zero-copy, full fidelity - identical or trivially convertible
//! - **BusinessClass**: Minor overhead, full fidelity - needs processing but lossless
//! - **Economy**: Moderate overhead, documented losses - some information lost
//! - **Wheelbarrow**: High overhead, significant losses - barely works
//! - **Incompatible**: Not convertible at all
//!
//! ## Usage
//!
//! ```rust,ignore
//! use protocol_squisher_compat::{CompatibilityAnalyzer, TransportClass};
//!
//! let analyzer = CompatibilityAnalyzer::new();
//! let result = analyzer.compare(&source_schema, &target_schema);
//!
//! println!("Transport class: {}", result.class);
//! for loss in &result.all_losses {
//!     println!("  - {}: {}", loss.path, loss.description);
//! }
//! ```
//!
//! ## Loss Documentation
//!
//! Every loss during conversion is documented with:
//! - **Kind**: What type of loss (precision, range, field dropped, etc.)
//! - **Path**: Where in the schema the loss occurs
//! - **Description**: Human-readable explanation
//! - **Severity**: How bad the loss is (info, minor, moderate, major, critical)

use protocol_squisher_ir::IrSchema;

pub mod transport;
pub mod compare;
pub mod schema;
pub mod ephapax_engine;

pub use transport::{TransportClass, ConversionLoss, LossKind, LossSeverity};
pub use compare::{compare_types, TypeComparison};
pub use schema::{compare_schemas, SchemaComparison, TypeDefComparison, ComparisonSummary};
pub use ephapax_engine::{
    EphapaxCompatibilityEngine, SchemaCompatibilityResult, TypeCompatibilityAnalysis,
    FieldCompatibility, ConversionSummary,
};

/// Compatibility analyzer for IR schemas
pub struct CompatibilityAnalyzer {
    /// Whether to include informational losses in output
    include_info: bool,
    /// Whether to fail fast on first incompatibility
    fail_fast: bool,
}

impl Default for CompatibilityAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl CompatibilityAnalyzer {
    /// Create a new analyzer with default settings
    pub fn new() -> Self {
        Self {
            include_info: true,
            fail_fast: false,
        }
    }

    /// Set whether to include informational losses
    pub fn include_info(mut self, include: bool) -> Self {
        self.include_info = include;
        self
    }

    /// Set whether to fail fast on incompatibility
    pub fn fail_fast(mut self, fail: bool) -> Self {
        self.fail_fast = fail;
        self
    }

    /// Compare two schemas for compatibility
    pub fn compare(&self, source: &IrSchema, target: &IrSchema) -> SchemaComparison {
        let mut result = compare_schemas(source, target);

        // Filter out info-level losses if not wanted
        if !self.include_info {
            result.all_losses.retain(|loss| loss.severity != LossSeverity::Info);
            for tc in result.type_comparisons.values_mut() {
                tc.losses.retain(|loss| loss.severity != LossSeverity::Info);
            }
        }

        result
    }

    /// Check if conversion from source to target is possible
    pub fn is_convertible(&self, source: &IrSchema, target: &IrSchema) -> bool {
        let result = self.compare(source, target);
        result.class.is_convertible()
    }

    /// Check if conversion is lossless
    pub fn is_lossless(&self, source: &IrSchema, target: &IrSchema) -> bool {
        let result = self.compare(source, target);
        result.class.is_lossless()
    }

    /// Get the transport class for a conversion
    pub fn classify(&self, source: &IrSchema, target: &IrSchema) -> TransportClass {
        let result = self.compare(source, target);
        result.class
    }
}

/// Quick comparison between two schemas
pub fn quick_compare(source: &IrSchema, target: &IrSchema) -> TransportClass {
    CompatibilityAnalyzer::new().classify(source, target)
}

/// Detailed comparison between two schemas
pub fn detailed_compare(source: &IrSchema, target: &IrSchema) -> SchemaComparison {
    CompatibilityAnalyzer::new().compare(source, target)
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{
        ContainerType, FieldDef, FieldMetadata, IrType, PrimitiveType,
        StructDef, TypeDef, TypeMetadata,
    };

    fn make_simple_schema(name: &str, field_type: PrimitiveType) -> IrSchema {
        let mut schema = IrSchema::new(name, "test");
        schema.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(field_type),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );
        schema
    }

    #[test]
    fn test_analyzer_creation() {
        let analyzer = CompatibilityAnalyzer::new();
        assert!(analyzer.include_info);
        assert!(!analyzer.fail_fast);
    }

    #[test]
    fn test_identical_is_concorde() {
        let schema = make_simple_schema("test", PrimitiveType::I64);
        let class = quick_compare(&schema, &schema);
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_widening_is_concorde() {
        let source = make_simple_schema("source", PrimitiveType::I32);
        let target = make_simple_schema("target", PrimitiveType::I64);
        let class = quick_compare(&source, &target);
        assert_eq!(class, TransportClass::Concorde);
    }

    #[test]
    fn test_narrowing_is_economy() {
        let source = make_simple_schema("source", PrimitiveType::I64);
        let target = make_simple_schema("target", PrimitiveType::I32);
        let class = quick_compare(&source, &target);
        assert_eq!(class, TransportClass::Economy);
    }

    #[test]
    fn test_incompatible_types() {
        let source = make_simple_schema("source", PrimitiveType::String);
        let target = make_simple_schema("target", PrimitiveType::Bool);
        let class = quick_compare(&source, &target);
        assert_eq!(class, TransportClass::Incompatible);
    }

    #[test]
    fn test_is_convertible() {
        let analyzer = CompatibilityAnalyzer::new();

        let source = make_simple_schema("source", PrimitiveType::I32);
        let target = make_simple_schema("target", PrimitiveType::I64);
        assert!(analyzer.is_convertible(&source, &target));

        let incompatible = make_simple_schema("incompatible", PrimitiveType::Bool);
        assert!(!analyzer.is_convertible(&source, &incompatible));
    }

    #[test]
    fn test_is_lossless() {
        let analyzer = CompatibilityAnalyzer::new();

        let source = make_simple_schema("source", PrimitiveType::I32);
        let target = make_simple_schema("target", PrimitiveType::I64);
        assert!(analyzer.is_lossless(&source, &target));

        let narrowing = make_simple_schema("narrowing", PrimitiveType::I16);
        assert!(!analyzer.is_lossless(&source, &narrowing));
    }

    #[test]
    fn test_detailed_comparison() {
        let source = make_simple_schema("source", PrimitiveType::I64);
        let target = make_simple_schema("target", PrimitiveType::I32);

        let result = detailed_compare(&source, &target);
        assert_eq!(result.class, TransportClass::Economy);
        assert!(!result.all_losses.is_empty());
        assert!(result.type_comparisons.contains_key("Record"));
    }

    #[test]
    fn test_filter_info_losses() {
        // Create schemas where we'd get info-level losses
        let mut source = IrSchema::new("source", "test");
        source.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Container(ContainerType::Set(
                        Box::new(IrType::Primitive(PrimitiveType::String))
                    )),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );

        let mut target = IrSchema::new("target", "test");
        target.add_type(
            "Record".to_string(),
            TypeDef::Struct(StructDef {
                name: "Record".to_string(),
                fields: vec![FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Container(ContainerType::Vec(
                        Box::new(IrType::Primitive(PrimitiveType::String))
                    )),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                }],
                metadata: TypeMetadata::default(),
            }),
        );

        let with_info = CompatibilityAnalyzer::new()
            .include_info(true)
            .compare(&source, &target);

        let without_info = CompatibilityAnalyzer::new()
            .include_info(false)
            .compare(&source, &target);

        // Without info should have fewer or equal losses
        assert!(without_info.all_losses.len() <= with_info.all_losses.len());
    }

    #[test]
    fn test_summary() {
        let source = make_simple_schema("source", PrimitiveType::I64);
        let target = make_simple_schema("target", PrimitiveType::I32);

        let result = detailed_compare(&source, &target);
        let summary = result.summary();

        assert_eq!(summary.total_types, 1);
        assert!(summary.total_losses > 0);
    }
}
