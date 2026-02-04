// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! # ephapax-Powered Optimizer
//!
//! Integrates ephapax transport class analysis with optimization suggestions.
//! Identifies which schema changes would improve transport classes.

use protocol_squisher_compat::{
    EphapaxCompatibilityEngine, FieldCompatibility,
    SchemaCompatibilityResult,
};
use protocol_squisher_ephapax_ir::TransportClass;
use protocol_squisher_ir::{FieldDef, IrSchema, IrType, PrimitiveType, TypeDef};
use std::collections::HashMap;

/// Suggestion for improving transport class
#[derive(Debug, Clone)]
pub struct OptimizationSuggestion {
    /// Type of optimization suggested
    pub kind: SuggestionKind,
    /// Field or type this suggestion applies to
    pub target: String,
    /// Current transport class
    pub current_class: TransportClass,
    /// Transport class after applying suggestion
    pub improved_class: TransportClass,
    /// Human-readable explanation
    pub reason: String,
    /// Estimated improvement (percentage points in zero-copy)
    pub impact: f64,
}

/// Type of optimization suggestion
#[derive(Debug, Clone, PartialEq)]
pub enum SuggestionKind {
    /// Widen a field type (e.g., i32 → i64)
    WidenType { from: IrType, to: IrType },
    /// Make a field optional to allow missing data
    MakeOptional,
    /// Add a field to target schema
    AddField { field: FieldDef },
    /// Change container type for better compatibility
    ChangeContainer { from: String, to: String },
    /// Align field names between schemas
    RenameField { from: String, to: String },
}

/// Result of ephapax-powered optimization analysis
#[derive(Debug, Clone)]
pub struct EphapaxOptimizationResult {
    /// Current compatibility analysis
    pub current: SchemaCompatibilityResult,
    /// Suggested optimizations (sorted by impact, highest first)
    pub suggestions: Vec<OptimizationSuggestion>,
    /// Estimated zero-copy percentage after applying all suggestions
    pub potential_zero_copy_percentage: f64,
    /// Whether schema would be production-ready after optimizations
    pub would_be_production_ready: bool,
}

/// Optimizer that uses ephapax transport class analysis
pub struct EphapaxOptimizer {
    engine: EphapaxCompatibilityEngine,
}

impl EphapaxOptimizer {
    /// Create a new ephapax optimizer
    pub fn new(engine: EphapaxCompatibilityEngine) -> Self {
        Self { engine }
    }

    /// Analyze schemas and suggest optimizations
    pub fn analyze_and_suggest(
        &self,
        source: &IrSchema,
        target: &IrSchema,
    ) -> EphapaxOptimizationResult {
        // Get current compatibility analysis
        let current = self.engine.analyze_schemas(source, target);

        // Generate suggestions
        let suggestions = self.generate_suggestions(source, target, &current);

        // Calculate potential improvement
        let potential_zero_copy = self.calculate_potential_improvement(&current, &suggestions);
        let would_be_production_ready = potential_zero_copy > 90.0;

        EphapaxOptimizationResult {
            current,
            suggestions,
            potential_zero_copy_percentage: potential_zero_copy,
            would_be_production_ready,
        }
    }

    /// Generate optimization suggestions based on current compatibility
    fn generate_suggestions(
        &self,
        source: &IrSchema,
        target: &IrSchema,
        current: &SchemaCompatibilityResult,
    ) -> Vec<OptimizationSuggestion> {
        let mut suggestions = Vec::new();

        // Analyze each type
        for type_analysis in &current.type_analyses {
            // Analyze each field for optimization opportunities
            for field_compat in &type_analysis.field_analyses {
                // Skip fields that are already Concorde (perfect)
                if field_compat.class == TransportClass::Concorde {
                    continue;
                }

                // Check if widening the target field would help
                if let Some(suggestion) =
                    self.suggest_type_widening(field_compat, &type_analysis.type_name, source, target)
                {
                    suggestions.push(suggestion);
                }

                // Check if making field optional would help
                if let Some(suggestion) =
                    self.suggest_optional(field_compat, &type_analysis.type_name, target)
                {
                    suggestions.push(suggestion);
                }
            }
        }

        // Sort by impact (highest first)
        suggestions.sort_by(|a, b| b.impact.partial_cmp(&a.impact).unwrap());

        suggestions
    }

    /// Suggest widening a type (e.g., i32 → i64 to avoid narrowing)
    fn suggest_type_widening(
        &self,
        field_compat: &FieldCompatibility,
        type_name: &str,
        source: &IrSchema,
        target: &IrSchema,
    ) -> Option<OptimizationSuggestion> {
        // Only suggest for Wheelbarrow fields (worst class)
        if field_compat.class != TransportClass::Wheelbarrow {
            return None;
        }

        // Get the struct definitions
        let source_type_id = type_name.to_string();
        let source_def = source.types.get(&source_type_id)?;
        let target_def = target.types.get(&source_type_id)?;

        // Extract struct fields
        let (source_struct, target_struct) = match (source_def, target_def) {
            (TypeDef::Struct(s), TypeDef::Struct(t)) => (s, t),
            _ => return None,
        };

        // Find the specific fields
        let source_field = source_struct
            .fields
            .iter()
            .find(|f| f.name == field_compat.field_name)?;
        let target_field = target_struct
            .fields
            .iter()
            .find(|f| f.name == field_compat.field_name)?;

        // Check if this is a narrowing conversion
        if let (IrType::Primitive(source_prim), IrType::Primitive(target_prim)) =
            (&source_field.ty, &target_field.ty)
        {
            if let Some(wider_type) = get_wider_type(source_prim, target_prim) {
                let improved_class = if wider_type == *source_prim {
                    TransportClass::Concorde // Perfect match
                } else {
                    TransportClass::Business // Widening conversion
                };

                // Count total fields across all types for impact calculation
                let total_fields = count_total_fields(source);

                return Some(OptimizationSuggestion {
                    kind: SuggestionKind::WidenType {
                        from: IrType::Primitive(*target_prim),
                        to: IrType::Primitive(wider_type),
                    },
                    target: format!("{}.{}", type_name, field_compat.field_name),
                    current_class: field_compat.class,
                    improved_class,
                    reason: format!(
                        "Widening target field '{}' from {:?} to {:?} would avoid data loss",
                        field_compat.field_name, target_prim, wider_type
                    ),
                    impact: 100.0 / total_fields as f64,
                });
            }
        }

        None
    }

    /// Suggest making a field optional
    fn suggest_optional(
        &self,
        field_compat: &FieldCompatibility,
        type_name: &str,
        target: &IrSchema,
    ) -> Option<OptimizationSuggestion> {
        // Only suggest for Wheelbarrow fields
        if field_compat.class != TransportClass::Wheelbarrow {
            return None;
        }

        let target_type_id = type_name.to_string();
        let target_def = target.types.get(&target_type_id)?;

        let target_struct = match target_def {
            TypeDef::Struct(s) => s,
            _ => return None,
        };

        let target_field = target_struct
            .fields
            .iter()
            .find(|f| f.name == field_compat.field_name)?;

        // If target field is required but might not always be compatible
        if !target_field.optional {
            let total_fields = count_total_fields(target);

            return Some(OptimizationSuggestion {
                kind: SuggestionKind::MakeOptional,
                target: format!("{}.{}", type_name, field_compat.field_name),
                current_class: field_compat.class,
                improved_class: TransportClass::Business,
                reason: format!(
                    "Making target field '{}' optional would allow graceful handling of incompatible data",
                    field_compat.field_name
                ),
                impact: 50.0 / total_fields as f64,
            });
        }

        None
    }

    /// Calculate potential zero-copy percentage after applying suggestions
    fn calculate_potential_improvement(
        &self,
        current: &SchemaCompatibilityResult,
        suggestions: &[OptimizationSuggestion],
    ) -> f64 {
        // Build a map of which fields would improve
        // Track the BEST improvement for each field (prefer Concorde over Business)
        let mut improvements: HashMap<String, TransportClass> = HashMap::new();

        for suggestion in suggestions {
            let current_best = improvements.get(&suggestion.target);
            let should_update = match current_best {
                None => true,
                Some(current) => {
                    // Only update if the new suggestion is better (lower enum value = better)
                    (suggestion.improved_class as u8) < (*current as u8)
                }
            };

            if should_update {
                improvements.insert(suggestion.target.clone(), suggestion.improved_class);
            }
        }

        // Count total fields and how many would be zero-copy after improvements
        let mut zero_copy_fields = 0;
        let mut total_fields = 0;

        for type_analysis in &current.type_analyses {
            for field_compat in &type_analysis.field_analyses {
                total_fields += 1;

                let field_path = format!("{}.{}", type_analysis.type_name, field_compat.field_name);
                let final_class = improvements
                    .get(&field_path)
                    .unwrap_or(&field_compat.class);

                if matches!(final_class, TransportClass::Concorde) {
                    zero_copy_fields += 1;
                }
            }
        }

        if total_fields == 0 {
            return 0.0;
        }

        (zero_copy_fields as f64 / total_fields as f64) * 100.0
    }
}

/// Count total fields across all root types in a schema
fn count_total_fields(schema: &IrSchema) -> usize {
    let mut count = 0;
    for root_id in &schema.roots {
        if let Some(type_def) = schema.types.get(root_id) {
            if let TypeDef::Struct(s) = type_def {
                count += s.fields.len();
            }
        }
    }
    count.max(1) // Avoid division by zero
}

/// Get the wider of two numeric types (or the source type if already wider)
fn get_wider_type(source: &PrimitiveType, target: &PrimitiveType) -> Option<PrimitiveType> {
    use PrimitiveType::*;

    match (source, target) {
        // Integer narrowing cases - return source (wider) type
        (I64, I32) | (I64, I16) | (I64, I8) => Some(I64),
        (I32, I16) | (I32, I8) => Some(I32),
        (I16, I8) => Some(I16),
        (U64, U32) | (U64, U16) | (U64, U8) => Some(U64),
        (U32, U16) | (U32, U8) => Some(U32),
        (U16, U8) => Some(U16),
        (F64, F32) => Some(F64),

        // Already widening or same - no suggestion
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use protocol_squisher_ir::{FieldMetadata, StructDef, TypeMetadata};
    use std::collections::BTreeMap;

    fn make_test_schemas() -> (IrSchema, IrSchema) {
        let source_struct = StructDef {
            name: "TestStruct".to_string(),
            fields: vec![
                FieldDef {
                    name: "id".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
                FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(PrimitiveType::F64),
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
            ],
            metadata: TypeMetadata::default(),
        };

        let target_struct = StructDef {
            name: "TestStruct".to_string(),
            fields: vec![
                FieldDef {
                    name: "id".to_string(),
                    ty: IrType::Primitive(PrimitiveType::I32), // Narrowing!
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
                FieldDef {
                    name: "value".to_string(),
                    ty: IrType::Primitive(PrimitiveType::F32), // Narrowing!
                    optional: false,
                    constraints: vec![],
                    metadata: FieldMetadata::default(),
                },
            ],
            metadata: TypeMetadata::default(),
        };

        let mut source_types = BTreeMap::new();
        source_types.insert("TestStruct".to_string(), TypeDef::Struct(source_struct));

        let mut target_types = BTreeMap::new();
        target_types.insert("TestStruct".to_string(), TypeDef::Struct(target_struct));

        let source = IrSchema {
            name: "SourceSchema".to_string(),
            version: "1.0.0".to_string(),
            source_format: "test".to_string(),
            types: source_types,
            roots: vec!["TestStruct".to_string()],
            metadata: Default::default(),
        };

        let target = IrSchema {
            name: "TargetSchema".to_string(),
            version: "1.0.0".to_string(),
            source_format: "test".to_string(),
            types: target_types,
            roots: vec!["TestStruct".to_string()],
            metadata: Default::default(),
        };

        (source, target)
    }

    #[test]
    fn test_optimizer_suggests_widening() {
        let (source, target) = make_test_schemas();
        let engine = EphapaxCompatibilityEngine::new();
        let optimizer = EphapaxOptimizer::new(engine);

        let result = optimizer.analyze_and_suggest(&source, &target);

        // Should suggest widening both fields
        assert!(result.suggestions.len() >= 2);

        // Check for i32 → i64 suggestion
        let id_suggestion = result
            .suggestions
            .iter()
            .find(|s| s.target.contains("id"))
            .expect("Should suggest widening 'id' field");

        assert_eq!(
            id_suggestion.current_class,
            TransportClass::Wheelbarrow
        );
        assert_eq!(
            id_suggestion.improved_class,
            TransportClass::Concorde
        );

        // Check for f32 → f64 suggestion
        let value_suggestion = result
            .suggestions
            .iter()
            .find(|s| s.target.contains("value"))
            .expect("Should suggest widening 'value' field");

        assert_eq!(
            value_suggestion.current_class,
            TransportClass::Wheelbarrow
        );
        assert_eq!(
            value_suggestion.improved_class,
            TransportClass::Concorde
        );
    }

    #[test]
    fn test_potential_improvement_calculation() {
        let (source, target) = make_test_schemas();
        let engine = EphapaxCompatibilityEngine::new();
        let optimizer = EphapaxOptimizer::new(engine);

        let result = optimizer.analyze_and_suggest(&source, &target);

        // Both fields have narrowing conversions (Wheelbarrow)
        // After widening both, should be 100% zero-copy
        assert_eq!(result.potential_zero_copy_percentage, 100.0);
        assert!(result.would_be_production_ready);
    }

    #[test]
    fn test_production_readiness_threshold() {
        let (source, target) = make_test_schemas();
        let engine = EphapaxCompatibilityEngine::new();
        let optimizer = EphapaxOptimizer::new(engine);

        let result = optimizer.analyze_and_suggest(&source, &target);

        // Would be production ready after optimizations (>90% zero-copy)
        assert!(result.would_be_production_ready);
    }

    #[test]
    fn test_suggestions_sorted_by_impact() {
        let (source, target) = make_test_schemas();
        let engine = EphapaxCompatibilityEngine::new();
        let optimizer = EphapaxOptimizer::new(engine);

        let result = optimizer.analyze_and_suggest(&source, &target);

        // Suggestions should be sorted by impact (descending)
        for i in 1..result.suggestions.len() {
            assert!(
                result.suggestions[i - 1].impact >= result.suggestions[i].impact,
                "Suggestions should be sorted by impact (descending)"
            );
        }
    }

    #[test]
    fn test_get_wider_type() {
        assert_eq!(
            get_wider_type(&PrimitiveType::I64, &PrimitiveType::I32),
            Some(PrimitiveType::I64)
        );
        assert_eq!(
            get_wider_type(&PrimitiveType::F64, &PrimitiveType::F32),
            Some(PrimitiveType::F64)
        );
        assert_eq!(
            get_wider_type(&PrimitiveType::U32, &PrimitiveType::U16),
            Some(PrimitiveType::U32)
        );

        // No suggestion for widening conversions
        assert_eq!(
            get_wider_type(&PrimitiveType::I32, &PrimitiveType::I64),
            None
        );
    }

    #[test]
    fn test_count_total_fields() {
        let (source, _) = make_test_schemas();
        assert_eq!(count_total_fields(&source), 2); // id + value
    }
}
