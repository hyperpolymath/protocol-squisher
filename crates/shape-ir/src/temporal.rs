// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! # Temporal Algebra — Schema Evolution Over Time
//!
//! Schemas aren't static — they evolve. A database table gains columns. An API
//! adds fields. A protocol bumps its version. The temporal module captures this
//! evolution as a first-class concept.
//!
//! ## Core Concepts
//!
//! - **[`SchemaTimeline`]**: An ordered sequence of shape versions with morphisms
//!   between consecutive versions. Think of it as the `git log` for a data shape.
//!
//! - **[`VersionedShape`]**: A shape at a specific point in time, tagged with a
//!   semantic version.
//!
//! - **[`EvolutionStep`]**: A classified change between consecutive versions —
//!   is it additive, breaking, or an isomorphism?
//!
//! - **[`SemverClassification`]**: Formal semantic versioning derived from
//!   morphism properties, not human judgement:
//!   - **Patch** = isomorphism (Concorde) — no information change
//!   - **Minor** = embedding (Business) — information added, none lost
//!   - **Major** = information loss (Economy/Wheelbarrow) — breaking change
//!
//! - **[`CompatibilityForecast`]**: Given two independently-evolving timelines,
//!   predict at which version they diverge beyond safe transport.
//!
//! - **[`EvolutionStrategy`]**: Given a current shape and a target shape, find
//!   the minimum-cost sequence of evolution steps to get there.
//!
//! ## Example
//!
//! ```
//! use shape_ir::*;
//! use shape_ir::temporal::*;
//!
//! let mut timeline = SchemaTimeline::new("users");
//!
//! // v1: just id and name
//! let v1 = Shape::struct_from(vec![
//!     ("id", Shape::Atom(AtomKind::I32)),
//!     ("name", Shape::Atom(AtomKind::String)),
//! ]);
//! timeline.add_version(SemanticVersion::new(1, 0, 0), v1);
//!
//! // v2: added email (optional — non-breaking)
//! let v2 = Shape::struct_from(vec![
//!     ("id", Shape::Atom(AtomKind::I32)),
//!     ("name", Shape::Atom(AtomKind::String)),
//!     ("email", Shape::optional(Shape::Atom(AtomKind::String))),
//! ]);
//! timeline.add_version(SemanticVersion::new(1, 1, 0), v2);
//!
//! // Check: was v1 → v2 a minor bump? Yes.
//! let step = &timeline.evolution_steps()[0];
//! assert_eq!(step.classification, SemverClassification::Minor);
//! ```

use crate::compare::compare;
use crate::information::InformationCost;
use crate::{Morphism, Shape, TransportClass};
use serde::{Deserialize, Serialize};
use std::fmt;

// ---------------------------------------------------------------------------
// Semantic version
// ---------------------------------------------------------------------------

/// A semantic version (major.minor.patch).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SemanticVersion {
    /// Major version — breaking changes.
    pub major: u32,
    /// Minor version — additive changes.
    pub minor: u32,
    /// Patch version — isomorphic changes (no information change).
    pub patch: u32,
}

impl SemanticVersion {
    /// Create a new semantic version.
    pub fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }

    /// Returns true if this version is compatible with `other` (same major).
    pub fn is_compatible_with(&self, other: &Self) -> bool {
        self.major == other.major
    }
}

impl fmt::Display for SemanticVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

// ---------------------------------------------------------------------------
// Semver classification
// ---------------------------------------------------------------------------

/// Formal semantic version classification derived from morphism properties.
///
/// This replaces human judgement with provable properties:
/// - **Patch**: The morphism is an isomorphism — zero information change.
/// - **Minor**: The morphism embeds the source in the target — information
///   added but none lost. Old consumers can still read the data.
/// - **Major**: The morphism loses information — breaking change. Old consumers
///   will fail or lose data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemverClassification {
    /// Isomorphism — no information change (Concorde transport).
    Patch,
    /// Embedding — additive, non-breaking (Business transport).
    Minor,
    /// Breaking — information loss (Economy or Wheelbarrow transport).
    Major,
}

impl SemverClassification {
    /// Classify a morphism's transport class into a semver bump.
    pub fn from_transport_class(tc: TransportClass) -> Self {
        match tc {
            TransportClass::Concorde => Self::Patch,
            TransportClass::Business => Self::Minor,
            TransportClass::Economy | TransportClass::Wheelbarrow => Self::Major,
        }
    }

    /// Is this a breaking change?
    pub fn is_breaking(&self) -> bool {
        *self == Self::Major
    }

    /// Is this safe for existing consumers?
    pub fn is_backward_compatible(&self) -> bool {
        matches!(self, Self::Patch | Self::Minor)
    }
}

impl fmt::Display for SemverClassification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Patch => write!(f, "patch"),
            Self::Minor => write!(f, "minor"),
            Self::Major => write!(f, "MAJOR (breaking)"),
        }
    }
}

// ---------------------------------------------------------------------------
// Versioned shape
// ---------------------------------------------------------------------------

/// A shape at a specific version.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VersionedShape {
    /// The semantic version of this shape.
    pub version: SemanticVersion,
    /// The shape at this version.
    pub shape: Shape,
}

// ---------------------------------------------------------------------------
// Evolution step
// ---------------------------------------------------------------------------

/// A classified change between two consecutive versions.
#[derive(Debug, Clone)]
pub struct EvolutionStep {
    /// Version we're evolving from.
    pub from_version: SemanticVersion,
    /// Version we're evolving to.
    pub to_version: SemanticVersion,
    /// The morphism describing the structural change.
    pub morphism: Morphism,
    /// Formal semver classification of this change.
    pub classification: SemverClassification,
    /// Information cost of this evolution step.
    pub information_cost: InformationCost,
}

impl EvolutionStep {
    /// Is the declared version bump consistent with the actual change?
    ///
    /// Returns `true` if the actual structural change is at most as severe
    /// as the declared version bump. E.g., a patch bump with a minor change
    /// returns `false`.
    pub fn version_is_consistent(&self) -> bool {
        let declared = self.declared_severity();
        let actual = self.classification;

        match (declared, actual) {
            // Declared major — anything is consistent
            (SemverClassification::Major, _) => true,
            // Declared minor — only minor or patch is consistent
            (SemverClassification::Minor, SemverClassification::Patch) => true,
            (SemverClassification::Minor, SemverClassification::Minor) => true,
            (SemverClassification::Minor, SemverClassification::Major) => false,
            // Declared patch — only patch is consistent
            (SemverClassification::Patch, SemverClassification::Patch) => true,
            (SemverClassification::Patch, _) => false,
        }
    }

    /// What severity does the version bump declare?
    fn declared_severity(&self) -> SemverClassification {
        if self.to_version.major != self.from_version.major {
            SemverClassification::Major
        } else if self.to_version.minor != self.from_version.minor {
            SemverClassification::Minor
        } else {
            SemverClassification::Patch
        }
    }
}

// ---------------------------------------------------------------------------
// Schema timeline
// ---------------------------------------------------------------------------

/// An ordered sequence of shape versions forming the evolution history
/// of a single schema.
///
/// The timeline is append-only: versions are added in chronological order,
/// and morphisms between consecutive versions are computed automatically.
#[derive(Debug, Clone)]
pub struct SchemaTimeline {
    /// Name of the schema being tracked.
    name: String,
    /// Ordered list of versioned shapes.
    versions: Vec<VersionedShape>,
    /// Evolution steps between consecutive versions.
    steps: Vec<EvolutionStep>,
}

impl SchemaTimeline {
    /// Create a new empty timeline.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            versions: Vec::new(),
            steps: Vec::new(),
        }
    }

    /// Get the timeline name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Add a version to the timeline. Automatically computes the evolution
    /// step from the previous version (if any).
    pub fn add_version(&mut self, version: SemanticVersion, shape: Shape) {
        if let Some(prev) = self.versions.last() {
            let morphism = compare(&prev.shape, &shape);
            let classification =
                SemverClassification::from_transport_class(morphism.transport_class);
            let information_cost = morphism.information_cost.clone();

            self.steps.push(EvolutionStep {
                from_version: prev.version.clone(),
                to_version: version.clone(),
                morphism,
                classification,
                information_cost,
            });
        }

        self.versions.push(VersionedShape { version, shape });
    }

    /// Get the current (latest) shape, if any.
    pub fn current(&self) -> Option<&VersionedShape> {
        self.versions.last()
    }

    /// Get a shape at a specific version.
    pub fn at_version(&self, version: &SemanticVersion) -> Option<&VersionedShape> {
        self.versions.iter().find(|v| &v.version == version)
    }

    /// Get all versions in chronological order.
    pub fn versions(&self) -> &[VersionedShape] {
        &self.versions
    }

    /// Get the evolution steps between consecutive versions.
    pub fn evolution_steps(&self) -> &[EvolutionStep] {
        &self.steps
    }

    /// Count versions.
    pub fn version_count(&self) -> usize {
        self.versions.len()
    }

    /// Check if the entire version history has consistent semver bumps.
    ///
    /// Returns the indices of any inconsistent steps.
    pub fn inconsistent_versions(&self) -> Vec<usize> {
        self.steps
            .iter()
            .enumerate()
            .filter(|(_, step)| !step.version_is_consistent())
            .map(|(i, _)| i)
            .collect()
    }

    /// Check if the entire timeline is backward-compatible (no breaking changes).
    pub fn is_fully_backward_compatible(&self) -> bool {
        self.steps
            .iter()
            .all(|step| step.classification.is_backward_compatible())
    }

    /// Find the first breaking change in the timeline.
    pub fn first_breaking_change(&self) -> Option<&EvolutionStep> {
        self.steps.iter().find(|step| step.classification.is_breaking())
    }

    /// Compute the morphism from any historical version to the current version.
    ///
    /// This composes all intermediate morphisms to give the total transformation.
    pub fn morphism_to_current(&self, from_version: &SemanticVersion) -> Option<Morphism> {
        let from_idx = self
            .versions
            .iter()
            .position(|v| &v.version == from_version)?;
        let current_idx = self.versions.len().checked_sub(1)?;

        if from_idx == current_idx {
            // Same version — identity morphism
            let shape = &self.versions[from_idx].shape;
            return Some(compare(shape, shape));
        }

        if from_idx >= current_idx {
            return None; // from_version is after current
        }

        // Direct comparison gives us the composed morphism
        let from_shape = &self.versions[from_idx].shape;
        let to_shape = &self.versions[current_idx].shape;
        Some(compare(from_shape, to_shape))
    }
}

// ---------------------------------------------------------------------------
// Compatibility forecast
// ---------------------------------------------------------------------------

/// Forecast of compatibility between two independently-evolving timelines.
///
/// Given two schemas that started compatible and are evolving independently,
/// this predicts at which version pair they diverge beyond safe transport.
#[derive(Debug, Clone)]
pub struct CompatibilityForecast {
    /// Name of the first timeline.
    pub timeline_a: String,
    /// Name of the second timeline.
    pub timeline_b: String,
    /// Pairwise compatibility between versions (indexed by version pair).
    pub compatibility_matrix: Vec<VersionPairCompat>,
    /// The last version pair where transport is safe (Concorde or Business).
    pub last_safe_pair: Option<(SemanticVersion, SemanticVersion)>,
    /// The first version pair where transport becomes unsafe.
    pub first_unsafe_pair: Option<(SemanticVersion, SemanticVersion)>,
}

/// Compatibility between a specific pair of versions from two timelines.
#[derive(Debug, Clone)]
pub struct VersionPairCompat {
    /// Version from timeline A.
    pub version_a: SemanticVersion,
    /// Version from timeline B.
    pub version_b: SemanticVersion,
    /// Transport class between the two shapes.
    pub transport_class: TransportClass,
    /// The morphism between the two shapes.
    pub morphism: Morphism,
}

/// Forecast compatibility between two timelines.
///
/// Compares each version pair (latest A vs each B, and vice versa) to find
/// where compatibility breaks down.
pub fn forecast_compatibility(
    timeline_a: &SchemaTimeline,
    timeline_b: &SchemaTimeline,
) -> CompatibilityForecast {
    let mut matrix = Vec::new();
    let mut last_safe = None;
    let mut first_unsafe = None;

    for va in &timeline_a.versions {
        for vb in &timeline_b.versions {
            let morphism = compare(&va.shape, &vb.shape);
            let tc = morphism.transport_class;

            let is_safe = tc == TransportClass::Concorde || tc == TransportClass::Business;
            if is_safe {
                last_safe = Some((va.version.clone(), vb.version.clone()));
            } else if first_unsafe.is_none() {
                first_unsafe = Some((va.version.clone(), vb.version.clone()));
            }

            matrix.push(VersionPairCompat {
                version_a: va.version.clone(),
                version_b: vb.version.clone(),
                transport_class: tc,
                morphism,
            });
        }
    }

    CompatibilityForecast {
        timeline_a: timeline_a.name().to_string(),
        timeline_b: timeline_b.name().to_string(),
        compatibility_matrix: matrix,
        last_safe_pair: last_safe,
        first_unsafe_pair: first_unsafe,
    }
}

// ---------------------------------------------------------------------------
// Evolution strategy
// ---------------------------------------------------------------------------

/// A strategy for evolving a shape from its current form to a target form
/// through a sequence of individual, classifiable steps.
#[derive(Debug, Clone)]
pub struct EvolutionStrategy {
    /// The source shape.
    pub source: Shape,
    /// The target shape.
    pub target: Shape,
    /// The direct morphism from source to target.
    pub direct_morphism: Morphism,
    /// Classification of the overall change.
    pub overall_classification: SemverClassification,
    /// Suggested version bump.
    pub suggested_version: SemverClassification,
}

/// Compute the evolution strategy from a current shape to a target shape.
///
/// This answers: "What kind of version bump do I need, and what exactly changes?"
pub fn plan_evolution(source: &Shape, target: &Shape) -> EvolutionStrategy {
    let morphism = compare(source, target);
    let classification = SemverClassification::from_transport_class(morphism.transport_class);

    EvolutionStrategy {
        source: source.clone(),
        target: target.clone(),
        direct_morphism: morphism,
        overall_classification: classification,
        suggested_version: classification,
    }
}

/// Given a current version and a planned evolution, compute the next version.
pub fn next_version(
    current: &SemanticVersion,
    classification: SemverClassification,
) -> SemanticVersion {
    match classification {
        SemverClassification::Major => SemanticVersion::new(current.major + 1, 0, 0),
        SemverClassification::Minor => {
            SemanticVersion::new(current.major, current.minor + 1, 0)
        }
        SemverClassification::Patch => {
            SemanticVersion::new(current.major, current.minor, current.patch + 1)
        }
    }
}
