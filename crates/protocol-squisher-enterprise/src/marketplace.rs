// SPDX-License-Identifier: PMPL-1.0-or-later

use crate::unix_timestamp_utc;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdapterListing {
    pub id: String,
    pub name: String,
    pub from_format: String,
    pub to_format: String,
    pub version: String,
    pub description: String,
    pub tags: Vec<String>,
    pub published_at_utc: String,
}

#[derive(Debug, Clone, Default)]
pub struct ListingFilter {
    pub from_format: Option<String>,
    pub to_format: Option<String>,
    pub tag: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublishListingRequest {
    pub id: String,
    pub name: String,
    pub from_format: String,
    pub to_format: String,
    pub version: String,
    pub description: String,
    pub tags: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct AdapterMarketplace {
    root: PathBuf,
}

impl AdapterMarketplace {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn publish(&self, request: PublishListingRequest) -> Result<AdapterListing> {
        let listing = AdapterListing {
            id: request.id,
            name: request.name,
            from_format: request.from_format,
            to_format: request.to_format,
            version: request.version,
            description: request.description,
            tags: request.tags,
            published_at_utc: unix_timestamp_utc(),
        };

        let path = self.listing_path(&listing.id);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).with_context(|| {
                format!("Failed to create marketplace dir {}", parent.display())
            })?;
        }
        let data = serde_json::to_string_pretty(&listing)
            .context("Failed to serialize marketplace item")?;
        fs::write(&path, data)
            .with_context(|| format!("Failed to write marketplace item {}", path.display()))?;
        Ok(listing)
    }

    pub fn get(&self, id: &str) -> Result<AdapterListing> {
        let path = self.listing_path(id);
        let raw = fs::read_to_string(&path)
            .with_context(|| format!("Failed to read marketplace item {}", path.display()))?;
        let listing = serde_json::from_str::<AdapterListing>(&raw)
            .with_context(|| format!("Failed to parse marketplace item {}", path.display()))?;
        Ok(listing)
    }

    pub fn list(&self, filter: &ListingFilter) -> Result<Vec<AdapterListing>> {
        let dir = self.root.join("listings");
        if !dir.exists() {
            return Ok(vec![]);
        }

        let mut listings = Vec::new();
        for entry in fs::read_dir(&dir)
            .with_context(|| format!("Failed to list marketplace dir {}", dir.display()))?
        {
            let entry = entry?;
            let path = entry.path();
            if path.extension().and_then(|ext| ext.to_str()) != Some("json") {
                continue;
            }
            let raw = fs::read_to_string(&path)?;
            let listing = serde_json::from_str::<AdapterListing>(&raw)?;
            if matches_filter(&listing, filter) {
                listings.push(listing);
            }
        }

        listings.sort_by(|a, b| a.id.cmp(&b.id));
        Ok(listings)
    }

    fn listing_path(&self, id: &str) -> PathBuf {
        self.root
            .join("listings")
            .join(format!("{}.json", sanitize(id)))
    }
}

fn matches_filter(listing: &AdapterListing, filter: &ListingFilter) -> bool {
    if let Some(from) = &filter.from_format {
        if !listing.from_format.eq_ignore_ascii_case(from) {
            return false;
        }
    }
    if let Some(to) = &filter.to_format {
        if !listing.to_format.eq_ignore_ascii_case(to) {
            return false;
        }
    }
    if let Some(tag) = &filter.tag {
        if !listing.tags.iter().any(|t| t.eq_ignore_ascii_case(tag)) {
            return false;
        }
    }
    true
}

fn sanitize(value: &str) -> String {
    value
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Validation result for a marketplace listing submission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListingValidation {
    /// Whether the listing is valid for publication.
    pub valid: bool,
    /// Issues found during validation.
    pub issues: Vec<String>,
}

/// Validate a listing request before publication.
pub fn validate_listing(request: &PublishListingRequest) -> ListingValidation {
    let mut issues = Vec::new();

    if request.id.trim().is_empty() {
        issues.push("Listing ID must not be empty".to_string());
    }
    if request.name.trim().is_empty() {
        issues.push("Listing name must not be empty".to_string());
    }
    if request.from_format.trim().is_empty() {
        issues.push("Source format must not be empty".to_string());
    }
    if request.to_format.trim().is_empty() {
        issues.push("Target format must not be empty".to_string());
    }
    if request.version.trim().is_empty() {
        issues.push("Version must not be empty".to_string());
    }
    if request.from_format == request.to_format {
        issues.push("Source and target formats must be different".to_string());
    }

    ListingValidation {
        valid: issues.is_empty(),
        issues,
    }
}

/// Compute a simple popularity score for a listing based on tag count and
/// description length. Returns a value from 0 to 100.
pub fn popularity_score(listing: &AdapterListing) -> u8 {
    let tag_score = (listing.tags.len() as u8).min(5) * 10; // 0-50
    let desc_score = if listing.description.len() > 100 {
        30
    } else if listing.description.len() > 50 {
        20
    } else if listing.description.len() > 10 {
        10
    } else {
        0
    };
    let format_bonus: u8 = 20; // All published adapters get a base score

    (tag_score + desc_score + format_bonus).min(100)
}

impl AdapterMarketplace {
    /// Search listings by keyword across name, description, and tags.
    pub fn search(&self, keyword: &str) -> Result<Vec<AdapterListing>> {
        let all = self.list(&ListingFilter::default())?;
        let kw = keyword.to_lowercase();
        Ok(all
            .into_iter()
            .filter(|l| {
                l.name.to_lowercase().contains(&kw)
                    || l.description.to_lowercase().contains(&kw)
                    || l.tags.iter().any(|t| t.to_lowercase().contains(&kw))
            })
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_market_dir() -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        std::env::temp_dir().join(format!("protocol-squisher-market-{nanos}"))
    }

    #[test]
    fn publish_and_filter_listings() {
        let root = temp_market_dir();
        let market = AdapterMarketplace::new(&root);
        market
            .publish(PublishListingRequest {
                id: "rust-to-python-v1".to_string(),
                name: "Rust to Python Adapter".to_string(),
                from_format: "rust".to_string(),
                to_format: "python".to_string(),
                version: "1.0.0".to_string(),
                description: "Safe adapter".to_string(),
                tags: vec!["safe".to_string(), "prod".to_string()],
            })
            .expect("publish listing");

        let only_rust = market
            .list(&ListingFilter {
                from_format: Some("rust".to_string()),
                ..Default::default()
            })
            .expect("list with filter");
        assert_eq!(only_rust.len(), 1);
        assert_eq!(only_rust[0].id, "rust-to-python-v1");

        fs::remove_dir_all(root).ok();
    }

    #[test]
    fn validate_listing_catches_empty_fields() {
        let bad_request = PublishListingRequest {
            id: "".to_string(),
            name: "Test".to_string(),
            from_format: "rust".to_string(),
            to_format: "python".to_string(),
            version: "1.0.0".to_string(),
            description: "An adapter".to_string(),
            tags: vec![],
        };
        let result = validate_listing(&bad_request);
        assert!(!result.valid);
        assert!(result.issues.iter().any(|i| i.contains("ID")));
    }

    #[test]
    fn validate_listing_rejects_same_format() {
        let bad_request = PublishListingRequest {
            id: "test-adapter".to_string(),
            name: "Test".to_string(),
            from_format: "rust".to_string(),
            to_format: "rust".to_string(),
            version: "1.0.0".to_string(),
            description: "Pointless adapter".to_string(),
            tags: vec![],
        };
        let result = validate_listing(&bad_request);
        assert!(!result.valid);
        assert!(result.issues.iter().any(|i| i.contains("different")));
    }

    #[test]
    fn validate_listing_accepts_good_request() {
        let good_request = PublishListingRequest {
            id: "rust-to-python".to_string(),
            name: "Rust to Python Adapter".to_string(),
            from_format: "rust".to_string(),
            to_format: "python".to_string(),
            version: "1.0.0".to_string(),
            description: "A well-tested adapter for Rust to Python schema conversion".to_string(),
            tags: vec!["production".to_string()],
        };
        let result = validate_listing(&good_request);
        assert!(result.valid);
        assert!(result.issues.is_empty());
    }

    #[test]
    fn popularity_score_reflects_tags_and_description() {
        let listing = AdapterListing {
            id: "test".to_string(),
            name: "Test".to_string(),
            from_format: "rust".to_string(),
            to_format: "python".to_string(),
            version: "1.0.0".to_string(),
            description: "A comprehensive adapter for converting Rust structs to Python dataclasses with full type safety guarantees and validation".to_string(),
            tags: vec!["production".to_string(), "safe".to_string(), "typed".to_string()],
            published_at_utc: "0".to_string(),
        };
        let score = popularity_score(&listing);
        assert!(score >= 50, "Expected score >= 50, got {score}");
    }

    #[test]
    fn search_by_keyword() {
        let root = temp_market_dir();
        let market = AdapterMarketplace::new(&root);
        market
            .publish(PublishListingRequest {
                id: "rust-to-python-v1".to_string(),
                name: "Rust to Python Adapter".to_string(),
                from_format: "rust".to_string(),
                to_format: "python".to_string(),
                version: "1.0.0".to_string(),
                description: "Safe adapter".to_string(),
                tags: vec!["safe".to_string()],
            })
            .expect("publish");
        market
            .publish(PublishListingRequest {
                id: "json-to-protobuf-v1".to_string(),
                name: "JSON to Protobuf Adapter".to_string(),
                from_format: "json-schema".to_string(),
                to_format: "protobuf".to_string(),
                version: "1.0.0".to_string(),
                description: "Protobuf converter".to_string(),
                tags: vec!["binary".to_string()],
            })
            .expect("publish");

        let results = market.search("python").expect("search");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].id, "rust-to-python-v1");

        fs::remove_dir_all(root).ok();
    }
}
