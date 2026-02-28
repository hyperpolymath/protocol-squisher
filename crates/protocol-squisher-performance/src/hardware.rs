// SPDX-License-Identifier: PMPL-1.0-or-later

use crate::simd::{xor_checksum, xor_checksum_scalar};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HardwareBackend {
    Scalar,
    Simd,
    Parallel,
}

pub fn recommended_backend() -> HardwareBackend {
    let cpu_count = std::thread::available_parallelism()
        .map(|v| v.get())
        .unwrap_or(1);

    if cpu_count >= 4 {
        HardwareBackend::Parallel
    } else {
        #[cfg(target_arch = "x86_64")]
        {
            if std::arch::is_x86_feature_detected!("sse2") {
                return HardwareBackend::Simd;
            }
        }
        HardwareBackend::Scalar
    }
}

pub fn checksum_with_backend(bytes: &[u8], backend: HardwareBackend) -> u8 {
    match backend {
        HardwareBackend::Scalar => xor_checksum_scalar(bytes),
        HardwareBackend::Simd => xor_checksum(bytes),
        HardwareBackend::Parallel => xor_checksum_parallel(bytes),
    }
}

pub fn xor_checksum_parallel(bytes: &[u8]) -> u8 {
    const CHUNK_SIZE: usize = 32 * 1024;
    bytes
        .par_chunks(CHUNK_SIZE)
        .map(xor_checksum_scalar)
        .reduce(|| 0u8, |a, b| a ^ b)
}

/// Detected hardware capabilities profile.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HardwareProfile {
    /// Estimated cache line size in bytes.
    pub cache_line_size: usize,
    /// SIMD register width in bytes (16 = SSE2, 32 = AVX2, etc.).
    pub simd_width: usize,
    /// Number of available CPU cores.
    pub core_count: usize,
    /// Recommended backend based on detection.
    pub recommended: HardwareBackend,
}

/// Detect hardware capabilities and return a profile.
pub fn detect_hardware() -> HardwareProfile {
    let core_count = std::thread::available_parallelism()
        .map(|v| v.get())
        .unwrap_or(1);

    let simd_width = detect_simd_width();

    HardwareProfile {
        cache_line_size: 64, // Standard on x86_64 and aarch64.
        simd_width,
        core_count,
        recommended: recommended_backend(),
    }
}

/// Detect SIMD register width in bytes.
fn detect_simd_width() -> usize {
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("avx2") {
            return 32;
        }
        if std::arch::is_x86_feature_detected!("sse2") {
            return 16;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        return 16; // NEON is always available on aarch64.
    }
    1 // Scalar fallback.
}

/// Compute the optimal chunk size for streaming operations based on hardware.
///
/// Returns a chunk size that aligns to cache lines and is large enough to
/// amortize overhead but small enough to fit in L1 cache.
pub fn optimal_chunk_size(profile: &HardwareProfile) -> usize {
    // Target: 32KB (typical L1 data cache half), aligned to cache line.
    let target = 32 * 1024;
    let aligned = (target / profile.cache_line_size) * profile.cache_line_size;
    aligned.max(profile.cache_line_size)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn backends_agree_on_checksum() {
        let data: Vec<u8> = (0..1_000_000).map(|i| (i % 251) as u8).collect();
        let scalar = checksum_with_backend(&data, HardwareBackend::Scalar);
        let simd = checksum_with_backend(&data, HardwareBackend::Simd);
        let parallel = checksum_with_backend(&data, HardwareBackend::Parallel);
        assert_eq!(scalar, simd);
        assert_eq!(scalar, parallel);
    }

    #[test]
    fn recommended_backend_is_valid() {
        let backend = recommended_backend();
        assert!(matches!(
            backend,
            HardwareBackend::Scalar | HardwareBackend::Simd | HardwareBackend::Parallel
        ));
    }

    #[test]
    fn hardware_profile_detection() {
        let profile = detect_hardware();
        assert!(profile.core_count >= 1);
        assert!(profile.cache_line_size > 0);
        assert!(profile.simd_width >= 1);
        assert!(matches!(
            profile.recommended,
            HardwareBackend::Scalar | HardwareBackend::Simd | HardwareBackend::Parallel
        ));
    }

    #[test]
    fn optimal_chunk_size_is_cache_aligned() {
        let profile = detect_hardware();
        let chunk = optimal_chunk_size(&profile);
        assert!(chunk >= profile.cache_line_size);
        assert_eq!(chunk % profile.cache_line_size, 0);
    }
}
