// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! SIMD-style byte operations using portable lane-parallel patterns.
//!
//! All functions here are safe Rust. They use chunked/lane processing that
//! maps well to auto-vectorization by LLVM, without requiring explicit
//! platform-specific SIMD intrinsics.

/// Lane width for chunked processing. 16 bytes maps to SSE2 register width
/// and is also a natural fit for NEON (ARM) and WASM SIMD.
const LANES: usize = 16;

/// Compute a simple XOR checksum using 16-byte lane reduction.
///
/// This stays fully safe-Rust while keeping chunked processing semantics
/// that LLVM can auto-vectorize on supported targets.
pub fn xor_checksum(bytes: &[u8]) -> u8 {
    let mut lane_acc = [0u8; LANES];
    let mut chunks = bytes.chunks_exact(LANES);

    for chunk in &mut chunks {
        for (acc, byte) in lane_acc.iter_mut().zip(chunk.iter()) {
            *acc ^= *byte;
        }
    }

    let mut out = lane_acc.iter().fold(0u8, |acc, byte| acc ^ *byte);
    out ^= chunks.remainder().iter().fold(0u8, |acc, byte| acc ^ *byte);
    out
}

/// Scalar XOR checksum for reference and small-buffer fallback.
pub fn xor_checksum_scalar(bytes: &[u8]) -> u8 {
    bytes.iter().fold(0u8, |acc, b| acc ^ *b)
}

/// Count the number of byte positions where two slices differ, using
/// lane-parallel processing.
///
/// If the slices have different lengths, every position beyond the shorter
/// slice counts as a difference.
pub fn count_differences(a: &[u8], b: &[u8]) -> usize {
    let common_len = a.len().min(b.len());
    let tail_diff = a.len().abs_diff(b.len());

    let mut diff_acc = [0u64; LANES];
    let mut chunks_a = a[..common_len].chunks_exact(LANES);
    let mut chunks_b = b[..common_len].chunks_exact(LANES);

    for (ca, cb) in chunks_a.by_ref().zip(chunks_b.by_ref()) {
        for i in 0..LANES {
            if ca[i] != cb[i] {
                diff_acc[i] += 1;
            }
        }
    }

    let remainder_diff: usize = chunks_a
        .remainder()
        .iter()
        .zip(chunks_b.remainder().iter())
        .filter(|(x, y)| x != y)
        .count();

    let lane_total: u64 = diff_acc.iter().sum();
    lane_total as usize + remainder_diff + tail_diff
}

/// Check whether two byte slices are identical, using lane-parallel
/// short-circuit comparison.
///
/// Returns `false` as soon as any differing lane is found.
pub fn bytes_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    let mut chunks_a = a.chunks_exact(LANES);
    let mut chunks_b = b.chunks_exact(LANES);

    for (ca, cb) in chunks_a.by_ref().zip(chunks_b.by_ref()) {
        for i in 0..LANES {
            if ca[i] != cb[i] {
                return false;
            }
        }
    }

    chunks_a
        .remainder()
        .iter()
        .zip(chunks_b.remainder().iter())
        .all(|(x, y)| x == y)
}

/// Compute a simple FNV-1a-style hash over a byte slice using lane folding.
///
/// This is NOT cryptographic. Useful for quick content fingerprinting to
/// detect whether a schema buffer has changed.
pub fn fast_hash(bytes: &[u8]) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x00000100000001B3;

    let mut hash = FNV_OFFSET;
    for &byte in bytes {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simd_checksum_matches_scalar() {
        let data: Vec<u8> = (0..10_000).map(|i| (i % 251) as u8).collect();
        assert_eq!(xor_checksum(&data), xor_checksum_scalar(&data));
    }

    #[test]
    fn count_differences_identical() {
        let data = vec![1u8, 2, 3, 4, 5];
        assert_eq!(count_differences(&data, &data), 0);
    }

    #[test]
    fn count_differences_all_different() {
        let a = vec![0u8; 100];
        let b = vec![1u8; 100];
        assert_eq!(count_differences(&a, &b), 100);
    }

    #[test]
    fn count_differences_length_mismatch() {
        let a = vec![1u8, 2, 3];
        let b = vec![1u8, 2, 3, 4, 5];
        assert_eq!(count_differences(&a, &b), 2); // 2 extra bytes in b
    }

    #[test]
    fn count_differences_large_buffer() {
        let mut a: Vec<u8> = (0..1000).map(|i| (i % 256) as u8).collect();
        let b = a.clone();
        // Flip every 10th byte
        for i in (0..1000).step_by(10) {
            a[i] = a[i].wrapping_add(1);
        }
        assert_eq!(count_differences(&a, &b), 100);
    }

    #[test]
    fn bytes_equal_identical() {
        let data = vec![42u8; 200];
        assert!(bytes_equal(&data, &data));
    }

    #[test]
    fn bytes_equal_different_lengths() {
        assert!(!bytes_equal(&[1, 2, 3], &[1, 2]));
    }

    #[test]
    fn bytes_equal_one_diff() {
        let a = vec![0u8; 100];
        let mut b = a.clone();
        b[99] = 1;
        assert!(!bytes_equal(&a, &b));
    }

    #[test]
    fn fast_hash_deterministic() {
        let data = b"protocol-squisher";
        assert_eq!(fast_hash(data), fast_hash(data));
    }

    #[test]
    fn fast_hash_different_inputs() {
        assert_ne!(fast_hash(b"hello"), fast_hash(b"world"));
    }

    #[test]
    fn empty_slices() {
        assert_eq!(xor_checksum(&[]), 0);
        assert_eq!(count_differences(&[], &[]), 0);
        assert!(bytes_equal(&[], &[]));
        assert_eq!(fast_hash(&[]), 0xcbf29ce484222325); // FNV offset basis
    }
}
