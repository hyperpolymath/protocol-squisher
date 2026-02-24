// SPDX-License-Identifier: PMPL-1.0-or-later

/// Compute a simple XOR checksum, using SIMD where available.
pub fn xor_checksum(bytes: &[u8]) -> u8 {
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("sse2") {
            // SAFETY: Gated by runtime feature detection.
            return unsafe { xor_checksum_sse2(bytes) };
        }
    }

    xor_checksum_scalar(bytes)
}

pub fn xor_checksum_scalar(bytes: &[u8]) -> u8 {
    bytes.iter().fold(0u8, |acc, b| acc ^ *b)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn xor_checksum_sse2(bytes: &[u8]) -> u8 {
    use std::arch::x86_64::{__m128i, _mm_loadu_si128, _mm_setzero_si128, _mm_storeu_si128, _mm_xor_si128};

    let mut acc: __m128i = _mm_setzero_si128();
    let mut i = 0usize;

    while i + 16 <= bytes.len() {
        let ptr = bytes.as_ptr().add(i).cast::<__m128i>();
        let chunk = _mm_loadu_si128(ptr);
        acc = _mm_xor_si128(acc, chunk);
        i += 16;
    }

    let mut lanes = [0u8; 16];
    _mm_storeu_si128(lanes.as_mut_ptr().cast::<__m128i>(), acc);
    let mut out = lanes.iter().fold(0u8, |v, b| v ^ *b);

    while i < bytes.len() {
        out ^= bytes[i];
        i += 1;
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simd_checksum_matches_scalar() {
        let data: Vec<u8> = (0..10_000).map(|i| (i % 251) as u8).collect();
        assert_eq!(xor_checksum(&data), xor_checksum_scalar(&data));
    }
}
