// SPDX-License-Identifier: PMPL-1.0-or-later

/// Compute a simple XOR checksum using 16-byte lane reduction.
///
/// This stays fully safe-Rust while keeping chunked processing semantics.
pub fn xor_checksum(bytes: &[u8]) -> u8 {
    const LANES: usize = 16;
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

pub fn xor_checksum_scalar(bytes: &[u8]) -> u8 {
    bytes.iter().fold(0u8, |acc, b| acc ^ *b)
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
