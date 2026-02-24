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
    bytes.par_chunks(CHUNK_SIZE)
        .map(xor_checksum_scalar)
        .reduce(|| 0u8, |a, b| a ^ b)
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
}
