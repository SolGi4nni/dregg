//! Serde helper for `[u8; 64]` (Ed25519 signature bytes).
//!
//! Standard serde only implements Serialize/Deserialize for arrays up to 32 bytes.
//! This module provides serialize/deserialize functions for 64-byte arrays used
//! as Ed25519 signature storage.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
    // Serialize as a byte slice (postcard will encode efficiently).
    bytes.as_slice().serialize(serializer)
}

pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
    let vec = Vec::<u8>::deserialize(deserializer)?;
    if vec.len() != 64 {
        return Err(serde::de::Error::custom(format!(
            "expected 64 bytes for signature, got {}",
            vec.len()
        )));
    }
    let mut arr = [0u8; 64];
    arr.copy_from_slice(&vec);
    Ok(arr)
}
