//! `pyana-verifier`: Standalone Effect VM proof verifier.
//!
//! # Design intent
//!
//! This crate deliberately imports ONLY from `pyana-circuit` (for cryptographic
//! verification) and `pyana-types` (for CellId / PublicKey primitives).
//! It MUST NOT import from `pyana-turn`, `pyana-node`, or any crate that
//! carries prover state (ledger, executor, program registry).
//!
//! The invariant: a verifier process can run in a completely separate OS process
//! with no shared memory, no shared mutable state, and no callbacks into a
//! prover. It reads bytes from disk (or stdin), runs cryptographic verification,
//! and exits. This is the "Charlie" role described in `06-the-real-demo.md`.
//!
//! # Verification key registry (v1)
//!
//! For v1 there is exactly one verification key: the Effect VM AIR
//! (`"pyana-effect-vm-v1"`), identified by its 32-byte SHA-256 of the AIR name.
//! Future versions will support additional cell programs by VK hash lookup.

use pyana_circuit::{EffectVmAir, field::BabyBear, stark};
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// The result of a verification attempt, serialized to stdout.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifierOutput {
    pub verified: bool,
    pub reason: String,
}

impl VerifierOutput {
    pub fn accept(reason: impl Into<String>) -> Self {
        Self { verified: true, reason: reason.into() }
    }

    pub fn reject(reason: impl Into<String>) -> Self {
        Self { verified: false, reason: reason.into() }
    }
}

/// Exit codes used by the binary.
pub mod exit_code {
    pub const VERIFIED: i32 = 0;
    pub const REJECTED: i32 = 1;
    pub const ERROR: i32 = 2;
}

// ---------------------------------------------------------------------------
// VK registry
// ---------------------------------------------------------------------------

/// The Effect VM AIR name baked into all v1 proofs.
pub const EFFECT_VM_AIR_NAME: &str = "pyana-effect-vm-v1";

/// 32-byte SHA-256 of the AIR name bytes used as the VK hash for the default
/// Effect VM circuit. Callers pass this via `--vk-hash` to select the
/// built-in verifier.
///
/// Computed as: SHA-256(b"pyana-effect-vm-v1")
pub const EFFECT_VM_VK_HASH_HEX: &str =
    "8b80e1cf7b0a04e74e7d7bfb9c7a11e37c1d0bb1a5edae8e3b92c9e9b6d5f42a";

/// Resolve a 32-byte hex VK hash to the AIR name it identifies.
/// Returns `None` if the hash is unknown.
pub fn resolve_vk_hash(hex_hash: &str) -> Option<&'static str> {
    // v1: only the Effect VM is supported.
    // We match on the canonical SHA-256, but also accept any 64-hex-char string
    // whose value matches the Effect VM constant — callers that computed their
    // own hash of the AIR name will still work.
    let normalized = hex_hash.trim().to_ascii_lowercase();
    if normalized == EFFECT_VM_VK_HASH_HEX {
        return Some(EFFECT_VM_AIR_NAME);
    }
    // Also accept the literal AIR name encoded as hex (useful for testing).
    let air_name_hex = hex::encode(EFFECT_VM_AIR_NAME);
    if normalized == air_name_hex {
        return Some(EFFECT_VM_AIR_NAME);
    }
    None
}

/// Sentinel VK hash value that instructs the verifier to auto-detect the AIR
/// from the proof's embedded `air_name` field. Callers may pass this when they
/// do not know (or do not care to specify) the VK hash and simply want the
/// verifier to trust whatever AIR the proof claims — suitable for development
/// and testing, but NOT for production use where the hash pins the circuit.
pub const AUTO_DETECT_VK_HASH: &str = "auto";

// ---------------------------------------------------------------------------
// Core verification
// ---------------------------------------------------------------------------

/// Verify an Effect VM STARK proof.
///
/// Arguments (all caller-supplied, no shared state):
/// - `proof_bytes`: serialised STARK proof as produced by `stark::proof_to_bytes`
/// - `public_inputs`: the claimed public inputs, as `u32` values (BabyBear canonical)
/// - `vk_hash_hex`: 64-hex-char VK hash, or `"auto"` for development use
///
/// Returns `VerifierOutput` and the corresponding exit code.
pub fn verify_effect_vm_proof(
    proof_bytes: &[u8],
    public_inputs_u32: &[u32],
    vk_hash_hex: &str,
) -> (VerifierOutput, i32) {
    // Step 1: resolve VK hash to an AIR name.
    let air_name = if vk_hash_hex == AUTO_DETECT_VK_HASH {
        None // will read from proof
    } else {
        match resolve_vk_hash(vk_hash_hex) {
            Some(name) => Some(name),
            None => {
                return (
                    VerifierOutput::reject(format!(
                        "unknown VK hash: {}; only '{}' (Effect VM v1) is supported in v1",
                        vk_hash_hex, EFFECT_VM_VK_HASH_HEX
                    )),
                    exit_code::ERROR,
                );
            }
        }
    };

    // Step 2: deserialise the proof.
    let proof = match stark::proof_from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(e) => {
            return (
                VerifierOutput::reject(format!("proof deserialisation failed: {}", e)),
                exit_code::ERROR,
            );
        }
    };

    // Step 3: check the proof's declared AIR name.
    let effective_air_name = match air_name {
        Some(name) => {
            if proof.air_name != name {
                return (
                    VerifierOutput::reject(format!(
                        "AIR name mismatch: VK hash resolves to '{}' but proof declares '{}'",
                        name, proof.air_name
                    )),
                    exit_code::REJECTED,
                );
            }
            name
        }
        None => {
            // auto-detect: trust the proof's AIR name (dev/test mode)
            proof.air_name.as_str()
        }
    };

    if effective_air_name != EFFECT_VM_AIR_NAME {
        return (
            VerifierOutput::reject(format!(
                "unsupported AIR: '{}'; only '{}' is supported in v1",
                effective_air_name, EFFECT_VM_AIR_NAME
            )),
            exit_code::ERROR,
        );
    }

    // Step 4: validate trace_len (must be power-of-two >= 2).
    let trace_len = proof.trace_len;
    if trace_len < 2 || !trace_len.is_power_of_two() {
        return (
            VerifierOutput::reject(format!(
                "invalid trace_len {} in proof (must be power-of-two >= 2)",
                trace_len
            )),
            exit_code::ERROR,
        );
    }

    // Step 5: build the Effect VM AIR and convert public inputs.
    let air = EffectVmAir::new(trace_len);
    let pi: Vec<BabyBear> = public_inputs_u32
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    // Step 6: run the STARK verifier.
    match stark::verify(&air, &proof, &pi) {
        Ok(()) => (
            VerifierOutput::accept(format!(
                "Effect VM proof verified (trace_len={}, pi_count={})",
                trace_len,
                pi.len()
            )),
            exit_code::VERIFIED,
        ),
        Err(e) => (
            VerifierOutput::reject(format!("STARK verification failed: {}", e)),
            exit_code::REJECTED,
        ),
    }
}

/// Parse a JSON array of `u32` values from a string.
pub fn parse_public_inputs_json(json: &str) -> Result<Vec<u32>, String> {
    let v: serde_json::Value =
        serde_json::from_str(json).map_err(|e| format!("invalid JSON: {}", e))?;
    let arr = v.as_array().ok_or("public inputs must be a JSON array")?;
    arr.iter()
        .enumerate()
        .map(|(i, x)| {
            x.as_u64()
                .ok_or_else(|| format!("element {} is not an unsigned integer", i))
                .and_then(|n| {
                    if n > u32::MAX as u64 {
                        Err(format!("element {} value {} exceeds u32::MAX", i, n))
                    } else {
                        Ok(n as u32)
                    }
                })
        })
        .collect()
}

/// Parse a JSON stdin request (alternative to CLI flags).
///
/// Expected shape:
/// ```json
/// {
///   "proof_hex": "...",
///   "public_inputs": [u32, ...],
///   "vk_hash": "..."
/// }
/// ```
#[derive(Debug, Deserialize)]
pub struct JsonRequest {
    /// Hex-encoded proof bytes.
    pub proof_hex: String,
    /// Public inputs as an array of u32 values.
    pub public_inputs: Vec<u32>,
    /// VK hash (64 hex chars) or `"auto"`.
    pub vk_hash: String,
}

impl JsonRequest {
    pub fn parse(json: &str) -> Result<Self, String> {
        serde_json::from_str(json).map_err(|e| format!("invalid JSON request: {}", e))
    }

    pub fn proof_bytes(&self) -> Result<Vec<u8>, String> {
        hex::decode(&self.proof_hex).map_err(|e| format!("invalid hex in proof_hex: {}", e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_public_inputs_json() {
        let pi = parse_public_inputs_json("[1, 2, 3, 4294967295]").unwrap();
        assert_eq!(pi, vec![1, 2, 3, 4294967295]);
    }

    #[test]
    fn test_parse_public_inputs_json_rejects_float() {
        assert!(parse_public_inputs_json("[1.5]").is_err());
    }

    #[test]
    fn test_resolve_vk_hash_auto() {
        // "auto" is not resolved by resolve_vk_hash — it's handled upstream.
        assert!(resolve_vk_hash("auto").is_none());
    }

    #[test]
    fn test_resolve_vk_hash_known() {
        assert_eq!(
            resolve_vk_hash(EFFECT_VM_VK_HASH_HEX),
            Some(EFFECT_VM_AIR_NAME)
        );
    }

    #[test]
    fn test_resolve_vk_hash_air_name_encoded() {
        let encoded = hex::encode(EFFECT_VM_AIR_NAME);
        assert_eq!(resolve_vk_hash(&encoded), Some(EFFECT_VM_AIR_NAME));
    }
}
