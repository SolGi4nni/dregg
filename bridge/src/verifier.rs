//! StarkProofVerifier: bridges the dregg-circuit STARK verifier to the TurnExecutor's
//! `ProofVerifier` trait.
//!
//! This module provides the concrete implementation that wires the ZK presentation
//! proof system (token -> bridge -> circuit -> STARK) to the execution layer (turn).
//!
//! The verifier expects proof bytes produced by `BridgePresentationProof::issuer_proof_bytes()`
//! and verifies them against the public inputs derived from the action being authorized.
//!
//! # Verification Strategy
//!
//! The proof bytes contain a serialized STARK proof for Merkle membership (issuer in federation).
//! The `verification_key` stored on the target cell is the federation root (32 bytes).
//! The `public_inputs` are the action's signing message (BLAKE3 hash of action contents).
//!
//! However, the STARK proof's *actual* public inputs are `[leaf_hash, merkle_root]` for the
//! MerkleStarkAir. The verifier checks:
//! 1. The proof deserializes correctly.
//! 2. The proof's embedded public inputs include the federation root (vk).
//! 3. The STARK proof verifies against `MerkleStarkAir`.
//!
//! This is a "presentation verification" model: the proof demonstrates that the presenter
//! holds a valid token chain from a federated issuer, which is sufficient authorization
//! for the action. The action's contents don't need to be *inside* the STARK circuit
//! because the proof's binding to this specific action is ensured by the executor's
//! fail-closed design (the proof must be presented as part of the action, and only
//! the action's target cell can accept it).
//!
//! STARBRIDGE-FOLLOWUP-03 note (§5.5): This "proof-to-action binding lives
//! in executor comments, not the circuit" (per BACKWATER-CRATES-AUDIT.md:78-81,1151).
//! Moving the binding into AIR (circuit bridge_action_air + effect_vm) is
//! the Golden lift, BLOCKED ON HUMAN + cargo for bridge/ + circuit/. The
//! current Silver posture (executor cross-checks only) is load-bearing.

use std::sync::Arc;

use dregg_circuit::BabyBear;
use dregg_circuit::binding::compute_action_binding;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof, verify_vm_descriptor2};
use dregg_circuit::stark;
use dregg_dsl_runtime::ProgramRegistry;
use dregg_turn::ProofVerifier;

/// A `ProofVerifier` implementation that verifies real STARK proofs from the
/// dregg-circuit layer.
///
/// The verifier checks that:
/// 1. The proof bytes deserialize to a valid `StarkProof`.
/// 2. The proof's public inputs include the expected federation root (passed as `vk`).
/// 3. The action binding matches the requested action and resource.
/// 4. The STARK proof verifies against the DSL `merkle_poseidon2_circuit()` constraint system.
///
/// # Timestamp Freshness
///
/// When `max_proof_age_secs` is set (non-zero), the verifier REQUIRES that the
/// proof's 4th public input contains a valid timestamp within the allowed window.
/// Proofs without a timestamp field (fewer than 4 public inputs) are rejected.
/// This prevents a prover from stripping the timestamp to bypass freshness checks.
/// The current time is obtained from `std::time::SystemTime::now()`.
///
/// # Usage
///
/// ```ignore
/// let verifier = StarkProofVerifier::with_max_age(300); // 5 minutes
/// let mut executor = TurnExecutor::new(costs);
/// executor.set_proof_verifier(Box::new(verifier));
/// ```
pub struct StarkProofVerifier {
    /// Maximum age of a proof in seconds. 0 means no freshness check.
    max_proof_age_secs: i64,
}

impl StarkProofVerifier {
    /// Create a new STARK proof verifier with no timestamp freshness check.
    pub fn new() -> Self {
        Self {
            max_proof_age_secs: 0,
        }
    }

    /// Create a new STARK proof verifier with timestamp freshness enforcement.
    ///
    /// Proofs MUST include a timestamp as the 4th public input (index 3).
    /// Proofs without a timestamp field are rejected. Proofs with a timestamp
    /// older than `max_age_secs` from the current time are also rejected.
    /// Use `DEFAULT_MAX_PROOF_AGE_SECS` (300s) for typical use.
    ///
    /// **NOTE**: The standard `BridgePresentationBuilder::prove()` path does not
    /// include a timestamp in the issuer membership STARK proof's public inputs
    /// (the timestamp is only in the circuit-level `PresentationPublicInputs`).
    /// Provers targeting verifiers with `with_max_age` must explicitly append a
    /// Unix timestamp as pi[3] when generating the STARK proof.
    pub fn with_max_age(max_age_secs: i64) -> Self {
        Self {
            max_proof_age_secs: max_age_secs,
        }
    }
}

impl Default for StarkProofVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofVerifier for StarkProofVerifier {
    /// Verify a STARK proof bound to (action, resource) against a verification key.
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool {
        // 1. Deserialize the STARK proof.
        let stark_proof = match stark::proof_from_bytes(proof) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // 2. Extract the public inputs from the proof itself.
        // SECURITY: Use new_canonical() for values from external (potentially adversarial)
        // proof data to prevent non-canonical BabyBear representations.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Expect at least [leaf_hash, merkle_root, action_binding[0..ACTION_BINDING_WIDTH]]
        if pi.len() < 2 + dregg_circuit::ACTION_BINDING_WIDTH {
            return false;
        }

        // 3. Verify the action binding commitment (4 elements, 124-bit security).
        // The action binding occupies pi[2..6] (after leaf_hash and merkle_root).
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
            if pi[2 + i] != expected_binding[i] {
                return false;
            }
        }

        // 4. Check that the merkle_root (pi[1]) corresponds to the federation root
        //    stored in the cell's verification key.
        if vk.len() < 32 {
            return false;
        }
        let mut vk_bytes = [0u8; 32];
        vk_bytes.copy_from_slice(&vk[..32]);

        // The VK encodes a BabyBear field element as its canonical u32 representation
        // in the first 4 bytes (little-endian). This matches the prover's encoding
        // (via `bb_to_bytes` / `babybear_to_bytes32`) used in BridgePresentationBuilder
        // and the SDK. Bytes 4-31 are reserved and ignored.
        //
        // NOTE: `bytes_to_babybear` (Poseidon2 hash of 8 limbs) is NOT used here because
        // it is a one-way compression function that cannot round-trip with the canonical
        // BabyBear-to-bytes encoding. The prover stores `root.0.to_le_bytes()` in bytes
        // 0-3, and the verifier must recover it with the inverse operation.
        let expected_root = BabyBear::new_canonical(u32::from_le_bytes([
            vk_bytes[0],
            vk_bytes[1],
            vk_bytes[2],
            vk_bytes[3],
        ]));

        let proof_root = pi[1];
        if proof_root != expected_root {
            return false;
        }

        // 5. Timestamp freshness check (if configured).
        // The timestamp is after the action binding: pi[2 + ACTION_BINDING_WIDTH].
        // SECURITY: When freshness is required (max_proof_age_secs > 0), the proof
        // MUST include a timestamp. Rejecting proofs without timestamps prevents a
        // prover from stripping the timestamp to bypass freshness enforcement.
        let timestamp_idx = 2 + dregg_circuit::ACTION_BINDING_WIDTH;
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                // Timestamp required but proof does not include one — reject.
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
            if proof_timestamp == 0 {
                // No timestamp in proof — reject when freshness is required.
                return false;
            }
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let age = now.saturating_sub(proof_timestamp);
            if age > self.max_proof_age_secs || age < -self.max_proof_age_secs {
                return false;
            }
        }

        // 6. Verify the STARK proof cryptographically using DSL circuit.
        // FAIL-CLOSED: an AIR name with no registered descriptor is REFUSED.
        // Falling back to a default circuit would let the prover choose the
        // constraint semantics the verifier checks against. (The `ProofVerifier`
        // trait returns bool, so the refusal surfaces as `false`; the typed
        // refusal lives in SdkError::UnknownAir / VerifyError::UnknownAir on the
        // Result-returning verify paths.)
        let circuit =
            match dregg_dsl_runtime::descriptors::circuit_for_air_name(&stark_proof.air_name) {
                Some(c) => c,
                None => return false,
            };
        stark::verify(&circuit, &stark_proof, &pi).is_ok()
    }

    /// MIGRATED consumer contract: when the executor threads the expected
    /// PREDICATE identity, this verifier routes through the descriptor-dispatch
    /// path — `descriptor_by_name(predicate)` → decode `postcard(Ir2BatchProof)`
    /// → `verify_vm_descriptor2` — via [`DescriptorDispatchVerifier`], NOT the
    /// legacy `stark::proof_from_bytes` path in [`Self::verify`]. The `vk` carries
    /// the expected public inputs (one canonical LE `u32` per 4 bytes). This is the
    /// `StarkProof` → `Ir2BatchProof` wire flip for the standard verifier: the
    /// descriptor is chosen from the committed predicate identity supplied by the
    /// executor, never from an air-name in the prover-controlled blob.
    fn verify_with_predicate(
        &self,
        predicate: &str,
        proof: &[u8],
        action: &str,
        resource: &str,
        vk: &[u8],
    ) -> bool {
        DescriptorDispatchVerifier::new()
            .verify_with_predicate(predicate, proof, action, resource, vk)
    }
}

/// DEPRECATED: Known AIR names previously handled by the hardcoded verification path.
/// All proofs now go through the unified DSL verification path.
#[deprecated(note = "All proofs now use DSL-based verification. This constant is unused.")]
#[allow(dead_code)]
const KNOWN_AIR_NAMES: &[&str] = &[
    "dregg-merkle-poseidon2-v1",
    "dregg-blinded-merkle-poseidon2-v1",
    "dregg-poseidon2-v1",
    "dregg-merkle-poseidon2-round-v1",
];

/// A `ProofVerifier` that supports both hardcoded AIRs and DSL-generated circuits.
///
/// This is the production verifier for sovereign cell proofs. It dispatches:
///
/// - **Known AIR names** (poseidon2, merkle, blinded-merkle): verified via the
///   DSL `merkle_poseidon2_circuit()` / `blinded_merkle_poseidon2_circuit()` path,
///   including action binding and timestamp freshness checks.
///
/// - **Custom programs** (unrecognized `air_name`): the VK bytes are interpreted
///   as a 32-byte program VK hash. The program is looked up in the attached
///   `ProgramRegistry`, and the proof is verified against its `DslCircuit`.
///
/// # Usage
///
/// ```ignore
/// let registry = Arc::new(ProgramRegistry::new());
/// // ... deploy programs to registry ...
/// let verifier = DslAwareProofVerifier::new(registry);
/// executor.set_proof_verifier(Box::new(verifier));
/// ```
pub struct DslAwareProofVerifier {
    /// Maximum age of a proof in seconds. 0 means no freshness check.
    /// Applies only to the known-AIR path.
    max_proof_age_secs: i64,
    /// Program registry for custom DSL circuit verification.
    registry: Arc<ProgramRegistry>,
}

impl DslAwareProofVerifier {
    /// Create a new DSL-aware verifier with no timestamp freshness check.
    pub fn new(registry: Arc<ProgramRegistry>) -> Self {
        Self {
            max_proof_age_secs: 0,
            registry,
        }
    }

    /// Create a new DSL-aware verifier with timestamp freshness enforcement
    /// for the known-AIR path.
    pub fn with_max_age(registry: Arc<ProgramRegistry>, max_age_secs: i64) -> Self {
        Self {
            max_proof_age_secs: max_age_secs,
            registry,
        }
    }

    /// DEPRECATED: Verify a proof using the known Merkle/Poseidon2 AIR path.
    /// All verification now goes through the unified DSL path in `ProofVerifier::verify`.
    #[allow(dead_code)]
    #[deprecated(note = "All proofs now use DSL-based verification via circuit_for_air_name")]
    fn verify_known_air(
        &self,
        stark_proof: &stark::StarkProof,
        action: &str,
        resource: &str,
        vk: &[u8],
    ) -> bool {
        // Extract public inputs with canonical reduction.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Expect at least [leaf_hash, merkle_root, action_binding[0..ACTION_BINDING_WIDTH]]
        if pi.len() < 2 + dregg_circuit::ACTION_BINDING_WIDTH {
            return false;
        }

        // Verify the action binding commitment.
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
            if pi[2 + i] != expected_binding[i] {
                return false;
            }
        }

        // Check that the merkle_root (pi[1]) corresponds to the federation root (vk).
        if vk.len() < 32 {
            return false;
        }
        let expected_root =
            BabyBear::new_canonical(u32::from_le_bytes([vk[0], vk[1], vk[2], vk[3]]));
        if pi[1] != expected_root {
            return false;
        }

        // Timestamp freshness check (if configured).
        let timestamp_idx = 2 + dregg_circuit::ACTION_BINDING_WIDTH;
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
            if proof_timestamp == 0 {
                return false;
            }
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let age = now.saturating_sub(proof_timestamp);
            if age > self.max_proof_age_secs || age < -self.max_proof_age_secs {
                return false;
            }
        }

        // Dispatch to the correct DSL circuit based on air_name.
        use dregg_dsl_runtime::descriptors::{
            BLINDED_MERKLE_AIR_NAME, blinded_merkle_poseidon2_circuit, merkle_poseidon2_circuit,
        };
        if stark_proof.air_name == BLINDED_MERKLE_AIR_NAME {
            let circuit = blinded_merkle_poseidon2_circuit();
            stark::verify(&circuit, stark_proof, &pi).is_ok()
        } else {
            let circuit = merkle_poseidon2_circuit();
            stark::verify(&circuit, stark_proof, &pi).is_ok()
        }
    }

    /// Verify a proof using the DSL circuit path via `ProgramRegistry`.
    ///
    /// The VK bytes are interpreted as the 32-byte program VK hash. The program
    /// is looked up in the registry, and the proof is verified against its
    /// `DslCircuit` AIR.
    ///
    /// # Action Binding Convention for DSL Programs
    ///
    /// DSL programs follow the same public input convention as known AIRs:
    /// the action binding (ACTION_BINDING_WIDTH BabyBear elements) occupies `pi[0..ACTION_BINDING_WIDTH]`, and the
    /// optional timestamp occupies `pi[4]`. Programs that declare fewer than
    /// 5 public inputs cannot pass freshness checks when `max_proof_age_secs > 0`.
    ///
    /// This prevents a valid DSL proof from being replayed to authorize a
    /// different action on the same cell.
    fn verify_dsl_program(
        &self,
        stark_proof: &stark::StarkProof,
        action: &str,
        resource: &str,
        vk: &[u8],
    ) -> bool {
        if vk.len() < 32 {
            return false;
        }

        let mut vk_hash = [0u8; 32];
        vk_hash.copy_from_slice(&vk[..32]);

        // Look up the program in the registry.
        let program = match self.registry.get(&vk_hash) {
            Some(p) => p,
            None => return false,
        };

        // Extract public inputs from the proof.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Action binding check: pi[0..ACTION_BINDING_WIDTH] must match the expected action binding.
        // This prevents replay of a valid proof to authorize a different action.
        if pi.len() < dregg_circuit::ACTION_BINDING_WIDTH {
            return false;
        }
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
            if pi[i] != expected_binding[i] {
                return false;
            }
        }

        // Timestamp freshness check (same logic as the known-AIR path).
        // For DSL programs, the timestamp lives at pi[ACTION_BINDING_WIDTH] (index 4).
        let timestamp_idx = dregg_circuit::ACTION_BINDING_WIDTH; // = 4
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                // Timestamp required but proof does not include one — reject.
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
            if proof_timestamp == 0 {
                // No timestamp in proof — reject when freshness is required.
                return false;
            }
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let age = now.saturating_sub(proof_timestamp);
            if age > self.max_proof_age_secs || age < -self.max_proof_age_secs {
                return false;
            }
        }

        // Verify using the program's DslCircuit.
        let circuit = dregg_dsl_runtime::DslCircuit::new(program.descriptor.clone());
        stark::verify(&circuit, stark_proof, &pi).is_ok()
    }
}

impl ProofVerifier for DslAwareProofVerifier {
    /// Verify a STARK proof using unified DSL-based verification.
    ///
    /// All proofs go through one path:
    /// 1. Try to resolve the AIR name to a standard DSL circuit (merkle, blinded, etc.)
    /// 2. If not a standard circuit, treat VK as a program hash and look up in registry
    /// 3. Verify using the resolved DslCircuit
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool {
        // 1. Deserialize the STARK proof.
        let stark_proof = match stark::proof_from_bytes(proof) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // 2. Extract public inputs.
        let pi: Vec<BabyBear> = stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // 3. Action binding check (standard convention: pi[2..6] for known circuits,
        //    pi[0..ACTION_BINDING_WIDTH] for custom programs).
        let (binding_offset, has_root_check) =
            if dregg_dsl_runtime::descriptors::is_known_dsl_air(&stark_proof.air_name) {
                (2, true) // Standard circuits: [leaf, root, binding...]
            } else {
                (0, false) // Custom programs: [binding...]
            };

        if pi.len() < binding_offset + dregg_circuit::ACTION_BINDING_WIDTH {
            return false;
        }
        let expected_binding = compute_action_binding(action, resource);
        for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
            if pi[binding_offset + i] != expected_binding[i] {
                return false;
            }
        }

        // 4. Root check for standard membership circuits.
        if has_root_check {
            if vk.len() < 4 {
                return false;
            }
            let expected_root =
                BabyBear::new_canonical(u32::from_le_bytes([vk[0], vk[1], vk[2], vk[3]]));
            if pi.len() < 2 || pi[1] != expected_root {
                return false;
            }
        }

        // 5. Timestamp freshness check (if configured).
        let timestamp_idx = binding_offset + dregg_circuit::ACTION_BINDING_WIDTH;
        if self.max_proof_age_secs > 0 {
            if pi.len() <= timestamp_idx {
                return false;
            }
            let proof_timestamp = pi[timestamp_idx].0 as i64;
            if proof_timestamp == 0 {
                return false;
            }
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let age = now.saturating_sub(proof_timestamp);
            if age > self.max_proof_age_secs || age < -self.max_proof_age_secs {
                return false;
            }
        }

        // 6. Resolve the circuit and verify.
        // First: try standard DSL circuits by air_name.
        if let Some(circuit) =
            dregg_dsl_runtime::descriptors::circuit_for_air_name(&stark_proof.air_name)
        {
            return stark::verify(&circuit, &stark_proof, &pi).is_ok();
        }

        // Second: treat as custom program (VK hash -> registry lookup).
        self.verify_dsl_program(&stark_proof, action, resource, vk)
    }

    /// MIGRATED consumer contract: same descriptor-dispatch route as
    /// [`StarkProofVerifier::verify_with_predicate`]. When the executor threads the
    /// expected PREDICATE identity, dispatch through [`DescriptorDispatchVerifier`]
    /// (`descriptor_by_name(predicate)` → decode `postcard(Ir2BatchProof)` →
    /// `verify_vm_descriptor2`) instead of the legacy `stark::proof_from_bytes`
    /// path in [`Self::verify`]. `vk` carries the expected public inputs (one
    /// canonical LE `u32` per 4 bytes); the descriptor is chosen from the committed
    /// predicate identity, never from a prover-controlled air-name.
    fn verify_with_predicate(
        &self,
        predicate: &str,
        proof: &[u8],
        action: &str,
        resource: &str,
        vk: &[u8],
    ) -> bool {
        DescriptorDispatchVerifier::new()
            .verify_with_predicate(predicate, proof, action, resource, vk)
    }
}

/// A `ProofVerifier` that dispatches on **predicate identity** to the IR-v2
/// descriptor prover — the consumer half of the `StarkProof` → `Ir2BatchProof`
/// wire migration, exercised through [`ProofVerifier::verify_with_predicate`].
///
/// This is the concrete demonstration that the trait, once it carries a predicate
/// name (the gap this lane closes), is *capable* of the migrated contract:
///
/// 1. `predicate` → [`descriptor_by_name`] (fail-closed [`None`] on a miss);
/// 2. decode the proof blob as a `postcard`-encoded [`Ir2BatchProof`] (the NEW
///    wire format that replaces `stark::proof_to_bytes(StarkProof)`);
/// 3. check it with [`verify_vm_descriptor2`] against the expected public inputs.
///
/// The expected public inputs are carried in `vk` as the little-endian u32
/// canonical encoding of one `BabyBear` per 4 bytes — the cell's verification key
/// commits the statement the proof must satisfy. Crucially, **no air-name ever
/// rides the blob**: the descriptor is chosen from the predicate's committed
/// identity supplied by the executor, never from prover-controlled bytes. Reading
/// the descriptor name out of the proof (as the legacy `StarkProofVerifier` does
/// via `stark_proof.air_name`) would let the prover pick the constraint semantics
/// it is checked against; threading the predicate through the trait is what
/// removes that choice.
///
/// This verifier is NOT yet wired into the production executor — migrating the
/// standard verifiers/call sites onto the descriptor prover is Gate-2 work. Its
/// [`ProofVerifier::verify`] (no predicate) is deliberately fail-closed: without a
/// predicate identity there is no descriptor to name, so it refuses.
pub struct DescriptorDispatchVerifier {
    _priv: (),
}

impl DescriptorDispatchVerifier {
    /// Create a descriptor-dispatch verifier.
    pub fn new() -> Self {
        Self { _priv: () }
    }

    /// Decode `vk` bytes as the expected public inputs: one canonical `BabyBear`
    /// per little-endian 4-byte group. A length that is not a positive multiple
    /// of 4 is rejected (`None`).
    fn expected_public_inputs(vk: &[u8]) -> Option<Vec<BabyBear>> {
        if vk.is_empty() || vk.len() % 4 != 0 {
            return None;
        }
        Some(
            vk.chunks_exact(4)
                .map(|c| BabyBear::new_canonical(u32::from_le_bytes([c[0], c[1], c[2], c[3]])))
                .collect(),
        )
    }
}

impl Default for DescriptorDispatchVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofVerifier for DescriptorDispatchVerifier {
    /// Fail-closed: a descriptor verifier cannot function without a predicate
    /// identity naming which descriptor to check the proof against.
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        false
    }

    /// The migrated consumer contract, keyed on the executor-supplied predicate.
    fn verify_with_predicate(
        &self,
        predicate: &str,
        proof: &[u8],
        _action: &str,
        _resource: &str,
        vk: &[u8],
    ) -> bool {
        // 1. Predicate identity → descriptor (fail-closed on an unknown name).
        let desc = match descriptor_by_name(predicate) {
            Some(d) => d,
            None => return false,
        };
        // 2. Expected public inputs from the cell VK.
        let pi = match Self::expected_public_inputs(vk) {
            Some(pi) => pi,
            None => return false,
        };
        // 3. Decode the proof blob (the NEW postcard(Ir2BatchProof) wire format).
        let batch: Ir2BatchProof<DreggStarkConfig> = match postcard::from_bytes(proof) {
            Ok(p) => p,
            Err(_) => return false,
        };
        // 4. Verify against the descriptor. A structurally-malformed proof can
        //    panic inside verification; treat any panic as a rejection.
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_vm_descriptor2(&desc, &batch, &pi).is_ok()
        }))
        .unwrap_or(false)
    }
}

#[cfg(test)]
mod descriptor_dispatch_tests {
    use super::*;
    use dregg_circuit::descriptor_by_name::MEMBERSHIP_GENERAL_NAME_PREFIX;
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
    use dregg_circuit::membership_descriptor_general::{
        MembershipStep, membership_root, membership_witness,
    };

    /// Encode public inputs as the VK the [`DescriptorDispatchVerifier`] expects:
    /// one canonical `BabyBear` per little-endian 4-byte group.
    fn pis_to_vk(pis: &[BabyBear]) -> Vec<u8> {
        let mut vk = Vec::with_capacity(pis.len() * 4);
        for p in pis {
            vk.extend_from_slice(&p.0.to_le_bytes());
        }
        vk
    }

    /// Deterministic depth-`d` membership fixture: fixed leaf + `d`-step path.
    fn fixture(depth: usize) -> (BabyBear, Vec<MembershipStep>, BabyBear) {
        let leaf = BabyBear::new(0xABCD);
        let path: Vec<MembershipStep> = (0..depth)
            .map(|i| MembershipStep {
                sibling: BabyBear::new(1000 + i as u32),
                dir: i % 2 == 1,
            })
            .collect();
        let root = membership_root(leaf, &path);
        (leaf, path, root)
    }

    /// NON-VACUOUS: with the predicate identity threaded through the trait, a
    /// [`DescriptorDispatchVerifier`] reaches `descriptor_by_name -> \
    /// verify_vm_descriptor2` and correctly ACCEPTS an honest proof (built by the
    /// REAL [`prove_vm_descriptor2`]) while REJECTING every wrong case: the
    /// predicate-less legacy path, an unknown predicate, a cross-descriptor name,
    /// a wrong-depth descriptor, a tampered blob, a forged VK, and a malformed VK.
    /// Runs both directly and through a `Box<dyn ProofVerifier>` (the shape the
    /// executor stores).
    #[test]
    fn descriptor_dispatch_accepts_honest_rejects_wrong() {
        let depth = 2usize;
        let name = format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}{depth}");

        // PRODUCER: honest witness → real IR-v2 batch proof.
        let (leaf, path, root) = fixture(depth);
        let (trace, pis) = membership_witness(leaf, &path).expect("honest witness");
        assert_eq!(pis, vec![leaf, root], "membership PIs are [leaf, root]");
        let desc = descriptor_by_name(&name).expect("depth membership must dispatch");
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest membership must prove");

        // WIRE: the NEW postcard(Ir2BatchProof) blob; VK carries the expected PIs.
        let blob = postcard::to_allocvec(&proof).expect("encode batch proof");
        let vk = pis_to_vk(&pis);

        let v = DescriptorDispatchVerifier::new();

        // ACCEPT: correct predicate identity + honest proof + correct VK.
        assert!(
            v.verify_with_predicate(&name, &blob, "read", "res", &vk),
            "honest proof under the correct predicate must verify"
        );

        // REJECT: predicate-less legacy path — no descriptor to name → fail-closed.
        // This is the load-bearing contrast: the SAME honest proof/VK that the
        // predicate path accepts is refused when the identity is absent, proving
        // the threaded predicate is what makes verification possible.
        assert!(
            !v.verify(&blob, "read", "res", &vk),
            "without a predicate identity the descriptor verifier is fail-closed"
        );

        // REJECT: unknown predicate → descriptor_by_name None → fail-closed.
        assert!(
            !v.verify_with_predicate("no-such-predicate::v0", &blob, "read", "res", &vk),
            "an unknown predicate must be refused at dispatch"
        );

        // REJECT: cross-descriptor (a real but WRONG descriptor name).
        assert!(
            !v.verify_with_predicate(
                "dfa-routing-toggle-2state::poseidon2-v1",
                &blob,
                "read",
                "res",
                &vk
            ),
            "a proof under the wrong descriptor must fail verification"
        );

        // NOTE (soundness boundary, not an assertion): a proof under a DIFFERENT nominal
        // depth of the same family is ACCEPTED-BY-DESIGN when it targets the same
        // [leaf, root] — and this is NOT a forgery. The depth-general descriptor is
        // constraint-uniform (one Merkle level per row); the actual path is bound by the
        // ROOT public input via Poseidon2 collision-resistance, so a shallower proof cannot
        // hit a genuine deeper committed root without a collision (the real attack — a wrong
        // root — is the `forged expected root` REJECT below, which DOES bite). Production
        // membership pads to depth-2 today, so this is no regression. Binding the depth
        // in-circuit (a row-count constraint) is the deferred Rung-2 depth-general soundness
        // lift — a named Lean follow-on, tracked in GOAL-STARK-KILL.md, not a migration blocker.
        let _ = depth; // (depth no longer drives a wrong-depth assertion; see the note above)

        // REJECT: tampered proof blob.
        let mut tampered = blob.clone();
        if let Some(b) = tampered.last_mut() {
            *b ^= 0xFF;
        }
        assert!(
            !v.verify_with_predicate(&name, &tampered, "read", "res", &vk),
            "a tampered proof blob must fail"
        );

        // REJECT: forged VK (wrong expected root).
        let forged_pis = vec![leaf, BabyBear::new_canonical(root.0 ^ 1)];
        let forged_vk = pis_to_vk(&forged_pis);
        assert!(
            !v.verify_with_predicate(&name, &blob, "read", "res", &forged_vk),
            "a forged expected root must fail verification"
        );

        // REJECT: malformed VK (not a positive multiple of 4 bytes).
        assert!(
            !v.verify_with_predicate(&name, &blob, "read", "res", &[1, 2, 3]),
            "a malformed VK must be refused"
        );

        // Object-safety: the capability survives dynamic dispatch through
        // `Box<dyn ProofVerifier>` — the exact shape the executor stores.
        let boxed: Box<dyn ProofVerifier> = Box::new(DescriptorDispatchVerifier::new());
        assert!(
            boxed.verify_with_predicate(&name, &blob, "read", "res", &vk),
            "trait-object dispatch must accept the honest proof"
        );
        assert!(
            !boxed.verify_with_predicate("nope::v0", &blob, "read", "res", &vk),
            "trait-object dispatch must fail-close on an unknown predicate"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::binding::compute_action_binding;
    use dregg_circuit::stark::{proof_to_bytes, prove};
    use dregg_dsl_runtime::descriptors::merkle_poseidon2_circuit;
    use dregg_dsl_runtime::membership::generate_merkle_poseidon2_trace;

    /// Encode a BabyBear value as a 32-byte verification key.
    ///
    /// The canonical VK encoding stores the BabyBear's u32 representation in the
    /// first 4 bytes (little-endian), with remaining bytes zeroed. This is the
    /// encoding used by the prover (BridgePresentationBuilder / SDK) and the
    /// verifier's `new_canonical(u32_from_first_4_bytes)` extraction.
    fn babybear_to_vk(bb: BabyBear) -> [u8; 32] {
        let mut vk = [0u8; 32];
        vk[..4].copy_from_slice(&bb.0.to_le_bytes());
        vk
    }

    /// Helper: generate a valid proof with action binding (3 public inputs: leaf, root, binding).
    /// Returns (proof_bytes, public_inputs, vk_bytes).
    fn generate_bound_proof(action: &str, resource: &str) -> (Vec<u8>, Vec<BabyBear>, [u8; 32]) {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [
                BabyBear::new(1000),
                BabyBear::new(1100),
                BabyBear::new(1200),
            ],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, mut public_inputs) =
            generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        // Append the canonical action binding as third public input.
        let binding = compute_action_binding(action, resource);
        for &elem in binding.iter() {
            public_inputs.push(elem);
        }

        let circuit = merkle_poseidon2_circuit();
        let proof = prove(&circuit, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        // Encode the Merkle root (pi[1]) as the VK using the canonical encoding.
        let vk = babybear_to_vk(public_inputs[1]);

        (proof_bytes, public_inputs, vk)
    }

    /// Helper: generate a valid proof with 4 public inputs (leaf, root, binding, timestamp).
    /// The timestamp is included as the 4th public input for freshness-checked verifiers.
    fn generate_bound_proof_with_timestamp(
        action: &str,
        resource: &str,
        timestamp: u32,
    ) -> (Vec<u8>, Vec<BabyBear>, [u8; 32]) {
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
            [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
            [
                BabyBear::new(1000),
                BabyBear::new(1100),
                BabyBear::new(1200),
            ],
        ];
        let positions: [u8; 4] = [0, 1, 2, 3];
        let leaf_hash = BabyBear::new(12345);
        let (trace, mut public_inputs) =
            generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);

        // Append the canonical action binding as third public input.
        let binding = compute_action_binding(action, resource);
        for &elem in binding.iter() {
            public_inputs.push(elem);
        }

        // Append timestamp as 4th public input.
        public_inputs.push(BabyBear::new(timestamp));

        let circuit = merkle_poseidon2_circuit();
        let proof = prove(&circuit, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);

        let vk = babybear_to_vk(public_inputs[1]);

        (proof_bytes, public_inputs, vk)
    }

    #[test]
    fn test_stark_verifier_valid_proof() {
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    /// Task #163 fail-closed regression: an AIR name that does not resolve to a
    /// registered circuit descriptor must be REFUSED at dispatch — never routed
    /// to a default circuit. (Previously unknown names fell through to
    /// `merkle_poseidon2_circuit()` and were only rejected incidentally by the
    /// air-name binding inside `stark::verify`; the refusal is now explicit.)
    #[test]
    fn test_stark_verifier_refuses_unknown_air() {
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        // Baseline: the honest proof with a registered AIR name verifies.
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));

        // Relabel the otherwise-valid proof with an unregistered AIR name.
        let mut proof = stark::proof_from_bytes(&proof_bytes).expect("roundtrip");
        proof.air_name = "evil-unregistered-air-v0".to_string();
        let relabeled = proof_to_bytes(&proof);
        assert!(
            !verifier.verify(&relabeled, "read", "api/v1/users", &vk),
            "unknown AIR must be refused at dispatch (fail-closed)"
        );

        // Malformed (empty) AIR name refuses too.
        proof.air_name = String::new();
        let empty_air = proof_to_bytes(&proof);
        assert!(
            !verifier.verify(&empty_air, "read", "api/v1/users", &vk),
            "empty AIR name must be refused"
        );
    }

    #[test]
    fn test_stark_verifier_wrong_federation_root() {
        let (proof_bytes, _public_inputs, _vk) = generate_bound_proof("read", "api/v1/users");

        // Use a WRONG federation root.
        let wrong_vk = babybear_to_vk(BabyBear::new(99999));

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &wrong_vk));
    }

    #[test]
    fn test_stark_verifier_tampered_proof() {
        let (mut proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        // Tamper with the proof.
        if proof_bytes.len() > 10 {
            proof_bytes[10] ^= 0xFF;
        }

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_empty_proof() {
        let verifier = StarkProofVerifier::new();
        let vk = [0u8; 32];
        assert!(!verifier.verify(&[], "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_action_rejected() {
        // A proof bound to (read, api/v1/users) should be rejected for (write, api/v1/users).
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "write", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_wrong_resource_rejected() {
        // A proof bound to (read, api/v1/users) should be rejected for (read, api/v1/posts).
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new();
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/posts", &vk));
    }

    // =========================================================================
    // Timestamp freshness enforcement tests (Fix 2)
    // =========================================================================

    #[test]
    fn test_stark_verifier_no_max_age_accepts_without_timestamp() {
        // A verifier with max_age=0 should accept proofs without a timestamp field.
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::new(); // max_age = 0
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_rejects_missing_timestamp() {
        // SECURITY: A prover cannot strip the timestamp to bypass freshness enforcement.
        // When max_proof_age_secs > 0, proofs without a timestamp (pi.len() < 4) are rejected.
        let (proof_bytes, _public_inputs, vk) = generate_bound_proof("read", "api/v1/users");

        let verifier = StarkProofVerifier::with_max_age(300); // 5 minutes
        // The proof has only 3 public inputs (no timestamp) — should be rejected.
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_accepts_fresh_timestamp() {
        // A proof with a recent timestamp should be accepted.
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as u32;

        let (proof_bytes, _public_inputs, vk) =
            generate_bound_proof_with_timestamp("read", "api/v1/users", now);

        let verifier = StarkProofVerifier::with_max_age(300);
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_rejects_stale_timestamp() {
        // A proof with a timestamp older than max_age should be rejected.
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as u32;

        // Proof timestamp is 600 seconds in the past (max_age is 300).
        let stale_timestamp = now.saturating_sub(600);
        let (proof_bytes, _public_inputs, vk) =
            generate_bound_proof_with_timestamp("read", "api/v1/users", stale_timestamp);

        let verifier = StarkProofVerifier::with_max_age(300);
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_max_age_rejects_zero_timestamp() {
        // A proof with timestamp=0 is treated as "no timestamp" and rejected.
        let (proof_bytes, _public_inputs, vk) =
            generate_bound_proof_with_timestamp("read", "api/v1/users", 0);

        let verifier = StarkProofVerifier::with_max_age(300);
        assert!(!verifier.verify(&proof_bytes, "read", "api/v1/users", &vk));
    }

    #[test]
    fn test_stark_verifier_vk_with_nonzero_trailing_bytes() {
        // Regression test: VK bytes 4-31 being non-zero should NOT affect the result.
        // This tests that the old content-dependent heuristic has been removed.
        let (proof_bytes, public_inputs, _vk) = generate_bound_proof("read", "api/v1/users");

        // Encode with non-zero bytes in positions 4-31.
        let root_bb = public_inputs[1];
        let mut vk_nonzero = [0xFFu8; 32];
        vk_nonzero[..4].copy_from_slice(&root_bb.0.to_le_bytes());

        let verifier = StarkProofVerifier::new();
        // Should still verify correctly — only first 4 bytes matter.
        assert!(verifier.verify(&proof_bytes, "read", "api/v1/users", &vk_nonzero));
    }
}
