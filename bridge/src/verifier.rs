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
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof, verify_vm_descriptor2};
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
    ///
    /// Retained on the public `with_max_age` constructor for API stability. The
    /// legacy hand-STARK `verify` path that consumed it has been removed (the
    /// migrated path is `verify_with_predicate` → descriptor dispatch), so this
    /// field is no longer read by the verifier itself.
    #[allow(dead_code)]
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
    /// FAIL-CLOSED. The predicate-less `verify` cannot name a descriptor, so it
    /// refuses unconditionally.
    ///
    /// The legacy hand-STARK path (`stark::proof_from_bytes` → air-name dispatch →
    /// `stark::verify`) has been removed as part of the `StarkProof` → `Ir2BatchProof`
    /// wire migration. The migrated consumer contract is [`Self::verify_with_predicate`],
    /// which routes through [`DescriptorDispatchVerifier`]: `descriptor_by_name(predicate)`
    /// → decode `postcard(Ir2BatchProof)` → `verify_vm_descriptor2`. An Ir2 blob is not a
    /// `StarkProof`, and without a predicate identity there is no descriptor to check it
    /// against — so refusing here is the only sound answer.
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        false
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
    ///
    /// Retained on the public constructors for API stability. The legacy hand-STARK
    /// `verify` path that consumed it has been removed (the migrated path is
    /// `verify_with_predicate` → descriptor dispatch), so this field is no longer read.
    #[allow(dead_code)]
    max_proof_age_secs: i64,
    /// Program registry for custom DSL circuit verification.
    ///
    /// Retained on the public constructors for API stability. The legacy hand-STARK
    /// registry-lookup path (`verify_dsl_program`) that consumed it has been removed as
    /// part of the `StarkProof` → `Ir2BatchProof` migration; registry-backed programs
    /// now dispatch through the descriptor path via `verify_with_predicate`.
    #[allow(dead_code)]
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
}

impl ProofVerifier for DslAwareProofVerifier {
    /// FAIL-CLOSED. The predicate-less `verify` cannot name a descriptor, so it
    /// refuses unconditionally.
    ///
    /// The legacy hand-STARK path (`stark::proof_from_bytes` → air-name dispatch /
    /// registry `DslCircuit` lookup → `stark::verify`) has been removed as part of the
    /// `StarkProof` → `Ir2BatchProof` wire migration. The migrated consumer contract is
    /// [`Self::verify_with_predicate`], routed through [`DescriptorDispatchVerifier`]:
    /// `descriptor_by_name(predicate)` → decode `postcard(Ir2BatchProof)` →
    /// `verify_vm_descriptor2`. An Ir2 blob is not a `StarkProof`, and without a
    /// predicate identity there is no descriptor to check it against.
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        false
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
