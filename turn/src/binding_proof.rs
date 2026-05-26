//! Effect-binding sidecar proofs.
//!
//! This module defines the on-wire shape for carrying per-effect
//! full-fidelity binding proofs alongside a `Turn`. Each binding proof
//! is a sidecar STARK produced by `dregg_circuit::effect_action_air`
//! (or the dedicated sibling AIRs `bridge_action_air` /
//! `bridge_lock_action_air`) that pins every typed parameter of one
//! runtime `Effect` at full fidelity:
//!   - 32-byte fields as 8 × 4-byte BabyBear limbs (~248-bit binding)
//!   - u64 amounts as 2 × 32-bit limbs (full 64-bit binding)
//!
//! # Why a sidecar?
//!
//! The Effect VM proof retains its 4-byte hash-truncation projection of
//! each effect for backwards compatibility of the existing trace shape.
//! The sidecar binding proof is what a verifier consults for
//! algebraic, full-fidelity parameter binding. Verifiers that have not
//! upgraded to consume binding proofs continue to apply turns with
//! executor-trusted enforcement; verifiers that do consume them get
//! strong-soundness enforcement.
//!
//! # Wire shape
//!
//! A `Turn` may optionally carry `effect_binding_proofs: Vec<EffectBindingProof>`.
//! Each entry references an effect by `(action_path, effect_index)` —
//! the index into the call_forest DFS-traversal of the named action's
//! effects — and carries the schema identifier, the serialized STARK
//! proof bytes, and the canonical public-input vector.
//!
//! The verifier walks the list, looks up each schema by `schema_id`,
//! re-derives the expected PI vector from the executor's view of the
//! effect's typed parameters, and verifies the STARK against that PI.
//! Any disagreement on any limb fails verification.

use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

/// A sidecar binding proof for one runtime `Effect`.
///
/// The proof binds the prover to the typed parameters of effect
/// `effect_index` (counted in DFS-traversal order over the turn's
/// call_forest) at full fidelity. The verifier re-derives the expected
/// public-input vector from the executor's view of the effect and
/// rejects any mismatch.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectBindingProof {
    /// Position of the effect this proof binds, in the canonical
    /// DFS-traversal order of the turn's call_forest. The verifier
    /// applies the same traversal to locate the effect's parameters.
    pub effect_index: u32,
    /// Schema identifier — matches the `kind_name` field of one of the
    /// `EffectActionSchema` constants in
    /// `dregg_circuit::effect_action_air`. Used to look up the schema
    /// for PI reconstruction and to verify cross-effect kind separation
    /// (a proof for kind A must not verify as kind B).
    pub schema_id: String,
    /// Serialized STARK proof bytes (postcard-encoded via
    /// `dregg_circuit::stark::proof_to_bytes`).
    pub proof_bytes: Vec<u8>,
    /// Canonical public-input vector this proof commits to. Encoded as
    /// raw u32 BabyBear values for stable wire format. The verifier
    /// converts these to `BabyBear` via `BabyBear::new` and checks them
    /// against its own re-derived PI from the effect's typed parameters.
    pub public_inputs: Vec<u32>,
}

impl EffectBindingProof {
    /// Convenience: convert the raw u32 PI vector to BabyBear elements
    /// for verification.
    pub fn public_inputs_babybear(&self) -> Vec<BabyBear> {
        self.public_inputs
            .iter()
            .map(|&v| BabyBear::new(v))
            .collect()
    }

    /// Stable byte representation for inclusion in `Turn::hash`. Length-
    /// prefixes every variable-length field so wire fuzzing cannot
    /// confuse boundaries.
    pub fn hash_into(&self, hasher: &mut blake3::Hasher) {
        hasher.update(&self.effect_index.to_le_bytes());
        hasher.update(&(self.schema_id.len() as u64).to_le_bytes());
        hasher.update(self.schema_id.as_bytes());
        hasher.update(&(self.proof_bytes.len() as u64).to_le_bytes());
        hasher.update(&self.proof_bytes);
        hasher.update(&(self.public_inputs.len() as u64).to_le_bytes());
        for v in &self.public_inputs {
            hasher.update(&v.to_le_bytes());
        }
    }
}

/// A cross-effect within-turn chain dependency.
///
/// Documents that the value of a named output field of the producer
/// effect must equal the value of a named input field of the consumer
/// effect. The canonical example: `Effect::NoteSpend` produces a
/// `nullifier`; if a later `Effect::BridgeMint` in the same turn
/// references that nullifier, the executor must enforce that the value
/// match. Without this, an executor that lies about the chain could
/// route the consumer effect to a different nullifier than the one
/// the producer actually produced.
///
/// The verifier walks this list and, for each dependency, reads the
/// producer effect's output field from the executor's view and the
/// consumer effect's input field from the same view, and rejects any
/// disagreement. The `value_commit` field is the executor's commitment
/// to the value being chained — encoded as 32 bytes so the verifier
/// can use the same 8-limb encoding as the binding proofs above.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectDependency {
    /// Index of the producing effect in DFS-traversal order.
    pub producer_index: u32,
    /// Index of the consuming effect in DFS-traversal order.
    /// Must be greater than `producer_index` (forward edges only —
    /// producers run before consumers in turn execution order).
    pub consumer_index: u32,
    /// Name of the field linking producer output and consumer input.
    /// Examples: "nullifier", "note_commitment", "escrow_id".
    pub field_name: String,
    /// The 32-byte value being chained. The verifier checks that the
    /// producer's output of `field_name` equals this value AND that
    /// the consumer's input of `field_name` equals this value. This
    /// gives a 3-way pin: producer ⟷ value_commit ⟷ consumer.
    pub value_commit: [u8; 32],
}

impl EffectDependency {
    /// Stable byte representation for inclusion in `Turn::hash`.
    pub fn hash_into(&self, hasher: &mut blake3::Hasher) {
        hasher.update(&self.producer_index.to_le_bytes());
        hasher.update(&self.consumer_index.to_le_bytes());
        hasher.update(&(self.field_name.len() as u64).to_le_bytes());
        hasher.update(self.field_name.as_bytes());
        hasher.update(&self.value_commit);
    }
}

/// A witness-blob → effect indexing entry.
///
/// Pins the witness blob that an effect E consumes. Without this, the
/// executor's `witness_blobs: Vec<WitnessBlob>` ordering is free — a
/// malicious executor could shuffle blobs so that an effect requiring
/// witness K reads the bytes that were meant for effect L. The AIR
/// enforces (per `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.2) that effect
/// `effect_index`'s required witness comes from
/// `witness_blobs[witness_index]`.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct EffectWitnessIndex {
    /// Index of the effect (DFS-traversal order over the turn's call_forest).
    pub effect_index: u32,
    /// Index into the action's `witness_blobs` vector. Note that
    /// `witness_blobs` is per-action; the verifier uses the
    /// `effect_index → action_path` resolution to scope this index.
    pub witness_index: u32,
}

impl EffectWitnessIndex {
    /// Stable byte representation for inclusion in `Turn::hash`.
    pub fn hash_into(&self, hasher: &mut blake3::Hasher) {
        hasher.update(&self.effect_index.to_le_bytes());
        hasher.update(&self.witness_index.to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn effect_binding_proof_roundtrip_serde() {
        let bp = EffectBindingProof {
            effect_index: 3,
            schema_id: "dregg-effect-note-spend-v1".to_string(),
            proof_bytes: vec![0x01, 0x02, 0x03],
            public_inputs: vec![10, 20, 30],
        };
        let bytes = postcard::to_allocvec(&bp).expect("serialize");
        let decoded: EffectBindingProof = postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(bp, decoded);
    }

    #[test]
    fn effect_binding_proof_public_inputs_babybear() {
        let bp = EffectBindingProof {
            effect_index: 0,
            schema_id: "x".to_string(),
            proof_bytes: vec![],
            public_inputs: vec![0xDEAD_BEEF, 0xCAFE_F00D],
        };
        let bb = bp.public_inputs_babybear();
        assert_eq!(bb.len(), 2);
        assert_eq!(bb[0], BabyBear::new(0xDEAD_BEEF));
        assert_eq!(bb[1], BabyBear::new(0xCAFE_F00D));
    }

    #[test]
    fn effect_binding_proof_hash_is_deterministic() {
        let bp = EffectBindingProof {
            effect_index: 2,
            schema_id: "kind".to_string(),
            proof_bytes: vec![1, 2, 3],
            public_inputs: vec![100],
        };
        let mut h1 = blake3::Hasher::new();
        bp.hash_into(&mut h1);
        let mut h2 = blake3::Hasher::new();
        bp.hash_into(&mut h2);
        assert_eq!(h1.finalize(), h2.finalize());
    }

    #[test]
    fn effect_binding_proof_hash_is_byte_sensitive() {
        // Changing any field changes the hash.
        let bp1 = EffectBindingProof {
            effect_index: 2,
            schema_id: "kind".to_string(),
            proof_bytes: vec![1, 2, 3],
            public_inputs: vec![100],
        };
        let mut bp2 = bp1.clone();
        bp2.effect_index = 3;
        let mut h1 = blake3::Hasher::new();
        bp1.hash_into(&mut h1);
        let mut h2 = blake3::Hasher::new();
        bp2.hash_into(&mut h2);
        assert_ne!(h1.finalize(), h2.finalize());

        let mut bp3 = bp1.clone();
        bp3.proof_bytes = vec![1, 2, 4];
        let mut h3 = blake3::Hasher::new();
        bp3.hash_into(&mut h3);
        assert_ne!(h1.finalize(), h3.finalize());

        let mut bp4 = bp1.clone();
        bp4.schema_id = "other-kind".to_string();
        let mut h4 = blake3::Hasher::new();
        bp4.hash_into(&mut h4);
        assert_ne!(h1.finalize(), h4.finalize());
    }

    #[test]
    fn effect_dependency_roundtrip_serde() {
        let dep = EffectDependency {
            producer_index: 1,
            consumer_index: 3,
            field_name: "nullifier".to_string(),
            value_commit: [0xAA; 32],
        };
        let bytes = postcard::to_allocvec(&dep).expect("serialize");
        let decoded: EffectDependency = postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(dep, decoded);
    }

    #[test]
    fn effect_witness_index_roundtrip_serde() {
        let ewi = EffectWitnessIndex {
            effect_index: 5,
            witness_index: 2,
        };
        let bytes = postcard::to_allocvec(&ewi).expect("serialize");
        let decoded: EffectWitnessIndex = postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(ewi, decoded);
    }
}
