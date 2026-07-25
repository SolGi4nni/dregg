//! Multi-step derivation chaining — the WITNESS side only (law #1: the circuit is Lean's).
//!
//! This module holds [`MultiStepWitness`] and its accumulator-chain producer
//! (`compute_accumulated_hashes`) — the authoritative off-circuit chain semantics. It authors
//! NO constraints: the multi-step chain circuit is emitted from
//! `metatheory/Dregg2/Circuit/Emit/MultiStepChainEmit.lean` (`multiStepChainDesc`, byte-pinned by
//! a Lean `#guard`), decoded by `descriptor_ir2::parse_vm_descriptor2` and proved through
//! `prove_vm_descriptor2` in `circuit-prove/tests/multi_step_emit_gate.rs`. Trace generation for
//! that witness lives in [`crate::dsl::derivation`] (`generate_multi_step_trace_dsl`).

use crate::derivation_air::{
    CircuitRule, DERIVATION_AIR_WIDTH, DerivationWitness, compute_policy_root,
};
use crate::field::BabyBear;
use crate::poseidon2::hash_2_to_1;

/// Multi-step AIR width.
pub const MULTI_STEP_AIR_WIDTH: usize = DERIVATION_AIR_WIDTH + 5;

/// Maximum derivation steps per proof (single-proof AIR constraint).
pub const MAX_STEPS: usize = 32;

/// Maximum delegation chain depth across all composed proofs.
///
/// Bounds the total proving time for a delegation chain: at an assumed ~500ms per
/// step (an order-of-magnitude estimate, not benchmarked) this caps it near ~50
/// seconds. Chains deeper than this are rejected at proof generation time
/// to prevent DoS via unbounded recursive proving.
///
/// This limit applies to the total chain from root issuer to final delegate. A single
/// proof covers up to MAX_STEPS steps; chains longer than MAX_STEPS use chunked
/// derivation (multiple proofs composed). This cap limits the TOTAL depth.
pub const MAX_DELEGATION_DEPTH: usize = 100;

/// The "allow" predicate marker value.
pub const ALLOW_PREDICATE: u32 = 0xA110;

/// Multi-step column indices (appended after derivation columns).
pub mod col {
    use super::DERIVATION_AIR_WIDTH;

    pub const STEP_INDEX: usize = DERIVATION_AIR_WIDTH;
    pub const ACCUMULATED_HASH: usize = DERIVATION_AIR_WIDTH + 1;
    pub const PREV_ACCUMULATED: usize = DERIVATION_AIR_WIDTH + 2;
    pub const IS_FINAL_STEP: usize = DERIVATION_AIR_WIDTH + 3;
    pub const IS_ACTIVE: usize = DERIVATION_AIR_WIDTH + 4;
}

/// Public input layout.
pub mod pi {
    pub const INITIAL_STATE_ROOT: usize = 0;
    pub const REQUEST_HASH: usize = 1;
    pub const CONCLUSION: usize = 2;
    pub const NUM_STEPS: usize = 3;
    pub const FINAL_ACCUMULATED_HASH: usize = 4;
    pub const POLICY_ROOT: usize = 5;
}

/// One body Merkle proof: `(leaf, sibling path, position bits)`.
type BodyMerkleProof = (BabyBear, Vec<[BabyBear; 3]>, Vec<u8>);

/// Witness for a multi-step derivation.
#[derive(Clone, Debug)]
pub struct MultiStepWitness {
    pub initial_state_root: BabyBear,
    pub request_hash: BabyBear,
    pub steps: Vec<DerivationWitness>,
    pub allow_predicate: BabyBear,
    pub policy_root: BabyBear,
    pub body_merkle_proofs: Option<Vec<BodyMerkleProof>>,
}

impl MultiStepWitness {
    pub fn conclusion(&self) -> BabyBear {
        if let Some(last) = self.steps.last() {
            if last.derived_predicate == self.allow_predicate {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        } else {
            BabyBear::ZERO
        }
    }

    pub fn compute_accumulated_hashes(&self) -> Vec<BabyBear> {
        let mut acc = Vec::with_capacity(self.steps.len());
        let mut prev = self.initial_state_root;
        for step in &self.steps {
            let derived_hash = step.derived_hash();
            let next = hash_2_to_1(prev, derived_hash);
            acc.push(next);
            prev = next;
        }
        acc
    }

    pub fn final_accumulated_hash(&self) -> BabyBear {
        self.compute_accumulated_hashes()
            .last()
            .copied()
            .unwrap_or(self.initial_state_root)
    }
}

/// Build a multi-step witness from components.
pub fn build_multi_step_witness(
    initial_state_root: BabyBear,
    request_hash: BabyBear,
    steps: Vec<DerivationWitness>,
) -> MultiStepWitness {
    let rules: Vec<&CircuitRule> = steps.iter().map(|s| &s.rule).collect();
    let policy_root = compute_policy_root(&rules);

    MultiStepWitness {
        initial_state_root,
        request_hash,
        steps,
        allow_predicate: BabyBear::new(ALLOW_PREDICATE),
        policy_root,
        body_merkle_proofs: None,
    }
}

// ── DELETED: the hand-authored Rust accumulator-chain constraints (law #1) ──────────────
//
// `multi_step_chaining_constraints()` used to author the chain algebra IN RUST as two
// `ConstraintExpr` literals (`ChainedHash2to1` + `Transition`) — dialect 3 of architectural
// law #1's three constraint dialects. It had ZERO callers: nothing ever assembled it into a
// descriptor, and its own doc conceded the descriptor assembly was "the remainder of the
// prerequisite". It was a hand-written stub of a circuit Lean already emits.
//
// THE ROUTE THAT REPLACES IT (authored in Lean, proved, and exercised):
//   * `metatheory/Dregg2/Circuit/Emit/MultiStepChainEmit.lean` — `multiStepChainDesc`, whose
//     `emitVmJson2` wire string is byte-pinned by a Lean `#guard`. It authors the SAME chain:
//       MS1  accᵢ = hash_2_to_1(prevᵢ, derived_hashᵢ)   — an arity-2 `Poseidon2Chip` absorb
//       MS2  prevᵢ₊₁ = accᵢ                              — a transition `window_gate`
//       MS3  first-row `initial_state_root` / last-row `final_accumulated_hash` `pi_binding`s
//     — i.e. it ALSO closes the boundary pins the deleted Rust stub left unauthored.
//   * `metatheory/Dregg2/Circuit/Emit/MultiStepChainRefine.lean` — the refinement.
//   * `circuit-prove/tests/multi_step_emit_gate.rs` — Rust DECODES the Lean-pinned string via
//     `descriptor_ir2::parse_vm_descriptor2`, proves an honest 4-step chain through
//     `prove_vm_descriptor2`, and RED-tests four mutation canaries (broken MS1 digest, broken
//     MS2 link, forged MS3a/MS3b PIs).
//
// This module keeps only the WITNESS side ([`MultiStepWitness`] +
// `compute_accumulated_hashes`), which that gate names as the authoritative producer the
// emitted descriptor is proved against. Trace generation is
// `dsl::derivation::generate_multi_step_trace_dsl` (the sole entry point; the passthrough
// `generate_multi_step_trace` wrapper and the dead `MultiStepDerivationAir` — an `impl
// constraint_prover::Air` over the mock interface purged 2026-07-16, whose `constraints()`
// already returned `vec![]` and which no code outside doc-comments named — went with it).
