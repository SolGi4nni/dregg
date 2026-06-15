//! `dregg-circuit`: Zero-knowledge proof circuits for dregg authorization token chains.
//!
//! # ⚠️ dregg1 hand-written AIRs vs the verified dregg2 descriptor path
//!
//! Most AIRs in this crate are **hand-written, UNVERIFIED dregg1 circuits**.
//! They are NOT the source of truth. The verified circuit semantics live in
//! Lean under `metatheory/Dregg2/Circuit/` — 52 per-effect descriptor
//! instances (`Inst/*.lean`), each with a full-state soundness keystone over
//! ALL kernel-state fields, grounded on the single named `Poseidon2SpongeCR`
//! hypothesis (kernel-clean: `lake build` green, `#assert_namespace_axioms`
//! whitelisting only `{propext, Classical.choice, Quot.sound}`).
//!
//! The Lean is verified at the **digest / state-transition layer**; it
//! abstracts Poseidon2 / Merkle / selector-dispatch as a hypothesis. The
//! hand-written AIRs here (`effect_vm/`, `note_spending_air`, `poseidon2_air`,
//! `effect_action_air`) are the layer that actually computes those hashes /
//! Merkle paths in-circuit — a DIFFERENT abstraction layer, not a competing
//! implementation. They retire one FRONTIER at a time as the Lean-emitted
//! descriptor interpreter (`lean_descriptor_air`) gains hash / limb / dispatch
//! gates. Do NOT duplicate or hand-extend a circuit without checking whether the
//! verified Lean descriptor already covers the statement; see
//! `metatheory/docs/rebuild/_RUST-CIRCUIT-CONSOLIDATION.md` and
//! `_DREGG1-DREGG2-UNIFICATION-LEDGER.md`. Dead/duplicate AIRs get deleted, not
//! kept (already gone: `effect_interp`, `garbled_air_p3`).
//!
//! # Trust Model
//!
//! This crate operates at the **TRUSTLESS** trust level.
//!
//! - **Soundness**: All proofs are independently verifiable by any party with access to
//!   the public inputs and verification key. A valid proof guarantees that the prover
//!   knows a witness satisfying the circuit constraints, with negligible soundness error
//!   (2^{-128} for STARK, conjectured for Plonky3).
//! - **Assumptions**: Cryptographic hardness of the hash function (BLAKE3/Poseidon2),
//!   correct circuit constraint encoding, and honest verifier randomness (Fiat-Shamir).
//!   No trust in any federation member, operator, or third party.
//! - **Verifiable by**: Anyone. Proofs are publicly verifiable with O(log n) verification
//!   time. Light clients, external auditors, and cross-federation peers can all verify
//!   independently.
//!
//! All code in this crate MUST maintain the property that a valid proof implies a valid
//! witness. Bugs here break the entire trust model -- a soundness bug allows forged
//! authorization tokens.
//!
//! This crate implements the circuit layer for the dregg ZK token system,
//! proving: "I hold a valid attenuated token chain whose final state authorizes
//! action X" without revealing the chain or capabilities.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                     Presentation Proof                               │
//! │                                                                     │
//! │  ┌──────────────┐   ┌──────────────┐         ┌──────────────┐     │
//! │  │  Fold AIR #1 │──▶│  Fold AIR #2 │──▶ ... ─▶│  Fold AIR #N │     │
//! │  │  (attenuation)│   │  (attenuation)│         │  (attenuation)│     │
//! │  └──────────────┘   └──────────────┘         └──────────────┘     │
//! │         │                                            │             │
//! │         │           initial_root                 final_root        │
//! │         │                                            │             │
//! │         ▼                                            ▼             │
//! │  ┌──────────────┐                          ┌──────────────┐      │
//! │  │ Merkle AIR   │                          │Derivation AIR│      │
//! │  │ (issuer key) │                          │(authorization)│      │
//! │  └──────────────┘                          └──────────────┘      │
//! │         │                                                         │
//! │         ▼                                                         │
//! │  federation_root                                                  │
//! └─────────────────────────────────────────────────────────────────────┘
//!
//! Public Inputs: [federation_root, request_predicate, timestamp]
//! Private Witness: [token_chain, derivation_trace, issuer_key]
//! ```
//!
//! # Features
//!
//! - `mock` (default): Uses a constraint satisfaction checker that evaluates
//!   AIR constraints directly without generating real STARK proofs.
//!   This validates circuit correctness and is suitable for development/testing.
//!
//! - `plonky3` (optional): Plonky3 dependencies available for future optimized prover.
//!
//! # Proof Backends
//!
//! - [`stark`]: Real STARK proof generation with FRI-based polynomial commitment.
//!   Produces actual cryptographic proofs (~24 KiB for a 4-level Merkle membership).
//!   Uses BLAKE3 Merkle trees, Fiat-Shamir transform, and Reed-Solomon encoding.
//! - [`constraint_prover`]: Constraint satisfaction checker that validates circuit
//!   logic by evaluating AIR constraints directly on the execution trace.
//!
//! # Security Properties
//!
//! The circuit enforces:
//! 1. **Fact membership**: Every referenced fact exists in the committed Merkle tree.
//! 2. **Valid narrowing**: Each attenuation step only removes facts or adds checks.
//! 3. **Derivation correctness**: The authorization follows from the final state via valid rules.
//! 4. **Issuer accountability**: The token chain originates from a federated issuer.
//! 5. **Freshness**: The proof is bound to a specific timestamp.
//!
//! # Components
//!
//! - [`field`]: BabyBear field arithmetic (p = 2^31 - 1).
//! - [`poseidon2`]: SNARK-friendly hash function for in-circuit hashing.
//! - [`merkle_air`]: 4-ary Merkle membership proof circuit.
//! - [`derivation_air`]: Single Datalog derivation step circuit.
//! - [`fold_air`]: Attenuation (fold) step circuit.
//! - [`presentation`]: Complete presentation proof combining all pieces.
//! - [`constraint_prover`]: Constraint satisfaction evaluator.
//! - [`stark`]: Real STARK prover/verifier (FRI + Merkle + Fiat-Shamir).

pub mod air_descriptor;
pub mod babybear8;
pub mod binding;
pub mod body_membership;
pub mod chunked_derivation;
pub mod constraint_prover;
#[allow(deprecated)]
pub mod cross_state_derivation;
pub mod dsl;
pub mod field;
pub mod ivc;

// Shared accumulator types used by both DSL and non-membership modules.
pub mod accumulator_types;

// Backward-compatible shim modules (type definitions + re-exports from DSL).
// These contain deprecated StarkAir impls superseded by DSL descriptors.
pub mod arithmetic_predicate_air;
pub mod block_transition_air;
pub mod bridge_action_air;
pub mod compound_predicate_air;
#[allow(deprecated)]
pub mod derivation_air;
pub mod effect_action_air;
pub mod fold_air;
pub mod fold_types;
#[allow(deprecated)]
pub mod garbled_air;
pub mod merkle_air;
pub mod merkle_types;
#[allow(deprecated)]
pub mod multi_step_air;
pub mod native_signature_air;
#[allow(deprecated)]
pub mod note_spending_air;
#[allow(deprecated)]
pub mod poseidon2_air;
pub mod predicate_air;
pub mod relational_predicate_air;
pub mod schnorr_air;
#[cfg(feature = "plonky3")]
pub mod temporal_predicate_air;

/// Backward-compatible re-export. Prefer [`constraint_prover`] for new code.
#[doc(hidden)]
pub mod mock_prover {
    pub use crate::constraint_prover::*;
}
pub mod poseidon2;
#[allow(deprecated)]
pub mod presentation;

/// The OPENABLE `capability_root` descriptor loader (cap-reshape crown #103, the ARGUS linchpin):
/// the Lean-verified `EffectVmDescriptor` that checks non-amplification (`granted ⊑ held` submask, per
/// bit) + production-authority (the mint opens the issuer cap from the producer's held-set root)
/// IN-CIRCUIT. Byte-pinned to `Dregg2.Circuit.Emit.EffectVmEmitCapReshape.capReshapeJson`; parsed by
/// the running `parse_vm_descriptor` (the prover authors no constraint). Standalone (not in the locked
/// `effect_vm_descriptors` registry).
pub mod cap_reshape_descriptor;
/// The canonical, openable capability-set commitment: a sorted Poseidon2 binary
/// Merkle tree over a cell's c-list. The SINGLE source of truth for the
/// `cap_root` value — `dregg-cell`'s `compute_canonical_capability_root` calls
/// it, and the EffectVM circuit seeds its `cap_root` column from the same value
/// (cap Phase A). Pure Poseidon2 (no plonky3): available in the `mock` build.
pub mod cap_root;
#[allow(deprecated)]
pub mod committed_threshold;
pub mod effect_vm;
/// The Lean-emitted EffectVM descriptor registry: every verified-by-construction
/// `EffectVmDescriptor` JSON, keyed by selector index, with an anti-drift
/// fingerprint guard. Foundation for the EffectVM circuit cutover.
pub mod effect_vm_descriptors;
#[allow(deprecated)]
pub mod garbled;
/// THE HEAP's canonical, openable commitment (REFINEMENT-DESIGN Decision 1):
/// the sorted Poseidon2 binary Merkle map over `(collection_id, key) → value`,
/// generalizing `cap_root` with the generic `hash[addr, value]` leaf. The
/// SINGLE source of truth for the `heap_root` register value; the descriptor
/// gadget (`EffectVmEmitHeapRoot.lean`) recomputes its address/leaf images
/// in-row. Pure Poseidon2 (no plonky3): available in the `mock` build.
pub mod heap_root;
pub mod native_signature;
#[allow(deprecated)]
pub mod non_membership;
pub mod predicate_program;
#[allow(deprecated)]
pub mod quantified_absence;
pub mod schnorr_curve;
pub mod schnorr_sig;
pub mod stark;
pub mod stark_zk;

pub mod temporal_predicate_dsl;

#[cfg(feature = "plonky3")]
pub mod plonky3_prover;

/// Generic Plonky3 AIR that interprets a Lean-emitted circuit descriptor at
/// `eval`-time and drives the real `p3-uni-stark` prover — so Lean-emitted
/// circuits REPLACE hand-coded AIRs. The data-driven analogue of
/// `plonky3_prover::P3MerklePoseidon2Air`. See module docs.
#[cfg(feature = "plonky3")]
pub mod lean_descriptor_air;

#[cfg(feature = "plonky3")]
pub mod plonky3_recursion;

#[cfg(feature = "plonky3")]
pub mod plonky3_verifier_air;

#[cfg(feature = "recursion")]
pub mod plonky3_recursion_impl;

/// LogUp-style range-check lookups for the Lean-emitted descriptor path — the
/// first concrete efficiency win for the verified extraction circuit. Replaces
/// the `lean_descriptor_air` bit-decomposition range gates (30 aux columns / 30
/// booleanity constraints per 30-bit wire) with a shared `[0,256)` byte-table
/// LogUp bus (4 byte-limb columns per 30-bit wire, table shared across all
/// wires), proved via `p3-batch-stark`. See module docs.
#[cfg(feature = "recursion")]
pub mod lean_lookup_air;

/// Descriptor IR v2 — THE EPOCH multi-table batch-STARK interpreter
/// (`docs/EPOCH-DESIGN.md`). Parses the versioned `"ir":2` wire emitted by Lean
/// (`Dregg2.Circuit.DescriptorIR2.emitVmJson2`) and assembles the five-table
/// batch STARK (main + Poseidon2 chip + range/byte + memory + map-ops) over the
/// fork's `p3-batch-stark` + `p3-lookup` LogUp argument. Hashing becomes a
/// boundary phenomenon: hash sites ride the chip bus, state accesses ride the
/// offline-memory-checking multiset (Blum), and authenticated openings only
/// materialize at the map-ops boundary. The law is descriptor-driven — Rust
/// authors NO constraints; it realizes the declared tables/lookups/mem-ops/
/// map-ops. v1 descriptors keep proving through `lean_descriptor_air` until the
/// flag-day. See module docs.
///
/// Gated on `any(recursion, verifier)`: the PROVE surface (`prove_vm_descriptor2*`,
/// trace assembly, `prove_batch`) is `recursion`-only, but the VERIFY surface
/// (`verify_vm_descriptor2{,_with_config}`, the AIRs, `ir2_config`) compiles under the
/// prover-free `verifier` feature so the wasm / no-lean-link verifier can verify
/// rotated proofs without the prover DFT (cutover C2).
#[cfg(any(feature = "recursion", feature = "verifier"))]
pub mod descriptor_ir2;

/// Recursive (Golden Vision) compression bridge for `dregg_turn::WitnessedReceipt`
/// scope-2 replay. See the module docs for the Silver→Golden mapping and
/// the VK v2 layered encoding of the recursive VK hash.
// The module's own inner `#![cfg(feature = "recursion")]` provides the gate.
pub mod recursive_witness_bundle;

/// Stage 7-γ.2 Phase 2 joint bilateral aggregation AIR. Consumes N per-cell
/// γ.2 PI vectors and the schedule-derived projection; emits a single outer
/// proof attesting bilateral consistency. See module docs and
/// `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`.
pub mod bilateral_aggregation_air;

/// Effect-VM-shape bridge AIR for the `p3-recursion` path. See module
/// docs — this is a *shape* mirror of `effect_vm::EffectVmAir` used to
/// measure that the recursion library accepts the Effect VM's column and
/// PI counts (Block 1/2 of the Golden Vision recursion lane).
#[cfg(feature = "recursion")]
pub mod effect_vm_p3_air;

/// Constraint-COMPLETE Plonky3 `Air` for the Effect VM (v1 hand-AIR): the v1
/// commit-path EffectVM proof on the audited `p3-batch-stark` verifier. Retained
/// under `#[cfg(not(feature = "recursion"))]` for the v1 floor; the recursion tower
/// proves through the rotated IR-v2 multi-table descriptor (`crate::descriptor_ir2`).
#[cfg(not(feature = "recursion"))]
pub mod effect_vm_p3_full_air;

/// Sorted-set neighbor-adjacency STARK: proves two leaves are *consecutive*
/// under a committed binary Merkle root, closing the Silver non-membership
/// wide-bracket forge. See module docs and `dregg_cell::predicate`'s
/// `SortedNeighborNonMembershipVerifier` / `CredentialSetMembershipVerifier`.
pub mod membership_adjacency_air;

pub mod backends;
// `ivc_turn_chain`'s inner `#![cfg(feature = "recursion")]` provides the gate.
pub mod ivc_turn_chain;
pub mod joint_turn_aggregation;
// `joint_turn_recursive`'s inner `#![cfg(feature = "recursion")]` provides the gate.
pub mod joint_turn_recursive;
pub mod proof_forest;
pub mod proof_tier;

#[cfg(test)]
#[allow(deprecated)]
mod tests;

#[cfg(test)]
#[allow(deprecated)]
mod soundness_tests;

// Proof tier types — prevents scaffold/test proofs from satisfying production verifiers.
pub use proof_tier::{CryptographicProof, ProofTier, VerifiedProof};

// Re-export primary types.
pub use binding::{
    ACTION_BINDING_WIDTH, ActionBinding, PRESENTATION_TAG_WIDTH, PresentationTag, WideHash,
    compute_action_binding, compute_action_binding_narrow, compute_presentation_tag,
    compute_presentation_tag_narrow,
};
pub use body_membership::{
    BodyFactMerkleProof, BodyMembershipProof, MembershipEntry, collect_body_fact_hashes,
    prove_authorization_with_membership, verify_authorization_with_membership,
};
pub use chunked_derivation::{
    ChunkedAuthorizationProof, DEFAULT_CHUNK_SIZE, prove_chunked_authorization,
    verify_chunked_authorization,
};
#[allow(deprecated)]
pub use committed_threshold::{
    CommittedThresholdAir, CommittedThresholdProof, CommittedThresholdWitness,
    compute_threshold_commitment, generate_blinding, prove_committed_threshold,
    verify_committed_threshold,
};
#[doc(hidden)]
pub use constraint_prover::MockProof;
#[doc(hidden)]
pub use constraint_prover::MockProofResult;
#[doc(hidden)]
pub use constraint_prover::MockProver;
pub use constraint_prover::{
    Air, ConstraintCheckResult, ConstraintProof, ConstraintProver, ConstraintViolation,
};
pub use cross_state_derivation::{
    CombiningRule, CrossStateDerivationProof, SourceDerivation, SourceInput,
    prove_cross_state_derivation, verify_cross_state_derivation,
};
#[cfg(not(feature = "recursion"))]
pub use effect_vm::EffectVmAir;
pub use effect_vm::{
    CellState, EFFECT_VM_WIDTH, Effect, NUM_EFFECTS, compute_effects_hash, encode_net_delta,
    extract_custom_proof_commitments, extract_net_delta, generate_effect_vm_trace,
    verify_balance_limb_pis,
};
pub use field::BabyBear;
pub use ivc::{
    FoldDelta, FoldMembershipEntry, FoldStepWitness, IvcBackend, IvcBackendProof, IvcBuilder,
    IvcPresentationProof, IvcProof, IvcVerification, MAX_FOLD_DEPTH, StateTransitionAir,
    ValidatedIvcProof, ValidatedIvcVerification, prove_ivc, prove_ivc_stark, prove_validated_ivc,
    verify_ivc, verify_ivc_stark, verify_validated_ivc,
};
pub use non_membership::{
    AugmentedDerivation, DerivationNonMembershipCheck, NonMembershipCheck, NonMembershipProof,
    NonMembershipProver, SetIdentifier, compute_set_accumulator, derive_alpha_for_set,
    verify_augmented_derivation, verify_non_membership_proof,
};
pub use presentation::{
    AuthorizationProof, PresentationAir, PresentationProof, PresentationVerification,
    PresentationWitness, RealPresentationProof, prove_authorization,
};
// Re-export predicate types at crate root for backward compatibility.
pub use predicate_air::{
    PredicateAir, PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment,
    prove_in_range, prove_predicate, verify_in_range, verify_predicate,
};

// Re-export arithmetic predicate types at crate root.
pub use arithmetic_predicate_air::{
    ArithExpr, ArithPredicate, ArithmeticPredicateProof, ArithmeticPredicateWitness, CompareOp,
    compute_arithmetic_fact_commitment, prove_arithmetic_dsl, prove_arithmetic_predicate,
    verify_arithmetic_dsl, verify_arithmetic_predicate,
};

// Re-export relational predicate types at crate root.
pub use relational_predicate_air::{
    RelationType, RelationalPredicateProof, RelationalPredicateWitness, RelationalProof,
    RelationalWitness, compute_value_commitment, prove_relational, prove_value_comparison,
    verify_relational,
};

// Re-export multi-step authorization proving functions.
pub use multi_step_air::{
    MAX_DELEGATION_DEPTH, prove_authorization_stark, try_prove_authorization_stark,
};

/// Backward-compatible module alias for predicate types.
pub mod predicate_types {
    pub use crate::arithmetic_predicate_air::*;
    pub use crate::dsl::predicates::compute_blinded_fact_commitment;
    pub use crate::predicate_air::*;
    pub use crate::relational_predicate_air::*;
}

// Schnorr signature scheme over BabyBear^8 elliptic curve.
pub use babybear8::BabyBear8;
pub use schnorr_curve::{CurvePoint, GENERATOR as SCHNORR_GENERATOR};
pub use schnorr_sig::{
    SchnorrPublicKey, SchnorrSecretKey, SchnorrSignature, compress_public_key, schnorr_keygen,
    schnorr_sign, schnorr_verify,
};
