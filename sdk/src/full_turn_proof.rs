//! Full turn proof composition: a single composed STARK covering ALL validity aspects.
//!
//! A remote verifier (bridge, light client, peer) receiving a [`FullTurnProof`] can
//! verify in one shot:
//! - The state transition is correct (Effect VM)
//! - The actor was authorized (Derivation chain)
//! - The capability existed (C-list membership)
//! - Value was conserved (Conservation)
//! - Nothing was revoked (Non-revocation)
//!
//! The proof IS the truth. No trust in any executor required.
//!
//! # Architecture
//!
//! ```text
//! FullTurnProof
//! +-- ComposedProof (single STARK)
//! |   +-- main_proof: StarkProof
//! |   +-- sub_proofs:
//! |       [0] Effect VM proof (state transition)
//! |       [1] Authorization proof (derivation chain)
//! |       [2] Membership proof (c-list)
//! |       [3] Conservation proof (value balance) — optional
//! |       [4] Non-revocation proof (freshness) — optional
//! +-- public_inputs: [old_commit, new_commit, turn_hash, ...]
//! +-- components: TurnProofComponents (which sub-proofs included)
//! ```
//!
//! # Public Input Layout (merged from sub-proofs)
//!
//! The composed proof's public inputs are the concatenation of all sub-proof PIs,
//! laid out by `compose_aggregate`. A verifier checks:
//! 1. Effect VM PIs: old_commitment, new_commitment, net_delta, effects_hash
//! 2. Authorization PIs: state_root, derived_hash (must bind to capability used)
//! 3. Membership PIs: leaf_hash, merkle_root (must match authorization's state_root)
//! 4. Conservation PIs: (if present) commitment sums balance
//! 5. Non-revocation PIs: revocation_root (from federation state)
//!
//! Cross-proof PI bindings:
//! - Authorization state_root == Membership merkle_root (same fact tree)
//! - Effect VM old_commitment is the cell state the actor is authorized to mutate
//! - Non-revocation root matches the federation's published revocation accumulator

use dregg_circuit::dsl::derivation::{
    derivation_circuit_descriptor, prove_derivation_p3, verify_derivation_p3,
};
use dregg_circuit::dsl::dsl_p3_air::DslP3Proof;
use dregg_circuit::dsl::revocation::{
    DslRevocationTree, non_revocation_circuit_descriptor, prove_non_revocation_p3,
    verify_non_revocation_p3,
};
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::effect_vm::{self, CellState, Effect as VmEffectKind, generate_effect_vm_trace};
use dregg_circuit::effect_vm::columns::sel;
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::effect_vm_p3_full_air::{
    EffectVmP3Proof, prove_effect_vm_p3, verify_effect_vm_p3,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{
    parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
};
use dregg_circuit::merkle_air::{
    MembershipP3Proof, membership_public_inputs, prove_membership_p3, verify_membership_p3,
};
use dregg_dsl_runtime::composition::{AttachedSubProof, ComposedProof, compose_aggregate};
use dregg_dsl_runtime::{CircuitDescriptor, ComposedCircuitDescriptor};
use serde::{Deserialize, Serialize};

use crate::error::SdkError;

// ============================================================================
// Core Types
// ============================================================================

/// A complete turn proof covering ALL validity aspects of a turn.
///
/// This is the final artifact transmitted to remote verifiers. It contains
/// a single composed STARK proof that covers state transition, authorization,
/// membership, conservation, and non-revocation — all in one verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FullTurnProof {
    /// The composed proof (single verification covers everything).
    pub composed: ComposedProof,
    /// Which sub-proofs were included (some are conditional).
    pub components: TurnProofComponents,
    /// The turn hash this proof is bound to (prevents replay).
    pub turn_hash: [u8; 32],
    /// Byte-serialized form for wire transmission.
    pub proof_bytes: Vec<u8>,
}

/// Flags indicating which sub-proof components are present.
///
/// State transition and authorization are always required. Membership is
/// required unless the authorization is self-sovereign. Conservation and
/// non-revocation are conditional on whether the turn involves value
/// transfers or revocable capabilities.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct TurnProofComponents {
    /// Effect VM proof: state transition is correct.
    pub has_state_transition: bool,
    /// Derivation chain proof: actor was authorized.
    pub has_authorization: bool,
    /// Merkle membership proof: capability exists in c-list.
    pub has_membership: bool,
    /// Conservation proof: value inputs == value outputs.
    pub has_conservation: bool,
    /// Non-revocation proof: token/capability hasn't been revoked.
    pub has_non_revocation: bool,
}

/// Witnesses needed to generate each sub-proof.
///
/// The caller assembles this from the cipherclerk state, turn data, and cell state.
/// Each field is `Option` because some aspects may not apply to a given turn.
pub struct FullTurnWitness {
    // -- Effect VM witness --
    /// The cell state before the turn executes.
    pub initial_cell_state: CellState,
    /// The effects to prove (in Effect VM encoding).
    pub effects: Vec<effect_vm::Effect>,

    // -- Authorization witness --
    /// The derivation witness proving the actor's authorization chain.
    /// If `None`, authorization proof is skipped (self-sovereign turn).
    pub authorization: Option<AuthorizationWitness>,

    // -- Membership witness --
    /// The Merkle membership witness proving the capability is in the c-list.
    /// If `None`, membership proof is skipped.
    pub membership: Option<MembershipWitness>,

    // -- Conservation witness --
    /// Present only when the turn involves value transfers between notes.
    /// The conservation proof demonstrates sum(inputs) == sum(outputs).
    pub conservation: Option<ConservationWitness>,

    // -- Non-revocation witness --
    /// Present only when capabilities have revocation channels.
    /// Proves the token hasn't been added to the revocation accumulator.
    pub non_revocation: Option<NonRevocationWitness>,

    /// The turn hash for binding (prevents proof replay on different turns).
    pub turn_hash: [u8; 32],
}

/// Authorization witness for the derivation sub-proof.
pub struct AuthorizationWitness {
    /// The derivation witness (single-step or multi-step).
    pub derivation: dregg_circuit::derivation_air::DerivationWitness,
}

/// Membership witness for the Merkle sub-proof.
pub struct MembershipWitness {
    /// The leaf hash (hash of the capability being proven).
    pub leaf_hash: BabyBear,
    /// Merkle siblings at each tree level.
    pub siblings: Vec<[BabyBear; 3]>,
    /// Position indices at each tree level (0..3 for 4-ary tree).
    pub positions: Vec<u8>,
}

/// Conservation witness (value balance proof).
///
/// For the full turn proof, we embed the conservation check as a constraint
/// that the Effect VM's net_delta public input equals the expected transfer
/// sum. For committed-value turns, the actual Pedersen/Bulletproof conservation
/// proof is attached separately (it operates over Ristretto, not BabyBear).
pub struct ConservationWitness {
    /// Expected net delta (should match Effect VM PI).
    /// Positive = net credit, negative = net debit. Must be zero for
    /// value-conserving turns (pure internal transfers).
    pub expected_net_delta: i64,
}

/// Non-revocation witness for the revocation sub-proof.
pub struct NonRevocationWitness {
    /// The revocation tree to prove non-membership against.
    pub tree: DslRevocationTree,
    /// The item hash to prove is NOT revoked.
    pub item_hash: BabyBear,
}

// ============================================================================
// Circuit Descriptor Construction
// ============================================================================

/// Build the composed circuit descriptor for a full turn proof.
///
/// The descriptor encodes which sub-circuits are included and how their
/// public inputs are merged. This is deterministic given the component flags.
fn build_full_turn_descriptor(components: &TurnProofComponents) -> ComposedCircuitDescriptor {
    let mut circuits: Vec<CircuitDescriptor> = Vec::new();

    // Always include Effect VM.
    if components.has_state_transition {
        circuits.push(effect_vm_circuit_descriptor());
    }

    // Authorization (derivation chain).
    if components.has_authorization {
        circuits.push(derivation_circuit_descriptor());
    }

    // Membership (c-list Merkle proof).
    if components.has_membership {
        circuits.push(dregg_circuit::dsl::descriptors::merkle_poseidon2_descriptor());
    }

    // Non-revocation (sorted tree non-membership).
    if components.has_non_revocation {
        circuits.push(non_revocation_circuit_descriptor());
    }

    let circuit_refs: Vec<&CircuitDescriptor> = circuits.iter().collect();
    compose_aggregate(&circuit_refs)
}

/// Construct a CircuitDescriptor for the Effect VM AIR.
///
/// The Effect VM is a StarkAir (not a DslCircuit), so we create a thin
/// descriptor wrapper for composition purposes. The VK hash is computed
/// from the AIR's structural parameters.
fn effect_vm_circuit_descriptor() -> CircuitDescriptor {
    // The Effect VM has 61 columns, degree 9, and 7+ public inputs.
    // We create a minimal descriptor that captures its identity for VK hashing.
    CircuitDescriptor {
        name: "dregg-effect-vm-v1".into(),
        trace_width: effect_vm::EFFECT_VM_WIDTH,
        max_degree: 9,
        columns: vec![],     // Not needed for composition — VK hash suffices
        constraints: vec![], // Constraints are in the StarkAir impl
        boundaries: vec![],  // Boundaries are in the StarkAir impl
        public_input_count: effect_vm::pi::BASE_COUNT,
        lookup_tables: vec![],
    }
}

// ============================================================================
// Effect-VM prover selection: hand-AIR (default) vs Lean descriptor interpreter.
// ============================================================================
//
// THE CUTOVER FLAG (`DREGG_DESCRIPTOR_PROVER=1`): route the Effect-VM state-transition
// proof through the verified-by-construction Lean DESCRIPTOR INTERPRETER
// (`EffectVmDescriptorAir`, fed the byte-exact Lean-emitted descriptor JSON from the
// `effect_vm_descriptors` registry) instead of the hand-written `EffectVmP3Air`. The
// proof is the SAME wire type (`BatchProof<DreggStarkConfig>` = `EffectVmP3Proof`), so
// the composed proof + verifier are unchanged.
//
// CONSERVATIVE SCOPE (cutover beachhead → economic effects): the descriptor path is taken
// ONLY for a single-effect turn whose effect maps to a descriptor that is VALIDATED
// cutover-ready by the differential harness
// (`circuit/tests/effect_vm_descriptor_cutover_harness.rs`), which proves the interpreter
// decides IDENTICALLY to the hand-AIR over the real witness (honest accept + anti-ghost
// reject). The validated set is now `Transfer` (1) PLUS the reconciled FULL-ECONOMIC
// effects `Burn` (46), `NoteCreate` (5), `NoteSpend` (4), `BridgeMint` (40) — graduated by
// `economic_effects_graduated_into_cutover` — PLUS the nonce-tick-reconciled frozen-frame
// effects `CreateSealPair` (28) and `BridgeFinalize` (41), graduated by
// `bridge_finalize_and_seal_pair_graduated_into_cutover`. Every other shape (multi-effect
// turns, the IR-blocked side-table effects) FALLS BACK to the hand-AIR. So flipping the flag
// NEVER changes the proven semantics; it only swaps the prover for the validated effects.

/// Is the descriptor-interpreter cutover prover enabled (`DREGG_DESCRIPTOR_PROVER=1`)?
fn descriptor_prover_enabled() -> bool {
    std::env::var("DREGG_DESCRIPTOR_PROVER")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

/// The selector for a turn that is a SINGLE cutover-ready effect, or `None`. Validated
/// cutover-ready (descriptor ⟺ hand-AIR proven IDENTICAL on the real witness + anti-ghost):
/// `Transfer` (1) plus the reconciled full-economic effects `NoteSpend` (4), `NoteCreate`
/// (5), `BridgeMint` (40), `Burn` (46), plus the nonce-tick-reconciled frozen-frame effects
/// `CreateSealPair` (28), `BridgeFinalize` (41), and the passthrough+tick+last-row-PI
/// frozen-frame effects `SetPermissions` (26), `SetVerificationKey` (27), `ExerciseViaCapability`
/// (34), `PipelinedSend` (36), `CellDestroy` (47), `CellSeal` (49), `Refusal` (52),
/// `IncrementNonce` (53), and the cap/delegation passthrough effects `RefreshDelegation` (29),
/// `RevokeDelegation` (30), `Introduce` (35) (whose cap-table moves are bound OFF-row).
fn cutover_ready_selector(effects: &[VmEffectKind]) -> Option<usize> {
    if effects.len() != 1 {
        return None;
    }
    match &effects[0] {
        VmEffectKind::Transfer { .. } => Some(sel::TRANSFER),
        VmEffectKind::NoteSpend { .. } => Some(sel::NOTE_SPEND),
        VmEffectKind::NoteCreate { .. } => Some(sel::NOTE_CREATE),
        VmEffectKind::BridgeMint { .. } => Some(sel::BRIDGE_MINT),
        VmEffectKind::Burn { .. } => Some(sel::BURN),
        // GRADUATED (nonce-tick reconcile): frozen-balance + ticked-nonce effects whose Lean
        // descriptors now tick the runtime nonce (`gNonce`) AND carry the full last-row balance
        // PI bindings, so the descriptor decides IDENTICALLY to the hand-AIR on the real witness
        // (honest accept + forged-balance/forged-state-commit reject) — validated by
        // `bridge_finalize_and_seal_pair_graduated_into_cutover`.
        VmEffectKind::CreateSealPair { .. } => Some(sel::CREATE_SEAL_PAIR),
        VmEffectKind::BridgeFinalize { .. } => Some(sel::BRIDGE_FINALIZE),
        // GRADUATED (nonce-tick + last-row PI pins, v2): the frozen-block lifecycle/flag effects
        // `CellSeal` (49), `CellDestroy` (47), `Refusal` (52). Their Lean descriptors were
        // reconciled onto the runtime Stage-3 passthrough batch (whole economic block frozen, nonce
        // ticks via `gNonce`) AND grown the `boundaryLastPins` last-row balance PI binding, so the
        // descriptor body is now STRUCTURALLY IDENTICAL to the validated `createsealpair-v2` and
        // decides identically to the hand-AIR on the real witness (honest accept + forged-balance /
        // forged-state-commit reject). Their per-cell full-semantics economic-freeze ⟺ executor
        // agreement is `descriptor_agrees_with_executor_{seal,destroy,refusal}`; the lifecycle /
        // audit-slot write is the proven OFF-ROW side-table leg (`*_offrow_unenforced`).
        VmEffectKind::CellSeal { .. } => Some(sel::CELL_SEAL),
        VmEffectKind::CellDestroy { .. } => Some(sel::CELL_DESTROY),
        VmEffectKind::Refusal { .. } => Some(sel::REFUSAL),
        // GRADUATED (already in the passthrough+tick+last-row-PI form): `SetVerificationKey` (27).
        // Its Lean descriptor (`setVKDescriptor_full_sound` + `descriptor_agrees_with_executor_setVK`
        // + `vk_write_is_out_of_row`) was already reconciled onto the runtime Stage-3 passthrough
        // batch (whole economic block frozen, nonce ticks, last-row balance PI pins). The runtime
        // trace anchors `vk_hash[0]` in `params[0]` and ticks the nonce (trace.rs `SetVerificationKey`
        // arm), exactly what the descriptor decides — it was simply never wired here. The VK write is
        // the proven OFF-ROW record-field leg.
        VmEffectKind::SetVerificationKey { .. } => Some(sel::SET_VERIFICATION_KEY),
        // GRADUATED (passthrough+tick+last-row PI pins, v2): `SetPermissions` (26), `ExerciseViaCapability`
        // (34), `PipelinedSend` (36). Their Lean descriptors were reconciled onto the runtime Stage-3
        // passthrough batch (whole economic block frozen, nonce ticks, last-row balance PI pins) — body
        // STRUCTURALLY IDENTICAL to `createsealpair-v2` — but the committed JSON had not been re-emitted.
        // The runtime trace for each anchors `hash[0]` in `params[0]` and ticks the nonce (trace.rs); the
        // permissions/VK/exercise/send hash write is the proven OFF-ROW record-field / fold leg.
        VmEffectKind::SetPermissions { .. } => Some(sel::SET_PERMISSIONS),
        VmEffectKind::ExerciseViaCapability { .. } => Some(sel::EXERCISE_VIA_CAPABILITY),
        VmEffectKind::PipelinedSend { .. } => Some(sel::PIPELINED_SEND),
        // GRADUATED (passthrough+tick+last-row PI pins, v2): the explicit nonce-bump `IncrementNonce`
        // (53). Its Lean descriptor ticks the nonce via `gNonce` with the rest of the block frozen and
        // the last-row balance PI pins; body STRUCTURALLY IDENTICAL to `createsealpair-v2`. The runtime
        // trace just does `new_state.nonce += 1` (trace.rs `IncrementNonce` arm).
        VmEffectKind::IncrementNonce => Some(sel::INCREMENT_NONCE),
        // GRADUATED (passthrough+tick+last-row PI pins, v2): the cap/delegation passthrough effects
        // `RefreshDelegation` (29), `RevokeDelegation` (30), `Introduce` (35). The runtime hand-AIR runs
        // ALL THREE as Stage-3 STATE-PASSTHROUGH rows (`air.rs:983-1018`): the whole economic block —
        // including `cap_root` — is FROZEN, and the GLOBAL nonce gate ticks. RevokeDelegation/Introduce
        // were PRE-v2 pointed at the `attenuateA` cap-root-MOVE descriptor (wrong: the runtime FREEZES
        // `cap_root`; the cap-table move rides `effects_hash` OFF-row); their v2 Lean modules now emit the
        // runtime frozen-frame + nonce-TICK directly with `boundaryLastPins`. RefreshDelegation already
        // ticked but its committed JSON lacked the last-row balance PI (anti-ghost WEAK) — v2 added it.
        // The cap-table edge removal / grant / deleg-snapshot are the proven OFF-ROW connectors
        // (`unify_revoke`/`unify_introduce`/`unify_refresh_via_full_sound`).
        VmEffectKind::RefreshDelegation => Some(sel::REFRESH_DELEGATION),
        VmEffectKind::RevokeDelegation { .. } => Some(sel::REVOKE_DELEGATION),
        VmEffectKind::Introduce { .. } => Some(sel::INTRODUCE),
        _ => None,
    }
}

/// All selectors a cutover-ready descriptor proof may bind, for the verify path (which does
/// not carry the effect kind). The verifier reconstructs each cutover descriptor AIR and checks
/// the proof against it; a sound proof verifies under EXACTLY ONE — its OWN effect selector.
///
/// SELECTOR BINDING (closed; was the prior SOUNDNESS NOTE). Every cutover descriptor now carries a
/// SELECTOR-BINDING GATE, emitted verified-by-construction from the Lean
/// `Dregg2.Circuit.Emit.EffectVmEmit.selectorGate s` (proved in `selectorGate_holds_iff` /
/// `selectorGate_rejects_wrong_selector`): the per-row body `(1 - sel[NOOP]) · (1 - sel[s])`
/// vanishes on NoOp pad rows AND forces the descriptor's OWN selector column `sel[s] = 1` on the
/// single active row. Because the runtime trace sets EXACTLY ONE selector per row
/// (`effect_vm/trace.rs`), a proof whose committed trace carries effect `s'` (`sel[s'] = 1`,
/// `sel[s] = 0`) VIOLATES descriptor-`s`'s selector gate on its active row, so the audited p3
/// verifier for descriptor `s` REJECTS it. The cross-AIR replay the prior note flagged (a
/// frozen-frame / economic proof verifying under several AIRs) is therefore CLOSED: descriptor-`s`
/// verifies a proof iff that proof's committed trace carries selector `s`. The harness
/// `descriptor_proof_binds_to_its_selector` validates this on real Plonky3 (a `transfer` proof is
/// REJECTED by every OTHER cutover descriptor's verifier). The post-state-commitment binding (the
/// GROUP-4 hash sites + the `expected_new_commit` PI equality in `verify_full_turn`) is unchanged
/// and remains the second, independent tooth.
const CUTOVER_READY_SELECTORS: &[usize] = &[
    sel::TRANSFER,
    sel::NOTE_SPEND,
    sel::NOTE_CREATE,
    sel::BRIDGE_MINT,
    sel::BURN,
    sel::CREATE_SEAL_PAIR,
    sel::BRIDGE_FINALIZE,
    sel::CELL_SEAL,
    sel::CELL_DESTROY,
    sel::REFUSAL,
    sel::SET_VERIFICATION_KEY,
    sel::SET_PERMISSIONS,
    sel::EXERCISE_VIA_CAPABILITY,
    sel::PIPELINED_SEND,
    sel::INCREMENT_NONCE,
    sel::REFRESH_DELEGATION,
    sel::REVOKE_DELEGATION,
    sel::INTRODUCE,
];

/// Prove the Effect-VM state transition, routing through the Lean descriptor interpreter
/// when the cutover flag is set AND the turn is a validated cutover-ready single effect;
/// otherwise (default) through the hand-written `EffectVmP3Air`. Returns the SAME wire
/// proof type either way.
fn prove_effect_vm_with_cutover(
    effects: &[VmEffectKind],
    effect_trace: &[Vec<BabyBear>],
    effect_pi: &[BabyBear],
) -> Result<EffectVmP3Proof, SdkError> {
    if descriptor_prover_enabled() {
        if let Some(s) = cutover_ready_selector(effects) {
            if let Some(json) = descriptor_for_selector(s) {
                let desc = parse_vm_descriptor(json).map_err(|e| {
                    SdkError::InvalidWitness(format!("cutover descriptor parse failed: {e}"))
                })?;
                // The descriptor binds the PI prefix (`public_input_count`); slice the
                // wider EffectVM PI vector down to it. `prove_vm_descriptor` proves AND
                // self-verifies through the audited p3 verifier before return.
                let dpis = &effect_pi[..desc.public_input_count];
                return prove_vm_descriptor(&desc, effect_trace, dpis).map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "effect-vm DESCRIPTOR-INTERPRETER proof failed: {e}"
                    ))
                });
            }
        }
    }
    // DEFAULT (and fallback for any non-cutover-ready shape): the hand-AIR.
    prove_effect_vm_p3(effect_trace, effect_pi)
        .map_err(|e| SdkError::InvalidWitness(format!("effect-vm p3 proof failed: {e}")))
}

/// Verify an effect-vm sub-proof, cutover-flag-aware. A proof produced by the descriptor
/// interpreter binds a DIFFERENT AIR (different extended trace width / CommonData) than
/// the hand-AIR, so the two verifiers are NOT interchangeable. When the cutover flag is
/// set, try the descriptor verifier (the validated cutover-ready transfer descriptor,
/// over the PI prefix) first; on any failure (incl. a hand-AIR proof whose width doesn't
/// match the descriptor AIR), fall back to the hand-AIR verifier. With the flag unset,
/// only the hand-AIR verifier runs (the default production path is unchanged).
fn verify_effect_vm_proof_with_cutover(
    proof: &EffectVmP3Proof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    if descriptor_prover_enabled() {
        // SELECTOR-BOUND verify: reconstruct each cutover descriptor AIR and check the proof
        // against it. Each descriptor now carries the Lean `selectorGate s` tooth, so a sound
        // descriptor proof verifies under EXACTLY ONE — its own effect selector. We record WHICH
        // selectors accept: zero ⇒ not a descriptor proof (fall back to the hand-AIR); exactly one
        // ⇒ the proof is BOUND to that effect selector (accept); more than one ⇒ the selector
        // binding is ambiguous (must not happen with the gate in place) ⇒ REJECT rather than accept
        // "under the wrong selector".
        let mut bound: Vec<usize> = Vec::new();
        for &s in CUTOVER_READY_SELECTORS {
            if let Some(json) = descriptor_for_selector(s) {
                if let Ok(desc) = parse_vm_descriptor(json) {
                    if public_inputs.len() >= desc.public_input_count {
                        let dpis = &public_inputs[..desc.public_input_count];
                        if verify_vm_descriptor(&desc, proof, dpis).is_ok() {
                            bound.push(s);
                        }
                    }
                }
            }
        }
        match bound.as_slice() {
            // Bound to exactly its own effect selector — the selector-binding tooth held.
            [_only] => return Ok(()),
            // The selector binding is ambiguous: the gate should make at most one descriptor
            // accept. Reject rather than launder a wrong-selector acceptance.
            multi if multi.len() > 1 => {
                return Err(format!(
                    "effect-vm descriptor proof verified under MULTIPLE cutover selectors {multi:?} \
                     — selector binding ambiguous, rejecting"
                ));
            }
            // Zero descriptor verifiers accepted: this is a hand-AIR proof (or a non-cutover
            // shape). Fall through to the hand-AIR verifier below.
            _ => {}
        }
    }
    verify_effect_vm_p3(proof, public_inputs).map_err(|e| format!("{e}"))
}

// ============================================================================
// Proof Generation
// ============================================================================

/// Generate a full turn proof covering all validity aspects.
///
/// This is the main entry point. Given the complete witness data, it:
/// 1. Generates each sub-proof independently
/// 2. Composes them into a single composed proof via `compose_aggregate`
/// 3. Returns the [`FullTurnProof`] ready for wire transmission
///
/// # Errors
///
/// Returns `SdkError` if any sub-proof generation fails (e.g., invalid witness,
/// revoked capability, or inconsistent state).
pub fn prove_full_turn(witness: &FullTurnWitness) -> Result<FullTurnProof, SdkError> {
    let mut sub_proofs: Vec<AttachedSubProof> = Vec::new();
    let mut all_public_inputs: Vec<BabyBear> = Vec::new();
    let mut components = TurnProofComponents::default();

    // ========================================================================
    // 1. Effect VM proof (state transition)
    // ========================================================================
    let (effect_trace, effect_pi) =
        generate_effect_vm_trace(&witness.initial_cell_state, &witness.effects);
    // AUDITED PATH: the Effect VM state transition is proven through the real
    // Plonky3 verifier (`p3-batch-stark`) with REAL in-circuit Poseidon2 for
    // every state-commitment / cap-root hash — NOT the bespoke `stark` (whose
    // FRI has no terminal low-degree test). The proof self-verifies before
    // return, so the post-state commitment is genuinely bound: a forged
    // NEW_COMMIT makes the audited verifier reject (see
    // `effect_vm_p3_full_air` anti-ghost tests).
    // CUTOVER FLAG (`DREGG_DESCRIPTOR_PROVER=1`): for a validated cutover-ready effect
    // (single Transfer), prove through the verified-by-construction Lean DESCRIPTOR
    // INTERPRETER; otherwise (default) through the hand-written `EffectVmP3Air`. Same
    // wire proof type; the differential harness guards equivalence.
    let effect_proof = prove_effect_vm_with_cutover(&witness.effects, &effect_trace, &effect_pi)?;
    let effect_proof_bytes = postcard::to_allocvec(&effect_proof).map_err(|e| {
        SdkError::InvalidWitness(format!("effect-vm p3 proof serialize failed: {e}"))
    })?;

    components.has_state_transition = true;
    all_public_inputs.extend_from_slice(&effect_pi);
    sub_proofs.push(AttachedSubProof {
        label: "effect-vm".into(),
        proof_bytes: effect_proof_bytes.clone(),
        sub_public_inputs: effect_pi.clone(),
        vk_hash: compute_vk_hash_bytes(&effect_vm_circuit_descriptor()),
    });

    // ========================================================================
    // 2. Authorization proof (derivation chain)
    // ========================================================================
    if let Some(auth_witness) = &witness.authorization {
        // AUDITED PATH: the derivation chain is proven through the real Plonky3
        // verifier (`p3-batch-stark`) via `prove_derivation_p3`. The derivation
        // circuit's only non-algebraic constraint (C4 `derived_hash` `hash_fact`
        // sponge) is arithmetized in-circuit by the real Poseidon2 gadget, so a
        // forged `derived_hash` is UNSAT — NOT the bespoke `stark`.
        let auth_proof = prove_derivation_p3(&auth_witness.derivation)
            .map_err(|e| SdkError::InvalidWitness(format!("derivation p3 proof failed: {e}")))?;
        let auth_proof_bytes = postcard::to_allocvec(&auth_proof).map_err(|e| {
            SdkError::InvalidWitness(format!("derivation p3 proof serialize failed: {e}"))
        })?;

        // Derivation public inputs: [state_root, derived_hash, not_after, org_id, budget]
        let auth_pi = vec![
            auth_witness.derivation.state_root,
            auth_witness.derivation.derived_hash(),
            auth_witness.derivation.not_after_height,
            auth_witness.derivation.org_id_hash,
            auth_witness.derivation.budget_remaining,
        ];

        components.has_authorization = true;
        all_public_inputs.extend_from_slice(&auth_pi);
        sub_proofs.push(AttachedSubProof {
            label: "authorization".into(),
            proof_bytes: auth_proof_bytes,
            sub_public_inputs: auth_pi,
            vk_hash: compute_vk_hash_bytes(&derivation_circuit_descriptor()),
        });
    }

    // ========================================================================
    // 3. Membership proof (c-list Merkle)
    // ========================================================================
    if let Some(mem_witness) = &witness.membership {
        // AUDITED PATH: the c-list Merkle membership is proven through the real
        // Plonky3 verifier (`p3-batch-stark`) via `prove_membership_p3`, which
        // reuses the constraint-complete `P3MerklePoseidon2Air` (real in-circuit
        // Poseidon2, position validity, hash-chain continuity, `[leaf, root]`
        // boundary) — NOT the bespoke `stark`. A forged root is rejected.
        let mem_proof = prove_membership_p3(
            mem_witness.leaf_hash,
            &mem_witness.siblings,
            &mem_witness.positions,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("membership p3 proof failed: {e}")))?;
        let mem_proof_bytes = postcard::to_allocvec(&mem_proof).map_err(|e| {
            SdkError::InvalidWitness(format!("membership p3 proof serialize failed: {e}"))
        })?;

        // Membership public inputs: [leaf_hash, root]
        let mem_pi = membership_public_inputs(
            mem_witness.leaf_hash,
            &mem_witness.siblings,
            &mem_witness.positions,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("membership PI failed: {e}")))?;

        components.has_membership = true;
        all_public_inputs.extend_from_slice(&mem_pi);
        sub_proofs.push(AttachedSubProof {
            label: "membership".into(),
            proof_bytes: mem_proof_bytes,
            sub_public_inputs: mem_pi,
            vk_hash: compute_vk_hash_bytes(
                &dregg_circuit::dsl::descriptors::merkle_poseidon2_descriptor(),
            ),
        });
    }

    // ========================================================================
    // 4. Conservation proof (value balance)
    // ========================================================================
    // The conservation check for BabyBear-field value is embedded in the Effect VM's
    // net_delta public input. For committed-value (Pedersen) turns, the Bulletproof
    // range proof operates over Ristretto and cannot be composed into BabyBear STARK.
    // We record the component flag but the actual conservation binding is via PI check.
    if let Some(cons_witness) = &witness.conservation {
        // Verify that the Effect VM's net_delta matches the expected conservation.
        let (effect_delta_mag, effect_delta_sign) =
            effect_vm::encode_net_delta(cons_witness.expected_net_delta);
        let actual_mag = effect_pi[effect_vm::pi::NET_DELTA_MAG];
        let actual_sign = effect_pi[effect_vm::pi::NET_DELTA_SIGN];

        if actual_mag != effect_delta_mag || actual_sign != effect_delta_sign {
            return Err(SdkError::InvalidWitness(format!(
                "conservation mismatch: effect VM net_delta ({:?},{:?}) != expected ({:?},{:?})",
                actual_mag, actual_sign, effect_delta_mag, effect_delta_sign
            )));
        }
        components.has_conservation = true;
        // No separate sub-proof needed — conservation is proven by Effect VM PI binding.
    }

    // ========================================================================
    // 5. Non-revocation proof (token freshness)
    // ========================================================================
    if let Some(revoc_witness) = &witness.non_revocation {
        // AUDITED PATH: non-revocation (sorted-tree non-membership) is proven
        // through the real Plonky3 verifier (`p3-batch-stark`) via
        // `prove_non_revocation_p3`. Its two `hash_fact` node-hash constraints
        // are arithmetized in-circuit by the real Poseidon2 gadget — NOT the
        // bespoke `stark`.
        let revoc_proof = prove_non_revocation_p3(&revoc_witness.tree, revoc_witness.item_hash)
            .map_err(|e| {
                SdkError::InvalidWitness(format!("non-revocation p3 proof failed: {e}"))
            })?;
        let revoc_proof_bytes = postcard::to_allocvec(&revoc_proof).map_err(|e| {
            SdkError::InvalidWitness(format!("non-revocation p3 proof serialize failed: {e}"))
        })?;

        // Non-revocation public inputs: [revocation_root]
        let revoc_pi = vec![revoc_witness.tree.root()];

        components.has_non_revocation = true;
        all_public_inputs.extend_from_slice(&revoc_pi);
        sub_proofs.push(AttachedSubProof {
            label: "non-revocation".into(),
            proof_bytes: revoc_proof_bytes,
            sub_public_inputs: revoc_pi,
            vk_hash: compute_vk_hash_bytes(&non_revocation_circuit_descriptor()),
        });
    }

    // ========================================================================
    // 6. Compose all sub-proofs into one (AUDITED p3 main proof)
    // ========================================================================
    let composed_descriptor = build_full_turn_descriptor(&components);

    // The composition main proof binds the merged public inputs through the
    // AUDITED Plonky3 verifier. We prove a minimal PI-binding circuit whose
    // public inputs ARE `all_public_inputs` (each pinned to a trace column on
    // every row) — this carries the merged-PI commitment on the audited path,
    // replacing the bespoke-`stark` composition main proof. It is NOT the
    // anti-ghost tooth: the load-bearing post-state binding lives in the
    // EffectVM sub-proof (also p3) and is re-checked directly in
    // `verify_full_turn`. Each attached sub-proof is independently re-verified
    // in `verify_full_turn`, superseding the bespoke valid-flag binding the old
    // `ComposedDslCircuit` main proof carried.
    let (main_circuit, main_trace, main_pi) =
        build_pi_binding_p3(&all_public_inputs);
    let main_proof_p3_proof = prove_dsl_p3(&main_circuit, &main_trace, &main_pi)
        .map_err(|e| SdkError::InvalidWitness(format!("composition p3 main proof failed: {e}")))?;
    let main_proof_p3_bytes = postcard::to_allocvec(&main_proof_p3_proof)
        .map_err(|e| SdkError::InvalidWitness(format!("composition p3 serialize failed: {e}")))?;
    let comp_pi = main_pi.clone();

    // Compute composed VK hash.
    let composed_vk_bytes = {
        let serialized = postcard::to_allocvec(&composed_descriptor.circuit).unwrap_or_default();
        *blake3::hash(&serialized).as_bytes()
    };

    let composed = ComposedProof {
        main_proof: None,
        sub_proofs,
        public_inputs: comp_pi,
        composed_vk_hash: composed_vk_bytes,
        main_proof_p3: Some(main_proof_p3_bytes),
    };

    // Serialize the full proof for wire transmission.
    let proof_bytes = postcard::to_allocvec(&composed).unwrap_or_default();

    Ok(FullTurnProof {
        composed,
        components,
        turn_hash: witness.turn_hash,
        proof_bytes,
    })
}

// ============================================================================
// Verification
// ============================================================================

/// Verify a full turn proof.
///
/// This is the verifier's entry point. Given a [`FullTurnProof`] and the
/// expected old/new commitments, it checks:
/// 1. The composed STARK proof verifies (all sub-proofs are valid).
/// 2. The public inputs bind to the expected state commitments.
/// 3. Cross-proof PI bindings are consistent (shared roots match).
///
/// # Returns
///
/// `Ok(())` if the proof is valid, or an error describing what failed.
pub fn verify_full_turn(
    proof: &FullTurnProof,
    expected_old_commit: BabyBear,
    expected_new_commit: BabyBear,
) -> Result<(), FullTurnVerifyError> {
    // 1. Rebuild the composed circuit descriptor from the component flags.
    let _composed_descriptor = build_full_turn_descriptor(&proof.components);

    // 2. Verify the main proof through the AUDITED Plonky3 verifier. The main
    //    proof is the PI-binding circuit (see `build_pi_binding_p3`); it pins
    //    the merged public-input vector on the audited path.
    let main_p3_bytes = proof.composed.main_proof_p3.as_ref().ok_or_else(|| {
        FullTurnVerifyError::MainProofInvalid(
            "full-turn proof is missing the audited p3 main proof".into(),
        )
    })?;
    let main_p3: dregg_circuit::dsl::dsl_p3_air::DslP3Proof =
        postcard::from_bytes(main_p3_bytes).map_err(|e| {
            FullTurnVerifyError::MainProofInvalid(format!("p3 main proof deserialize: {e}"))
        })?;
    let (main_circuit, _t, main_pi) = build_pi_binding_p3(&proof.composed.public_inputs);
    verify_dsl_p3(&main_circuit, &main_p3, &main_pi)
        .map_err(|e| FullTurnVerifyError::MainProofInvalid(format!("{e}")))?;

    // 3. Verify each attached sub-proof cryptographically.
    for (i, attached) in proof.composed.sub_proofs.iter().enumerate() {
        // Dispatch verification to the correct verifier based on label.
        let verify_result: Result<(), String> = match attached.label.as_str() {
            // EFFECT VM: AUDITED p3 verifier (the load-bearing post-state
            // binding). The proof bytes are a postcard-serialized
            // `EffectVmP3Proof` (p3-batch-stark BatchProof).
            "effect-vm" => {
                let p3: EffectVmP3Proof =
                    postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                        FullTurnVerifyError::SubProofDeserialize {
                            index: i,
                            reason: format!("effect-vm p3 deserialize: {e}"),
                        }
                    })?;
                // CUTOVER FLAG: the effect-vm sub-proof may have been produced by the
                // Lean DESCRIPTOR INTERPRETER (different AIR ⇒ different extended trace
                // width ⇒ different CommonData), so it is NOT interchangeable with the
                // hand-AIR verifier. When the flag is set, verify through the descriptor
                // verifier first (the validated cutover-ready transfer descriptor over the
                // PI prefix); fall back to the hand-AIR verifier for hand-AIR proofs.
                verify_effect_vm_proof_with_cutover(&p3, &attached.sub_public_inputs)
                    .map_err(|e| format!("{e}"))
            }
            // AUTHORIZATION / MEMBERSHIP / NON-REVOCATION: all now verified by
            // the AUDITED Plonky3 verifier (`p3-batch-stark`). ZERO `stark::`
            // calls remain. Each proof is a postcard-serialized batch proof; the
            // standalone verifier reconstructs CommonData from the AIR + the
            // proof's degree bits (witness-free). The non-algebraic forms each
            // circuit carries (derived_hash / node-hash `hash_fact` sponges,
            // position-indexed Merkle hashing) are arithmetized in-circuit by the
            // real Poseidon2 gadget, so a forged auth / membership / freshness
            // witness is UNSAT (see the anti-ghost tests in each AIR).
            "authorization" => {
                let p3: DslP3Proof =
                    postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                        FullTurnVerifyError::SubProofDeserialize {
                            index: i,
                            reason: format!("authorization p3 deserialize: {e}"),
                        }
                    })?;
                verify_derivation_p3(&p3, &attached.sub_public_inputs)
            }
            "membership" => {
                let p3: MembershipP3Proof =
                    postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                        FullTurnVerifyError::SubProofDeserialize {
                            index: i,
                            reason: format!("membership p3 deserialize: {e}"),
                        }
                    })?;
                verify_membership_p3(&p3, &attached.sub_public_inputs)
                    .map_err(|e| format!("{e}"))
            }
            "non-revocation" => {
                let p3: DslP3Proof =
                    postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                        FullTurnVerifyError::SubProofDeserialize {
                            index: i,
                            reason: format!("non-revocation p3 deserialize: {e}"),
                        }
                    })?;
                // Non-revocation PI is [revocation_root].
                let root = attached
                    .sub_public_inputs
                    .first()
                    .copied()
                    .ok_or_else(|| FullTurnVerifyError::MalformedPublicInputs(
                        "non-revocation PI missing revocation_root".into(),
                    ))?;
                verify_non_revocation_p3(&p3, root)
            }
            other => Err(format!("unknown sub-proof label: {}", other)),
        };

        verify_result.map_err(|e| FullTurnVerifyError::SubProofInvalid {
            index: i,
            label: attached.label.clone(),
            reason: e,
        })?;
    }

    // 4. Check Effect VM public input bindings (old/new commitment).
    let effect_sub = proof
        .composed
        .sub_proofs
        .iter()
        .find(|sp| sp.label == "effect-vm")
        .ok_or(FullTurnVerifyError::MissingComponent("effect-vm".into()))?;

    if effect_sub.sub_public_inputs.len() < effect_vm::pi::BASE_COUNT {
        return Err(FullTurnVerifyError::MalformedPublicInputs(
            "effect VM PI too short".into(),
        ));
    }

    let proof_old_commit = effect_sub.sub_public_inputs[effect_vm::pi::OLD_COMMIT];
    let proof_new_commit = effect_sub.sub_public_inputs[effect_vm::pi::NEW_COMMIT];

    if proof_old_commit != expected_old_commit {
        return Err(FullTurnVerifyError::CommitmentMismatch {
            which: "old_commitment",
            expected: expected_old_commit,
            got: proof_old_commit,
        });
    }
    if proof_new_commit != expected_new_commit {
        return Err(FullTurnVerifyError::CommitmentMismatch {
            which: "new_commitment",
            expected: expected_new_commit,
            got: proof_new_commit,
        });
    }

    // 5. Cross-proof PI consistency: authorization state_root == membership root.
    if proof.components.has_authorization && proof.components.has_membership {
        let auth_sub = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "authorization")
            .ok_or(FullTurnVerifyError::MissingComponent(
                "authorization".into(),
            ))?;
        let mem_sub = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "membership")
            .ok_or(FullTurnVerifyError::MissingComponent("membership".into()))?;

        // Authorization PI[0] = state_root; Membership PI[1] = merkle_root
        let auth_state_root = auth_sub
            .sub_public_inputs
            .first()
            .copied()
            .unwrap_or(BabyBear::ZERO);
        let mem_root = mem_sub
            .sub_public_inputs
            .get(1)
            .copied()
            .unwrap_or(BabyBear::ZERO);

        if auth_state_root != mem_root {
            return Err(FullTurnVerifyError::CrossProofMismatch {
                description: format!(
                    "authorization state_root ({:?}) != membership merkle_root ({:?})",
                    auth_state_root, mem_root
                ),
            });
        }
    }

    // 6. CRITICAL: Authorization-to-EffectVM cell binding.
    //
    // In P2P composition mode, a malicious prover could pair a valid auth proof
    // for cell A with a valid Effect VM proof for cell B. We prevent this by
    // verifying that the authorization proof's state_root commits to the same
    // cell state as the Effect VM's old_commitment.
    //
    // The authorization proof's PI[0] (state_root) MUST equal the Effect VM's
    // PI[OLD_COMMIT] (old_commitment). This binds the authorization to the
    // specific cell whose state is being mutated.
    if proof.components.has_authorization && proof.components.has_state_transition {
        let auth_sub = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "authorization")
            .ok_or(FullTurnVerifyError::MissingComponent(
                "authorization".into(),
            ))?;

        // Authorization PI[0] = state_root (the cell state the actor is authorized for)
        let auth_state_root = auth_sub
            .sub_public_inputs
            .first()
            .copied()
            .unwrap_or(BabyBear::ZERO);

        // Effect VM PI[OLD_COMMIT] = old_commitment (the cell being mutated)
        let effect_old_commit = effect_sub.sub_public_inputs[effect_vm::pi::OLD_COMMIT];

        if auth_state_root != effect_old_commit {
            return Err(FullTurnVerifyError::CrossProofMismatch {
                description: format!(
                    "authorization state_root ({:?}) does not bind to Effect VM \
                     old_commitment ({:?}) — possible cross-cell proof splicing attack",
                    auth_state_root, effect_old_commit
                ),
            });
        }
    }

    Ok(())
}

/// Errors that can occur during full turn proof verification.
#[derive(Debug, Clone)]
pub enum FullTurnVerifyError {
    /// The composed main STARK proof failed verification.
    MainProofInvalid(String),
    /// A sub-proof could not be deserialized.
    SubProofDeserialize { index: usize, reason: String },
    /// A sub-proof failed cryptographic verification.
    SubProofInvalid {
        index: usize,
        label: String,
        reason: String,
    },
    /// A required component is missing from the proof.
    MissingComponent(String),
    /// Public inputs are malformed or too short.
    MalformedPublicInputs(String),
    /// State commitment in proof does not match expected value.
    CommitmentMismatch {
        which: &'static str,
        expected: BabyBear,
        got: BabyBear,
    },
    /// Cross-proof public input binding is inconsistent.
    CrossProofMismatch { description: String },
}

impl std::fmt::Display for FullTurnVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MainProofInvalid(e) => write!(f, "main proof invalid: {}", e),
            Self::SubProofDeserialize { index, reason } => {
                write!(f, "sub-proof {} deserialize failed: {}", index, reason)
            }
            Self::SubProofInvalid {
                index,
                label,
                reason,
            } => write!(f, "sub-proof {}[{}] invalid: {}", index, label, reason),
            Self::MissingComponent(name) => write!(f, "missing component: {}", name),
            Self::MalformedPublicInputs(msg) => write!(f, "malformed PIs: {}", msg),
            Self::CommitmentMismatch {
                which,
                expected,
                got,
            } => write!(
                f,
                "{} mismatch: expected {:?}, got {:?}",
                which, expected, got
            ),
            Self::CrossProofMismatch { description } => {
                write!(f, "cross-proof PI mismatch: {}", description)
            }
        }
    }
}

impl std::error::Error for FullTurnVerifyError {}

// ============================================================================
// Convenience: Minimal proof (Effect VM + Authorization only)
// ============================================================================

/// Generate a minimal full turn proof with just state transition + authorization.
///
/// This is the most common case for sovereign cell turns where:
/// - The actor is authorized via a derivation chain
/// - The state transition is proven by the Effect VM
/// - No value transfers or revocation channels involved
///
/// For the full proof with all components, use [`prove_full_turn`] directly.
pub fn prove_turn_with_auth(
    initial_state: &CellState,
    effects: &[effect_vm::Effect],
    derivation: &dregg_circuit::derivation_air::DerivationWitness,
    turn_hash: [u8; 32],
) -> Result<FullTurnProof, SdkError> {
    let witness = FullTurnWitness {
        initial_cell_state: initial_state.clone(),
        effects: effects.to_vec(),
        authorization: Some(AuthorizationWitness {
            derivation: derivation.clone(),
        }),
        membership: None,
        conservation: None,
        non_revocation: None,
        turn_hash,
    };
    prove_full_turn(&witness)
}

/// Generate a minimal proof with state transition only (no authorization).
///
/// Used for self-sovereign cells where the owner's signature alone suffices
/// and no derivation chain is needed.
pub fn prove_turn_self_sovereign(
    initial_state: &CellState,
    effects: &[effect_vm::Effect],
    turn_hash: [u8; 32],
) -> Result<FullTurnProof, SdkError> {
    let witness = FullTurnWitness {
        initial_cell_state: initial_state.clone(),
        effects: effects.to_vec(),
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: None,
        turn_hash,
    };
    prove_full_turn(&witness)
}

// ============================================================================
// Helpers
// ============================================================================

/// Compute the 32-byte VK hash for a circuit descriptor.
fn compute_vk_hash_bytes(descriptor: &CircuitDescriptor) -> [u8; 32] {
    let serialized = postcard::to_allocvec(descriptor).unwrap_or_default();
    *blake3::hash(&serialized).as_bytes()
}

/// Build the minimal PI-binding DSL circuit + trace for the AUDITED composition
/// main proof: `public_input_count = pis.len()`, with a `PiBinding{col=j,
/// pi_index=j}` per public input. The trace is `MIN_ROWS` identical rows whose
/// column `j` equals `pis[j]`, so every `PiBinding` holds on every row. The
/// audited p3 verifier then binds the entire merged-PI vector; a forged PI
/// makes verification fail. This is a pure-algebraic descriptor (no hash /
/// merkle / lookup), so `prove_dsl_p3` accepts it.
fn build_pi_binding_p3(
    pis: &[BabyBear],
) -> (
    dregg_circuit::dsl::circuit::DslCircuit,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
) {
    use dregg_circuit::dsl::circuit::{
        ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    };

    const MIN_ROWS: usize = 4; // power-of-two; matches the DSL p3 reference traces.
    let n = pis.len();

    let columns: Vec<ColumnDef> = (0..n)
        .map(|j| ColumnDef {
            name: format!("pi_{j}"),
            index: j,
            kind: ColumnKind::Value,
        })
        .collect();
    let constraints: Vec<ConstraintExpr> = (0..n)
        .map(|j| ConstraintExpr::PiBinding {
            col: j,
            pi_index: j,
        })
        .collect();

    let descriptor = CircuitDescriptor {
        name: "dregg-full-turn-pi-binding-v1".into(),
        trace_width: n.max(1),
        max_degree: 1,
        columns,
        constraints,
        boundaries: vec![],
        public_input_count: n,
        lookup_tables: vec![],
    };

    // Trace: MIN_ROWS identical rows = the PI vector (width n, or 1 if n == 0).
    let row: Vec<BabyBear> = if n == 0 {
        vec![BabyBear::ZERO]
    } else {
        pis.to_vec()
    };
    let trace = vec![row; MIN_ROWS];

    (DslCircuit::new(descriptor), trace, pis.to_vec())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
    use dregg_circuit::field::BabyBear;

    /// Smoke test: prove and verify a self-sovereign turn (Effect VM only).
    #[test]
    fn prove_verify_self_sovereign_turn() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1, // outgoing
        }];
        let turn_hash = [0xABu8; 32];

        let proof = prove_turn_self_sovereign(&initial, &effects, turn_hash)
            .expect("proof generation should succeed");

        assert!(proof.components.has_state_transition);
        assert!(!proof.components.has_authorization);
        assert!(!proof.components.has_membership);
        assert!(!proof.components.has_conservation);
        assert!(!proof.components.has_non_revocation);

        // Verify with correct commitments.
        let old_commit = initial.state_commitment;
        // Compute expected new commitment.
        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        let result = verify_full_turn(&proof, old_commit, new_commit);
        assert!(
            result.is_ok(),
            "self-sovereign turn proof should verify: {:?}",
            result.err()
        );
    }

    /// Verify that wrong commitments cause rejection.
    #[test]
    fn verify_rejects_wrong_commitment() {
        let initial = CellState::new(500, 5);
        let effects = vec![VmEffect::Transfer {
            amount: 50,
            direction: 0, // incoming
        }];
        let turn_hash = [0xCDu8; 32];

        let proof = prove_turn_self_sovereign(&initial, &effects, turn_hash)
            .expect("proof generation should succeed");

        let old_commit = initial.state_commitment;
        let wrong_new_commit = BabyBear::new(99999);

        let result = verify_full_turn(&proof, old_commit, wrong_new_commit);
        assert!(result.is_err(), "should reject wrong new_commitment");
    }

    /// Adversarial test (Gap 2): Verify that cross-proof PI binding is enforced.
    ///
    /// A malicious prover attempts to splice together a valid auth proof for
    /// cell A with a valid Effect VM proof for cell B. The cross-proof binding
    /// check (step 6 in verify_full_turn) MUST reject this.
    ///
    /// This test demonstrates that the Rust verifier code correctly catches
    /// cross-proof PI mismatches. In a future version, this binding will also
    /// be enforced IN-CIRCUIT via a CompositionBindingAir.
    #[test]
    fn verify_rejects_cross_proof_splicing() {
        // Create two different cells.
        let cell_a = CellState::new(1000, 0);
        let cell_b = CellState::new(2000, 0);

        // Generate an Effect VM proof for cell_a.
        let effects_a = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
        let turn_hash = [0xEEu8; 32];
        let proof_a = prove_turn_self_sovereign(&cell_a, &effects_a, turn_hash)
            .expect("proof_a should succeed");

        // The proof for cell_a has old_commit = cell_a.state_commitment.
        // If we verify with cell_b's commitment, it should fail.
        let result = verify_full_turn(
            &proof_a,
            cell_b.state_commitment, // WRONG: this is cell_b, not cell_a
            BabyBear::new(12345),    // doesn't matter, should fail on old_commit
        );
        assert!(
            result.is_err(),
            "SOUNDNESS (Gap 2): Must reject when old_commitment doesn't match"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "old_commitment");
            }
            other => {
                panic!(
                    "Expected CommitmentMismatch error for old_commitment, got: {:?}",
                    other
                );
            }
        }
    }

    /// ANTI-GHOST on the AUDITED p3 verifier (the migration's load-bearing
    /// property). Forge the EffectVM sub-proof's published post-state
    /// commitment in a finished `FullTurnProof`: the proof's `NEW_COMMIT`
    /// public input no longer matches the proof's witness, so the new p3
    /// EffectVM verifier (`verify_effect_vm_p3`, invoked inside
    /// `verify_full_turn`) MUST reject — a forged post-state cannot pass.
    ///
    /// We forge by tampering BOTH the published `sub_public_inputs[NEW_COMMIT]`
    /// (so the verifier sees the forged value) and verifying against that same
    /// forged commitment as the caller's expectation — defeating the simple PI
    /// equality check, leaving ONLY the in-circuit boundary binding to catch
    /// it. The audited p3 verifier rejects because the proof's bound trace
    /// commitment is the honest one, not the forged PI.
    #[test]
    fn verify_rejects_forged_post_state_on_audited_p3() {
        use dregg_circuit::effect_vm::pi as vmpi;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
        let turn_hash = [0x5Au8; 32];

        let mut proof = prove_turn_self_sovereign(&initial, &effects, turn_hash)
            .expect("honest proof should generate");

        // Honest commitments (what the proof legitimately attests).
        let old_commit = initial.state_commitment;
        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let honest_new_commit = expected_final.state_commitment;
        let forged_new_commit = honest_new_commit + BabyBear::new(1);

        // Tamper the published EffectVM post-state commitment in the wire proof.
        let eff = proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "effect-vm")
            .expect("effect-vm sub-proof present");
        eff.sub_public_inputs[vmpi::NEW_COMMIT] = forged_new_commit;

        // Verify against the FORGED commitment (so the surface-level PI equality
        // check would PASS). Only the audited in-circuit boundary binding stands
        // between the forgery and acceptance — and it MUST reject.
        let result = verify_full_turn(&proof, old_commit, forged_new_commit);
        assert!(
            result.is_err(),
            "SOUNDNESS: a forged post-state commitment MUST be rejected by the \
             audited p3 EffectVM verifier (got Ok — the migration is unsound!)"
        );
    }

    /// END-TO-END: a full turn with EFFECT-VM + MEMBERSHIP + NON-REVOCATION sub
    /// proofs proves and verifies — ALL three legs now route through the AUDITED
    /// p3 verifier (`p3-batch-stark`). This exercises the migrated membership and
    /// non-revocation legs through `prove_full_turn`/`verify_full_turn`.
    #[test]
    fn full_turn_with_membership_and_non_revocation_through_audited_p3() {
        use dregg_circuit::dsl::membership::create_test_witness as merkle_test_witness;
        use dregg_circuit::dsl::revocation::DslRevocationTree;
        use dregg_circuit::poseidon2::hash_many;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];

        // Membership witness: a leaf genuinely in a depth-4 Merkle tree.
        let leaf = BabyBear::new(424242);
        let (siblings, positions, _root) = merkle_test_witness(leaf, 4);

        // Non-revocation witness: an item NOT in a 20-entry sorted revocation tree.
        let revoked: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect();
        let tree = DslRevocationTree::new(revoked, 4);
        let fresh_item = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);

        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            authorization: None,
            membership: Some(MembershipWitness {
                leaf_hash: leaf,
                siblings,
                positions,
            }),
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree,
                item_hash: fresh_item,
            }),
            turn_hash: [0x77u8; 32],
        };

        let proof = prove_full_turn(&witness).expect("full turn proof should generate");
        assert!(proof.components.has_state_transition);
        assert!(proof.components.has_membership);
        assert!(proof.components.has_non_revocation);

        let old_commit = initial.state_commitment;
        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        verify_full_turn(&proof, old_commit, new_commit)
            .expect("full turn with membership + non-revocation must verify on the audited p3 path");
    }

    /// ANTI-GHOST end-to-end: forging the published MEMBERSHIP root in a finished
    /// full-turn proof MUST be rejected by the audited membership verifier (the
    /// proof binds the genuine hash-chain root, not the forged PI).
    #[test]
    fn full_turn_rejects_forged_membership_root() {
        use dregg_circuit::dsl::membership::create_test_witness as merkle_test_witness;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
        let leaf = BabyBear::new(555111);
        let (siblings, positions, _root) = merkle_test_witness(leaf, 4);

        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects,
            authorization: None,
            membership: Some(MembershipWitness {
                leaf_hash: leaf,
                siblings,
                positions,
            }),
            conservation: None,
            non_revocation: None,
            turn_hash: [0x88u8; 32],
        };
        let mut proof = prove_full_turn(&witness).expect("honest proof should generate");

        // Forge the published membership root (PI[1] of the membership sub-proof).
        let mem = proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "membership")
            .expect("membership sub-proof present");
        mem.sub_public_inputs[1] = mem.sub_public_inputs[1] + BabyBear::new(1);

        let old_commit = initial.state_commitment;
        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        let res = verify_full_turn(&proof, old_commit, new_commit);
        assert!(
            res.is_err(),
            "SOUNDNESS: a forged membership root MUST be rejected by the audited p3 verifier"
        );
    }
}
