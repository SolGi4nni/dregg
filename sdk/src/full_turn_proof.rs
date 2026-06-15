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
//! - Authorization derived_hash == Allow(effects_hash): the authorization
//!   conclusion is bound to THIS turn's effects (effect-kind + cell + params),
//!   not merely to "some fact in this cell's tree" (see [`effect_action_binding`])
//! - Non-revocation root matches the federation's published revocation accumulator

use dregg_circuit::cap_root::CapLeaf;
use dregg_circuit::dsl::cap_membership::{
    cap_membership_circuit_descriptor, prove_cap_membership_p3, verify_cap_membership_p3,
};
use dregg_circuit::dsl::derivation::{
    derivation_circuit_descriptor, prove_derivation_p3, verify_derivation_p3,
};
use dregg_circuit::dsl::dsl_p3_air::DslP3Proof;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::dsl::revocation::{
    DslRevocationTree, non_revocation_circuit_descriptor, prove_non_revocation_p3,
    verify_non_revocation_p3,
};
use dregg_circuit::effect_vm::{self, CellState, Effect as VmEffectKind, generate_effect_vm_trace};
// The v1 hand-AIR EffectVM proof type + prover/verifier. The `effect_vm_p3_full_air` module is
// `#[cfg(not(feature = "recursion"))]` in `dregg-circuit` (v1 floor only), and every use-site here
// (`prove_effect_vm_with_cutover`, `verify_effect_vm_proof_with_cutover`, the `"effect-vm"` verify
// arm, the v1 prove leg, `revalidate_turn_self_sovereign`) is likewise `not(recursion)`-gated — the
// recursion tower proves/verifies rotated IR-v2. So this import must match.
#[cfg(not(feature = "recursion"))]
use dregg_circuit::effect_vm_p3_full_air::{
    EffectVmP3Proof, prove_effect_vm_p3, verify_effect_vm_p3,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::merkle_air::{
    MembershipP3Proof, membership_public_inputs, prove_membership_p3, verify_membership_p3,
};
use dregg_circuit::multi_step_air::ALLOW_PREDICATE;
use dregg_circuit::poseidon2::hash_fact;
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
    /// Cap-membership proof (cap Phase D): the CONSUMED capability's 7-field
    /// leaf is a member of the holder's pre-state openable `capability_root`
    /// (the sorted-Poseidon2 tree of cap Phase A). `serde(default)` keeps
    /// pre-Phase-D wire proofs deserializable (they carry no cap leg).
    #[serde(default)]
    pub has_cap_membership: bool,
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

    // -- Cap-membership witness (cap Phase D) --
    /// Present for a capability-gated turn: the CONSUMED capability's leaf
    /// preimage + sorted-Merkle path against the holder's pre-state
    /// `capability_root` (from the Phase-C
    /// `TurnReceipt::consumed_capabilities` witness).
    pub cap_membership: Option<CapMembershipWitness>,

    /// The turn hash for binding (prevents proof replay on different turns).
    pub turn_hash: [u8; 32],

    // -- ROTATION witness (C4 cutover, the rotated effect-vm leg) --
    /// Present when the caller has threaded the per-turn rotation producer witnesses for the
    /// acting cell's before/after `RecordKernelState`. When present (and `recursion` is on),
    /// [`prove_full_turn`] proves the effect-vm leg through the ROTATED IR-v2 path
    /// ([`prove_effect_vm_rotated_ir2_with_caveat`]) and attaches it as the `"effect-vm-rotated"`
    /// sub-proof (a multi-table `Ir2BatchProof`); [`verify_full_turn`] verifies it via
    /// `descriptor_ir2::verify_vm_descriptor2`. When ABSENT (or under `not(recursion)`), the
    /// byte-identical v1 `"effect-vm"` leg is used — so pre-rotation callers are unaffected.
    ///
    /// NOT feature-gated: its types are always-available (`RotationWitness` from `dregg-turn`,
    /// `RotatedCaveatManifest` from `dregg-circuit::effect_vm::trace_rotated`), so downstream
    /// crates without their own `recursion` feature (e.g. `dregg-node`) set `rotation: None`
    /// unconditionally. Only the rotated PROVE/VERIFY code is `recursion`-gated; under
    /// `not(recursion)` a present `rotation` is ignored (the v1 leg runs).
    pub rotation: Option<RotationTurnWitness>,
}

/// The per-turn rotation witnesses + caveat manifest for the rotated effect-vm leg of a full
/// turn. The producer witnesses are minted by
/// `dregg_turn::rotation_witness::produce(cell, ledger, nullifier_root, receipt_log)` for the
/// acting cell's before/after `RecordKernelState`; the caveat manifest defaults to the empty
/// (non-transfer) manifest.
pub struct RotationTurnWitness {
    /// The acting cell's BEFORE-state rotation producer witness.
    pub before: dregg_turn::rotation_witness::RotationWitness,
    /// The acting cell's AFTER-state rotation producer witness.
    pub after: dregg_turn::rotation_witness::RotationWitness,
    /// The rotated caveat manifest (the transfer reference manifest for a single transfer;
    /// the empty manifest otherwise). Defaults via [`RotationTurnWitness::for_effects`].
    pub caveat: dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
}

impl RotationTurnWitness {
    /// Build with the caveat manifest defaulted by the turn's effects (transfer → the
    /// two-domain reference manifest; everything else → empty), matching the standalone
    /// `prove_effect_vm_rotated_ir2`.
    pub fn for_effects(
        before: dregg_turn::rotation_witness::RotationWitness,
        after: dregg_turn::rotation_witness::RotationWitness,
        effects: &[VmEffectKind],
    ) -> Self {
        use dregg_circuit::effect_vm::trace_rotated::{
            empty_caveat_manifest, transfer_caveat_manifest,
        };
        let caveat = match effects {
            [VmEffectKind::Transfer { .. }] => transfer_caveat_manifest(),
            _ => empty_caveat_manifest(),
        };
        Self {
            before,
            after,
            caveat,
        }
    }

    /// PATH-PRESERVE §4 (the non-synthetic-cell lift): reconstruct the Effect-VM `CellState`
    /// that seeds `initial_vm_state` from THIS witness's BEFORE-block producer limbs, so the v1
    /// prefix the rotated generator emits (`generate_effect_vm_trace(initial_state, …)`, whose
    /// `pi[OLD_COMMIT]` the verifier pins to `expected_old_commit`) and the rotated leg's welded
    /// scalars (`fill_block` overrides `r0..r10`/`cap_root` from THAT v1 state block,
    /// `trace_rotated.rs:294-307`) are derived from the SAME felts — so OLD_COMMIT agrees with
    /// the real (field-bearing / cap-holding) cell BY CONSTRUCTION (§4.2).
    ///
    /// The welded limbs are read straight off `before.pre_limbs` in the Lean-pinned order
    /// (`rotation_witness.rs:260-290`): `r0 = pre_limbs[1]` (balance_lo) · `r1 = pre_limbs[2]`
    /// (nonce) · `r2 = pre_limbs[3]` (balance_hi) · `r3..r10 = pre_limbs[4..12]` (fields[0..8],
    /// already `fold_bytes32_to_bb`'d — copied verbatim, the same value the v1 state block
    /// carries) · `cap_root = pre_limbs[B_CAP_ROOT]` (the canonical openable root). The
    /// authority-bearing residue (permissions/VK/delegate/program/mode + fields[8..16]) rides
    /// the witness-carried authority digest `r23` in the rotated commit — it is NOT part of the
    /// v1-prefix `compute_commitment` (which hashes only balance/nonce/fields[0..8]/cap_root), so
    /// the EffectVm `CellState` losslessly holds everything OLD_COMMIT binds. `sealed_field_mask`
    /// / `mode_flag` do not enter `compute_commitment` either; left at 0 (their only trace home is
    /// the v1 `RESERVED` column, which OLD_COMMIT does not absorb and the rotated weld carries via
    /// r23).
    pub fn before_cell_state(&self) -> Result<CellState, SdkError> {
        use dregg_circuit::effect_vm::trace_rotated::B_CAP_ROOT;
        let pre = &self.before.pre_limbs;
        // The before-block must carry the full pre-iroot limb vector (the rotated generator
        // requires it too). Guard so a malformed witness is a loud `InvalidWitness`, not a panic.
        if pre.len() <= B_CAP_ROOT {
            return Err(SdkError::InvalidWitness(format!(
                "rotation before-witness has {} pre-limbs, need > {B_CAP_ROOT} to seed \
                 initial_vm_state",
                pre.len()
            )));
        }
        // balance: invert `split_u64` (lo = low 30 bits, hi = val >> 30) on the welded limbs.
        let lo = pre[1].0 as u64;
        let hi = pre[3].0 as u64;
        let balance = lo | (hi << 30);
        let nonce = pre[2].0;
        let mut fields = [BabyBear::ZERO; 8];
        for (i, f) in fields.iter_mut().enumerate() {
            *f = pre[4 + i]; // r3..r10 — the already-folded field felts, verbatim.
        }
        let capability_root = pre[B_CAP_ROOT];
        let mut s = CellState {
            balance,
            nonce,
            fields,
            capability_root,
            state_commitment: BabyBear::ZERO,
            sealed_field_mask: 0,
            mode_flag: 0,
        };
        s.refresh_commitment();
        Ok(s)
    }
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

/// Cap-membership witness (cap Phase D): the CONSUMED capability's full
/// 7-field leaf preimage + sorted-Merkle membership path against the holder's
/// pre-state openable `capability_root`. The prover side of the AUTHORITY leg;
/// the Phase-C executor witness ([`dregg_turn::ConsumedCapWitness`]) carries
/// exactly this data — see [`CapMembershipWitness::from_consumed`].
pub struct CapMembershipWitness {
    /// The consumed capability's canonical 7-field leaf preimage.
    pub leaf: CapLeaf,
    /// Sibling digests along the membership path, bottom-up
    /// (`CAP_TREE_DEPTH` entries).
    pub siblings: Vec<BabyBear>,
    /// Direction bits (0 = current node is the LEFT child, 1 = right).
    pub directions: Vec<u8>,
}

impl CapMembershipWitness {
    /// Build from the Phase-C executor witness threaded through
    /// `TurnReceipt::consumed_capabilities`.
    pub fn from_consumed(w: &dregg_turn::ConsumedCapWitness) -> Self {
        Self {
            leaf: w.cap_leaf(),
            siblings: w.siblings.iter().map(|&s| BabyBear::new(s)).collect(),
            directions: w.directions.clone(),
        }
    }
}

/// What the VERIFIER expects the cap-membership leg to attest (cap Phase D —
/// the AUTHORITY binding). Mirrors the freshness close's
/// `expected_revocation_root`: both fields are recomputed by the verifier from
/// data it trusts (the canonical pre-state c-list / the hash-bound receipt
/// witness), never taken from the proof.
pub struct CapMembershipExpectation {
    /// The consumed capability's leaf preimage AS DISCLOSED in the receipt
    /// (`ConsumedCapWitness` leaf fields, bound by `receipt_hash` v3). The
    /// verifier recomputes its 7-field Poseidon2 digest and pins the leg's
    /// `pi[LEAF_DIGEST]` to it — so the proven member IS the disclosed
    /// capability (an inflated-mask tamper mismatches).
    pub leaf: CapLeaf,
    /// The holder's CANONICAL pre-state `capability_root` (the same value the
    /// EffectVm row's `cap_root` column is seeded from — cap Phase A). The
    /// verifier pins the leg's `pi[CAP_ROOT]` to it — so membership is in THE
    /// holder's real c-list tree, not a prover-chosen one.
    pub cap_root: BabyBear,
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

    // Cap-membership (consumed capability ∈ openable capability_root).
    if components.has_cap_membership {
        circuits.push(cap_membership_circuit_descriptor());
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
    // The Effect VM has 61 columns, degree 9, and ACTIVE_BASE_COUNT public inputs
    // in the PI v3 layout.
    // We create a minimal descriptor that captures its identity for VK hashing.
    CircuitDescriptor {
        name: "dregg-effect-vm-v1".into(),
        trace_width: effect_vm::EFFECT_VM_WIDTH,
        max_degree: 9,
        columns: vec![],     // Not needed for composition — VK hash suffices
        constraints: vec![], // Constraints are in the StarkAir impl
        boundaries: vec![],  // Boundaries are in the StarkAir impl
        public_input_count: effect_vm::pi::ACTIVE_BASE_COUNT,
        lookup_tables: vec![],
    }
}

// ============================================================================
// Authorization ⟷ effect binding (the capability-security weld)
// ============================================================================

/// The canonical "this actor may perform THIS effect" fact hash for a turn.
///
/// This is the fact that a verifying authorization sub-proof MUST conclude for
/// its derivation to authorize the turn's state transition. It is
/// `hash_fact(ALLOW_PREDICATE, [effects_commit, 0, 0, 0])` where `effects_commit`
/// is position 0 of the Effect-VM 4-felt effects hash — i.e.
/// `compute_effects_hash(effects).0`.
///
/// # Why this is a real binding (not a loose check)
///
/// `effects_commit` is `PI[EFFECTS_HASH_BASE]` of the Effect-VM proof, which the
/// Effect-VM AIR pins **in-circuit** to the Poseidon2-chained effects column via
/// a row-0 boundary constraint (`effect_vm/air.rs` "Effects hash binding"). A
/// forged effects commitment makes the audited Effect-VM verifier reject. The
/// authorization proof's `derived_hash` (auth PI[1]) is pinned **in-circuit** to
/// `hash_fact(HEAD_PRED, HEAD_TERM[0..4])` by the derivation circuit's C4/C6
/// (`dsl/derivation.rs`). Requiring `auth.derived_hash == effect_action_binding(effects)`
/// therefore welds the two audited proofs: the authorization conclusion must
/// commit to exactly the effects the Effect-VM proof certifies. An authorization
/// proof whose conclusion is for a DIFFERENT effect (different kind / target
/// cell / amount / params ⇒ different `effects_commit`) produces a different
/// `derived_hash` and is rejected by [`verify_full_turn`].
///
/// We bind position 0 of the effects hash (the AIR-boundary-bound element)
/// rather than the full 4-felt form because, in the composed-turn verify path,
/// only position 0 is enforced in-circuit by the audited Effect-VM verifier;
/// positions 1..3 are the Effect-VM PI-matching-loop's responsibility (off-AIR,
/// not run here) — see `AUDIT[stage1-pi-only-bound]` in `effect_vm::pi`. Binding
/// the off-AIR positions here would not be cryptographically enforced, so we
/// bind the one element that is.
pub fn effect_action_binding(effects: &[effect_vm::Effect]) -> BabyBear {
    let effects_commit = effect_vm::compute_effects_hash(effects).0;
    hash_fact(
        BabyBear::new(ALLOW_PREDICATE),
        &[
            effects_commit,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    )
}

/// Reconstruct the expected [`effect_action_binding`] directly from the Effect-VM
/// sub-proof's published public inputs (verifier side — the effect list is not
/// transmitted, but its AIR-bound commitment is `PI[EFFECTS_HASH_BASE]`).
///
/// This is the verifier twin of [`effect_action_binding`]: the prover binds the
/// authorization conclusion to `effect_action_binding(effects)`, and the verifier
/// recomputes the same value from the in-circuit-bound effects commitment carried
/// in the Effect-VM PIs, without needing the plaintext effects.
fn effect_action_binding_from_effect_pi(effect_pi: &[BabyBear]) -> BabyBear {
    let effects_commit = effect_pi[effect_vm::pi::EFFECTS_HASH_BASE];
    hash_fact(
        BabyBear::new(ALLOW_PREDICATE),
        &[
            effects_commit,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    )
}

/// Index of `derived_hash` in the authorization sub-proof's public-input vector.
/// Layout (see `prove_full_turn`): `[state_root, derived_hash, not_after, org_id, budget]`.
const AUTH_PI_DERIVED_HASH: usize = 1;

// ============================================================================
// Effect-VM prover selection: Lean descriptor interpreter (DEFAULT) vs hand-AIR.
// ============================================================================
//
// THE CUTOVER (default ON): the Effect-VM state-transition proof routes through the
// verified-by-construction Lean DESCRIPTOR INTERPRETER (`EffectVmDescriptorAir`, fed the
// byte-exact Lean-emitted descriptor JSON from the `effect_vm_descriptors` registry)
// for every turn shape the differential harness has GRADUATED
// (`circuit/tests/effect_vm_descriptor_cutover_harness.rs`: descriptor ⟺ hand-AIR proven
// IDENTICAL on the real witness, honest accept + anti-ghost reject, selector-bound). The
// proof is the SAME wire type (`BatchProof<DreggStarkConfig>` = `EffectVmP3Proof`), so the
// composed proof + verifier are unchanged.
//
// `DREGG_DESCRIPTOR_PROVER=0` is the OPT-OUT: it forces the legacy hand-written
// `EffectVmP3Air` prover for comparison runs. The env var affects ONLY the prover;
// verification is SHAPE-DRIVEN and accepts proofs from either engine regardless of the
// flag (see `verify_effect_vm_proof_with_cutover`).
//
// Non-graduated shapes (the DEEPER divergence selectors, the no-descriptor selectors,
// heterogeneous multi-effect turns, the PI-slot multi-instance shapes) FALL BACK to the
// hand-AIR automatically, each with a NAMED, logged reason (`CutoverFallback`) — never a
// silent len check. Routing never changes the proven semantics; it only swaps the prover
// for the validated shapes.

/// Is the descriptor-interpreter cutover prover enabled? DEFAULT ON.
/// `DREGG_DESCRIPTOR_PROVER=0` (or `false`/`off`) is the opt-OUT that forces the legacy
/// hand-AIR prover for comparison. (v1 floor only; the recursion tower proves rotated IR-v2.)
#[cfg(not(feature = "recursion"))]
fn descriptor_prover_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_DESCRIPTOR_PROVER").as_deref(),
        Ok("0") | Ok("false") | Ok("FALSE") | Ok("False") | Ok("off") | Ok("OFF")
    )
}

/// The graduated descriptor selector for ONE effect, or `None` if the effect's selector
/// has not graduated the differential harness (DEEPER divergence / no descriptor).
///
/// The graduated set (23 selectors, `enumerate_all_descriptor_divergences` AGREE):
/// `Transfer` (1), the full-economic effects `NoteSpend` (4) / `NoteCreate` (5) /
/// `BridgeMint` (40) / `Burn` (46), the observation-log `EmitEvent` (25), the
/// frozen-frame + nonce-tick effects `SetPermissions` (26), `SetVerificationKey` (27),
/// `RefreshDelegation` (29), `RevokeDelegation` (30), `ExerciseViaCapability` (34),
/// `Introduce` (35), `PipelinedSend` (36), `CellDestroy` (47), `CellSeal` (49),
/// `Refusal` (52), `IncrementNonce` (53), the lifecycle/birth family `CreateCell` (31) /
/// `SpawnWithDelegation` (32) / `CreateCellFromFactory` (13) (the wire descriptor is the
/// ACTING cell's frozen-frame+tick row; the born-empty CHILD faces stay verified in
/// their Lean modules as named off-row stories), `ReceiptArchive` (51) (frozen-frame +
/// tick; the lifecycle write is off-row), `MakeSovereign` (12) (frame-freeze +
/// RESERVED +256 mode-bit + tick), and `CellUnseal` (50) (frozen-frame + tick, the
/// cellSeal row shape; the Sealed→Live flip is off-row). Their off-trace semantics
/// (cap-table moves, lifecycle/audit/VK writes, the event log, the born-empty child)
/// are bound OFF-row by each Lean module's proven connector.
///
/// NOT graduated (the automatic hand-AIR fallback, each a named census entry):
/// the cap-reshape family `GrantCapability` (3) / `AttenuateCapability` (48) (the
/// descriptor DSL lacks the Merkle-membership + lattice-table constraint kinds of cap
/// Phase B — reserved for the cap-crown lanes), and the no-descriptor selectors
/// `SetField` (2) (the Lean module emits a PER-SLOT family `setFieldVmDescriptor
/// (slot : Fin 8)` but the runtime row selects the slot DYNAMICALLY via the
/// Lagrange-basis index gate — no single registry descriptor until that gate is
/// emitted) / `Custom` (8) (needs an accumulator/recursive proof-binding constraint
/// kind) / `RevokeCapability` (24) (cap-root advance, mid-reshape).
#[cfg(not(feature = "recursion"))]
fn selector_for_effect(effect: &VmEffectKind) -> Option<usize> {
    match effect {
        VmEffectKind::Transfer { .. } => Some(sel::TRANSFER),
        VmEffectKind::NoteSpend { .. } => Some(sel::NOTE_SPEND),
        VmEffectKind::NoteCreate { .. } => Some(sel::NOTE_CREATE),
        VmEffectKind::BridgeMint { .. } => Some(sel::BRIDGE_MINT),
        VmEffectKind::Burn { .. } => Some(sel::BURN),
        VmEffectKind::EmitEvent { .. } => Some(sel::EMIT_EVENT),
        VmEffectKind::CellSeal { .. } => Some(sel::CELL_SEAL),
        VmEffectKind::CellDestroy { .. } => Some(sel::CELL_DESTROY),
        VmEffectKind::Refusal { .. } => Some(sel::REFUSAL),
        VmEffectKind::SetVerificationKey { .. } => Some(sel::SET_VERIFICATION_KEY),
        VmEffectKind::SetPermissions { .. } => Some(sel::SET_PERMISSIONS),
        VmEffectKind::ExerciseViaCapability { .. } => Some(sel::EXERCISE_VIA_CAPABILITY),
        VmEffectKind::PipelinedSend { .. } => Some(sel::PIPELINED_SEND),
        VmEffectKind::IncrementNonce => Some(sel::INCREMENT_NONCE),
        VmEffectKind::RefreshDelegation => Some(sel::REFRESH_DELEGATION),
        VmEffectKind::RevokeDelegation { .. } => Some(sel::REVOKE_DELEGATION),
        VmEffectKind::Introduce { .. } => Some(sel::INTRODUCE),
        VmEffectKind::CreateCell { .. } => Some(sel::CREATE_CELL),
        VmEffectKind::SpawnWithDelegation { .. } => Some(sel::SPAWN_WITH_DELEGATION),
        VmEffectKind::CreateCellFromFactory { .. } => Some(sel::CREATE_CELL_FROM_FACTORY),
        VmEffectKind::ReceiptArchive { .. } => Some(sel::RECEIPT_ARCHIVE),
        VmEffectKind::MakeSovereign => Some(sel::MAKE_SOVEREIGN),
        VmEffectKind::CellUnseal { .. } => Some(sel::CELL_UNSEAL),
        _ => None,
    }
}

/// The selectors whose HOMOGENEOUS MULTI-EFFECT turns route to the descriptor prover —
/// EXACTLY the x2-differential AGREE set of the harness's `multi_effect_agreement_census`
/// (a descriptor's per-row gates + selector gate natively hold over a multi-row trace of
/// its OWN effect; the PI bindings pin first-row pre-state / last-row post-state, so the
/// single registry descriptor IS the per-row conjunction — no proof splitting needed).
///
/// NOT in the set (the `MultiInstancePiSlot` fallback): `NoteSpend` (4) / `NoteCreate`
/// (5) / `EmitEvent` (25) / `Burn` (46) bind per-turn SCALAR PI slots (one nullifier /
/// commitment / event hash / burn amount), so the HAND-AIR itself rejects their
/// multi-instance traces. The descriptor ACCEPTS those traces (its PI prefix stops before
/// the slot), i.e. it is MORE PERMISSIVE there — routing them would change the proven
/// semantics, exactly what the cutover must never do.
#[cfg(not(feature = "recursion"))]
const MULTI_EFFECT_READY_SELECTORS: &[usize] = &[
    sel::TRANSFER,
    sel::CREATE_CELL_FROM_FACTORY,
    sel::SET_PERMISSIONS,
    sel::SET_VERIFICATION_KEY,
    sel::REFRESH_DELEGATION,
    sel::REVOKE_DELEGATION,
    sel::CREATE_CELL,
    sel::SPAWN_WITH_DELEGATION,
    sel::EXERCISE_VIA_CAPABILITY,
    sel::INTRODUCE,
    sel::PIPELINED_SEND,
    sel::BRIDGE_MINT,
    sel::CELL_DESTROY,
    sel::CELL_SEAL,
    sel::CELL_UNSEAL,
    sel::RECEIPT_ARCHIVE,
    sel::REFUSAL,
    sel::INCREMENT_NONCE,
];

/// Why a turn shape stays on the hand-AIR fallback engine — every fallback is NAMED and
/// logged (`prove_effect_vm_with_cutover`), never a silent len/match miss.
#[cfg(not(feature = "recursion"))]
#[derive(Debug)]
enum CutoverFallback {
    /// A turn with no effects (NoOp-only trace); no descriptor models the empty turn.
    EmptyTurn,
    /// An effect's selector has not graduated the differential harness (DEEPER
    /// divergence or no Lean descriptor emitted). Carries the selector when known.
    NonGraduatedEffect { selector: Option<usize> },
    /// All effects graduated but carry DIFFERENT selectors. No Lean-emitted conjunction
    /// descriptor exists for selector SETS (each descriptor's selector gate
    /// `(1-sel[NOOP])·(1-sel[s])` rejects rows of any other selector — pinned by the
    /// harness's `heterogeneous_multi_effect_is_not_descriptor_provable`), and
    /// hand-merging constraint sets in Rust would forfeit verified-by-construction.
    HeterogeneousSelectors { selectors: Vec<usize> },
    /// A multi-instance turn of a PI-slot effect (NoteSpend / NoteCreate / EmitEvent /
    /// Burn): the per-turn scalar PI slot makes the HAND-AIR itself reject the trace,
    /// and the descriptor (whose PI prefix stops before the slot) would be MORE
    /// permissive — see `MULTI_EFFECT_READY_SELECTORS`.
    MultiInstancePiSlot { selector: usize },
}

#[cfg(not(feature = "recursion"))]
impl std::fmt::Display for CutoverFallback {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyTurn => write!(f, "empty turn (NoOp-only trace)"),
            Self::NonGraduatedEffect { selector } => match selector {
                Some(s) => write!(f, "selector {s} has not graduated the differential harness"),
                None => write!(f, "effect has no graduated descriptor selector"),
            },
            Self::HeterogeneousSelectors { selectors } => write!(
                f,
                "heterogeneous multi-effect turn (selectors {selectors:?}): no Lean-emitted \
                 conjunction descriptor for selector sets"
            ),
            Self::MultiInstancePiSlot { selector } => write!(
                f,
                "multi-instance turn of PI-slot selector {selector}: per-turn scalar PI slot \
                 (hand-AIR rejects; descriptor would be more permissive)"
            ),
        }
    }
}

/// Route a turn: the ONE graduated descriptor selector that proves it, or the NAMED
/// fallback reason keeping it on the hand-AIR.
///
/// * single graduated effect → its selector (the original cutover beachhead);
/// * N effects, ALL the SAME multi-effect-ready selector → that selector (the registry
///   descriptor natively proves the multi-row trace — validated by the harness's
///   `homogeneous_multi_effect_turns_graduate_into_cutover`);
/// * anything else → a [`CutoverFallback`].
#[cfg(not(feature = "recursion"))]
fn cutover_route(effects: &[VmEffectKind]) -> Result<usize, CutoverFallback> {
    if effects.is_empty() {
        return Err(CutoverFallback::EmptyTurn);
    }
    let mut selectors = Vec::with_capacity(effects.len());
    for e in effects {
        match selector_for_effect(e) {
            Some(s) => selectors.push(s),
            None => return Err(CutoverFallback::NonGraduatedEffect { selector: None }),
        }
    }
    let first = selectors[0];
    if selectors.iter().any(|&s| s != first) {
        let mut uniq = selectors.clone();
        uniq.sort_unstable();
        uniq.dedup();
        return Err(CutoverFallback::HeterogeneousSelectors { selectors: uniq });
    }
    if selectors.len() == 1 {
        return Ok(first);
    }
    if MULTI_EFFECT_READY_SELECTORS.contains(&first) {
        Ok(first)
    } else {
        Err(CutoverFallback::MultiInstancePiSlot { selector: first })
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
#[cfg(not(feature = "recursion"))]
const CUTOVER_READY_SELECTORS: &[usize] = &[
    sel::TRANSFER,
    sel::NOTE_SPEND,
    sel::NOTE_CREATE,
    sel::EMIT_EVENT,
    sel::BRIDGE_MINT,
    sel::BURN,
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
    sel::MAKE_SOVEREIGN,
    sel::CREATE_CELL_FROM_FACTORY,
    sel::CREATE_CELL,
    sel::SPAWN_WITH_DELEGATION,
    sel::RECEIPT_ARCHIVE,
    sel::CELL_UNSEAL,
];

/// Prove the Effect-VM state transition: by DEFAULT through the Lean descriptor
/// interpreter for every graduated turn shape (`cutover_route`), with an automatic,
/// LOGGED hand-AIR fallback for non-graduated shapes. `DREGG_DESCRIPTOR_PROVER=0`
/// opts out (forces the legacy hand-AIR for comparison). Returns the SAME wire proof
/// type either way.
#[cfg(not(feature = "recursion"))]
fn prove_effect_vm_with_cutover(
    effects: &[VmEffectKind],
    effect_trace: &[Vec<BabyBear>],
    effect_pi: &[BabyBear],
) -> Result<EffectVmP3Proof, SdkError> {
    if descriptor_prover_enabled() {
        match cutover_route(effects) {
            Ok(s) => {
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
                // A graduated selector with no registry JSON would be a registry bug —
                // fall back honestly rather than fail the turn, but say so loudly.
                tracing::warn!(
                    selector = s,
                    "cutover route returned a selector with NO registry descriptor — \
                     falling back to the hand-AIR (registry/route mismatch)"
                );
            }
            Err(fallback) => {
                tracing::info!(
                    reason = %fallback,
                    "effect-vm prover FALLBACK to hand-AIR (descriptor cutover does not \
                     cover this turn shape)"
                );
            }
        }
    } else {
        tracing::info!(
            "DREGG_DESCRIPTOR_PROVER=0: descriptor prover opted OUT; proving through the \
             legacy hand-AIR"
        );
    }
    // FALLBACK ENGINE (and the opt-out path): the hand-written `EffectVmP3Air`.
    prove_effect_vm_p3(effect_trace, effect_pi)
        .map_err(|e| SdkError::InvalidWitness(format!("effect-vm p3 proof failed: {e}")))
}

// ============================================================================
// THE ROTATED IR-v2 ROUTE (G1, STAGED-ADDITIVE) — beside the live v1 path.
// ============================================================================
//
// The live `prove_effect_vm_with_cutover` above proves the Effect-VM state transition over the
// 186-column v1 trace through the IR-v1 descriptor interpreter (or the hand-AIR fallback) —
// that is the DEFAULT and stays byte-identical. The route below is the rotated R=24 path: it
// drives the LIVE rotated trace generator (`dregg_circuit::effect_vm::trace_rotated`) from the
// real per-turn producer witnesses (`dregg_turn::rotation_witness`) and proves the 311-column
// rotated trace + 38-PI vector through the IR-v2 batch prover (`descriptor_ir2`). It is OFF by
// default — gated BOTH by the `recursion` feature (compiles `descriptor_ir2`) AND the runtime
// flag `DREGG_ROTATED_PROVER=1` (precedent: `DREGG_DESCRIPTOR_PROVER`). The flag-day cutover
// (default v1 → rotated, `EmitAllJson→v3Registry` live, NUM_REGISTERS 16→24, VK epoch) is G2.

/// Is the rotated IR-v2 (R=24) route enabled at runtime? DEFAULT OFF (the live v1 path is the
/// byte-identical default). `DREGG_ROTATED_PROVER=1` (or `true`/`on`) opts IN. The `recursion`
/// feature must ALSO be compiled in for the route to exist.
#[cfg(feature = "recursion")]
pub fn rotated_prover_enabled() -> bool {
    matches!(
        std::env::var("DREGG_ROTATED_PROVER").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE") | Ok("True") | Ok("on") | Ok("ON")
    )
}

/// **`prove_effect_vm_rotated_ir2`** (G1, staged-additive) — prove ONE transfer-shaped turn
/// through the rotated R=24 IR-v2 path: the LIVE rotated trace generator (fed the real
/// per-turn producer witnesses) + the IR-v2 batch prover over `transferVmDescriptor2R24`.
///
/// * `initial_state` / `effects` — the v1 turn the rotated generator extends;
/// * `before_w` / `after_w` — the per-turn producer witnesses
///   (`dregg_turn::rotation_witness::produce(cell, ledger, nullifier_root, receipt_log)`) for
///   the acting cell's before/after `RecordKernelState`.
///
/// Returns the IR-v2 batch proof (the rotated wire type — NOT an `EffectVmP3Proof`; this route
/// is opt-in and additive, so it is NOT wired into the v1-typed composed `prove_full_turn`
/// path until the G2 cutover bumps the wire). The proof self-verifies before return.
///
/// STAGED-ADDITIVE: nothing on the live wire path calls this. The descriptor JSON is the
/// committed staged registry entry (`V3_STAGED_REGISTRY_TSV`); the four appended PIs are the
/// rotated OLD/NEW commit · committed height · caveat commit the generator publishes.
#[cfg(feature = "recursion")]
pub fn prove_effect_vm_rotated_ir2(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::effect_vm::trace_rotated::{
        empty_caveat_manifest, transfer_caveat_manifest,
    };

    // The transfer-shaped caveat manifest stays the validated reference for a single transfer
    // effect (it exercises BOTH caveat domains); every other cohort effect proves with the
    // default empty manifest. The rotated shape is identical either way.
    let caveat = match effects {
        [VmEffectKind::Transfer { .. }] => transfer_caveat_manifest(),
        _ => empty_caveat_manifest(),
    };
    prove_effect_vm_rotated_ir2_with_caveat(initial_state, effects, before_w, after_w, &caveat)
}

/// Re-derive the rotated 38-PI vector for a turn (the same `dpis` the rotated prover binds).
/// Used by [`prove_full_turn`] to record the rotated leg's `sub_public_inputs` and to extend
/// the composed PI without re-proving.
#[cfg(feature = "recursion")]
fn rotated_effect_pi_for(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    rot: &RotationTurnWitness,
) -> Result<Vec<BabyBear>, SdkError> {
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, generate_rotated_effect_vm_trace,
    };
    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
    };
    let before = bridge(&rot.before)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated before-witness: {e}")))?;
    let after = bridge(&rot.after)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated after-witness: {e}")))?;
    let (_trace, dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, &before, &after, &rot.caveat)
            .map_err(|e| SdkError::InvalidWitness(format!("rotated PI re-derive: {e}")))?;
    Ok(dpis)
}

/// The cohort-general rotated IR-v2 prover (G4): proves ANY of the 26 rotated cohort effects
/// (resolved by `rotated_descriptor_name_for_effect`) through the shared 311-column trace,
/// with an explicit caveat manifest. Returns the IR-v2 batch proof; self-verifies before
/// return. Fails closed (`InvalidWitness`) if the turn's effect is NOT in the rotated cohort
/// (no rotated descriptor exists for it) or if the turn is empty / heterogeneous.
#[cfg(feature = "recursion")]
pub fn prove_effect_vm_rotated_ir2_with_caveat(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    };
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
    };
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;

    // Resolve the cohort descriptor NAME for this turn's effect. A homogeneous multi-effect
    // turn (every effect the same cohort member) routes to that member's descriptor — the
    // rotated per-effect constraint family natively holds over a multi-row trace of its own
    // effect (the PI pins bind first-row pre / last-row post). Heterogeneous / empty turns
    // fail closed.
    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("rotated prover: empty turn".into()))?;
    let name = rotated_descriptor_name_for_effect(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "rotated prover: effect {lead:?} is not in the rotated cohort (no R=24 descriptor)"
        ))
    })?;
    if effects.len() > 1 {
        for e in &effects[1..] {
            if rotated_descriptor_name_for_effect(e) != Some(name) {
                return Err(SdkError::InvalidWitness(
                    "rotated prover: heterogeneous multi-effect turn (one rotated descriptor \
                     per proof)"
                        .into(),
                ));
            }
        }
    }

    // Resolve the committed rotated descriptor JSON for that name.
    let json = V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(name) {
                let _name = it.next();
                it.next()
            } else {
                None
            }
        })
        .ok_or_else(|| {
            SdkError::InvalidWitness(format!("{name} not in staged rotated registry"))
        })?;
    let desc = parse_vm_descriptor2(json)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated descriptor parse: {e}")))?;

    // Bridge the producer witnesses into the pure-circuit generator inputs.
    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated after-witness: {e}")))?;

    // LIVE-generate the 311-column rotated trace + 38-PI vector.
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, &before, &after, caveat)
            .map_err(|e| SdkError::InvalidWitness(format!("rotated trace generation: {e}")))?;

    // Prove through the IR-v2 batch prover (self-verifies before return).
    prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| SdkError::InvalidWitness(format!("rotated IR-v2 proof: {e}")))
}

/// Resolve the committed rotated cohort descriptor JSON for a turn's effects (the SAME
/// resolution `prove_effect_vm_rotated_ir2_with_caveat` performs): the lead effect's cohort
/// name via `rotated_descriptor_name_for_effect`, requiring a homogeneous cohort, then the
/// registry JSON string from `V3_STAGED_REGISTRY_TSV`. Fails closed for empty / heterogeneous /
/// non-cohort turns. Returns `(name, json)`.
#[cfg(feature = "recursion")]
fn rotated_descriptor_json_for_effects(
    effects: &[VmEffectKind],
) -> Result<(&'static str, &'static str), SdkError> {
    use dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect;
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;

    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("rotated vk_hash: empty turn".into()))?;
    let name = rotated_descriptor_name_for_effect(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "rotated vk_hash: effect {lead:?} is not in the rotated cohort (no R=24 descriptor)"
        ))
    })?;
    for e in &effects[1..] {
        if rotated_descriptor_name_for_effect(e) != Some(name) {
            return Err(SdkError::InvalidWitness(
                "rotated vk_hash: heterogeneous multi-effect turn (one rotated descriptor per proof)"
                    .into(),
            ));
        }
    }
    let json = V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(name) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .ok_or_else(|| {
            SdkError::InvalidWitness(format!("{name} not in staged rotated registry"))
        })?;
    Ok((name, json))
}

/// The rotated effect-vm leg's `vk_hash` (Wall A.1): the blake3 fingerprint of the committed
/// rotated cohort descriptor JSON. This pins the rotated leg to its OWN descriptor — the verifier
/// re-derives the same fingerprint from the (uniquely) accepting cohort descriptor and rejects a
/// tampered vk_hash. (The committed registry JSON is the canonical pin the rotated path already
/// uses to resolve + parse the descriptor at prove/verify time, so fingerprinting it is consistent.)
#[cfg(feature = "recursion")]
fn rotated_effect_vm_vk_hash(effects: &[VmEffectKind]) -> Result<[u8; 32], SdkError> {
    let (_name, json) = rotated_descriptor_json_for_effects(effects)?;
    Ok(*blake3::hash(json.as_bytes()).as_bytes())
}

// ============================================================================
// PATH-PRESERVE — the N-leg cohort-run chain (heterogeneous-turn rotation).
//
// `docs/PATH-PRESERVE.md` §2/§3/§5. A heterogeneous turn (one actor doing >1
// distinct cohort effect) cannot prove as ONE rotated leg — the rotated prover
// proves exactly ONE cohort descriptor per call (`descriptor_ir2.rs:3832`) and
// fails closed on a heterogeneous slice (`prove_effect_vm_rotated_ir2_with_caveat`,
// :873-883). PATH-PRESERVE splits the turn into MAXIMAL homogeneous cohort-runs,
// proves each as its OWN rotated leg, threads the per-run pre/post state, and the
// verifier chains them (leg_k.OLD == leg_{k-1}.NEW). This is Rust composition over
// already-Lean-emitted per-cohort legs — NO new descriptor/AIR/constraint (LAW #1).
// ============================================================================

/// Split a VmEffect sequence into maximal runs where every effect in a run resolves to the SAME
/// rotated cohort descriptor (`rotated_descriptor_name_for_effect`, `trace_rotated.rs:464`).
///
/// A homogeneous turn yields exactly ONE run (so the chained path is byte-identical to today's
/// single rotated leg for the existing fleet — the §7 Phase-1 additive guarantee). A
/// `[Transfer, SetField, Transfer]` turn yields THREE runs (`0..1, 1..2, 2..3` — Transfer and
/// SetField are different cohorts; consecutive same-cohort effects coalesce). A `SetField`
/// family run coalesces only when the per-slot descriptor name matches (`setFieldVmDescriptor2-0R24`
/// vs `-1R24` are DISTINCT cohorts and so split — each per-slot descriptor is its own AIR).
///
/// `None`-resolving effects (NoOp / non-cohort) terminate a run and form their own singleton run
/// of "no cohort"; the chained prover rejects such a turn (it cannot rotate a non-cohort effect),
/// matching the per-run rotated prover's fail-closed contract. Returns the runs in chain order.
pub fn split_into_cohort_runs(effects: &[VmEffectKind]) -> Vec<core::ops::Range<usize>> {
    use dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect;
    let mut runs: Vec<core::ops::Range<usize>> = Vec::new();
    let mut start = 0usize;
    // The descriptor name of the run currently being accumulated. `None` is a sentinel for
    // "no run open yet"; a non-cohort effect resolves to its own `Option<&str>` value (also
    // `None`), so we track "is a run open" separately via `start < i` is insufficient — use a
    // dedicated current-name slot that distinguishes "unset" from "cohort = None".
    let mut current: Option<Option<&'static str>> = None;
    for (i, e) in effects.iter().enumerate() {
        let name = rotated_descriptor_name_for_effect(e);
        match current {
            None => {
                current = Some(name);
                start = i;
            }
            Some(cur) if cur == name => { /* extend the open run */ }
            Some(_) => {
                runs.push(start..i);
                current = Some(name);
                start = i;
            }
        }
    }
    if current.is_some() && start < effects.len() {
        runs.push(start..effects.len());
    }
    runs
}

/// Read the post-state `CellState` off the v1 trace's last REAL effect row's `STATE_AFTER` columns
/// — the generator's OWN emitted state block (NOT a hand-replay of effect semantics; the same
/// `STATE_AFTER` cols the rotated weld copies, `trace_rotated.rs:299-307`). `n_effects` is the
/// number of real effect rows (rows `0..n_effects`; padding follows). Used to thread the synthetic
/// interior boundary states the executor never materialized.
#[cfg(feature = "recursion")]
fn cell_state_after_run(
    trace: &[Vec<BabyBear>],
    n_effects: usize,
    seed_for_unchanged: &CellState,
) -> CellState {
    use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, state};
    // An empty run (no real effect rows) leaves the state unchanged — return the seed.
    if n_effects == 0 || trace.is_empty() {
        return seed_for_unchanged.clone();
    }
    let last_real = (n_effects - 1).min(trace.len() - 1);
    let row = &trace[last_real];
    // BabyBear is `BabyBear(pub u32)` in canonical form `[0, p-1]` (`field.rs:29`), so `.0` is
    // the canonical integer — the inverse of the `split_u64` / `BabyBear::new(nonce)` the
    // generator wrote into these columns.
    let lo = row[STATE_AFTER_BASE + state::BALANCE_LO].0 as u64;
    let hi = row[STATE_AFTER_BASE + state::BALANCE_HI].0 as u64;
    // `split_u64`: lo = low 30 bits, hi = val >> 30 (`effect_vm/helpers.rs:13`).
    let balance = lo | (hi << 30);
    let nonce = row[STATE_AFTER_BASE + state::NONCE].0;
    let mut fields = [BabyBear::ZERO; 8];
    for (i, f) in fields.iter_mut().enumerate() {
        *f = row[STATE_AFTER_BASE + state::FIELD_BASE + i];
    }
    let capability_root = row[STATE_AFTER_BASE + state::CAP_ROOT];
    let reserved = row[STATE_AFTER_BASE + state::RESERVED].0;
    let sealed_field_mask = reserved & 0xFF;
    let mode_flag = reserved >> 8;
    let mut s = CellState {
        balance,
        nonce,
        fields,
        capability_root,
        state_commitment: BabyBear::ZERO,
        sealed_field_mask,
        mode_flag,
    };
    s.refresh_commitment();
    s
}

/// The chained ROTATED prover (PATH-PRESERVE §2.3). Proves a heterogeneous turn as N
/// `"effect-vm-rotated"` legs — one per maximal homogeneous cohort-run — threading the per-run
/// pre/post state so the verifier (the step-4 collect + chain-check in `verify_full_turn_bound`)
/// can chain them.
///
/// The single producer witnesses (`rot.before` / `rot.after`) are REUSED across runs: their
/// witness-carried limbs (cells_root, iroot, lifecycle, epoch, r11..r23) are turn-invariant
/// (`rotation_witness.rs:46-49`), so the before-block of EVERY run and the after-block of every
/// INTERIOR run use `rot.before`; only the final run's after-block uses `rot.after`. The changing
/// per-run scalars (balance/nonce/fields/cap_root) ride the welds, which `fill_block`
/// (`trace_rotated.rs:294-307`) overrides per-row from each run's own v1 sub-trace — so the
/// interior chain closes by construction: `leg_k.NEW` and `leg_{k+1}.OLD` are both
/// `wireCommitR(rot.before carried-limbs, s_{k+1} welds)` (the SAME object).
///
/// Returns the legs in chain order. Each leg is the EXACT shape the single-leg path attaches: a
/// postcard `Ir2BatchProof`, the rotated PI vector, the cohort vk_hash. A homogeneous turn yields
/// ONE leg, byte-identical to the single-leg path.
///
/// Fails closed (`InvalidWitness`) if any run is non-cohort (a NoOp / non-graduated effect) — the
/// per-run rotated prover cannot rotate it; such a turn keeps the v1 leg upstream.
#[cfg(feature = "recursion")]
fn prove_cohort_run_chain(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    rot: &RotationTurnWitness,
) -> Result<Vec<AttachedSubProof>, SdkError> {
    let runs = split_into_cohort_runs(effects);
    if runs.is_empty() {
        return Err(SdkError::InvalidWitness(
            "chained rotated prover: empty turn (no cohort runs)".into(),
        ));
    }
    let n_runs = runs.len();
    let mut legs: Vec<AttachedSubProof> = Vec::with_capacity(n_runs);
    let mut s_k = initial_state.clone();
    for (k, run) in runs.iter().enumerate() {
        let run_effects = &effects[run.clone()];
        // Per-run caveat manifest (transfer-shaped single transfer → the two-domain reference
        // manifest, matching `RotationTurnWitness::for_effects` / the single-leg path).
        let caveat = match run_effects {
            [VmEffectKind::Transfer { .. }] => {
                dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest()
            }
            _ => dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
        };
        // before-block witness = real before-cell's producer (ALL runs); after-block witness =
        // before-cell's for interior runs, the real after-cell's for the final run.
        let is_final = k + 1 == n_runs;
        let after_w = if is_final { &rot.after } else { &rot.before };
        let proof = prove_effect_vm_rotated_ir2_with_caveat(
            &s_k,
            run_effects,
            &rot.before,
            after_w,
            &caveat,
        )?;
        // Re-derive this run's rotated PI vector (the prover self-verified it; we need the felts
        // for the composed PI + the leg's `sub_public_inputs`). Build a throwaway per-run witness
        // so we reuse the single-leg PI re-derivation helper.
        let run_rot = RotationTurnWitness {
            before: rot.before.clone(),
            after: after_w.clone(),
            caveat,
        };
        let rot_pi = rotated_effect_pi_for(&s_k, run_effects, &run_rot)?;
        let proof_bytes = postcard::to_allocvec(&proof).map_err(|e| {
            SdkError::InvalidWitness(format!(
                "chained rotated proof serialize failed (run {k}): {e}"
            ))
        })?;
        legs.push(AttachedSubProof {
            label: "effect-vm-rotated".into(),
            proof_bytes,
            sub_public_inputs: rot_pi,
            vk_hash: rotated_effect_vm_vk_hash(run_effects)?,
        });
        // Thread s_k → s_{k+1} off the generator's own STATE_AFTER columns (no hand-replay).
        if !is_final {
            let (v1_trace, _v1_pi) = generate_effect_vm_trace(&s_k, run_effects);
            s_k = cell_state_after_run(&v1_trace, run_effects.len(), &s_k);
        }
    }
    Ok(legs)
}

/// Verify an effect-vm sub-proof, SHAPE-DRIVEN — deliberately independent of
/// `DREGG_DESCRIPTOR_PROVER` (the env var tunes the PROVER only; a peer must accept any
/// sound proof regardless of its own environment). A proof produced by the descriptor
/// interpreter binds a DIFFERENT AIR (different extended trace width / CommonData) than
/// the hand-AIR, so the two verifiers are NOT interchangeable: try the descriptor
/// verifiers (selector-bound) first; if none accepts, fall back to the hand-AIR verifier.
#[cfg(not(feature = "recursion"))]
fn verify_effect_vm_proof_with_cutover(
    proof: &EffectVmP3Proof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    // SELECTOR-BOUND verify: reconstruct each cutover descriptor AIR and check the proof
    // against it. Each descriptor carries the Lean `selectorGate s` tooth, so a sound
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
    verify_effect_vm_p3(proof, public_inputs).map_err(|e| format!("{e}"))
}

/// Verify a ROTATED effect-vm sub-proof (the C4 `"effect-vm-rotated"` leg): deserialize the
/// `Ir2BatchProof` and verify it SELECTOR-BOUND against the rotated cohort descriptors. A sound
/// rotated proof binds its own descriptor (each carries the Lean selector tooth), so exactly one
/// cohort member accepts. Zero ⇒ not a rotated cohort proof (reject); more than one ⇒ ambiguous
/// (reject rather than launder a wrong-descriptor acceptance).
#[cfg(feature = "recursion")]
fn verify_effect_vm_rotated_with_cutover(
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
    expected_vk_hash: &[u8; 32],
) -> Result<(), String> {
    use dregg_circuit::descriptor_ir2::{
        DreggStarkConfig, Ir2BatchProof, parse_vm_descriptor2, verify_vm_descriptor2,
    };
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;

    let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
        .map_err(|e| format!("rotated effect-vm proof deserialize: {e}"))?;

    // The accepting cohort descriptor(s) AND the JSON each was parsed from (so we can re-derive
    // and re-check the attached vk_hash — Wall A.1 makes vk_hash load-bearing on the rotated leg).
    let mut bound: Vec<(&str, &str)> = Vec::new();
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        let name = match it.next() {
            Some(n) => n,
            None => continue,
        };
        let _display = it.next();
        let json = match it.next() {
            Some(j) => j,
            None => continue,
        };
        if let Ok(desc) = parse_vm_descriptor2(json) {
            if public_inputs.len() >= desc.public_input_count {
                let dpis = &public_inputs[..desc.public_input_count];
                if verify_vm_descriptor2(&desc, &proof, dpis).is_ok() {
                    bound.push((name, json));
                }
            }
        }
    }
    match bound.as_slice() {
        [(_name, json)] => {
            // Re-derive the rotated vk_hash from the uniquely-accepting cohort descriptor's
            // committed JSON and pin it to the attached vk_hash. A tampered vk_hash is rejected
            // even though the proof itself is selector-bound (defends the descriptor-identity
            // metadata the wire carries).
            let derived = *blake3::hash(json.as_bytes()).as_bytes();
            if &derived != expected_vk_hash {
                return Err(format!(
                    "rotated effect-vm vk_hash mismatch: attached {expected_vk_hash:?} != \
                     accepting cohort descriptor fingerprint {derived:?}"
                ));
            }
            Ok(())
        }
        [] => Err("rotated effect-vm proof verified under NO cohort descriptor".to_string()),
        multi => Err(format!(
            "rotated effect-vm proof verified under MULTIPLE cohort descriptors {:?} — \
             selector binding ambiguous, rejecting",
            multi.iter().map(|(n, _)| *n).collect::<Vec<_>>()
        )),
    }
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
    // STAGED CUTOVER (Wall A.3): the v1 Effect-VM trace + PI are computed ONLY when the
    // rotated leg is NOT taken (no rotation witness, or `not(recursion)`). On the rotated
    // path the v1 trace would be dead work whose only escaping value (net_delta for the
    // conservation leg) is carried in the rotated PI prefix instead — so the rotated branch
    // is fully self-sufficient and carries ZERO v1 dependency. Under `not(recursion)` a
    // present `rotation` is ignored, so `use_rotated` is always false and this is byte-identical.
    #[cfg(feature = "recursion")]
    let use_rotated = witness.rotation.is_some();
    #[cfg(not(feature = "recursion"))]
    let use_rotated = false;
    #[allow(clippy::type_complexity)]
    let v1_effect: Option<(Vec<Vec<BabyBear>>, Vec<BabyBear>)> = if use_rotated {
        None
    } else {
        Some(generate_effect_vm_trace(
            &witness.initial_cell_state,
            &witness.effects,
        ))
    };
    // AUDITED PATH: the Effect VM state transition is proven through the real
    // Plonky3 verifier (`p3-batch-stark`) with REAL in-circuit Poseidon2 for
    // every state-commitment / cap-root hash — NOT the bespoke `stark` (whose
    // FRI has no terminal low-degree test). The proof self-verifies before
    // return, so the post-state commitment is genuinely bound: a forged
    // NEW_COMMIT makes the audited verifier reject (see
    // `effect_vm_p3_full_air` anti-ghost tests).
    // THE CUTOVER (default ON): for every graduated turn shape, prove through the
    // verified-by-construction Lean DESCRIPTOR INTERPRETER; non-graduated shapes fall
    // back to the hand-written `EffectVmP3Air` with a named, logged reason.
    // `DREGG_DESCRIPTOR_PROVER=0` opts out. Same wire proof type either way; the
    // differential harness guards equivalence.
    // THE ROTATED LEG (C4 cutover): when the caller threaded the rotation producer witnesses,
    // prove the effect-vm transition through the ROTATED IR-v2 path (the multi-table
    // `Ir2BatchProof`) and attach it as the `"effect-vm-rotated"` sub-proof. Its PI vector is
    // the rotated 38-PI (the v1 prefix `[0..34)` — OLD/NEW_COMMIT/turn-id/effects-hash carried
    // at their v1 offsets — plus the 4 appended rotated commit/height/caveat pins at 34..37).
    // The v1 `"effect-vm"` leg is the byte-identical default when no rotation witness is present.
    components.has_state_transition = true;
    // PATH-PRESERVE §2/§3: the rotated leg is now N legs — one per maximal homogeneous cohort-run
    // (`split_into_cohort_runs`). A HOMOGENEOUS turn yields exactly ONE run, so this is
    // byte-identical to the prior single rotated leg for the existing fleet (the §7 additive
    // guarantee). A heterogeneous turn (only reachable when a caller explicitly threads a rotation
    // witness for it — the live node's cohort gate still returns `None`, so the live path is
    // unchanged) emits N chained legs `prove_cohort_run_chain` built, threading per-run pre/post
    // state. The collected PI vectors flow to the conservation leg (Σ net_delta) + the `is_none`
    // v1 guard.
    #[cfg(feature = "recursion")]
    let rotated_effect_pis: Option<Vec<Vec<BabyBear>>> = if let Some(rot) = &witness.rotation {
        let legs = prove_cohort_run_chain(&witness.initial_cell_state, &witness.effects, rot)?;
        let mut leg_pis: Vec<Vec<BabyBear>> = Vec::with_capacity(legs.len());
        for leg in legs {
            all_public_inputs.extend_from_slice(&leg.sub_public_inputs);
            leg_pis.push(leg.sub_public_inputs.clone());
            sub_proofs.push(leg);
        }
        Some(leg_pis)
    } else {
        None
    };
    #[cfg(not(feature = "recursion"))]
    let rotated_effect_pis: Option<Vec<Vec<BabyBear>>> = None;

    if rotated_effect_pis.is_none() {
        // RECURSION TOWER: the v1 effect-vm leg is GONE (the rotated chained leg is the
        // sole effect-vm prover — PATH-PRESERVE Phases 0-4). A finalized-turn prove with no
        // rotation witness can no longer fall back to v1, so it FAILS CLOSED. This enforces
        // the Phase-4 invariant in code: under `recursion`, every reachable finalized turn
        // threads a rotation witness, so `rotation.is_none()` here is unreachable for the
        // live node (whose cohort gate always yields `Some`); a caller that reaches it gets a
        // structured error rather than a silent v1 proof.
        #[cfg(feature = "recursion")]
        {
            let _ = &v1_effect;
            return Err(SdkError::InvalidWitness(
                "full-turn prove under `recursion`: no rotation witness threaded and the v1 \
                 effect-vm fallback has been retired — thread a rotation witness (the live node \
                 always does)"
                    .into(),
            ));
        }
        // V1 FLOOR: the byte-identical hand-AIR / descriptor-interpreter leg.
        // `v1_effect` is `Some` exactly when the rotated leg was NOT taken.
        #[cfg(not(feature = "recursion"))]
        {
            let (effect_trace, effect_pi) = v1_effect
                .as_ref()
                .expect("v1 effect trace present on the non-rotated path");
            let effect_proof =
                prove_effect_vm_with_cutover(&witness.effects, effect_trace, effect_pi)?;
            let effect_proof_bytes = postcard::to_allocvec(&effect_proof).map_err(|e| {
                SdkError::InvalidWitness(format!("effect-vm p3 proof serialize failed: {e}"))
            })?;
            all_public_inputs.extend_from_slice(effect_pi);
            sub_proofs.push(AttachedSubProof {
                label: "effect-vm".into(),
                proof_bytes: effect_proof_bytes.clone(),
                sub_public_inputs: effect_pi.clone(),
                vk_hash: compute_vk_hash_bytes(&effect_vm_circuit_descriptor()),
            });
        }
    }

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
        // Wall A.2 + PATH-PRESERVE §2.4: read net_delta from whichever effect-vm leg(s) were
        // actually proven. The rotated PI carries NET_DELTA_MAG(16)/NET_DELTA_SIGN(17) at their
        // v1 offsets (both < V1_PI_COUNT=34, the carried v1 prefix). On the rotated path the turn
        // may carry N chained legs (one per cohort-run); each leg's `generate_effect_vm_trace`
        // accumulates ONLY its own run's effects' delta (`trace.rs:506`), so the turn-level
        // conservation is Σ_k net_delta(leg_k). A homogeneous turn (1 leg) sums to that single
        // leg — byte-identical to the prior single-leg read. The v1 path reads the one v1 PI.
        let actual_net_delta: i64 = match (rotated_effect_pis.as_ref(), v1_effect.as_ref()) {
            (Some(leg_pis), _) => {
                let mut sum: i64 = 0;
                for pi in leg_pis {
                    let mag = pi[effect_vm::pi::NET_DELTA_MAG].0 as i64;
                    let sign = pi[effect_vm::pi::NET_DELTA_SIGN].0;
                    sum += if sign == 1 { -mag } else { mag };
                }
                sum
            }
            (None, Some((_, v1_pi))) => {
                let mag = v1_pi[effect_vm::pi::NET_DELTA_MAG].0 as i64;
                let sign = v1_pi[effect_vm::pi::NET_DELTA_SIGN].0;
                if sign == 1 { -mag } else { mag }
            }
            (None, None) => {
                return Err(SdkError::InvalidWitness(
                    "conservation: no effect-vm PI available (neither rotated nor v1)".into(),
                ));
            }
        };

        if actual_net_delta != cons_witness.expected_net_delta {
            return Err(SdkError::InvalidWitness(format!(
                "conservation mismatch: effect VM net_delta {} != expected {} (chain-summed)",
                actual_net_delta, cons_witness.expected_net_delta
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

        // Non-revocation public inputs: [revocation_root, queried_item]. The
        // queried item is the spent nullifier; the non-revocation AIR binds it
        // in-circuit to the bracketed control-row COL_0 (row-0 QUERIED_ITEM
        // boundary), so this is a real handle the verifier can compare to the
        // Effect-VM nullifier (no-double-spend binding "b").
        let revoc_pi = vec![revoc_witness.tree.root(), revoc_witness.item_hash];

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
    // 5b. Cap-membership proof (consumed capability — cap Phase D)
    // ========================================================================
    if let Some(cap_witness) = &witness.cap_membership {
        // AUDITED PATH: capability membership in the openable sorted-Poseidon2
        // capability tree is proven through the real Plonky3 verifier
        // (`p3-batch-stark`) via `prove_cap_membership_p3`. Every node hash
        // (`hash_fact(left, [right])` — the exact `CanonicalCapTree` node) is
        // arithmetized in-circuit by the real Poseidon2 gadget, and the leaf
        // digest / path-top root are pinned by row-0 / last-row boundaries.
        let leaf_digest = cap_witness.leaf.digest();
        let (cap_proof, cap_pi) =
            prove_cap_membership_p3(leaf_digest, &cap_witness.siblings, &cap_witness.directions)
                .map_err(|e| {
                    SdkError::InvalidWitness(format!("cap-membership p3 proof failed: {e}"))
                })?;
        let cap_proof_bytes = postcard::to_allocvec(&cap_proof).map_err(|e| {
            SdkError::InvalidWitness(format!("cap-membership p3 proof serialize failed: {e}"))
        })?;

        components.has_cap_membership = true;
        all_public_inputs.extend_from_slice(&cap_pi);
        sub_proofs.push(AttachedSubProof {
            label: "cap-membership".into(),
            proof_bytes: cap_proof_bytes,
            sub_public_inputs: cap_pi,
            vk_hash: compute_vk_hash_bytes(&cap_membership_circuit_descriptor()),
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
    let (main_circuit, main_trace, main_pi) = build_pi_binding_p3(&all_public_inputs);
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
/// This delegates to [`verify_full_turn_bound`] with `expected_revocation_root
/// = None`, i.e. it does NOT pin the non-revocation sub-proof's accumulator root
/// to a canonical one. A caller on the no-double-spend / freshness-critical path
/// (a federation member finalizing a spend) MUST instead call
/// [`verify_full_turn_bound`] with the canonical accumulator root, so the
/// freshness proof is bound to THE canonical nullifier set for this turn rather
/// than a tree of the prover's choosing.
///
/// # Returns
///
/// `Ok(())` if the proof is valid, or an error describing what failed.
pub fn verify_full_turn(
    proof: &FullTurnProof,
    expected_old_commit: BabyBear,
    expected_new_commit: BabyBear,
) -> Result<(), FullTurnVerifyError> {
    verify_full_turn_bound(proof, expected_old_commit, expected_new_commit, None, None)
}

/// Verify a full turn proof, additionally binding the non-revocation sub-proof's
/// accumulator root to a caller-supplied canonical root.
///
/// This is the freshness-critical (no-double-spend) verifier entry point. It is
/// identical to [`verify_full_turn`] except for the `expected_revocation_root`
/// argument:
///
/// - `expected_revocation_root = Some(root)`: the non-revocation sub-proof's
///   published `revocation_root` PI MUST equal `root` (the canonical published
///   accumulator the verifier expects, bound to the authenticated pre-state /
///   federation receipt). The non-revocation AIR pins that PI to the Merkle
///   tree the proof authenticated against (boundary at the path tops,
///   `circuit/src/dsl/revocation.rs:324-336`), so a prover who proves freshness
///   against its OWN tree — an empty / stale / hand-picked accumulator in which
///   the item is trivially absent — publishes a different root and is rejected
///   with [`FullTurnVerifyError::RevocationRootMismatch`]. This is binding (a)
///   of the no-double-spend gap: the freshness is against THE canonical
///   nullifier set, not one of the prover's choosing.
///
/// - `expected_revocation_root = None`: no canonical-root binding is performed
///   (the legacy behaviour of [`verify_full_turn`]). The non-revocation
///   sub-proof is still verified for internal soundness (item genuinely absent
///   from the tree it published), but the verifier does not assert WHICH tree.
///
/// # No-double-spend binding (b) — CLOSED (item == this turn's nullifier)
///
/// The full no-double-spend property needs a SECOND tooth beyond (a): the item
/// the non-revocation proof proves fresh must be THIS turn's nullifier
/// (`PI[NOTESPEND_NULLIFIER]` of the Effect-VM sub-proof), not some other item.
/// This is now enforced (step 8 below). The audited non-revocation circuit
/// publishes the queried item as its second public input
/// (`pi::QUERIED_ITEM`), bound IN-CIRCUIT to the bracketed control-row
/// `col::COL_0` by a row-0 `PiBinding` boundary
/// (`circuit/src/dsl/revocation.rs`). Because `col::COL_0` on the control row is
/// the exact value the ordering constraints C6/C7/C10/C11 pin strictly between
/// two adjacent sorted leaves, that PI is a REAL binding — a proof whose
/// published `pi[1]` differs from the genuinely-bracketed item is UNSAT, so the
/// felt is NOT a free wire. The prover sets `revoc_pi = vec![root, item_hash]`
/// with `item_hash` the spent nullifier; this verifier (step 8) then enforces
/// `revoc_pi[QUERIED_ITEM] == effect_pi[<nullifier slot>]` for any turn that
/// genuinely spends a note (non-zero nullifier slot). The nullifier slot is
/// leg-dependent: the v1 leg publishes it at `pi::NOTESPEND_NULLIFIER` (offset
/// 198, the per-row D5 binding); the rotated leg publishes it at rotated PI slot
/// `ROT_NULLIFIER_PI` (38), the C4 fifth-pin weld
/// (`EffectVmEmitRotationV3.noteSpendV3`) — present iff the rotated leg carries a
/// 39-element PI (a single-spend note-spend turn). A non-revocation proof proving
/// freshness for a DIFFERENT item is rejected with
/// [`FullTurnVerifyError::NullifierMismatch`]. Together (a)+(b): freshness is
/// against THE canonical accumulator AND for THIS turn's nullifier — on BOTH legs
/// (the rotated note-spend leg no longer refuses; C4 closed). The test
/// `freshness_binding_b_rejects_wrong_item` pins the anti-forgery property and
/// `revocation_item_pi_exposed_binding_b_closed` guards that the circuit keeps
/// exposing the item PI.
///
/// # AUTHORITY / cap-membership binding (cap Phase D)
///
/// `expected_cap_membership = Some(expectation)` is the capability-gated
/// (hosted-authority) verifier entry point. The expectation's two fields are
/// recomputed by the CALLER from data it trusts — the consumed capability's
/// leaf preimage from the hash-bound receipt witness
/// (`TurnReceipt::consumed_capabilities`, cap Phase C) and the holder's
/// CANONICAL pre-state `capability_root` (the same value the EffectVm row's
/// `cap_root` column is seeded from, cap Phase A) — never from the proof. The
/// check (step 9) then enforces, against the cap-membership sub-proof's
/// in-circuit-bound public inputs:
///
/// - **leg present**: a capability-gated turn whose proof carries NO
///   cap-membership leg is rejected ([`FullTurnVerifyError::MissingComponent`])
///   — the leg cannot be silently stripped;
/// - **root binding**: `pi[CAP_ROOT]` (the path top, pinned by the circuit's
///   last-row boundary) MUST equal the canonical pre-state `capability_root` —
///   a membership path into a prover-chosen tree is rejected
///   ([`FullTurnVerifyError::CapRootMismatch`]);
/// - **leaf binding**: `pi[LEAF_DIGEST]` (row-0 boundary) MUST equal the
///   7-field Poseidon2 digest of the disclosed consumed-cap leaf — a
///   leaf-field tamper (e.g. an inflated `EffectMask`) is rejected
///   ([`FullTurnVerifyError::CapLeafMismatch`]).
///
/// `None` skips the binding (self-sovereign turns consume no capability).
pub fn verify_full_turn_bound(
    proof: &FullTurnProof,
    expected_old_commit: BabyBear,
    expected_new_commit: BabyBear,
    expected_revocation_root: Option<BabyBear>,
    expected_cap_membership: Option<&CapMembershipExpectation>,
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
    let main_p3: dregg_circuit::dsl::dsl_p3_air::DslP3Proof = postcard::from_bytes(main_p3_bytes)
        .map_err(|e| {
        FullTurnVerifyError::MainProofInvalid(format!("p3 main proof deserialize: {e}"))
    })?;
    let (main_circuit, _t, main_pi) = build_pi_binding_p3(&proof.composed.public_inputs);
    verify_dsl_p3(&main_circuit, &main_p3, &main_pi)
        .map_err(|e| FullTurnVerifyError::MainProofInvalid(format!("{e}")))?;

    // 3. Verify each attached sub-proof cryptographically.
    for (i, attached) in proof.composed.sub_proofs.iter().enumerate() {
        // Dispatch verification to the correct verifier based on label.
        let verify_result: Result<(), String> = match attached.label.as_str() {
            // EFFECT VM (v1 floor): AUDITED p3 verifier of the v1 hand-AIR / descriptor-interpreter
            // leg. The proof bytes are a postcard-serialized `EffectVmP3Proof`. The recursion tower
            // never produces the `"effect-vm"` label (it emits `"effect-vm-rotated"` below), so this
            // arm is `not(recursion)`-only; a recursion-built verifier presented a v1 leg rejects it
            // at the catch-all.
            #[cfg(not(feature = "recursion"))]
            "effect-vm" => {
                let p3: EffectVmP3Proof =
                    postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                        FullTurnVerifyError::SubProofDeserialize {
                            index: i,
                            reason: format!("effect-vm p3 deserialize: {e}"),
                        }
                    })?;
                // SHAPE-DRIVEN verify (env-independent): the effect-vm sub-proof may have
                // been produced by the Lean DESCRIPTOR INTERPRETER (different AIR ⇒
                // different extended trace width ⇒ different CommonData), so it is NOT
                // interchangeable with the hand-AIR verifier. Try the selector-bound
                // descriptor verifiers first; fall back to the hand-AIR verifier for
                // hand-AIR proofs. `DREGG_DESCRIPTOR_PROVER` never gates verification.
                verify_effect_vm_proof_with_cutover(&p3, &attached.sub_public_inputs)
                    .map_err(|e| format!("{e}"))
            }
            // EFFECT VM ROTATED (C4 cutover): the multi-table `Ir2BatchProof` over a rotated
            // R=24 descriptor. Resolve the descriptor SELECTOR-BOUND (a sound rotated proof
            // verifies under exactly one cohort descriptor — its own effect's), then verify
            // via the audited IR-v2 batch verifier. `not(recursion)` builds never produce this
            // leg, so the arm is recursion-gated.
            #[cfg(feature = "recursion")]
            "effect-vm-rotated" => verify_effect_vm_rotated_with_cutover(
                &attached.proof_bytes,
                &attached.sub_public_inputs,
                &attached.vk_hash,
            ),
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
                let p3: DslP3Proof = postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
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
                verify_membership_p3(&p3, &attached.sub_public_inputs).map_err(|e| format!("{e}"))
            }
            "non-revocation" => {
                let p3: DslP3Proof = postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                    FullTurnVerifyError::SubProofDeserialize {
                        index: i,
                        reason: format!("non-revocation p3 deserialize: {e}"),
                    }
                })?;
                // Non-revocation PI is [revocation_root, queried_item]. Both are
                // bound in-circuit; the queried item must be carried so the
                // audited verifier re-binds it (a freshness proof for a different
                // item is UNSAT under this item).
                let root = attached.sub_public_inputs.first().copied().ok_or_else(|| {
                    FullTurnVerifyError::MalformedPublicInputs(
                        "non-revocation PI missing revocation_root".into(),
                    )
                })?;
                let queried_item = attached.sub_public_inputs.get(1).copied().ok_or_else(|| {
                    FullTurnVerifyError::MalformedPublicInputs(
                        "non-revocation PI missing queried_item (pi[1])".into(),
                    )
                })?;
                verify_non_revocation_p3(&p3, root, queried_item)
            }
            "cap-membership" => {
                let p3: DslP3Proof = postcard::from_bytes(&attached.proof_bytes).map_err(|e| {
                    FullTurnVerifyError::SubProofDeserialize {
                        index: i,
                        reason: format!("cap-membership p3 deserialize: {e}"),
                    }
                })?;
                // Cap-membership PI is [leaf_digest, cap_root]; both bound
                // in-circuit (row-0 / last-row boundaries). Carrying both to
                // the audited verifier re-binds them (a proof for a different
                // leaf or tree is UNSAT under these PIs).
                let leaf_digest = attached.sub_public_inputs.first().copied().ok_or_else(|| {
                    FullTurnVerifyError::MalformedPublicInputs(
                        "cap-membership PI missing leaf_digest (pi[0])".into(),
                    )
                })?;
                let cap_root = attached.sub_public_inputs.get(1).copied().ok_or_else(|| {
                    FullTurnVerifyError::MalformedPublicInputs(
                        "cap-membership PI missing cap_root (pi[1])".into(),
                    )
                })?;
                verify_cap_membership_p3(&p3, leaf_digest, cap_root)
            }
            other => Err(format!("unknown sub-proof label: {}", other)),
        };

        verify_result.map_err(|e| FullTurnVerifyError::SubProofInvalid {
            index: i,
            label: attached.label.clone(),
            reason: e,
        })?;
    }

    // 4. Check Effect VM public input bindings (old/new commitment). Each effect-vm leg is
    //    EITHER the v1 `"effect-vm"` (204-PI) or the rotated `"effect-vm-rotated"` (38-PI).
    //    The rotated 38-PI is the v1 prefix `[0..34)` + 4 appended pins, so OLD_COMMIT(0) /
    //    NEW_COMMIT(4) / TURN_HASH(25) / EFFECTS_HASH(8) / NET_DELTA(16-17) all carry the SAME
    //    values at the SAME offsets — the cross-bindings below read those unchanged. Only
    //    offsets >= 34 (e.g. NOTESPEND_NULLIFIER at 198) are absent from the rotated leg.
    //
    //    PATH-PRESERVE §3: a heterogeneous turn carries N chained rotated legs (one per cohort
    //    run, in `sub_proofs` order = chain order s0→s1→…→sN). COLLECT all effect-vm legs, then
    //    CHAIN-CHECK: first.OLD == expected_old, last.NEW == expected_new, and adjacency
    //    leg_k.OLD == leg_{k-1}.NEW. Each leg is already cryptographically re-verified in step 3.
    //    A single-leg turn (N=1, the existing fleet) collapses to EXACTLY the prior two endpoint
    //    checks (no adjacency window) — byte-identical behavior.
    let effect_legs: Vec<&AttachedSubProof> = proof
        .composed
        .sub_proofs
        .iter()
        .filter(|sp| sp.label == "effect-vm" || sp.label == "effect-vm-rotated")
        .collect();
    if effect_legs.is_empty() {
        return Err(FullTurnVerifyError::MissingComponent("effect-vm".into()));
    }
    // `effect_sub` = the FIRST leg: steps 6/6b bind the authorization to the turn's PRE-state
    // (this leg's OLD_COMMIT) and to the turn's effects (this leg's EFFECTS_HASH). Auth-gated
    // turns are single-leg on the live path (the cohort gate keeps heterogeneous cap turns on
    // v1), so the first leg IS the whole turn there.
    let effect_sub = effect_legs[0];

    // Every leg must carry at least the v1 prefix it publishes at: the rotated leg >= V1_PI_COUNT
    // (34); the v1 leg the full ACTIVE_BASE_COUNT. The cross-bindings only read offsets < 34.
    for leg in &effect_legs {
        let leg_is_rotated = leg.label == "effect-vm-rotated";
        let min_pi = if leg_is_rotated {
            dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT
        } else {
            effect_vm::pi::ACTIVE_BASE_COUNT
        };
        if leg.sub_public_inputs.len() < min_pi {
            return Err(FullTurnVerifyError::MalformedPublicInputs(
                "effect VM PI too short".into(),
            ));
        }
    }
    let effect_is_rotated = effect_sub.label == "effect-vm-rotated";

    // Endpoints: the chain's first OLD and last NEW pin the turn's pre/post commitments.
    let first_leg = effect_legs[0];
    let last_leg = effect_legs[effect_legs.len() - 1];
    let proof_old_commit = first_leg.sub_public_inputs[effect_vm::pi::OLD_COMMIT];
    let proof_new_commit = last_leg.sub_public_inputs[effect_vm::pi::NEW_COMMIT];

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

    // Adjacency: each leg's OLD must equal the previous leg's NEW — the chain closes with no gap
    // and no splice. A tampered / dropped middle leg breaks this (anti-ghost at the chain layer).
    for w in effect_legs.windows(2) {
        let prev_new = w[0].sub_public_inputs[effect_vm::pi::NEW_COMMIT];
        let this_old = w[1].sub_public_inputs[effect_vm::pi::OLD_COMMIT];
        if this_old != prev_new {
            return Err(FullTurnVerifyError::CommitmentMismatch {
                which: "chain_adjacency",
                expected: prev_new,
                got: this_old,
            });
        }
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

        // 6b. CRITICAL (capability-security): Authorization-to-EffectVM EFFECT
        //     binding. The cell binding above proves the actor is authorized for
        //     SOME fact in this cell's tree; it does NOT prove the actor may
        //     perform THIS effect. We close that gap by requiring the
        //     authorization proof's conclusion (auth PI[1] = derived_hash, pinned
        //     in-circuit to hash_fact(HEAD_PRED, HEAD_TERM) by the derivation
        //     circuit's C4/C6) to equal the "may perform THIS effect" fact —
        //     Allow(effects_commit) — reconstructed from the Effect-VM proof's
        //     in-circuit-bound effects commitment (PI[EFFECTS_HASH_BASE]). An
        //     authorization proof whose derivation concludes a may-perform fact
        //     for a DIFFERENT effect (kind / target cell / amount / params)
        //     carries a different derived_hash and is rejected here.
        //
        //     This tooth binds the CONCLUSION (`Allow(h)`) to the effect. That the
        //     conclusion genuinely follows from a capability the actor HOLDS is the
        //     membership leg's job: the derivation circuit proves "body fact ⊢
        //     Allow(h)" but treats the body fact hash as a free (nonzero) witness;
        //     the c-list membership proof (bound via step 5: auth state_root ==
        //     membership root) is what proves that body fact actually exists in the
        //     cell's fact tree. Together: membership(fact ∈ tree) + derivation(fact
        //     ⊢ Allow(h)) + this tooth(h == this effect) + the cell binding above
        //     (tree == cell mutated) = the full capability-security chain.
        let auth_derived_hash = auth_sub
            .sub_public_inputs
            .get(AUTH_PI_DERIVED_HASH)
            .copied()
            .ok_or_else(|| {
                FullTurnVerifyError::MalformedPublicInputs(
                    "authorization PI missing derived_hash (PI[1])".into(),
                )
            })?;
        let expected_action_binding =
            effect_action_binding_from_effect_pi(&effect_sub.sub_public_inputs);
        if auth_derived_hash != expected_action_binding {
            return Err(FullTurnVerifyError::AuthEffectMismatch {
                auth_derived_hash,
                expected_action_binding,
            });
        }
    }

    // 7. FRESHNESS / no-double-spend: bind the non-revocation sub-proof's
    //    accumulator root to the caller's canonical root (binding (a)).
    //
    //    The non-revocation sub-proof's `revocation_root` PI is pinned IN-CIRCUIT
    //    to the Merkle tree the proof authenticated against (boundary at the path
    //    tops, `circuit/src/dsl/revocation.rs:324-336`). Step 3 already verified
    //    the non-membership math against THAT root. But internally-sound
    //    non-membership against the PROVER's tree only proves "item ∉ some tree";
    //    a counterfeiter could pick an empty / stale accumulator in which the
    //    item is trivially absent. Requiring the published root to equal the
    //    canonical accumulator the verifier expects (bound to the authenticated
    //    pre-state / federation receipt) upgrades that to "item ∉ THE canonical
    //    nullifier set for this turn" — the no-double-spend property.
    //
    //    Only enforced when the caller supplies the canonical root (the
    //    freshness-critical path); `None` preserves the legacy
    //    internal-soundness-only behaviour. The companion tooth (item == this
    //    turn's nullifier) is a circuit residual — see the
    //    [`verify_full_turn_bound`] SOUNDNESS BOUNDARY doc.
    if let Some(expected_root) = expected_revocation_root {
        if proof.components.has_non_revocation {
            let revoc_sub = proof
                .composed
                .sub_proofs
                .iter()
                .find(|sp| sp.label == "non-revocation")
                .ok_or(FullTurnVerifyError::MissingComponent(
                    "non-revocation".into(),
                ))?;
            // Non-revocation PI is [revocation_root].
            let proof_root = revoc_sub
                .sub_public_inputs
                .first()
                .copied()
                .ok_or_else(|| {
                    FullTurnVerifyError::MalformedPublicInputs(
                        "non-revocation PI missing revocation_root".into(),
                    )
                })?;
            if proof_root != expected_root {
                return Err(FullTurnVerifyError::RevocationRootMismatch {
                    expected: expected_root,
                    got: proof_root,
                });
            }
        }
    }

    // 8. FRESHNESS / no-double-spend — binding (b): the item the non-revocation
    //    proof proved fresh IS THIS turn's nullifier.
    //
    //    The non-revocation sub-proof now publishes the queried item as its
    //    SECOND public input (`pi[QUERIED_ITEM]`), bound IN-CIRCUIT to the
    //    bracketed control-row COL_0 by a row-0 boundary
    //    (`circuit/src/dsl/revocation.rs`, `QUERIED_ITEM` PI). Step 3 already
    //    re-verified the sub-proof against that published item, so it is a
    //    cryptographically-bound handle on the genuinely-proven item — NOT a
    //    free felt. Requiring it to equal the Effect-VM proof's NoteSpend
    //    nullifier (`PI[NOTESPEND_NULLIFIER]`, pinned in-circuit to the spend
    //    row's folded nullifier — `effect_vm/air.rs`) closes binding (b): the
    //    freshness is for THIS turn's nullifier, not some other item a prover
    //    proved fresh and stapled on.
    //
    //    Gating: only a turn that genuinely SPENDS a note has a nullifier, so
    //    we enforce this only when `PI[NOTESPEND_NULLIFIER]` is populated
    //    (non-zero sentinel). A non-spend turn may still legitimately carry a
    //    non-revocation proof whose item is a CAPABILITY hash (token freshness),
    //    which is not a nullifier and must not be forced to equal the zero slot.
    //    Together (a)+(b): freshness is against THE canonical accumulator AND
    //    for THIS turn's nullifier — the full no-double-spend property.
    if proof.components.has_non_revocation && proof.components.has_state_transition {
        // The published spent nullifier — read at the leg-appropriate PI offset. THE C4 CLOSE:
        // the rotated note-spend leg now EXPOSES the nullifier (it no longer refuses).
        //
        //  * v1 leg (204-PI): the D5 cross-binding lives at `NOTESPEND_NULLIFIER` (offset 198),
        //    pinned PER-ROW in the hand-AIR to every spend row's folded `param0`.
        //  * rotated leg: the C4 weld (`EffectVmEmitRotationV3.noteSpendV3`) appends a FIFTH PI
        //    pin binding the spend row's folded `param0` to rotated PI slot 38
        //    (`ROT_NULLIFIER_PI`) on the FIRST row, so a note-spend rotated leg carries a
        //    39-element PI (`ROT_NULLIFIER_PI_COUNT`). The rotated generator emits the fifth slot
        //    ONLY for a single-spend NoteSpend turn (a multi-spend turn fails closed and stays on
        //    v1, where a second distinct nullifier is UNSAT) — so a 39-PI rotated leg is a
        //    single-spend turn whose row-0 nullifier IS PI[38], faithfully the v1 binding. A
        //    NON-note-spend rotated leg carries the 38-PI prefix with NO nullifier slot, so there
        //    is nothing to cross-check (treated as the ZERO sentinel — no spend, no binding).
        // PATH-PRESERVE §3.5: the nullifier rides whichever leg carries the (single) NoteSpend, not
        // necessarily leg-0. The single-spend invariant holds across the chain
        // (`trace_rotated.rs:264-275` + the cap-less builder gate) — at most ONE leg is a note-spend
        // leg. Scan the chain for it: the rotated note-spend leg (39-PI, `ROT_NULLIFIER_PI_COUNT`)
        // or the v1 leg's `NOTESPEND_NULLIFIER` slot. N=1 collapses to exactly the prior read.
        let effect_nullifier = {
            use dregg_circuit::effect_vm::trace_rotated::{
                ROT_NULLIFIER_PI, ROT_NULLIFIER_PI_COUNT,
            };
            let mut nullifier = BabyBear::ZERO;
            for leg in &effect_legs {
                let leg_nullifier = if leg.label == "effect-vm-rotated" {
                    if leg.sub_public_inputs.len() >= ROT_NULLIFIER_PI_COUNT {
                        leg.sub_public_inputs[ROT_NULLIFIER_PI]
                    } else {
                        // 38-PI rotated leg: not a note-spend, no nullifier published.
                        BabyBear::ZERO
                    }
                } else {
                    leg.sub_public_inputs[effect_vm::pi::NOTESPEND_NULLIFIER]
                };
                if leg_nullifier != BabyBear::ZERO {
                    nullifier = leg_nullifier;
                    break;
                }
            }
            nullifier
        };
        let _ = effect_is_rotated; // (single-leg shape is now folded into the per-leg scan above)
        if effect_nullifier != BabyBear::ZERO {
            let revoc_sub = proof
                .composed
                .sub_proofs
                .iter()
                .find(|sp| sp.label == "non-revocation")
                .ok_or(FullTurnVerifyError::MissingComponent(
                    "non-revocation".into(),
                ))?;
            let proven_item = revoc_sub.sub_public_inputs.get(1).copied().ok_or_else(|| {
                FullTurnVerifyError::MalformedPublicInputs(
                    "non-revocation PI missing queried_item (pi[1])".into(),
                )
            })?;
            if proven_item != effect_nullifier {
                return Err(FullTurnVerifyError::NullifierMismatch {
                    proven_item,
                    effect_nullifier,
                });
            }
        }
    }

    // 9. AUTHORITY / cap-membership binding (cap Phase D — the payoff).
    //
    //    The cap-membership sub-proof's two PIs are pinned IN-CIRCUIT
    //    (`dsl::cap_membership`: row-0 boundary = leaf digest, last-row
    //    boundary = the path top) and step 3 already re-verified the sub-proof
    //    against them, so both are cryptographically-bound handles — NOT free
    //    felts. Requiring:
    //
    //      (a) pi[CAP_ROOT]    == the holder's CANONICAL pre-state
    //          `capability_root` (caller-recomputed from the authoritative
    //          c-list — the same value seeded into the EffectVm row's cap_root
    //          column, cap Phase A), and
    //      (b) pi[LEAF_DIGEST] == digest of the receipt-disclosed consumed-cap
    //          leaf preimage (caller-recomputed from the receipt-hash-bound
    //          Phase-C witness),
    //
    //    upgrades "some leaf ∈ some tree" to "THE disclosed capability ∈ THE
    //    holder's real pre-state c-list" — production authority, in-proof.
    //    A capability-gated turn whose proof LACKS the leg is rejected
    //    outright (the leg cannot be stripped).
    if let Some(expected) = expected_cap_membership {
        if !proof.components.has_cap_membership {
            return Err(FullTurnVerifyError::MissingComponent(
                "cap-membership (capability-gated turn carries no AUTHORITY leg)".into(),
            ));
        }
        let cap_sub = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "cap-membership")
            .ok_or(FullTurnVerifyError::MissingComponent(
                "cap-membership".into(),
            ))?;
        let proof_leaf_digest = cap_sub.sub_public_inputs.first().copied().ok_or_else(|| {
            FullTurnVerifyError::MalformedPublicInputs(
                "cap-membership PI missing leaf_digest (pi[0])".into(),
            )
        })?;
        let proof_cap_root = cap_sub.sub_public_inputs.get(1).copied().ok_or_else(|| {
            FullTurnVerifyError::MalformedPublicInputs(
                "cap-membership PI missing cap_root (pi[1])".into(),
            )
        })?;
        if proof_cap_root != expected.cap_root {
            return Err(FullTurnVerifyError::CapRootMismatch {
                expected: expected.cap_root,
                got: proof_cap_root,
            });
        }
        let expected_leaf_digest = expected.leaf.digest();
        if proof_leaf_digest != expected_leaf_digest {
            return Err(FullTurnVerifyError::CapLeafMismatch {
                expected: expected_leaf_digest,
                got: proof_leaf_digest,
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
    /// The authorization proof's conclusion (`derived_hash`) does not bind to
    /// the turn's effect: the actor proved authorization for a DIFFERENT effect
    /// than the one the Effect-VM proof certifies. This is the capability-security
    /// anti-forgery tooth — `derived_hash` must equal `Allow(effects_commit)` for
    /// the bound effects (see [`effect_action_binding`]).
    AuthEffectMismatch {
        /// The authorization proof's bound conclusion (`auth PI[1]`).
        auth_derived_hash: BabyBear,
        /// The "may perform THIS effect" fact reconstructed from the Effect-VM PIs.
        expected_action_binding: BabyBear,
    },
    /// The cap-membership sub-proof's path tops a root that is NOT the
    /// holder's canonical pre-state `capability_root`. This is the AUTHORITY
    /// anti-forgery tooth (cap Phase D): the circuit's last-row boundary pins
    /// the published root to the path the proof actually authenticated, so a
    /// membership path into a prover-chosen tree (or a DIFFERENT cell's
    /// cap_root spliced in) publishes a different root and is rejected here.
    CapRootMismatch {
        /// The canonical pre-state capability root the verifier expects.
        expected: BabyBear,
        /// The root the proof's membership path actually tops.
        got: BabyBear,
    },
    /// The cap-membership sub-proof proves membership of a leaf that is NOT
    /// the consumed capability disclosed in the receipt. The circuit's row-0
    /// boundary pins the published leaf digest to the genuinely-proven member,
    /// and the verifier recomputes the expected digest from the receipt's
    /// 7-field leaf preimage — so a leaf-field tamper (e.g. an inflated
    /// `EffectMask`) mismatches and is rejected here.
    CapLeafMismatch {
        /// Digest of the receipt-disclosed consumed-cap leaf.
        expected: BabyBear,
        /// The leaf digest the proof actually attests.
        got: BabyBear,
    },
    /// The non-revocation sub-proof proves freshness against a revocation
    /// accumulator root that is NOT the canonical root the verifier expects for
    /// this turn. This is the no-double-spend / freshness anti-forgery tooth:
    /// the non-revocation AIR pins its published `revocation_root` PI to the
    /// Merkle tree the proof actually authenticated against (boundary at the
    /// path tops, `dsl/revocation.rs` C-`boundaries`), so a prover who supplies
    /// its OWN tree (an empty / stale / hand-picked accumulator in which the
    /// item is trivially absent) publishes a different root than the canonical
    /// one and is rejected here. Without this tooth the internally-sound
    /// non-membership math proves "item ∉ SOME tree of the prover's choosing",
    /// not "item ∉ THE canonical nullifier set for this turn".
    RevocationRootMismatch {
        /// The canonical accumulator root the verifier expects (bound to the
        /// authenticated pre-state / federation receipt).
        expected: BabyBear,
        /// The revocation root the non-revocation sub-proof actually published.
        got: BabyBear,
    },
    /// The non-revocation sub-proof proved freshness for an item that is NOT
    /// this turn's spent nullifier. This is the no-double-spend / freshness
    /// anti-forgery tooth, binding (b): the non-revocation AIR now publishes
    /// the queried item as `pi[QUERIED_ITEM]`, bound in-circuit to the
    /// bracketed control-row COL_0 (`dsl/revocation.rs`). Requiring it to equal
    /// the Effect-VM proof's `PI[NOTESPEND_NULLIFIER]` (pinned in-circuit to the
    /// spend row's folded nullifier) ensures the freshness attests THIS turn's
    /// nullifier, not some other item a prover proved fresh and attached. Only
    /// enforced for turns that genuinely spend a note (non-zero nullifier slot).
    NullifierMismatch {
        /// The item the non-revocation sub-proof actually proved fresh
        /// (`non-revocation pi[QUERIED_ITEM]`).
        proven_item: BabyBear,
        /// This turn's spent nullifier (`Effect-VM PI[NOTESPEND_NULLIFIER]`).
        effect_nullifier: BabyBear,
    },
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
            Self::AuthEffectMismatch {
                auth_derived_hash,
                expected_action_binding,
            } => write!(
                f,
                "authorization conclusion ({:?}) does not authorize this effect: \
                 expected Allow(effects_commit) = {:?} — the authorization proves a \
                 different action than the turn performs",
                auth_derived_hash, expected_action_binding
            ),
            Self::CapRootMismatch { expected, got } => write!(
                f,
                "cap-membership proof root ({:?}) is not the holder's canonical pre-state \
                 capability_root ({:?}) — the membership path is into a different \
                 (prover-chosen / spliced) capability tree (AUTHORITY tooth, cap Phase D)",
                got, expected
            ),
            Self::CapLeafMismatch { expected, got } => write!(
                f,
                "cap-membership proof attests leaf digest ({:?}), not the receipt-disclosed \
                 consumed capability ({:?}) — the proven member's fields differ from the \
                 disclosed witness (leaf-tamper, AUTHORITY tooth, cap Phase D)",
                got, expected
            ),
            Self::RevocationRootMismatch { expected, got } => write!(
                f,
                "non-revocation proof root ({:?}) is not the canonical accumulator \
                 root ({:?}) — the freshness proof is against a different (prover-chosen) \
                 nullifier set than this turn's canonical one (no-double-spend tooth)",
                got, expected
            ),
            Self::NullifierMismatch {
                proven_item,
                effect_nullifier,
            } => write!(
                f,
                "non-revocation proof proved freshness for item ({:?}), not this turn's \
                 spent nullifier ({:?}) — the freshness attests a DIFFERENT item than the \
                 turn spends (no-double-spend binding b)",
                proven_item, effect_nullifier
            ),
        }
    }
}

impl std::error::Error for FullTurnVerifyError {}

// ============================================================================
// Convenience: Minimal proof (Effect VM + Authorization only)
// ============================================================================

/// Build a derivation witness whose conclusion authorizes EXACTLY `effects`.
///
/// This is the prover-side twin of the [`verify_full_turn`] authorization↔effect
/// tooth: it constructs a satisfiable single-step [`DerivationWitness`] whose
/// conclusion is the may-perform fact `Allow(effects_commit)` (see
/// [`effect_action_binding`]). The conclusion's term is a head VARIABLE bound by
/// the substitution to the Effect-VM effects commitment, so the derivation
/// circuit's substitution-application constraint (C10) holds and the resulting
/// `derived_hash` equals `effect_action_binding(effects)`.
///
/// `capability_fact_hash` is the hash of the body fact the actor holds (the
/// capability evidence whose Merkle membership the c-list proof attests), and
/// `state_root` is the cell's fact-tree root it lives in — both bound in-circuit
/// (C5 ties the body root to auth `PI[0] = state_root`, which the caller must
/// pass as the cell's `old_commitment` so the cell-binding tooth also holds).
///
/// Carrying the real `capability_fact_hash` + `state_root` keeps the derivation
/// honest: the conclusion follows from a body fact present in the cell tree, it
/// is not a free-floating "Allow" — the membership leg still has to prove that
/// fact exists, and the head is welded to the executed effect.
pub fn derivation_authorizing_effects(
    effects: &[effect_vm::Effect],
    capability_fact_hash: BabyBear,
    state_root: BabyBear,
) -> dregg_circuit::derivation_air::DerivationWitness {
    use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};

    let effects_commit = effect_vm::compute_effects_hash(effects).0;
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);

    // Rule: Allow(?0) :- capability(?0). Head term 0 is variable index 0, which
    // the substitution binds to the effects commitment. The single body atom is
    // the actor's held capability fact (present in the cell's fact tree).
    let rule = CircuitRule {
        id: 1,
        num_body_atoms: 1,
        num_variables: 1,
        head_predicate: allow_pred,
        head_terms: [
            (true, BabyBear::ZERO), // variable, index 0 -> substitution[0]
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
        ],
        body_atoms: vec![BodyAtomPattern {
            predicate: allow_pred,
            terms: [
                (true, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
        }],
        equal_checks: vec![],
        memberof_checks: vec![],
        gte_check: None,
        lt_check: None,
    };

    DerivationWitness {
        rule,
        state_root,
        body_fact_hashes: vec![capability_fact_hash],
        substitution: vec![effects_commit],
        derived_predicate: allow_pred,
        derived_terms: [
            effects_commit,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    }
}

/// Generate a minimal full turn proof with just state transition + authorization.
///
/// This is the most common case for sovereign cell turns where:
/// - The actor is authorized via a derivation chain
/// - The state transition is proven by the Effect VM
/// - No value transfers or revocation channels involved
///
/// The `derivation`'s conclusion MUST authorize exactly `effects` — i.e. its
/// `derived_hash` must equal [`effect_action_binding(effects)`](effect_action_binding) —
/// or [`verify_full_turn`] rejects the proof with
/// [`FullTurnVerifyError::AuthEffectMismatch`]. Use
/// [`derivation_authorizing_effects`] to construct a conforming witness.
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
        cap_membership: None,
        turn_hash,
        rotation: None,
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
        cap_membership: None,
        turn_hash,
        rotation: None,
    };
    prove_full_turn(&witness)
}

/// Self-sovereign proof with the per-turn ROTATION producer witnesses threaded (cutover FLOW-B):
/// the effect-vm leg proves through the LEAN-emitted rotated descriptor (`"effect-vm-rotated"`,
/// a multi-table `Ir2BatchProof`) instead of the v1 hand-AIR. `rotation` carries the acting
/// cell's before/after [`RotationTurnWitness`] (minted by
/// `dregg_turn::rotation_witness::produce`). When `rotation` is `None`, this is byte-identical to
/// [`prove_turn_self_sovereign`]. Under `not(recursion)` a present `rotation` is ignored (the v1
/// leg runs) so the wasm/no-lean-link build is unaffected.
pub fn prove_turn_self_sovereign_rotated(
    initial_state: &CellState,
    effects: &[effect_vm::Effect],
    turn_hash: [u8; 32],
    rotation: Option<RotationTurnWitness>,
) -> Result<FullTurnProof, SdkError> {
    let witness = FullTurnWitness {
        initial_cell_state: initial_state.clone(),
        effects: effects.to_vec(),
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: None,
        cap_membership: None,
        turn_hash,
        rotation,
    };
    prove_full_turn(&witness)
}

/// FRI-free DIRECT witness revalidation for a self-sovereign turn (F-DOS-1).
///
/// Re-executes the turn from `initial_state` to regenerate the Effect-VM trace,
/// then checks that EVERY AIR constraint vanishes via the circuit's FRI-free
/// `bespoke_air_accepts` — the exact predicate the audited verifier accepts, but
/// WITHOUT generating a STARK proof. Per the bench
/// (`circuit/tests/turn_revalidation_vs_prove.rs`) this is ~0.98 ms vs the
/// prover's ~749 ms (≈765x), so a commit path can revalidate the witness inline
/// — soundly, since the witness is CHECKED not trusted — and defer the succinct
/// STARK attestation to an async prover off any hot lock.
///
/// Returns the proven post-state commitment (the boundary public input the
/// prover would bind) on accept, or `Err(())` if the regenerated witness fails
/// any constraint (the turn must then be rejected, NOT committed).
///
/// v1 floor only: it runs the v1 hand-AIR predicate `bespoke_air_accepts`. The recursion tower's
/// FRI-free inline revalidation is the rotated descriptor's constraint check (a future lane).
#[cfg(not(feature = "recursion"))]
pub fn revalidate_turn_self_sovereign(
    initial_state: &CellState,
    effects: &[effect_vm::Effect],
) -> Result<BabyBear, ()> {
    // Fixed, distinct, non-zero probe alphas: several independent alphas make
    // the alpha-fold a faithful AND of the individual gates (one unlucky alpha
    // could spuriously cancel a non-trivial gate; k alphas drive the
    // false-accept probability to ~(#gates/|F|)^k ≈ 0).
    const ALPHAS: [u32; 4] = [0x1234_5678, 0x9abc_def1, 0x2468_ace0, 0x7777_7777];
    let alphas: Vec<BabyBear> = ALPHAS.iter().map(|&a| BabyBear::new(a)).collect();

    let (trace, mut pis) = effect_vm::generate_effect_vm_trace(initial_state, effects);
    pis[dregg_circuit::effect_vm::pi::IS_AGENT_CELL] = BabyBear::ONE;

    if dregg_circuit::effect_vm_p3_full_air::bespoke_air_accepts(&trace, &pis, &alphas) {
        Ok(pis[dregg_circuit::effect_vm::pi::NEW_COMMIT])
    } else {
        Err(())
    }
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
    use dregg_circuit::dsl::circuit::{ColumnDef, ColumnKind, ConstraintExpr, DslCircuit};

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
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
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
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];

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
            cap_membership: None,
            turn_hash: [0x77u8; 32],
            rotation: None,
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

        verify_full_turn(&proof, old_commit, new_commit).expect(
            "full turn with membership + non-revocation must verify on the audited p3 path",
        );
    }

    /// FRESHNESS / no-double-spend — binding (a), HONEST: a full turn whose
    /// non-revocation proof proves freshness against the CANONICAL accumulator
    /// root verifies through `verify_full_turn_bound(Some(canonical_root))`.
    #[test]
    fn freshness_bound_turn_with_canonical_root_verifies() {
        use dregg_circuit::dsl::revocation::DslRevocationTree;
        use dregg_circuit::poseidon2::hash_many;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];

        // THE canonical published nullifier accumulator for this turn.
        let revoked: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect();
        let canonical_tree = DslRevocationTree::new(revoked, 4);
        let canonical_root = canonical_tree.root();
        let fresh_item = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);

        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects,
            authorization: None,
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree: canonical_tree,
                item_hash: fresh_item,
            }),
            cap_membership: None,
            turn_hash: [0x91u8; 32],
            rotation: None,
        };
        let proof = prove_full_turn(&witness).expect("honest fresh-spend proof should generate");

        let old_commit = initial.state_commitment;
        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        verify_full_turn_bound(&proof, old_commit, new_commit, Some(canonical_root), None).expect(
            "honest fresh spend (freshness proven against THE canonical accumulator root) must verify",
        );
    }

    /// FRESHNESS / no-double-spend — binding (a), ANTI-FORGERY (the gap this
    /// closes): a turn whose non-revocation proof proves freshness against a
    /// DIFFERENT (prover-chosen) accumulator root — here an EMPTY tree, in which
    /// the item is trivially absent — MUST be rejected when the verifier pins the
    /// canonical root. This is the counterfeiting hole: an internally-sound
    /// non-membership proof against a tree of the prover's choosing is NOT a
    /// proof of freshness against the canonical nullifier set. The
    /// `RevocationRootMismatch` tooth is the ONLY thing standing between the
    /// prover's hand-picked accumulator and acceptance — and it MUST reject.
    #[test]
    fn freshness_bound_turn_rejects_prover_chosen_root() {
        use dregg_circuit::dsl::revocation::DslRevocationTree;
        use dregg_circuit::poseidon2::hash_many;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];

        // THE canonical accumulator the verifier expects (the item IS revoked in it).
        let spent = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);
        let canonical_revoked: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .chain(std::iter::once(spent)) // the item the prover wants to re-spend IS here
            .collect();
        let canonical_tree = DslRevocationTree::new(canonical_revoked, 4);
        let canonical_root = canonical_tree.root();
        assert!(
            canonical_tree.contains(&spent),
            "precondition: the item is genuinely revoked in the canonical accumulator",
        );

        // The PROVER picks its OWN accumulator that OMITS the item, so its
        // internally-sound non-membership proof succeeds — against the WRONG tree.
        let prover_revoked: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect(); // `spent` deliberately ABSENT
        let prover_tree = DslRevocationTree::new(prover_revoked, 4);
        let prover_root = prover_tree.root();
        assert_ne!(
            prover_root, canonical_root,
            "the prover's hand-picked accumulator must differ from the canonical one",
        );

        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects,
            authorization: None,
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree: prover_tree, // freshness "proven" against the prover's own tree
                item_hash: spent,
            }),
            cap_membership: None,
            turn_hash: [0x92u8; 32],
            rotation: None,
        };
        let proof = prove_full_turn(&witness)
            .expect("proof generates (the forgery is a verify-time property)");

        let old_commit = initial.state_commitment;
        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        // With the canonical root pinned, the prover-chosen root is rejected.
        let result =
            verify_full_turn_bound(&proof, old_commit, new_commit, Some(canonical_root), None);
        match result {
            Err(FullTurnVerifyError::RevocationRootMismatch { expected, got }) => {
                assert_eq!(expected, canonical_root);
                assert_eq!(got, prover_root);
            }
            Ok(()) => panic!(
                "SOUNDNESS (no-double-spend): verify_full_turn_bound ACCEPTED a turn whose \
                 freshness was proven against a PROVER-CHOSEN accumulator (the item is revoked \
                 in the canonical one) — the counterfeiting hole is OPEN!"
            ),
            Err(other) => panic!(
                "expected RevocationRootMismatch (the no-double-spend tooth), got: {other:?}",
            ),
        }

        // CONTROL: the legacy `verify_full_turn` (no canonical root pinned) does
        // NOT catch this — confirming the tooth, not some unrelated check, is
        // what rejects above. (Internal non-membership math is sound against the
        // prover's tree, so the legacy path accepts.)
        verify_full_turn(&proof, old_commit, new_commit).expect(
            "legacy verify_full_turn (root unpinned) accepts the internally-sound proof — \
             proving binding (a) is exactly what closes the gap",
        );
    }

    /// BINDING (b) CLOSED — circuit guard: the audited non-revocation circuit
    /// now exposes the queried item as its second public input
    /// (`pi::QUERIED_ITEM`), bound in-circuit to control-row `COL_0` by a row-0
    /// `PiBinding` boundary. This guards against silent regression of the
    /// circuit half of binding (b): if the item PI is ever removed (back to
    /// `public_input_count == 1` / no row-0 COL_0 boundary), the verifier's
    /// nullifier tooth (step 8) would have nothing real to compare and this test
    /// fails LOUDLY.
    #[test]
    fn revocation_item_pi_exposed_binding_b_closed() {
        use dregg_circuit::dsl::circuit::{BoundaryDef, BoundaryRow};
        use dregg_circuit::dsl::revocation::{col as rcol, pi as rpi};

        let desc = dregg_circuit::dsl::revocation::non_revocation_circuit_descriptor();
        assert_eq!(
            desc.public_input_count, 2,
            "the audited non-revocation circuit must publish [revocation_root, queried_item] so \
             verify_full_turn_bound can bind the proven-fresh item to this turn's nullifier \
             (no-double-spend binding b)",
        );
        // The queried-item PI must be a REAL binding: a row-0 PiBinding tying
        // control-row COL_0 (the value the ordering constraints bracket) to
        // pi[QUERIED_ITEM]. A free felt would make the SDK tooth vacuous.
        let has_item_boundary = desc.boundaries.iter().any(|b| {
            matches!(
                b,
                BoundaryDef::PiBinding {
                    row: BoundaryRow::Index(0),
                    col,
                    pi_index,
                } if *col == rcol::COL_0 && *pi_index == rpi::QUERIED_ITEM
            )
        });
        assert!(
            has_item_boundary,
            "the queried-item PI must be pinned by a row-0 PiBinding on COL_0 — otherwise pi[1] is \
             a free wire and the item==nullifier tooth would be vacuous",
        );
    }

    /// FRESHNESS / no-double-spend — binding (b), HONEST: a turn that SPENDS a
    /// note (so `PI[NOTESPEND_NULLIFIER]` is populated) and carries a
    /// non-revocation proof of freshness for EXACTLY that nullifier verifies
    /// through `verify_full_turn` — the new step-8 nullifier tooth accepts when
    /// the proven-fresh item IS this turn's nullifier.
    #[test]
    fn freshness_binding_b_honest_spend_verifies() {
        use dregg_circuit::dsl::revocation::DslRevocationTree;
        use dregg_circuit::effect_vm::pi as vmpi;
        use dregg_circuit::poseidon2::hash_many;

        let initial = CellState::new(1000, 0);
        // This turn's spent nullifier — a value known fresh against the tree
        // below (the same item the binding-(a) tests prove non-membership for).
        let nullifier = hash_many(&[BabyBear::new(0xBEEF), BabyBear::new(0xCAFE)]);
        let effects = vec![VmEffect::NoteSpend {
            nullifier,
            value: 500,
        }];

        // A revocation accumulator in which the nullifier is NOT yet present
        // (the note has not been spent before — it is fresh).
        let revoked: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect();
        let tree = DslRevocationTree::new(revoked, 4);

        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            authorization: None,
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree,
                item_hash: nullifier, // freshness proven for THIS turn's nullifier
            }),
            cap_membership: None,
            turn_hash: [0xB1u8; 32],
            rotation: None,
        };
        let proof = prove_full_turn(&witness).expect("honest fresh-spend proof should generate");

        // Sanity: the EffectVM PI carries the nullifier (so step 8 actually fires).
        let eff = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm")
            .unwrap();
        assert_eq!(
            eff.sub_public_inputs[vmpi::NOTESPEND_NULLIFIER],
            nullifier,
            "precondition: the spend turn surfaces its nullifier into PI[NOTESPEND_NULLIFIER]",
        );

        let old_commit = initial.state_commitment;
        let new_commit = eff.sub_public_inputs[vmpi::NEW_COMMIT];

        verify_full_turn(&proof, old_commit, new_commit).expect(
            "honest spend whose freshness is proven for THIS turn's nullifier must verify \
             (binding b accepts item == nullifier)",
        );
    }

    /// FRESHNESS / no-double-spend — binding (b), ANTI-FORGERY (the gap this
    /// closes): a turn that spends nullifier N but whose non-revocation proof
    /// proves freshness for a DIFFERENT item M (≠ N) MUST be rejected by
    /// `verify_full_turn` with `NullifierMismatch`. This is the counterfeiting
    /// hole binding (b) closes: proving "some OTHER item is fresh" must not let a
    /// double-spend of N through. The queried item is bound in-circuit to the
    /// non-revocation proof (row-0 COL_0 boundary), so the published `pi[1]` is
    /// the genuinely-proven item — step 8's `pi[1] != PI[NOTESPEND_NULLIFIER]`
    /// comparison is the ONLY thing between the mismatched freshness and
    /// acceptance, and it MUST reject.
    #[test]
    fn freshness_binding_b_rejects_wrong_item() {
        use dregg_circuit::dsl::revocation::DslRevocationTree;
        use dregg_circuit::effect_vm::pi as vmpi;
        use dregg_circuit::poseidon2::hash_many;

        let initial = CellState::new(1000, 0);
        // This turn spends nullifier N.
        let nullifier = hash_many(&[BabyBear::new(0x0_7E), BabyBear::new(0x5EED)]);
        let effects = vec![VmEffect::NoteSpend {
            nullifier,
            value: 500,
        }];

        // The prover proves freshness for a DIFFERENT item M (not the nullifier),
        // which is genuinely absent from the accumulator — an internally-sound
        // non-membership proof, but for the WRONG item.
        let other_item = hash_many(&[BabyBear::new(0xDEC0), BabyBear::new(0xDED)]);
        assert_ne!(other_item, nullifier);
        let revoked: Vec<BabyBear> = (1..=20u32)
            .map(|i| hash_many(&[BabyBear::new(i * 100), BabyBear::new(0xDEAD)]))
            .collect();
        let tree = DslRevocationTree::new(revoked, 4);

        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            authorization: None,
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree,
                item_hash: other_item, // freshness proven for the WRONG item
            }),
            cap_membership: None,
            turn_hash: [0xB2u8; 32],
            rotation: None,
        };
        let proof = prove_full_turn(&witness)
            .expect("proof generates (the mismatch is a verify-time property)");

        let eff = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm")
            .unwrap();
        let old_commit = initial.state_commitment;
        let new_commit = eff.sub_public_inputs[vmpi::NEW_COMMIT];

        let result = verify_full_turn(&proof, old_commit, new_commit);
        match result {
            Err(FullTurnVerifyError::NullifierMismatch {
                proven_item,
                effect_nullifier,
            }) => {
                assert_eq!(proven_item, other_item);
                assert_eq!(effect_nullifier, nullifier);
            }
            Ok(()) => panic!(
                "SOUNDNESS (no-double-spend binding b): verify_full_turn ACCEPTED a spend of \
                 nullifier N whose freshness was proven for a DIFFERENT item M — the \
                 counterfeiting hole is OPEN!"
            ),
            Err(other) => {
                panic!("expected NullifierMismatch (the binding-b tooth), got: {other:?}",)
            }
        }
    }

    /// HONEST authorization-bound turn: a derivation whose conclusion is
    /// `Allow(effects_commit)` for the turn's actual effects (built via
    /// `derivation_authorizing_effects`) verifies through `verify_full_turn`,
    /// including the new authorization↔effect binding tooth.
    #[test]
    fn auth_bound_turn_with_matching_effect_verifies() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
        let old_commit = initial.state_commitment;

        // The actor's capability evidence lives at the cell's fact-tree root
        // (== old_commitment, so the cell-binding tooth also holds).
        let capability_fact_hash = BabyBear::new(0xCA9A);
        let derivation = derivation_authorizing_effects(&effects, capability_fact_hash, old_commit);

        let proof = prove_turn_with_auth(&initial, &effects, &derivation, [0x11u8; 32])
            .expect("auth-bound proof should generate");
        assert!(proof.components.has_authorization);
        assert!(proof.components.has_state_transition);

        let mut expected_final = initial.clone();
        expected_final.balance = 900;
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        verify_full_turn(&proof, old_commit, new_commit)
            .expect("honest auth-bound turn must verify (derivation concludes Allow(this effect))");
    }

    /// ANTI-FORGERY (the gap this closes): a turn whose authorization proof
    /// authorizes a DIFFERENT effect than the Effect-VM proof certifies MUST be
    /// rejected by `verify_full_turn`. We build a fully valid authorization proof
    /// whose derivation concludes `Allow(effects_B)` (a different amount), splice
    /// it onto an Effect-VM proof for `effects_A`, fix up the shared cell-binding
    /// PI so the prior teeth (cell binding, commitments) all PASS, and confirm the
    /// new authorization↔effect tooth is the ONLY thing standing between the
    /// mismatched authorization and acceptance — and that it rejects.
    #[test]
    fn auth_bound_turn_rejects_authorization_for_different_effect() {
        let initial = CellState::new(1000, 0);
        let old_commit = initial.state_commitment;

        // The turn the Effect-VM proof actually performs: transfer 100 out.
        let effects_a = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
        // A DIFFERENT effect the malicious authorization is really for: transfer 500.
        let effects_b = vec![VmEffect::Transfer {
            amount: 500,
            direction: 1,
        }];
        // Sanity: the two effects have distinct in-circuit commitments.
        assert_ne!(
            effect_vm::compute_effects_hash(&effects_a).0,
            effect_vm::compute_effects_hash(&effects_b).0
        );

        // Authorization proof that genuinely concludes Allow(effects_B), rooted at
        // the SAME cell (so the cell-binding tooth cannot be what rejects).
        let capability_fact_hash = BabyBear::new(0xBAD0);
        let derivation_b =
            derivation_authorizing_effects(&effects_b, capability_fact_hash, old_commit);

        // Prove the turn with effects_A but the effects_B-authorizing derivation.
        let proof = prove_turn_with_auth(&initial, &effects_a, &derivation_b, [0x22u8; 32])
            .expect("proof generation succeeds (mismatch is a verify-time property)");

        let mut expected_final = initial.clone();
        expected_final.balance = 900; // effects_A: 1000 - 100
        expected_final.nonce = 1;
        expected_final.refresh_commitment();
        let new_commit = expected_final.state_commitment;

        let result = verify_full_turn(&proof, old_commit, new_commit);
        match result {
            Err(FullTurnVerifyError::AuthEffectMismatch { .. }) => { /* exactly the tooth */ }
            Ok(()) => panic!(
                "SOUNDNESS (capability-security): verify_full_turn ACCEPTED a turn whose \
                 authorization authorizes a DIFFERENT effect than the one performed — the \
                 authorization↔effect binding is not enforced!"
            ),
            Err(other) => panic!(
                "expected AuthEffectMismatch (the authorization↔effect tooth), got a \
                 different rejection: {other:?} — verify the test reached the new check",
            ),
        }
    }

    /// ANTI-GHOST end-to-end: forging the published MEMBERSHIP root in a finished
    /// full-turn proof MUST be rejected by the audited membership verifier (the
    /// proof binds the genuine hash-chain root, not the forged PI).
    #[test]
    fn full_turn_rejects_forged_membership_root() {
        use dregg_circuit::dsl::membership::create_test_witness as merkle_test_witness;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
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
            cap_membership: None,
            turn_hash: [0x88u8; 32],
            rotation: None,
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

    // ════════════════════════════════════════════════════════════════════════
    // PATH-PRESERVE — Phase 0 (run-splitter + Shape-3 confirmation, pure/fast)
    // ════════════════════════════════════════════════════════════════════════

    #[test]
    fn split_homogeneous_turn_is_one_run() {
        // A homogeneous turn (every effect the same cohort) is ONE run — so the chained path is
        // byte-identical to the single rotated leg for the existing fleet.
        let effects = vec![
            VmEffect::Transfer {
                amount: 10,
                direction: 1,
            },
            VmEffect::Transfer {
                amount: 20,
                direction: 1,
            },
            VmEffect::Transfer {
                amount: 5,
                direction: 0,
            },
        ];
        let runs = split_into_cohort_runs(&effects);
        assert_eq!(
            runs,
            vec![0..3],
            "consecutive same-cohort effects coalesce into one run"
        );
    }

    #[test]
    fn split_heterogeneous_turn_yields_runs() {
        // Transfer and SetField are DIFFERENT cohorts ⇒ three runs (no coalescing across cohorts).
        let effects = vec![
            VmEffect::Transfer {
                amount: 10,
                direction: 1,
            },
            VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(7),
            },
            VmEffect::Transfer {
                amount: 5,
                direction: 0,
            },
        ];
        let runs = split_into_cohort_runs(&effects);
        assert_eq!(runs, vec![0..1, 1..2, 2..3]);
    }

    #[test]
    fn split_coalesces_then_breaks() {
        // Two Transfers coalesce, then a SetField opens a new run.
        let effects = vec![
            VmEffect::Transfer {
                amount: 1,
                direction: 1,
            },
            VmEffect::Transfer {
                amount: 2,
                direction: 1,
            },
            VmEffect::SetField {
                field_idx: 1,
                value: BabyBear::new(3),
            },
            VmEffect::SetField {
                field_idx: 1,
                value: BabyBear::new(4),
            },
        ];
        let runs = split_into_cohort_runs(&effects);
        // Same field index ⇒ same per-slot descriptor ⇒ the two SetFields coalesce.
        assert_eq!(runs, vec![0..2, 2..4]);
    }

    #[test]
    fn split_distinct_setfield_slots_are_distinct_cohorts() {
        // `setFieldVmDescriptor2-0R24` vs `-1R24` are distinct AIRs ⇒ distinct cohorts ⇒ split.
        let effects = vec![
            VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(3),
            },
            VmEffect::SetField {
                field_idx: 1,
                value: BabyBear::new(4),
            },
        ];
        let runs = split_into_cohort_runs(&effects);
        assert_eq!(runs, vec![0..1, 1..2]);
    }

    #[test]
    fn split_empty_turn_is_no_runs() {
        let runs = split_into_cohort_runs(&[]);
        assert!(runs.is_empty(), "an empty turn has no cohort runs");
    }

    /// PATH-PRESERVE Phase 0 / Shape 3 CONFIRMATION (the CORRECTED §1 finding): a NoOp-only /
    /// empty projection is NOT provable on EITHER leg — the v1 generator ASSERTS non-empty
    /// (`trace.rs:383` `assert!(!effects.is_empty(), "Need at least one effect")`), so an empty
    /// `vm_effects` reaching `prove_and_verify_finalized_turn*` (`turn_proving.rs:526`) would
    /// PANIC today — a PRE-EXISTING condition PATH-PRESERVE neither introduces nor fixes. The
    /// rotated cohort gate ALSO refuses an empty slice (`split_into_cohort_runs(&[])` is empty, and
    /// the chained prover fails closed on zero runs). So Shape 3 must be UNREACHABLE on the live
    /// finalized path (the node only proves turns with ≥1 actor-affecting effect); this is the
    /// documented invariant. No NoOp rotated descriptor is built — that would be a NEW Lean
    /// descriptor (out of scope; an ember decision per §8) and is contingent on Shape 3 being
    /// reachable, which the v1 panic shows it is NOT (an empty projection never reached the prover
    /// without crashing, so the live path cannot be feeding it empty slices).
    #[test]
    fn shape3_empty_projection_is_not_provable_on_either_leg() {
        // The v1 generator asserts non-empty: an empty projection PANICS (pre-existing). Silence
        // the panic hook for the duration so the expected panic does not spam the test log.
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let r = std::panic::catch_unwind(|| {
            let initial = CellState::new(1234, 7);
            let _ = generate_effect_vm_trace(&initial, &[]);
        });
        std::panic::set_hook(prev_hook);
        assert!(
            r.is_err(),
            "Phase-0: the v1 generator must ASSERT non-empty (an empty projection cannot prove); \
             if this stops panicking, re-evaluate the Shape-3 invariant"
        );
        // The rotated path agrees there is nothing to rotate: zero cohort runs.
        assert!(
            split_into_cohort_runs(&[]).is_empty(),
            "an empty turn yields zero cohort runs (the chained prover fails closed on it)"
        );
        // And the chained prover fails closed (not panics) on an empty turn — its own guard.
        #[cfg(feature = "recursion")]
        {
            let initial = CellState::new(1234, 7);
            let rot = RotationTurnWitness {
                before: dregg_turn::rotation_witness::produce(
                    &dregg_cell::Cell::with_balance([0xE0; 32], [0u8; 32], 1234),
                    &dregg_cell::Ledger::new(),
                    &[0u8; 32],
                    &[[0x11u8; 32]],
                ),
                after: dregg_turn::rotation_witness::produce(
                    &dregg_cell::Cell::with_balance([0xE0; 32], [0u8; 32], 1234),
                    &dregg_cell::Ledger::new(),
                    &[0u8; 32],
                    &[[0x11u8; 32]],
                ),
                caveat: dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
            };
            let res = prove_cohort_run_chain(&initial, &[], &rot);
            assert!(
                res.is_err(),
                "the chained prover must fail closed on an empty turn"
            );
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // PATH-PRESERVE — Phase 1 (the chained N-leg prover + chain verifier; SLOW)
    //
    // Gated on `recursion` (the rotated IR-v2 path). These prove real STARKs.
    // Run with: cargo nextest run -p dregg-sdk path_preserve_chain --features recursion
    // ════════════════════════════════════════════════════════════════════════

    /// Build the per-turn rotation witnesses for a turn over a real before/after cell — the SAME
    /// construction the node's `rotation_witness_for_self_sovereign` uses, but inlined here so the
    /// SDK test does not depend on the node crate. The before/after cells are the real
    /// `RecordKernelState` the producer reads; the per-run welds carry the changing scalars.
    #[cfg(feature = "recursion")]
    fn rotation_witness_for_cells(
        before_cell: &dregg_cell::Cell,
        after_cell: &dregg_cell::Cell,
        receipt_hashes: &[[u8; 32]],
    ) -> RotationTurnWitness {
        use dregg_turn::rotation_witness as rw;
        let mut ctx_ledger = dregg_cell::Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());
        let nullifier_root = [0u8; 32];
        let before_w = rw::produce(before_cell, &ctx_ledger, &nullifier_root, receipt_hashes);
        let after_w = rw::produce(after_cell, &ctx_ledger, &nullifier_root, receipt_hashes);
        // The caveat is recomputed per-run inside the chained prover; the manifest stored here is
        // only the single-leg default and is unused by `prove_cohort_run_chain`.
        RotationTurnWitness {
            before: before_w,
            after: after_w,
            caveat: dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
        }
    }

    /// THE LOAD-BEARING DIFFERENTIAL (§6.1): a heterogeneous turn `[Transfer, SetField, Transfer]`
    /// on a real cell proves as a chain of N rotated legs whose endpoints + interior boundaries
    /// agree with the MONOLITHIC v1 reference transition, and whose Σ net_delta equals the
    /// monolithic net_delta. Then the full chained proof VERIFIES against the real pre/post
    /// commitments.
    #[cfg(feature = "recursion")]
    #[test]
    fn path_preserve_chain_equals_monolithic_and_verifies() {
        // A real (synthetic-shaped) actor cell with a balance. Heterogeneous: debit, set field,
        // credit — three cohort runs.
        let pre_balance: i64 = 1_000;
        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance);
        let effects = vec![
            VmEffect::Transfer {
                amount: 100,
                direction: 1,
            }, // -100, nonce+1
            VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(7),
            }, // field, nonce+1
            VmEffect::Transfer {
                amount: 30,
                direction: 0,
            }, // +30, nonce+1
        ];

        let initial = CellState::new(pre_balance as u64, 0);

        // The MONOLITHIC v1 reference: one trace over ALL effects from the real pre-state.
        let (_mono_trace, mono_pi) = generate_effect_vm_trace(&initial, &effects);
        let mono_old = mono_pi[effect_vm::pi::OLD_COMMIT];
        let mono_new = mono_pi[effect_vm::pi::NEW_COMMIT];
        let mono_mag = mono_pi[effect_vm::pi::NET_DELTA_MAG].0 as i64;
        let mono_sign = mono_pi[effect_vm::pi::NET_DELTA_SIGN].0;
        let mono_net = if mono_sign == 1 { -mono_mag } else { mono_mag };
        // Sanity: net = -100 + 30 = -70.
        assert_eq!(mono_net, -70);

        // The real after-cell: balance 1000 - 100 + 30 = 930, field[0] set, nonce 3.
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance(930);
        after_cell.state.fields[0] = {
            // field_element_to_bb's inverse is not needed here — set the cell field to the same
            // 32-byte encoding the SetField projects. The SetField value is BabyBear::new(7);
            // the cell stores a [u8;32]. For OLD/NEW agreement we only need the EFFECT-VM
            // commitment to match, which is driven by the welds from the v1 trace, not the cell's
            // raw field bytes — so the after-cell's field bytes need only be SOME non-zero marker
            // for the producer's authority/heap views. Use the canonical little-endian of 7.
            let mut b = [0u8; 32];
            b[0] = 7;
            b
        };

        let rot = rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]]);

        // Build the chained legs directly (the prover the composed path uses).
        let legs = prove_cohort_run_chain(&initial, &effects, &rot)
            .expect("heterogeneous turn must prove as a chain of rotated legs");
        assert_eq!(legs.len(), 3, "three cohort runs ⇒ three rotated legs");
        for leg in &legs {
            assert_eq!(leg.label, "effect-vm-rotated");
        }

        // ENDPOINTS agree with the monolithic transition.
        let first_old = legs[0].sub_public_inputs[effect_vm::pi::OLD_COMMIT];
        let last_new = legs[2].sub_public_inputs[effect_vm::pi::NEW_COMMIT];
        assert_eq!(first_old, mono_old, "chain start OLD == monolithic OLD");
        assert_eq!(last_new, mono_new, "chain end NEW == monolithic NEW");

        // INTERIOR chain closes: leg_k.NEW == leg_{k+1}.OLD.
        for w in legs.windows(2) {
            assert_eq!(
                w[0].sub_public_inputs[effect_vm::pi::NEW_COMMIT],
                w[1].sub_public_inputs[effect_vm::pi::OLD_COMMIT],
                "interior chain boundary must close"
            );
        }

        // Σ net_delta across the chain == monolithic net_delta.
        let mut chain_net: i64 = 0;
        for leg in &legs {
            let mag = leg.sub_public_inputs[effect_vm::pi::NET_DELTA_MAG].0 as i64;
            let sign = leg.sub_public_inputs[effect_vm::pi::NET_DELTA_SIGN].0;
            chain_net += if sign == 1 { -mag } else { mag };
        }
        assert_eq!(
            chain_net, mono_net,
            "Σ net_delta(legs) == monolithic net_delta"
        );

        // The FULL composed chained proof proves + verifies against the real pre/post commitments.
        let proof = prove_turn_self_sovereign_rotated(&initial, &effects, [0x5A; 32], Some(rot))
            .expect("chained composed proof must generate");
        let labels: Vec<&str> = proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert_eq!(
            labels.iter().filter(|l| **l == "effect-vm-rotated").count(),
            3,
            "the composed proof carries THREE rotated legs; labels = {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "no v1 leg on the chained path; labels = {labels:?}"
        );
        verify_full_turn(&proof, mono_old, mono_new)
            .expect("the chained heterogeneous proof must verify against the chain endpoints");
    }

    /// ANTI-GHOST (§6.2): a tampered MIDDLE-leg commitment breaks the chain — `verify_full_turn`
    /// rejects (either the leg's own re-verification fails because PI desyncs from proof, OR the
    /// adjacency chain-check fires). Either rejection path is the soundness tooth.
    #[cfg(feature = "recursion")]
    #[test]
    fn path_preserve_tampered_middle_leg_is_rejected() {
        let before_cell = dregg_cell::Cell::with_balance([0xA2; 32], [0u8; 32], 1_000);
        let effects = vec![
            VmEffect::Transfer {
                amount: 100,
                direction: 1,
            },
            VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(7),
            },
            VmEffect::Transfer {
                amount: 30,
                direction: 0,
            },
        ];
        let initial = CellState::new(1_000, 0);
        let (_mt, mono_pi) = generate_effect_vm_trace(&initial, &effects);
        let mono_old = mono_pi[effect_vm::pi::OLD_COMMIT];
        let mono_new = mono_pi[effect_vm::pi::NEW_COMMIT];

        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance(930);
        after_cell.state.fields[0] = {
            let mut b = [0u8; 32];
            b[0] = 7;
            b
        };
        let rot = rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]]);

        let mut proof =
            prove_turn_self_sovereign_rotated(&initial, &effects, [0x5A; 32], Some(rot))
                .expect("chained composed proof must generate");
        // Honest proof verifies.
        verify_full_turn(&proof, mono_old, mono_new).expect("honest chained proof verifies");

        // TAMPER the middle leg's NEW_COMMIT PI (off by one felt) — the chain no longer closes.
        let rotated_idx: Vec<usize> = proof
            .composed
            .sub_proofs
            .iter()
            .enumerate()
            .filter(|(_, sp)| sp.label == "effect-vm-rotated")
            .map(|(i, _)| i)
            .collect();
        assert_eq!(rotated_idx.len(), 3);
        let mid = rotated_idx[1];
        proof.composed.sub_proofs[mid].sub_public_inputs[effect_vm::pi::NEW_COMMIT] =
            proof.composed.sub_proofs[mid].sub_public_inputs[effect_vm::pi::NEW_COMMIT]
                + BabyBear::new(1);

        let res = verify_full_turn(&proof, mono_old, mono_new);
        assert!(
            res.is_err(),
            "SOUNDNESS: a tampered middle-leg commitment MUST be rejected (chain break / leg \
             re-verify), got Ok"
        );
    }

    /// CONSERVATION across the chain (§6.4): a turn whose runs have OPPOSING deltas (outgoing then
    /// incoming Transfer) sums to the net; the conservation leg checks Σ. A homogeneous run can't
    /// expose this (a single Transfer cohort coalesces), so we interpose a SetField to force two
    /// Transfer runs with opposite signs.
    #[cfg(feature = "recursion")]
    #[test]
    fn path_preserve_conservation_sums_across_the_chain() {
        let before_cell = dregg_cell::Cell::with_balance([0xA3; 32], [0u8; 32], 1_000);
        let effects = vec![
            VmEffect::Transfer {
                amount: 100,
                direction: 1,
            }, // -100
            VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(7),
            },
            VmEffect::Transfer {
                amount: 100,
                direction: 0,
            }, // +100  ⇒ net 0
        ];
        let initial = CellState::new(1_000, 0);
        let (_mt, mono_pi) = generate_effect_vm_trace(&initial, &effects);
        let mono_old = mono_pi[effect_vm::pi::OLD_COMMIT];
        let mono_new = mono_pi[effect_vm::pi::NEW_COMMIT];

        // After: balance back to 1000, field set, nonce 3.
        let mut after_cell = before_cell.clone();
        after_cell.state.fields[0] = {
            let mut b = [0u8; 32];
            b[0] = 7;
            b
        };
        let rot = rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]]);

        // Compose WITH a conservation witness of the correct net (0). The prover's conservation
        // block sums Σ net_delta across the legs and must equal 0.
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            authorization: None,
            membership: None,
            conservation: Some(ConservationWitness {
                expected_net_delta: 0,
            }),
            non_revocation: None,
            cap_membership: None,
            turn_hash: [0x5A; 32],
            rotation: Some(rot),
        };
        let proof = prove_full_turn(&witness)
            .expect("chained proof with a correct Σ-net=0 conservation witness must generate");
        assert!(proof.components.has_conservation);
        verify_full_turn(&proof, mono_old, mono_new)
            .expect("the conserving chained proof must verify");
    }

    /// CONSERVATION anti-ghost: a WRONG expected net (the prover claims +5 when Σ = 0) is rejected
    /// at prove time by the chain-summed conservation check.
    #[cfg(feature = "recursion")]
    #[test]
    fn path_preserve_conservation_wrong_net_is_rejected() {
        let before_cell = dregg_cell::Cell::with_balance([0xA4; 32], [0u8; 32], 1_000);
        let effects = vec![
            VmEffect::Transfer {
                amount: 100,
                direction: 1,
            },
            VmEffect::SetField {
                field_idx: 0,
                value: BabyBear::new(7),
            },
            VmEffect::Transfer {
                amount: 100,
                direction: 0,
            },
        ];
        let initial = CellState::new(1_000, 0);
        let mut after_cell = before_cell.clone();
        after_cell.state.fields[0] = {
            let mut b = [0u8; 32];
            b[0] = 7;
            b
        };
        let rot = rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]]);
        let witness = FullTurnWitness {
            initial_cell_state: initial,
            effects,
            authorization: None,
            membership: None,
            conservation: Some(ConservationWitness {
                expected_net_delta: 5,
            }), // WRONG
            non_revocation: None,
            cap_membership: None,
            turn_hash: [0x5A; 32],
            rotation: Some(rot),
        };
        let res = prove_full_turn(&witness);
        assert!(
            res.is_err(),
            "SOUNDNESS: a wrong chain-summed conservation net MUST be rejected at prove time"
        );
    }
}
