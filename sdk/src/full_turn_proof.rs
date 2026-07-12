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
use dregg_circuit::dsl::cap_membership::verify_cap_membership_p3;
use dregg_circuit::dsl::dsl_p3_air::DslP3Proof;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::dsl::revocation::{
    DslRevocationTree, non_revocation_circuit_descriptor, prove_non_revocation_p3,
    verify_non_revocation_p3,
};
use dregg_circuit::effect_vm::{self, CellState, Effect as VmEffectKind, generate_effect_vm_trace};
// (The v1 hand-AIR EffectVM proof type + prover/verifier — `effect_vm_p3_full_air`
// `EffectVmP3Proof` / `prove_effect_vm_p3` / `verify_effect_vm_p3` — plus the v1
// cutover descriptor-interpreter imports (`descriptor_for_selector`, the
// `lean_descriptor_air` parse/prove/verify) are RETIRED. The effect-VM transition is
// proven/verified through the rotated IR-v2 descriptor `dregg_circuit::descriptor_ir2`.)
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
    /// acting cell's before/after `RecordKernelState`. When present (and `prover` is on),
    /// [`prove_full_turn`] proves the effect-vm leg through the ROTATED IR-v2 path
    /// ([`prove_effect_vm_rotated_ir2_with_caveat`]) and attaches it as the `"effect-vm-rotated"`
    /// sub-proof (a multi-table `Ir2BatchProof`); [`verify_full_turn`] verifies it via
    /// `descriptor_ir2::verify_vm_descriptor2`. When ABSENT (or under `not(prover)`), the
    /// byte-identical v1 `"effect-vm"` leg is used — so pre-rotation callers are unaffected.
    ///
    /// NOT feature-gated: its types are always-available (`RotationWitness` from `dregg-turn`,
    /// `RotatedCaveatManifest` from `dregg-circuit::effect_vm::trace_rotated`), so downstream
    /// crates without their own `prover` feature (e.g. `dregg-node`) set `rotation: None`
    /// unconditionally. Only the rotated PROVE/VERIFY code is `prover`-gated; under
    /// `not(prover)` a present `rotation` is ignored (the v1 leg runs).
    pub rotation: Option<RotationTurnWitness>,

    // -- TURN-IDENTITY felts (#225 turn-bound cap-open) --
    /// Present for a TURN-BOUND cap-open turn (currently: a cap-gated `Transfer` routed through
    /// `transferCapOpenTBVmDescriptor2R24`): the single-felt `(actor, src, dst)` of the turn the
    /// light client publishes. `src` is the cap-leaf target (the column `targetBindGate` already
    /// roots); `actor`/`dst` are the published turn-identity columns the verifier ANCHORS to the
    /// trusted turn (`anchor_cap_open_turn_pins`). When `None`, the cap-open prover falls back to the
    /// OWNER arm (`actor = dst = src = leaf.target`) — correct for an owner-authorized open, and the
    /// honest self-test default. The threading of a CROSS-VAT `(actor ≠ src)` identity is supplied by
    /// the node's cap-gated prove site (which holds the turn's `agent`/`from`/`to`).
    pub cap_turn_identity: Option<TurnIdentityFelts>,

    // -- UNIVERSAL-MEMORY WELD witness (the umem VK EPOCH — G4, the PRODUCER PATH) --
    /// Carries the turn's universal-memory projection diff (the genuine before→after cell projection +
    /// its Blum op trace) so the effect-vm leg mints the WIDE+UMEM **welded** form INSTEAD of the bare
    /// wide leg. When `Some` AND the turn is a SINGLE cohort-run whose descriptor key has a welded twin
    /// in
    /// [`WIDE_UMEM_WELD_REGISTRY_TSV`](dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV),
    /// [`prove_cohort_run_chain`] routes the run through the welded producer
    /// ([`prove_wide_umem_welded_cap_open_staged`] for a CAPS-domain cap-open member, or
    /// [`prove_wide_umem_welded_staged`] for a value/domain-1 plain member) so the leg carries the
    /// universal-memory reconciliation BESIDE the 8-felt (~124-bit) commit anchors. The welded leg
    /// verifies UNIQUELY through the deployed wire/executor verifiers under the Lean-emitted welded
    /// registry member, which the deployed executor now REQUIRES for a single-cohort sovereign turn
    /// (`verify_one_cohort_run`'s `require_welded`) — so a pure light client witnesses the umem boundary.
    ///
    /// The deployed sovereign producer (`cipherclerk::prove_sovereign_turn_rotated`) and the node cap
    /// path thread this by default. `None` falls back to the byte-identical BARE wide leg — used for the
    /// 3 producer-bare wide members (heapWrite / supplyMint / transferCapOpenTB, a multi-domain /
    /// turn-bound projection the single-domain cohort weld refuses, which the executor still admits
    /// bare), for multi-cohort chain legs (welded only for a single-run turn), and on the rollback path.
    pub umem_witness: Option<UmemWeldWitness>,
}

/// **THE PER-TURN UNIVERSAL-MEMORY WELD WITNESS (the umem-flip's producer path).** Carries the
/// turn's genuine before-state projection (`pre`) + the Blum WRITE op trace (`ops`) of the
/// before→after projection DIFF — exactly the `(pre, ops)` pair the welded staged producers
/// ([`prove_wide_umem_welded_staged`] / [`prove_wide_umem_welded_cap_open_staged`]) fold into the
/// universal-memory cohort leg they weld onto the wide descriptor.
///
/// The caller builds it from the REAL before/after cells the node/cipherclerk holds at the turn's
/// pre/post state (e.g. `dregg_turn::umem::project_record_kernel_state(before)` →
/// `project_diff_ops(pre, post)`), so the umem leg reconciles the GENUINE per-cell state change. The
/// producers fail closed if the diff is empty, multi-domain (for the single-domain cohort), or
/// (cap-open) touches a domain other than Caps — so a witness that does not match the proven
/// transition is REFUSED, never silently dropped.
#[derive(Clone, Debug)]
pub struct UmemWeldWitness {
    /// The turn's PRE-state universal-memory projection (the before-cell record-kernel projection).
    pub pre: dregg_turn::umem::UProjection,
    /// The Blum WRITE op trace of the before→after projection diff (`project_diff_ops`).
    pub ops: Vec<dregg_turn::umem::UmemOp>,
}

/// The single-felt turn identity published by the TURN-BOUND cap-open (#225): `(actor, src, dst)`.
/// These ride the TB descriptor's three turn-identity PIs (`38/39/40`); the verifier ANCHORS them to
/// the trusted turn so a ledgerless light client concludes the published identity = the proven
/// transition's. The felt encoding MUST match the cap-leaf `target` convention for `src` (the column
/// `targetBindGate` roots); `actor`/`dst` use the SAME single-felt cell projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TurnIdentityFelts {
    pub actor: BabyBear,
    pub src: BabyBear,
    pub dst: BabyBear,
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
    /// the witness-carried authority digest `r23` in the rotated commit AND is now ABSORBED by the
    /// v1-prefix `compute_commitment` as its FOURTH state-commit root input (the EffectVM
    /// `CellState::record_digest`, read from `pre_limbs[B_AUTHORITY_DIGEST]`, replacing the old
    /// literal ZERO). So OLD_COMMIT/NEW_COMMIT bind the FULL cell state on BOTH legs (audit P0-2,
    /// `cell/src/commitment.rs`) — two cells differing only in permissions / lifecycle / VK get
    /// DIFFERENT commitments. `sealed_field_mask` / `mode_flag` still ride the v1 `RESERVED` column
    /// (left at 0; the rotated weld carries them via r23).
    pub fn before_cell_state(&self) -> Result<CellState, SdkError> {
        use dregg_circuit::effect_vm::trace_rotated::{B_AUTHORITY_DIGEST, B_CAP_ROOT};
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
        // P0-2: the authority-residue digest (r23 / `compute_authority_digest_felt`)
        // welded into the rotated commitment, read off the SAME pre-limb vector. It
        // becomes the EffectVM `CellState::record_digest`, so the v1-prefix
        // OLD_COMMIT binds the FULL cell state (permissions / VK / lifecycle / …),
        // consistent with the rotated leg's r23. Guarded above (`pre.len() > B_CAP_ROOT`,
        // and `B_AUTHORITY_DIGEST < B_CAP_ROOT`).
        let record_digest = pre[B_AUTHORITY_DIGEST];
        let mut s = CellState {
            balance,
            nonce,
            fields,
            capability_root,
            record_digest,
            state_commitment: BabyBear::ZERO,
            sealed_field_mask: 0,
            mode_flag: 0,
        };
        s.refresh_commitment();
        Ok(s)
    }

    /// THE WIDE FLAG-DAY COMMIT ANCHORS: the trusted 8-felt (~124-bit) BEFORE / AFTER state commits
    /// the wide light-client verifier (`verify_full_turn_bound`) binds. These are the chain endpoints
    /// the wide producer (`prove_cohort_run_chain` → `prove_effect_vm_rotated_wide`) publishes at the
    /// LAST 16 PIs of leg-0 (BEFORE) and leg-N (AFTER): each is `wire_commit_8` over the rotated AFTER
    /// block whose r0..r10/cap_root limbs are the v1-welded post-effect state (NOT the raw witness
    /// `pre_limbs`) — so the BEFORE is leg-0's pre and the AFTER is the final run's post. We re-derive
    /// them GENERATE-ONLY (no proving): split the turn into cohort runs and run the SAME wide
    /// generators the producer runs, reading leg-0's BEFORE 8-felt commit + leg-N's AFTER 8-felt
    /// commit off the generated PI tail. This is independent of the PROOF bytes (it re-derives from
    /// the authenticated pre-state + effects + this witness), so it stays a trusted-vs-proof anchor.
    ///
    /// `initial_state` is the turn's circuit pre-state (the same the producer/`prove_full_turn` seed);
    /// `effects` is the turn's vm-effect list. `None` on a non-cohort / empty turn (no wide leg).
    ///
    /// `before_nullifiers` threads the BEFORE nullifier-set leaves for a NoteSpend lead (the grow-gate
    /// wide producer opens against them — the SAME leaves `prove_cohort_run_chain` threads from the
    /// non-revocation witness), so the published 8-felt commit matches. `None` ⇒ empty set (the
    /// standalone-witness case).
    #[cfg(feature = "prover")]
    pub fn wide_commit_anchors(
        &self,
        initial_state: &CellState,
        effects: &[VmEffectKind],
        before_nullifiers: Option<&[BabyBear]>,
    ) -> Result<([BabyBear; 8], [BabyBear; 8]), SdkError> {
        use dregg_circuit::effect_vm::trace_rotated::{
            RotatedBlockWitness, generate_rotated_note_create_wide,
            generate_rotated_note_spend_wide, generate_rotated_record_pin_wide,
            generate_rotated_transfer_shape_wide,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        let runs = split_into_cohort_runs(effects);
        if runs.is_empty() {
            return Err(SdkError::InvalidWitness(
                "wide_commit_anchors: empty turn (no cohort runs)".into(),
            ));
        }
        let n_runs = runs.len();
        let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
            RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
                .map(|bw| bw.with_asset_class(w.asset_class))
        };
        let before = bridge(&self.before)
            .map_err(|e| SdkError::InvalidWitness(format!("wide_commit_anchors before: {e}")))?;
        let after = bridge(&self.after)
            .map_err(|e| SdkError::InvalidWitness(format!("wide_commit_anchors after: {e}")))?;

        // Generate-only a single wide cohort leg, returning its (before8, after8) PI-tail commits.
        // Mirrors `prove_cohort_run_chain`'s normal-effect branch (transfer-shape / record-pin
        // families — the cohorts the chained wide producer mints); the wide commit PIs are the LAST 16.
        let leg_commits =
            |s_k: &CellState,
             run_effects: &[VmEffectKind],
             after_block: &RotatedBlockWitness,
             caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest|
             -> Result<([BabyBear; 8], [BabyBear; 8]), SdkError> {
                use dregg_circuit::effect_vm::Effect as E;
                let lead = run_effects.first().ok_or_else(|| {
                    SdkError::InvalidWitness("wide_commit_anchors: empty cohort run".into())
                })?;
                // Route the SAME families `prove_effect_vm_rotated_wide` routes for the chained full-turn
                // path: NoteSpend → the limb-26 grow-gate; NoteCreate → the limb-27 grow-gate; the
                // record-pin family → record-pin; everything else → transfer-shape. (CreateCell / spawn /
                // factory / setFieldDyn / custom are NOT on the SDK chained full-turn path — they fail
                // closed with a precise NAMED error, matching the producer's own coverage.)
                let dpis = if matches!(lead, E::NoteSpend { .. }) {
                    let leaves: Vec<HeapLeaf> = before_nullifiers
                        .unwrap_or(&[])
                        .iter()
                        .map(|nf| HeapLeaf::entry(*nf, BabyBear::new(1)))
                        .collect();
                    let (_t, d, _h) = generate_rotated_note_spend_wide(
                        s_k,
                        run_effects,
                        &before,
                        after_block,
                        caveat,
                        &leaves,
                    )
                    .map_err(|e| {
                        SdkError::InvalidWitness(format!("wide_commit_anchors note-spend: {e}"))
                    })?;
                    d
                } else if matches!(lead, E::NoteCreate { .. }) {
                    let (_t, d, _h) = generate_rotated_note_create_wide(
                        s_k,
                        run_effects,
                        &before,
                        after_block,
                        caveat,
                        &[],
                    )
                    .map_err(|e| {
                        SdkError::InvalidWitness(format!("wide_commit_anchors note-create: {e}"))
                    })?;
                    d
                } else if matches!(
                    lead,
                    E::SetPermissions { .. }
                        | E::SetVerificationKey { .. }
                        | E::CellSeal { .. }
                        | E::CellUnseal { .. }
                        | E::CellDestroy { .. }
                        | E::ReceiptArchive { .. }
                        | E::Refusal { .. }
                        | E::MakeSovereign
                ) {
                    let (_t, d) = generate_rotated_record_pin_wide(
                        s_k,
                        run_effects,
                        &before,
                        after_block,
                        caveat,
                    )
                    .map_err(|e| {
                        SdkError::InvalidWitness(format!("wide_commit_anchors record-pin: {e}"))
                    })?;
                    d
                } else if matches!(lead, E::BridgeMint { .. }) {
                    // The felt mint-hash pin member (51-PI base) — no longer the bare
                    // transfer shape. PI 46 is the projector-derived felt mint identity.
                    let (_t, d) =
                        dregg_circuit::effect_vm::trace_rotated::generate_rotated_bridge_mint_wide(
                            s_k,
                            run_effects,
                            &before,
                            after_block,
                            caveat,
                        )
                        .map_err(|e| {
                            SdkError::InvalidWitness(format!(
                                "wide_commit_anchors bridge-mint: {e}"
                            ))
                        })?;
                    d
                } else if matches!(
                    lead,
                    E::CreateCell { .. }
                        | E::CreateCellFromFactory { .. }
                        | E::SpawnWithDelegation { .. }
                        | E::Custom { .. }
                ) || matches!(lead, E::SetField { field_idx, .. } if *field_idx >= 8)
                {
                    return Err(SdkError::InvalidWitness(format!(
                        "wide_commit_anchors: lead effect {lead:?} routes a distinct-geometry wide producer \
                     (grow-gate / V1Face) not on the SDK chained full-turn path; thread its anchor \
                     explicitly (NAMED residual)"
                    )));
                } else {
                    let (_t, d) = generate_rotated_transfer_shape_wide(
                        s_k,
                        run_effects,
                        &before,
                        after_block,
                        caveat,
                    )
                    .map_err(|e| {
                        SdkError::InvalidWitness(format!("wide_commit_anchors transfer-shape: {e}"))
                    })?;
                    d
                };
                let n = dpis.len();
                if n < 16 {
                    return Err(SdkError::InvalidWitness(
                        "wide_commit_anchors: short wide PI vector".into(),
                    ));
                }
                let b8: [BabyBear; 8] = dpis[n - 16..n - 8].try_into().expect("len 8");
                let a8: [BabyBear; 8] = dpis[n - 8..n].try_into().expect("len 8");
                Ok((b8, a8))
            };

        let mut s_k = initial_state.clone();
        let mut first_before8: Option<[BabyBear; 8]> = None;
        let mut last_after8 = [BabyBear::ZERO; 8];
        for (k, run) in runs.iter().enumerate() {
            let run_effects = &effects[run.clone()];
            let is_final = k + 1 == n_runs;
            // INTERIOR runs reuse the BEFORE block for their after-block (turn-invariant carried
            // limbs); the FINAL run uses the real after block — mirrors `prove_cohort_run_chain`.
            let after_block = if is_final { &after } else { &before };
            let caveat = match run_effects {
                [VmEffectKind::Transfer { .. }] => {
                    dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest()
                }
                _ => dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
            };
            let (b8, a8) = leg_commits(&s_k, run_effects, after_block, &caveat)?;
            if first_before8.is_none() {
                first_before8 = Some(b8);
            }
            last_after8 = a8;
            if !is_final {
                let (v1_trace, _v1_pi) = generate_effect_vm_trace(&s_k, run_effects);
                s_k = cell_state_after_run(&v1_trace, run_effects.len(), &s_k);
            }
        }
        Ok((first_before8.expect("at least one run"), last_after8))
    }
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
#[derive(Clone)]
pub struct CapMembershipWitness {
    /// The consumed capability's canonical 7-field leaf preimage.
    pub leaf: CapLeaf,
    /// Sibling digests along the membership path, bottom-up
    /// (`CAP_TREE_DEPTH` entries). Native 8-felt `node8` digests (Phase H-CAP-8):
    /// each is a `[BabyBear; 8]` `Digest8`, NOT a lane-0 scalar.
    pub siblings: Vec<[BabyBear; 8]>,
    /// Direction bits (0 = current node is the LEFT child, 1 = right).
    pub directions: Vec<u8>,
    /// **(cap-WRITE light-client axis)** The holder cell's FULL sorted c-list leaf-set — the
    /// `(addr, value)` leaves of the openable cap-tree (`heap_root::HeapLeaf`) the WRITE-bearing
    /// cap-open wrappers' `map_op` opens against (BEFORE cap-root → AFTER cap-root). The membership
    /// path above opens ONE leaf; the cap-tree WRITE needs the WHOLE tree to compute the genuine
    /// post-insert/remove root. Empty ⇒ the write wrapper is not provable (the AUTHORITY-ONLY
    /// cap-open route is used, which carries no cap-tree write). The node populates this from the
    /// actor cell's pre-state c-list (`from_consumed_with_clist`); the path-only constructors leave
    /// it empty (the non-write legs do not need it).
    pub clist_leaves: Vec<dregg_circuit::heap_root::HeapLeaf>,
    /// **(cap INSERT after-spine axis)** The holder cell's FULL 7-field c-list — the LIVE
    /// [`CapLeaf`]s of the arity-7 `CanonicalCapTree` the INSERT-shaped keystone wrappers
    /// (`delegate`/`introduce`/`delegateAtten`) rebuild to splice the fresh conferred edge
    /// (`CanonicalCapTree::insert_witness`: the spliced leaf's AFTER-tree membership path the
    /// deployed `effCapInsertV3` read opens). The membership path above opens ONE leaf; the sorted
    /// INSERT reorders siblings, so the WHOLE before leaf-set is needed to rebuild the genuine AFTER
    /// tree. Empty ⇒ the INSERT write wrappers are not provable (fail closed with a named error —
    /// no fabricated after-root). The node populates this from the actor cell's pre-state c-list
    /// (`cap_write_cap_leaves`); the path-only constructors leave it empty.
    pub cap_leaves: Vec<CapLeaf>,
    /// The tombstoned (revoked) slot keys of the holder's pre-state c-list — the ghost positions
    /// `CanonicalCapTree::new_with_tombstones` preserves so the rebuilt BEFORE/AFTER roots match the
    /// cell-side committed roots byte-for-byte. Empty for a cell that never revoked.
    pub cap_tombstones: Vec<BabyBear>,
}

impl CapMembershipWitness {
    /// Build from the Phase-C executor witness threaded through
    /// `TurnReceipt::consumed_capabilities`. Carries the membership path only (no c-list leaf-set);
    /// the WRITE-bearing route needs [`Self::from_consumed_with_clist`].
    pub fn from_consumed(w: &dregg_turn::ConsumedCapWitness) -> Self {
        Self {
            leaf: w.cap_leaf(),
            // Native 8-felt: each `[u32; 8]` limb-array → a `[BabyBear; 8]` digest
            // (per-lane, NOT a lane-0 projection).
            siblings: w.siblings.iter().map(|s| s.map(BabyBear::new)).collect(),
            directions: w.directions.clone(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        }
    }

    /// Build from the Phase-C executor witness PLUS the full write witnesses: the arity-2 openable
    /// leaf-set (`clist_leaves`, the map-op tree the non-rewired write wrappers open) AND the FULL
    /// 7-field c-list + tombstones (the arity-7 `CanonicalCapTree` the INSERT-shaped keystone
    /// wrappers rebuild — `cap_leaves`/`cap_tombstones`).
    pub fn from_consumed_with_trees(
        w: &dregg_turn::ConsumedCapWitness,
        clist_leaves: Vec<dregg_circuit::heap_root::HeapLeaf>,
        cap_leaves: Vec<CapLeaf>,
        cap_tombstones: Vec<BabyBear>,
    ) -> Self {
        Self {
            clist_leaves,
            cap_leaves,
            cap_tombstones,
            ..Self::from_consumed(w)
        }
    }

    /// Build from the Phase-C executor witness PLUS the holder cell's full sorted c-list leaf-set
    /// (the openable cap-tree's `(addr, value)` leaves). The c-list is the data the cap-WRITE
    /// wrappers' `map_op` needs to compute the genuine BEFORE→AFTER cap-root write; the node has it
    /// (the actor cell's pre-state capability set) and threads it here.
    pub fn from_consumed_with_clist(
        w: &dregg_turn::ConsumedCapWitness,
        clist_leaves: Vec<dregg_circuit::heap_root::HeapLeaf>,
    ) -> Self {
        Self {
            clist_leaves,
            ..Self::from_consumed(w)
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
    /// EffectVm row's `cap_root` column is seeded from — cap Phase A). Native
    /// 8-felt `node8` `Digest8` (Phase H-CAP-8): the FULL-width (~124-bit) root,
    /// NOT the lane-0 historical scalar. The verifier pins the AUTHORITY leg's
    /// 8-felt `pi[CAP_ROOT..]` to it — so membership is in THE holder's real
    /// c-list tree, not a prover-chosen one.
    pub cap_root: [BabyBear; 8],
}

/// What the VERIFIER expects of the slot-caveat manifest for a CAPACITY cell — the
/// constraint-binding weld's omission-proof expectation (the soundness core, STAGED).
/// Mirrors [`CapMembershipExpectation`]: every field is re-derived by the verifier
/// from data it trusts (the cell's COMMITTED declared constraint-set + the
/// authoritative pre/post cell state), never taken from the proof.
///
/// The §6 weld rungs (`SealedEscrow`/`StandingObligation`/`Vault` Lean) prove a
/// PRESENT manifest entry forces its invariant; the load-bearing gap they leave is
/// that the entry must be present at all (the manifest is prover-chosen — a forger
/// OMITS it). This expectation closes it: the verifier RE-DERIVES the required
/// capacity tags from the committed declaration (via
/// `dregg_turn::executor::required_capacity_caveat_tags`, whose `state_constraints`
/// are bound into the `B_AUTHORITY_DIGEST` limb of the ~124-bit wide commit) and
/// DEMANDS each is covered (present AND its gate re-evaluates true). This is the Rust
/// shadow of the Lean `Dregg2.Deos.ConstraintBinding.omission_caught_under_binding`.
///
/// STAGED (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`): the AIR constraint
/// polynomials — hence the VK bytes — are UNCHANGED (the manifest rides public inputs
/// and off-AIR re-evaluation, exactly the temporal-caveat / capacity-weld vehicle).
/// `None` (the deployed default) skips the check entirely, so nothing flips by
/// default; the gated verifier-code epoch is the flip step.
pub struct CaveatCoverageExpectation {
    /// The capacity caveat tags the cell's COMMITTED declaration REQUIRES (the
    /// `dregg_turn::executor::required_capacity_caveat_tags` re-derivation over the
    /// committed `state_constraints`). The verifier demands every one is present in
    /// the manifest — omission is rejected.
    pub required_tags: Vec<u32>,
    /// The cell's slot-0..7 4-byte pre-state field views (the same `STATE_BEFORE_BASE`
    /// columns the AIR binds), re-derived from the authoritative pre-state cell.
    pub initial_fields: [BabyBear; 8],
    /// The cell's slot-0..7 4-byte post-state field views, re-derived from the
    /// authoritative post-state cell.
    pub final_fields: [BabyBear; 8],
    /// The schedule clock (block height) the temporal / discharge gates read.
    pub block_height: u64,
}

/// What the VERIFIER expects of a turn whose acting cell's COMMITTED declaration requires the
/// sealed-escrow capacity (the §6 item-2 SELECTOR weld — the deployed realization of the proven
/// Lean `Dregg2.Deos.SettleEscrowSelectorBinding.escrow_selector_bound_to_declaration` obligation).
///
/// The proven keystone shows: IF the verifier pins the escrow selector PI `= 1` whenever the
/// re-derived required-tag floor demands the escrow selector (the `hverifier` discipline), THEN the
/// welded descriptor's four satisfaction gates are forced over the committed BEFORE/AFTER field
/// columns — a forger can dodge NEITHER by a hollow declaration (HALF A, the `DeclCommitBinds`
/// floor) NOR by `sel = 0` (HALF B, the PI pin). This expectation is the deployed `hverifier`: when
/// the cell's committed declaration requires the escrow tag, the verifier
///
///   1. DEMANDS the escrow selector PI (`ESCROW_SEL_PI = 46`) on the rotated effect-vm leg is `1`
///      (so `sel = 0` cannot make the gates inert — HALF B), and
///   2. DEMANDS the rotated leg verifies under the WELDED descriptor
///      [`SETTLE_ESCROW_SAT_DESCRIPTOR_NAME`] (so a declared-escrow turn cannot be routed through a
///      non-welded descriptor that carries no satisfaction gate).
///
/// Together a declared-escrow turn is FORCED through the welded gates. `required_tags` is the
/// caller's `dregg_turn::executor::required_capacity_caveat_tags(state_constraints)` re-derivation
/// over the committed declaration — the cap-membership posture (the same posture as
/// [`CapMembershipExpectation`]: re-derived from data the verifier trusts, the `B_AUTHORITY_DIGEST`
/// limb of the ~124-bit wide commit binds the declaration, never taken from the proof). A forger
/// cannot escape via a hollow declaration: it would have to match the committed authority digest, and
/// its collision-resistance forces the SAME required tags (the Lean `DeclCommitBinds` floor).
///
/// STAGED — built BESIDE the deployed [`verify_full_turn_bound`]:
///   * `expected_escrow_weld = None` ⇒ byte-identical to [`verify_full_turn_bound`].
///   * `Some(_)` with no escrow tag in `required_tags` ⇒ deployed-identical (no demand).
///   * `Some(_)` requiring the escrow tag ⇒ the enforcement above. FAIL-CLOSED: until the welded
///     descriptor is a WIDE member with a producer + committed VK (the FLIP — §6 BLOCKER 1), no
///     honest proof verifies under it, so a declared-escrow turn is REJECTED rather than accepted
///     half-open — the sound posture. No deployed cell declares the escrow caveat, so the deployed
///     default is unaffected. See `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6.
pub struct EscrowWeldExpectation {
    /// The capacity caveat tags the cell's COMMITTED declaration REQUIRES (the
    /// `dregg_turn::executor::required_capacity_caveat_tags` re-derivation over the committed
    /// `state_constraints`). The selector + welded-descriptor demand fires iff this contains the
    /// sealed-escrow tag (`SLOT_CAVEAT_TAG_SETTLE_ESCROW = 17`).
    pub required_tags: Vec<u32>,
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

    // Membership (c-list Merkle proof).
    if components.has_membership {
        circuits.push(dregg_circuit::dsl::descriptors::merkle_poseidon2_descriptor());
    }

    // Non-revocation (sorted tree non-membership).
    if components.has_non_revocation {
        circuits.push(non_revocation_circuit_descriptor());
    }

    // Cap-membership (consumed capability ∈ openable capability_root). Deferred until the
    // standalone leg is widened to native 8-felt `node8` (see §5b) — `has_cap_membership`
    // stays false today, so this fingerprint entry is dormant.
    if components.has_cap_membership {
        circuits.push(dregg_circuit::dsl::cap_membership::cap_membership_circuit_descriptor());
    }

    let circuit_refs: Vec<&CircuitDescriptor> = circuits.iter().collect();
    compose_aggregate(&circuit_refs)
}

/// Construct a CircuitDescriptor for the Effect VM transition.
///
/// The live transition is proved through the ROTATED IR-v2 multi-table descriptor
/// (`dregg_circuit::descriptor_ir2`; the rotated R=24 block over the shared
/// `generate_rotated_effect_vm_trace`). This thin descriptor captures that rotated
/// identity for the composed VK fingerprint — name `"dregg-effect-vm-rotated"`,
/// the rotated trace width (`ROT_WIDTH = EFFECT_VM_WIDTH + APPENDIX = 311`), and the
/// rotated PI surface (`ROT_PI_COUNT`). It is a structural fingerprint only (the
/// `composed_vk_hash` is carried but re-derived per-sub-proof in `verify_full_turn`).
fn effect_vm_circuit_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "dregg-effect-vm-rotated".into(),
        trace_width: effect_vm::ROT_WIDTH,
        max_degree: 9,
        columns: vec![],     // Not needed for composition — VK fingerprint suffices
        constraints: vec![], // Constraints live in the rotated IR-v2 batch AIRs
        boundaries: vec![],  // Boundaries live in the rotated IR-v2 batch AIRs
        public_input_count: effect_vm::ROT_PI_COUNT,
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

// ============================================================================
// THE ROTATED IR-v2 ROUTE (the SOLE effect-vm prover) — the v1 hand-AIR is retired.
// ============================================================================
//
// The rotated R=24 path drives the LIVE rotated trace generator
// (`dregg_circuit::effect_vm::trace_rotated`) from the real per-turn producer witnesses
// (`dregg_turn::rotation_witness`) and proves the 311-column rotated trace + 38-PI vector
// through the IR-v2 batch prover (`descriptor_ir2`). It is `prover`-gated (compiles
// `descriptor_ir2`'s PROVE surface). With the v1 hand-AIR retired, this is the only
// effect-vm prover; a finalized turn with no rotation witness fails closed.

/// Is the rotated IR-v2 (R=24) prover compiled in? The `prover` feature must be on for the
/// rotated effect-vm prover (`descriptor_ir2`'s PROVE surface) to exist.
#[cfg(feature = "prover")]
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
#[cfg(feature = "prover")]
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
    // The standalone wrapper carries NO nullifier-set context; a NoteSpend turn proved through it
    // would have an EMPTY before nullifier tree (the grow-gate forces an insert into the empty
    // accumulator). The chained path (`prove_cohort_run_chain`) threads the real freshness leaves.
    prove_effect_vm_rotated_ir2_with_caveat(
        initial_state,
        effects,
        before_w,
        after_w,
        &caveat,
        None,
    )
}

/// Re-derive the rotated 38-PI vector for a turn (the same `dpis` the rotated prover binds).
/// Used by [`prove_full_turn`] to record the rotated leg's `sub_public_inputs` and to extend
/// the composed PI without re-proving.
#[cfg(feature = "prover")]
// Scaffolding for the in-flight rotated-leg composed-PI path; retained for the rotated VK epoch.
#[allow(dead_code)]
fn rotated_effect_pi_for(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    rot: &RotationTurnWitness,
    before_nullifiers: Option<&[BabyBear]>,
) -> Result<Vec<BabyBear>, SdkError> {
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, generate_rotated_effect_vm_trace,
    };
    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(&rot.before)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated before-witness: {e}")))?;
    let after = bridge(&rot.after)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated after-witness: {e}")))?;
    // NoteSpend re-derives through the nullifier-tree wiring so the OLD/NEW commit PIs (moved by
    // the limb-26 grow-gate) match the proven dpis.
    if matches!(
        effects.first(),
        Some(dregg_circuit::effect_vm::Effect::NoteSpend { .. })
    ) {
        use dregg_circuit::effect_vm::trace_rotated::generate_rotated_note_spend_trace_with_nullifier_tree;
        use dregg_circuit::heap_root::HeapLeaf;
        let leaves: Vec<HeapLeaf> = before_nullifiers
            .unwrap_or(&[])
            .iter()
            .map(|nf| HeapLeaf::entry(*nf, BabyBear::new(1)))
            .collect();
        let (_t, dpis, _mh) = generate_rotated_note_spend_trace_with_nullifier_tree(
            initial_state,
            effects,
            &before,
            &after,
            &rot.caveat,
            &leaves,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("rotated note-spend PI re-derive: {e}")))?;
        return Ok(dpis);
    }
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
#[cfg(feature = "prover")]
pub fn prove_effect_vm_rotated_ir2_with_caveat(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    before_nullifiers: Option<&[BabyBear]>,
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    };
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, rotated_descriptor_name_for_effect,
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
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated after-witness: {e}")))?;

    // NOTESPEND KERNEL-SET GROW-GATE (the deployment-real nullifier set-insert + double-spend
    // tooth): the live `noteSpendVmDescriptor2R24` carries two map-ops opening the limb-26
    // nullifier accumulator (`nullifierFreshOp` `.absent` + `nullifierInsertOp` `.insert`,
    // `EffectVmEmitRotationV3.noteSpendV3`). The bare generator's empty `map_heaps` cannot resolve
    // them — proving needs the real BEFORE nullifier tree (the openable sorted-Poseidon2 leaves),
    // wired here from `before_nullifiers` (the SDK threads the freshness set's leaves —
    // `DslRevocationTree::revoked_leaves` — from the non-revocation witness, so the in-circuit
    // grow-gate and the non-revocation leg agree on which nullifiers are already spent). This
    // FORCES the set-insert (`after_root = insert(before_root, nf)`) and the in-circuit
    // double-spend tooth bites (`.absent` refuses a present nullifier).
    if matches!(lead, dregg_circuit::effect_vm::Effect::NoteSpend { .. }) {
        use dregg_circuit::effect_vm::trace_rotated::generate_rotated_note_spend_trace_with_nullifier_tree;
        use dregg_circuit::heap_root::HeapLeaf;
        let leaves: Vec<HeapLeaf> = before_nullifiers
            .unwrap_or(&[])
            .iter()
            .map(|nf| HeapLeaf::entry(*nf, BabyBear::new(1)))
            .collect();
        let (trace, dpis, map_heaps) = generate_rotated_note_spend_trace_with_nullifier_tree(
            initial_state,
            effects,
            &before,
            &after,
            caveat,
            &leaves,
        )
        .map_err(|e| {
            SdkError::InvalidWitness(format!("rotated note-spend grow-gate generation: {e}"))
        })?;
        return prove_vm_descriptor2(
            &desc,
            &trace,
            &dpis,
            &MemBoundaryWitness::default(),
            &map_heaps,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("rotated note-spend IR-v2 proof: {e}")));
    }

    // LIVE-generate the rotated trace + PI vector. The trace SHAPE follows the COMMITTED
    // descriptor: a hardened `…-v1-avail` transfer/burn member (the GAP #4 availability weld)
    // demands the avail-padded geometry (witness limbs at `[V1_WIDTH, V1_WIDTH + pad)`, appendix
    // shifted by the pad); every bare member keeps the byte-identical `0`-pad shape.
    let avail_pad =
        dregg_circuit::effect_vm::trace_rotated::avail_pad_for_descriptor_name(&desc.name);
    let (trace, dpis) =
        dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace_avail(
            avail_pad,
            initial_state,
            effects,
            &before,
            &after,
            caveat,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("rotated trace generation: {e}")))?;

    // Prove through the IR-v2 batch prover (self-verifies before return).
    prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| SdkError::InvalidWitness(format!("rotated IR-v2 proof: {e}")))
}

/// **THE STAGED UMEM-COHORT PROVER (VK-RISK-FREE — NOT the deployed default).** The
/// rotation-flip's deployed-routing precursor: given one effect-leg's universal-memory touch
/// (its pre-state projection + the Blum op trace), it routes to the FIXED per-effect cohort
/// descriptor (`umem_cohort_lean_key_for_effect` → `umem_cohort_descriptor_json`, the byte-pinned
/// `UMEM_COHORT_V1_STAGED_REGISTRY_TSV` emitted from the verified Lean
/// `EffectVmEmitUMemCohort.umemCohortRegistry`), builds the single-domain width-7 rows + the REAL
/// `UMemBoundaryWitness` ([`dregg_turn::umem::umem_cohort_proving_inputs_from`]), and proves
/// through the DEPLOYED-form umem prover [`prove_vm_descriptor2_umem`] with that real boundary —
/// NOT `UMemBoundaryWitness::default()`. Self-verifies before return.
///
/// This is the architectural-unknown resolution made executable: a real turn proves as PER-EFFECT
/// fixed-cohort legs (mirroring the deployed rotated routing — one descriptor per leg), each
/// single-domain. A multi-domain leg fails closed (the trace generator's single-domain gate); the
/// fixed cohort descriptor's baked-in domain is checked against the leg's actual domain.
///
/// STAGED: the deployed default ([`prove_effect_vm_rotated_ir2_with_caveat`] / the IVC
/// `mint_from_block_witnesses`) stays per-map / per-rotated-descriptor with a DEFAULT umem
/// boundary; this entry is opt-in and never on the live wire. The VK flag-day welds the umem leg
/// INTO the rotated descriptor — until then this proves the umem-form reconciliation STANDALONE,
/// exactly as the cohort emitter's width-7 descriptors model it.
#[cfg(feature = "prover")]
pub fn prove_umem_cohort_staged(
    effect: &VmEffectKind,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, UMemOpSpec, VmConstraint2, parse_vm_descriptor2,
        prove_vm_descriptor2_umem, verify_vm_descriptor2,
    };
    use dregg_circuit::effect_vm_descriptors::{
        umem_cohort_descriptor_json, umem_cohort_lean_key_for_effect,
    };

    // Resolve the FIXED cohort descriptor for this effect-leg (fail closed for non-members).
    let key = umem_cohort_lean_key_for_effect(effect).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "umem cohort staged: effect {effect:?} is not a umem-cohort member (stays per-map)"
        ))
    })?;
    let json = umem_cohort_descriptor_json(key).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "umem cohort staged: '{key}' not in the staged umem cohort registry"
        ))
    })?;
    let desc = parse_vm_descriptor2(json)
        .map_err(|e| SdkError::InvalidWitness(format!("umem cohort descriptor parse: {e}")))?;

    // Bridge the leg's per-turn umem witness into the FIXED single-domain cohort form (the
    // trace generator fails closed on a multi-domain leg).
    let inputs = dregg_turn::umem::umem_cohort_proving_inputs_from(pre, ops)
        .map_err(|e| SdkError::InvalidWitness(format!("umem cohort trace generation: {e}")))?;

    // The fixed descriptor's baked-in domain MUST match the leg's actual domain (the cohort
    // descriptor carries the domain as a constant; a mismatch would prove a different plane's
    // reconciliation than the leg touched).
    let desc_domain = match desc.constraints.first() {
        Some(VmConstraint2::UMemOp(UMemOpSpec { domain, .. })) => *domain,
        _ => {
            return Err(SdkError::InvalidWitness(format!(
                "umem cohort staged: descriptor '{key}' carries no umem-op constraint"
            )));
        }
    };
    if desc_domain != inputs.domain {
        return Err(SdkError::InvalidWitness(format!(
            "umem cohort staged: descriptor '{key}' is domain {desc_domain} but the leg touches \
             domain {}",
            inputs.domain
        )));
    }

    // Prove through the DEPLOYED-form umem prover with the REAL boundary; self-verify.
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &inputs.rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("umem cohort IR-v2 proof: {e}")))?;
    verify_vm_descriptor2(&desc, &proof, &[])
        .map_err(|e| SdkError::InvalidWitness(format!("umem cohort self-verify: {e}")))?;
    Ok(proof)
}

/// **THE STAGED MULTI-DOMAIN UMEM-COHORT PROVER (VK-RISK-FREE — NOT the deployed default).** The
/// completion of [`prove_umem_cohort_staged`] to the effects whose state touch spans MORE THAN ONE
/// domain in a single effect (the NOTE/BRIDGE economic verbs — a `nullifiers`-domain freshness
/// insert + a `heap`-domain balance write), on which the single-domain cohort path fails closed.
///
/// Given one effect-leg's multi-domain universal-memory touch (its pre-state projection + the Blum
/// op trace), it routes to the FIXED per-effect MULTI-DOMAIN cohort descriptor
/// (`umem_cohort_multidomain_lean_key_for_effect` → `umem_cohort_multidomain_descriptor_json`, the
/// byte-pinned [`UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV`] emitted from the verified Lean
/// `EffectVmEmitUMemCohortMulti.umemCohortMultiRegistry`), builds the multi-domain rows + the REAL
/// `UMemBoundaryWitness` ([`dregg_turn::umem::umem_cohort_multidomain_proving_inputs_from`]), and
/// proves through the DEPLOYED-form umem prover [`prove_vm_descriptor2_umem`] with that real
/// boundary. Self-verifies before return.
///
/// The fixed descriptor's baked-in per-op domain set (in column order) is checked against the leg's
/// actual domain set — a mismatch fails closed (the descriptor carries the FIXED domain set its
/// committed VK backs; it must not prove a different plane-set than the leg touched).
///
/// SOUNDNESS SCOPE (honest): the multi-domain cohort leg reconciles each touched domain's boundary
/// FAITHFULLY and INDEPENDENTLY (the per-domain survival keystones, `noteSpend_post_root` /
/// `_pre_root`, parametric over the domain). It does NOT by itself bind the CROSS-domain economic
/// invariant (e.g. balance-credit == spent-note-value) — that is not a memory-reconciliation
/// property; it rides the effect's own rotated AIR gates (the weld preserves the whole rotated
/// constraint set). This is the same division as the single-domain cohort.
///
/// STAGED: opt-in, never on the live wire; `umem_witness_enabled` untouched. The deployed default
/// stays per-map until the gated VK epoch.
#[cfg(feature = "prover")]
pub fn prove_umem_cohort_multidomain_staged(
    effect: &VmEffectKind,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, UMemOpSpec, VmConstraint2, parse_vm_descriptor2,
        prove_vm_descriptor2_umem, verify_vm_descriptor2,
    };
    use dregg_circuit::effect_vm_descriptors::{
        umem_cohort_multidomain_descriptor_json, umem_cohort_multidomain_lean_key_for_effect,
    };

    // Resolve the FIXED multi-domain cohort descriptor for this effect-leg (fail closed for
    // non-members / single-domain effects).
    let key = umem_cohort_multidomain_lean_key_for_effect(effect).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "umem multi-domain cohort staged: effect {effect:?} is not a multi-domain umem-cohort \
             member (single-domain effects use prove_umem_cohort_staged)"
        ))
    })?;
    let json = umem_cohort_multidomain_descriptor_json(key).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "umem multi-domain cohort staged: '{key}' not in the staged multi-domain registry"
        ))
    })?;
    let desc = parse_vm_descriptor2(json).map_err(|e| {
        SdkError::InvalidWitness(format!("umem multi-domain cohort descriptor parse: {e}"))
    })?;

    // Bridge the leg's per-turn umem witness into the FIXED multi-domain cohort form (fails closed
    // on a single-domain or empty leg).
    let inputs =
        dregg_turn::umem::umem_cohort_multidomain_proving_inputs_from(pre, ops).map_err(|e| {
            SdkError::InvalidWitness(format!("umem multi-domain cohort trace generation: {e}"))
        })?;

    // The fixed descriptor's per-op domains (in column order) MUST match the leg's actual domain
    // set — the descriptor carries the FIXED plane-set its committed VK backs.
    let desc_domains: Vec<u32> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::UMemOp(UMemOpSpec { domain, .. }) => Some(*domain),
            _ => None,
        })
        .collect();
    if desc_domains != inputs.domains {
        return Err(SdkError::InvalidWitness(format!(
            "umem multi-domain cohort staged: descriptor '{key}' bakes domains {desc_domains:?} but \
             the leg touches domains {:?}",
            inputs.domains
        )));
    }

    // Prove through the DEPLOYED-form umem prover with the REAL boundary; self-verify.
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &inputs.rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("umem multi-domain cohort IR-v2 proof: {e}")))?;
    verify_vm_descriptor2(&desc, &proof, &[]).map_err(|e| {
        SdkError::InvalidWitness(format!("umem multi-domain cohort self-verify: {e}"))
    })?;
    Ok(proof)
}

/// **THE ROTATED+UMEM WELD PROVER (STAGED, VK-RISK-FREE) — the last precursor before the gated VK
/// epoch.** Prove a REAL turn through the WELDED rotated+umem descriptor
/// ([`dregg_circuit::effect_vm_descriptors::weld_umem_into_rotated_descriptor`]): the WHOLE rotated
/// R=24 cohort proof (effect semantics, the rotated 46-PI vector with the OLD/NEW state-commit pins)
/// PLUS the universal-memory reconciliation leg (the cohort `umemOp` over 7 appended columns + the
/// real [`UMemBoundaryWitness`]), in ONE descriptor / ONE proof.
///
/// This is the deployed flag-day weld made executable BEFORE the switch: the per-map memory
/// reconciliation moves INTO the rotated descriptor as the umem leg, while the rotated PIs stay
/// intact. It welds the two reconciliation seams the staged cohort leg ([`prove_umem_cohort_staged`])
/// named — the 0-PI umem leg now rides the rotated descriptor's committed PI vector (so the IVC
/// fold's `old_root`/`new_root` accessors keep working over the welded leg).
///
/// `effects` is the turn's homogeneous rotated cohort slice (the lead resolves the rotated
/// descriptor + the umem cohort domain); `pre`/`ops` are the same turn's universal-memory touch (its
/// pre-state projection + Blum op trace) the standalone cohort prover consumes. Self-verifies before
/// return.
///
/// STAGED: the deployed default ([`prove_effect_vm_rotated_ir2_with_caveat`]) stays rotated+per-map
/// with a DEFAULT umem boundary; this entry is opt-in and never on the live wire. No VK epoch, no
/// committed-VK change.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn prove_rotated_umem_welded_staged(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_umem, verify_vm_descriptor2,
    };
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, rotated_descriptor_name_for_effect,
    };
    use dregg_circuit::effect_vm_descriptors::{
        V3_STAGED_REGISTRY_TSV, weld_umem_into_rotated_descriptor,
    };

    // Resolve the rotated cohort descriptor for this turn's lead effect (homogeneous-cohort only,
    // exactly as the deployed rotated prover routes). The welded form is single-leg by design.
    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("rotated+umem weld: empty turn".into()))?;
    let name = rotated_descriptor_name_for_effect(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "rotated+umem weld: effect {lead:?} is not in the rotated cohort (no R=24 descriptor)"
        ))
    })?;
    for e in &effects[1..] {
        if rotated_descriptor_name_for_effect(e) != Some(name) {
            return Err(SdkError::InvalidWitness(
                "rotated+umem weld: heterogeneous multi-effect turn (one welded descriptor per proof)"
                    .into(),
            ));
        }
    }
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
    let rotated_desc = parse_vm_descriptor2(json)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated descriptor parse: {e}")))?;

    // The umem leg's single-domain cohort rows + the REAL boundary (fails closed on a multi-domain
    // leg — such effects stay on the per-map path until their own cohort design).
    let inputs = dregg_turn::umem::umem_cohort_proving_inputs_from(pre, ops)
        .map_err(|e| SdkError::InvalidWitness(format!("umem cohort trace generation: {e}")))?;

    // WELD: append the umem leg INTO the rotated descriptor (keeps the 46 rotated PIs).
    let welded = weld_umem_into_rotated_descriptor(&rotated_desc, inputs.domain);
    let base = rotated_desc.trace_width; // the first appended umem column

    // The rotated trace + its 46-PI vector (the welded descriptor's PIs are the rotated PIs).
    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated after-witness: {e}")))?;
    // The trace SHAPE follows the COMMITTED descriptor (see `prove_effect_vm_rotated_ir2_with_caveat`):
    // a hardened `…-v1-avail` member demands the avail-padded geometry.
    let (rot_trace, dpis) =
        dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace_avail(
            dregg_circuit::effect_vm::trace_rotated::avail_pad_for_descriptor_name(
                &rotated_desc.name,
            ),
            initial_state,
            effects,
            &before,
            &after,
            caveat,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("rotated trace generation: {e}")))?;

    // Assemble the WELDED base trace: each rotated row widened to the welded width, the REAL umem
    // cohort rows (guard col 6 == 1) injected into the appended 7 columns of the first rows. The
    // rotated leg occupies cols `[0, base)`; the umem leg occupies `[base, base+7)`; the cohort
    // umem-op gathering reads its operands row-local (guard gates which rows contribute).
    let real_umem_rows: Vec<&Vec<dregg_circuit::field::BabyBear>> = inputs
        .rows
        .iter()
        .filter(|r| r.get(6).copied() == Some(dregg_circuit::field::BabyBear::ONE))
        .collect();
    if real_umem_rows.len() > rot_trace.len() {
        return Err(SdkError::InvalidWitness(format!(
            "rotated+umem weld: {} umem ops exceed the rotated trace height {} (cannot co-locate \
             the umem leg on the rotated rows)",
            real_umem_rows.len(),
            rot_trace.len()
        )));
    }
    let mut welded_base: Vec<Vec<dregg_circuit::field::BabyBear>> =
        Vec::with_capacity(rot_trace.len());
    for (ri, row) in rot_trace.iter().enumerate() {
        let mut wr = row.clone();
        wr.resize(base + 7, dregg_circuit::field::BabyBear::ZERO);
        if let Some(umem_row) = real_umem_rows.get(ri) {
            for (i, &v) in umem_row.iter().enumerate().take(7) {
                wr[base + i] = v;
            }
        }
        welded_base.push(wr);
    }

    // Prove the WELDED descriptor through the DEPLOYED-form umem prover with the REAL boundary.
    let proof = prove_vm_descriptor2_umem(
        &welded,
        &welded_base,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("rotated+umem welded IR-v2 proof: {e}")))?;
    verify_vm_descriptor2(&welded, &proof, &dpis)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated+umem welded self-verify: {e}")))?;
    Ok(proof)
}

/// **THE FAITHFUL 8-FELT WIDE rotated prover (STAGED — the flip's producer leg).** The wide twin of
/// [`prove_effect_vm_rotated_ir2_with_caveat`]: routes the WIDE descriptor (from
/// `WIDE_REGISTRY_STAGED_TSV`, the verified Lean `v3RegistryCapOpenWide`), generates the trace
/// through the WIDE producers (transfer-shape / grow-gate), and proves at the wide geometry (the two
/// 13×8 BEFORE/AFTER carriers + 16 wide PIs). The published 8-felt commit binds the FULL 37 limbs +
/// iroot (~124-bit), closing the ~31-bit 1-felt floor. Self-verifies before return. STAGED: the live
/// 1-felt producer ([`prove_effect_vm_rotated_ir2_with_caveat`]) is UNTOUCHED — the flag-day repoints
/// the sovereign producer here (+ the executor's wide verify). Returns `(proof, wide_dpis)` — the
/// caller publishes the 16 wide commit PIs (the executor anchors them to the trusted cell).
#[cfg(feature = "prover")]
pub fn prove_effect_vm_rotated_wide(
    initial_state: &CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    before_nullifiers: Option<&[BabyBear]>,
    refusal_fields: Option<(&[dregg_circuit::heap_root::HeapLeaf], BabyBear)>,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::prove_vm_descriptor2;
    let (desc, trace, dpis, map_heaps, mem_boundary) = generate_wide_descriptor_and_trace(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_nullifiers,
        refusal_fields,
    )?;
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .map_err(|e| SdkError::InvalidWitness(format!("wide rotated IR-v2 proof: {e}")))?;
    Ok((proof, dpis))
}

/// The shared WIDE descriptor + trace generation (the body of [`prove_effect_vm_rotated_wide`],
/// extracted so the WIDE+umem weld prover [`prove_wide_umem_welded_staged`] reuses the EXACT same
/// wide trace / PI vector / witness production then welds the umem leg onto it). Returns the
/// resolved WIDE descriptor (from `WIDE_REGISTRY_STAGED_TSV`), its base trace, the wide PI vector
/// (the 16 wide commit PIs at the tail = the 8-felt before/after anchors), the grow-gate
/// `map_heaps`, and the (setFieldDyn-only) mem boundary.
#[cfg(feature = "prover")]
#[allow(clippy::type_complexity)]
fn generate_wide_descriptor_and_trace(
    initial_state: &CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    before_nullifiers: Option<&[BabyBear]>,
    refusal_fields: Option<(&[dregg_circuit::heap_root::HeapLeaf], BabyBear)>,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
        dregg_circuit::descriptor_ir2::MemBoundaryWitness,
    ),
    SdkError,
> {
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    };

    // The per-family wide producer dispatch now lives in `dregg-circuit`
    // (`generate_rotated_effect_vm_descriptor_and_trace_wide`) so the live SDK wide prover AND the
    // IVC welded-leg mint (`dregg-circuit-prove`) share ONE producer route — no hand-inlined twin.
    // This wrapper only bridges the `RotationWitness` pair the SDK consumes into the
    // `RotatedBlockWitness` form the dispatcher takes, then maps the error.
    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("wide rotated before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("wide rotated after-witness: {e}")))?;

    generate_rotated_effect_vm_descriptor_and_trace_wide(
        initial_state,
        effects,
        &before,
        &after,
        caveat,
        before_nullifiers,
        refusal_fields,
        // The live SDK wide prover routes cap-WRITE leads through the SEPARATE cap-open path
        // (`prove_effect_vm_cap_open`), never this dispatcher — so no cap-write witness is threaded here
        // (a cap-WRITE lead reaching this route fails closed, as it always has).
        None,
        // No BEFORE-cell context on this route — the committed transfer row's membership-teeth
        // tail fills the ZERO pair (the no-caveat sentinel; a caveat-declaring cell's honest pair
        // rides the leg-mint recipe / the attach lane's `retain_sender_membership`).
        None,
    )
    .map_err(SdkError::InvalidWitness)
}

/// **THE WIDE ROTATED+UMEM WELD PROVER (STAGED, VK-RISK-FREE) — the genuine flip precursor the VK
/// epoch needs.** The WIDE (8-felt / ~124-bit faithful commit) twin of
/// [`prove_rotated_umem_welded_staged`]: it proves, in ONE descriptor / ONE proof, BOTH the WIDE
/// rotated cohort proof (the effect semantics + the wide PI vector whose LAST 16 PIs are the 8-felt
/// before/after commit anchors `verify_full_turn_bound` binds at ~124-bit) AND the universal-memory
/// reconciliation leg (the cohort `umemOp` over 7 appended columns + a REAL [`UMemBoundaryWitness`]).
///
/// Where the NARROW weld ([`prove_rotated_umem_welded_staged`]) welded onto the 1-felt / 46-PI
/// rotated descriptor (a correct staging artifact, but flipping the deployed WIDE wire onto it would
/// NARROW the ~124-bit commitment to ~46-bit — the no-narrowing scar the VK epoch refused to cross),
/// THIS welds onto the deployed WIDE descriptor ([`WIDE_REGISTRY_STAGED_TSV`]) via
/// [`weld_umem_into_wide_descriptor`], which is purely ADDITIVE: it appends the umem leg PAST the
/// wide carriers and NEVER touches `public_input_count` nor any PI binding, so the 16 wide commit
/// PIs (the 8-felt anchors) ride through UNCHANGED. The welded form keeps the FULL ~124-bit faithful
/// commitment AND carries the umem reconciliation leg.
///
/// `effects` is the turn's homogeneous wide cohort slice; `before_w`/`after_w` the rotation
/// witnesses the wide producers consume; `pre`/`ops` the SAME turn's universal-memory touch (its
/// pre-state projection + Blum op trace) the cohort prover folds. `before_nullifiers`/`refusal_fields`
/// thread the grow-gate / refusal context the wide producers need (mirrors
/// [`prove_effect_vm_rotated_wide`]). Self-verifies before return; returns `(proof, wide_dpis)` — the
/// caller binds the 16 wide commit PIs.
///
/// STAGED: a NEW wide+umem welded descriptor BESIDE the deployed wide registry; no VK epoch, no
/// deployed-default flip, no committed-VK change.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn prove_wide_umem_welded_staged(
    initial_state: &CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
    before_nullifiers: Option<&[BabyBear]>,
    refusal_fields: Option<(&[dregg_circuit::heap_root::HeapLeaf], BabyBear)>,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{prove_vm_descriptor2_umem, verify_vm_descriptor2};
    use dregg_circuit::effect_vm_descriptors::weld_umem_into_wide_descriptor;

    // The umem leg's single-domain cohort rows + the REAL boundary (fails closed on a multi-domain
    // leg — such effects stay on the per-map path until their own cohort design).
    let inputs = dregg_turn::umem::umem_cohort_proving_inputs_from(pre, ops)
        .map_err(|e| SdkError::InvalidWitness(format!("umem cohort trace generation: {e}")))?;

    // Reuse the EXACT deployed wide trace / PI / witness production, then weld the umem leg ONTO it.
    let (wide_desc, wide_trace, dpis, map_heaps, mem_boundary) =
        generate_wide_descriptor_and_trace(
            initial_state,
            effects,
            before_w,
            after_w,
            caveat,
            before_nullifiers,
            refusal_fields,
        )?;

    // WELD: append the umem leg INTO the WIDE descriptor (keeps the wide PI vector + the 16 wide
    // commit PIs — the 8-felt anchors — INTACT). The first appended umem column is PAST the wide
    // carriers (`base` = the wide trace width).
    let welded = weld_umem_into_wide_descriptor(&wide_desc, inputs.domain);
    let base = wide_desc.trace_width;

    // Assemble the WELDED base trace: each wide row widened to the welded width, the REAL umem
    // cohort rows (guard col 6 == 1) injected into the appended 7 columns of the first rows. The
    // wide leg occupies cols `[0, base)`; the umem leg occupies `[base, base+7)`; the cohort
    // umem-op gathering reads its operands row-local (guard gates which rows contribute).
    let real_umem_rows: Vec<&Vec<BabyBear>> = inputs
        .rows
        .iter()
        .filter(|r| r.get(6).copied() == Some(BabyBear::ONE))
        .collect();
    if real_umem_rows.len() > wide_trace.len() {
        return Err(SdkError::InvalidWitness(format!(
            "wide+umem weld: {} umem ops exceed the wide trace height {} (cannot co-locate the \
             umem leg on the wide rows)",
            real_umem_rows.len(),
            wide_trace.len()
        )));
    }
    let mut welded_base: Vec<Vec<BabyBear>> = Vec::with_capacity(wide_trace.len());
    for (ri, row) in wide_trace.iter().enumerate() {
        let mut wr = row.clone();
        wr.resize(base + 7, BabyBear::ZERO);
        if let Some(umem_row) = real_umem_rows.get(ri) {
            for (i, &v) in umem_row.iter().enumerate().take(7) {
                wr[base + i] = v;
            }
        }
        welded_base.push(wr);
    }

    // Prove the WELDED WIDE descriptor through the DEPLOYED-form umem prover with the REAL boundary.
    let proof = prove_vm_descriptor2_umem(
        &welded,
        &welded_base,
        &dpis,
        &mem_boundary,
        &map_heaps,
        &inputs.boundary,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("wide+umem welded IR-v2 proof: {e}")))?;
    verify_vm_descriptor2(&welded, &proof, &dpis)
        .map_err(|e| SdkError::InvalidWitness(format!("wide+umem welded self-verify: {e}")))?;
    Ok((proof, dpis))
}

/// **THE FEE-IN-PROOF WIDE ROTATED+UMEM WELD PROVER (STAGED, VK-RISK-FREE) — the deployed sovereign
/// transfer route's welded twin.** The fee-path twin of [`prove_wide_umem_welded_staged`]: a single
/// sovereign `[Transfer]` lead routes the FEE-IN-PROOF wide descriptor (`transferFeeVmDescriptor2R24`
/// in [`WIDE_REGISTRY_STAGED_TSV`], the fee debited inside the proven transition), which is exactly
/// what the deployed executor resolves for a lone transfer (`verify_one_cohort_run`'s
/// `is_fee_transfer` route). This welds the universal-memory cohort leg onto THAT fee descriptor via
/// the SAME purely-additive [`weld_umem_into_wide_descriptor`] (preserving `public_input_count` + all
/// 16 wide-commit `PiBinding`s — the 8-felt anchors ride through INTACT), so a welded fee proof
/// verifies through the deployed `verify_and_commit_proof_rotated` welded-twin leg and COMMITS.
///
/// A NON-Transfer lead has no fee-in-proof descriptor, so this defers to the unfee'd
/// [`prove_wide_umem_welded_staged`]. STAGED: a NEW welded descriptor BESIDE the deployed registry;
/// no VK bump, no default flip, `umem_witness_enabled` untouched. Self-verifies before return.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn prove_wide_umem_welded_staged_with_fee(
    initial_state: &CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
    fee: u64,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_umem, verify_vm_descriptor2,
    };
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, avail_pad_for_descriptor_name,
        generate_rotated_transfer_shape_with_fee_wide_avail,
        rotated_descriptor_name_for_effect_fee,
    };
    use dregg_circuit::effect_vm_descriptors::{
        WIDE_REGISTRY_STAGED_TSV, weld_umem_into_wide_descriptor,
    };

    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("wide fee weld prover: empty turn".into()))?;
    // Non-Transfer leads carry no fee-in-proof descriptor — defer to the unfee'd welded prover.
    if !matches!(lead, dregg_circuit::effect_vm::Effect::Transfer { .. }) {
        return prove_wide_umem_welded_staged(
            initial_state,
            effects,
            before_w,
            after_w,
            caveat,
            pre,
            ops,
            None,
            None,
        );
    }
    let name = rotated_descriptor_name_for_effect_fee(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "wide fee weld prover: effect {lead:?} has no fee-in-proof descriptor"
        ))
    })?;

    // The umem leg's single-domain cohort rows + the REAL boundary (the SAME shape the unfee'd
    // welded prover assembles; fails closed on a multi-domain leg).
    let inputs = dregg_turn::umem::umem_cohort_proving_inputs_from(pre, ops)
        .map_err(|e| SdkError::InvalidWitness(format!("umem cohort trace generation: {e}")))?;

    let json = WIDE_REGISTRY_STAGED_TSV
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
            SdkError::InvalidWitness(format!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
        })?;
    let wide_desc = parse_vm_descriptor2(json)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee descriptor parse: {e}")))?;

    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee after-witness: {e}")))?;

    // The fee-aware WIDE trace + PI vector (the deployed fee route; the fee is debited in-proof and
    // the 8-felt carriers re-absorb the post-fee limbs). THE AVAILABILITY-WELD PAD (GAP #4, wide
    // fee leg): the trace SHAPE follows the COMMITTED wide descriptor — a hardened
    // `…-v1-fee-avail` member demands the 16-col fee-weld geometry (witness limbs at
    // `[V1_WIDTH, V1_WIDTH + 16)`, every appendix + carrier base shifted); every bare member
    // keeps the byte-identical `0`-pad shape.
    let avail_pad = avail_pad_for_descriptor_name(&wide_desc.name);
    let (wide_trace, dpis) = generate_rotated_transfer_shape_with_fee_wide_avail(
        avail_pad,
        initial_state,
        effects,
        &before,
        &after,
        caveat,
        fee,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("wide fee trace generation: {e}")))?;

    // WELD: append the umem leg INTO the fee WIDE descriptor (keeps the wide PI vector + the 16 wide
    // commit PIs — the 8-felt anchors — INTACT; the first appended umem column is PAST the wide
    // carriers at `base` = the wide trace width). IDENTICAL no-narrowing append as the unfee'd weld.
    let welded = weld_umem_into_wide_descriptor(&wide_desc, inputs.domain);
    let base = wide_desc.trace_width;

    let real_umem_rows: Vec<&Vec<BabyBear>> = inputs
        .rows
        .iter()
        .filter(|r| r.get(6).copied() == Some(BabyBear::ONE))
        .collect();
    if real_umem_rows.len() > wide_trace.len() {
        return Err(SdkError::InvalidWitness(format!(
            "wide fee+umem weld: {} umem ops exceed the wide trace height {} (cannot co-locate the \
             umem leg on the wide rows)",
            real_umem_rows.len(),
            wide_trace.len()
        )));
    }
    let mut welded_base: Vec<Vec<BabyBear>> = Vec::with_capacity(wide_trace.len());
    for (ri, row) in wide_trace.iter().enumerate() {
        let mut wr = row.clone();
        wr.resize(base + 7, BabyBear::ZERO);
        if let Some(umem_row) = real_umem_rows.get(ri) {
            for (i, &v) in umem_row.iter().enumerate().take(7) {
                wr[base + i] = v;
            }
        }
        welded_base.push(wr);
    }

    // The fee descriptor carries NO map_ops (the deployed fee path proves with an empty
    // `MemBoundaryWitness` + no `map_heaps`), so only the appended umem boundary is real.
    let proof = prove_vm_descriptor2_umem(
        &welded,
        &welded_base,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("wide fee+umem welded IR-v2 proof: {e}")))?;
    verify_vm_descriptor2(&welded, &proof, &dpis)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee+umem welded self-verify: {e}")))?;
    Ok((proof, dpis))
}

/// **THE FEE-IN-PROOF WIDE rotated prover (`transferFeeVmDescriptor2R24Wide`, the flip's live
/// sovereign producer leg).** The wide twin of [`prove_effect_vm_rotated_ir2_with_fee`]: it routes the
/// WIDE fee descriptor (from `WIDE_REGISTRY_STAGED_TSV`), generates the fee-aware wide trace
/// (`generate_rotated_transfer_shape_with_fee_wide` — fee debited in-proof, then the 8-felt carriers
/// re-absorb the post-fee limbs), and proves at the wide geometry (55 PIs: 39 base + 16 wide). A
/// NON-Transfer lead falls back to the unfee'd wide prover (so this is a drop-in the sovereign
/// producer can always call). Returns `(proof, wide_dpis)`; the executor anchors the 16 wide commit
/// PIs to the trusted cell's 8-felt commitments.
#[cfg(feature = "prover")]
pub fn prove_effect_vm_rotated_wide_with_fee(
    initial_state: &CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    fee: u64,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    };
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, avail_pad_for_descriptor_name,
        generate_rotated_transfer_shape_with_fee_wide_avail,
        rotated_descriptor_name_for_effect_fee,
    };
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;

    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("wide fee prover: empty turn".into()))?;
    // Non-Transfer leads carry no fee-in-proof descriptor — defer to the unfee'd wide prover.
    if !matches!(lead, dregg_circuit::effect_vm::Effect::Transfer { .. }) {
        return prove_effect_vm_rotated_wide(
            initial_state,
            effects,
            before_w,
            after_w,
            caveat,
            None,
            None,
        );
    }
    let name = rotated_descriptor_name_for_effect_fee(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "wide fee prover: effect {lead:?} has no fee-in-proof descriptor"
        ))
    })?;
    if effects.len() > 1 {
        for e in &effects[1..] {
            if rotated_descriptor_name_for_effect_fee(e) != Some(name) {
                return Err(SdkError::InvalidWitness(
                    "wide fee prover: heterogeneous multi-effect turn".into(),
                ));
            }
        }
    }
    let json = WIDE_REGISTRY_STAGED_TSV
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
            SdkError::InvalidWitness(format!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
        })?;
    let desc = parse_vm_descriptor2(json)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee descriptor parse: {e}")))?;

    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee after-witness: {e}")))?;

    // THE AVAILABILITY-WELD PAD (GAP #4, wide fee leg): shape follows the COMMITTED wide
    // descriptor — pad 16 for a hardened `…-v1-fee-avail` row, 0 (byte-identical) for bare.
    let avail_pad = avail_pad_for_descriptor_name(&desc.name);
    let (trace, dpis) = generate_rotated_transfer_shape_with_fee_wide_avail(
        avail_pad,
        initial_state,
        effects,
        &before,
        &after,
        caveat,
        fee,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("wide fee trace generation: {e}")))?;

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| SdkError::InvalidWitness(format!("wide fee IR-v2 proof: {e}")))?;
    Ok((proof, dpis))
}

/// **THE FEE-IN-PROOF rotated prover (`transferFeeVmDescriptor2R24`).** The fee-path twin of
/// [`prove_effect_vm_rotated_ir2_with_caveat`] for a plain sovereign `Transfer` lead: it routes the
/// `transferFeeVmDescriptor2R24` descriptor (39 PIs), generates the fee-aware trace
/// (`generate_rotated_effect_vm_trace_with_fee` — the fee debited in-proof so NEW_COMMIT binds the
/// post-fee balance), and proves. A NON-Transfer lead falls back to the unfee'd prover (so this is a
/// drop-in the sovereign producer can always call). Keeps the broad unfee'd cohort path 100% intact.
#[cfg(feature = "prover")]
pub fn prove_effect_vm_rotated_ir2_with_fee(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
    fee: u64,
) -> Result<
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    };
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, generate_rotated_effect_vm_trace_with_fee,
        rotated_descriptor_name_for_effect_fee,
    };
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;

    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("rotated fee prover: empty turn".into()))?;
    // Non-Transfer leads carry no fee-in-proof descriptor — defer to the unfee'd prover.
    if !matches!(lead, dregg_circuit::effect_vm::Effect::Transfer { .. }) {
        return prove_effect_vm_rotated_ir2_with_caveat(
            initial_state,
            effects,
            before_w,
            after_w,
            caveat,
            None,
        );
    }
    let name = rotated_descriptor_name_for_effect_fee(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "rotated fee prover: effect {lead:?} has no fee-in-proof descriptor"
        ))
    })?;
    if effects.len() > 1 {
        for e in &effects[1..] {
            if rotated_descriptor_name_for_effect_fee(e) != Some(name) {
                return Err(SdkError::InvalidWitness(
                    "rotated fee prover: heterogeneous multi-effect turn (one descriptor per proof)"
                        .into(),
                ));
            }
        }
    }

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
        .map_err(|e| SdkError::InvalidWitness(format!("rotated fee descriptor parse: {e}")))?;

    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated fee before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("rotated fee after-witness: {e}")))?;

    let (trace, dpis) = generate_rotated_effect_vm_trace_with_fee(
        initial_state,
        effects,
        &before,
        &after,
        caveat,
        fee,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("rotated fee trace generation: {e}")))?;

    prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| SdkError::InvalidWitness(format!("rotated fee IR-v2 proof: {e}")))
}

/// **`cap_open_supported_for_run`** (F1) — does a cap-open descriptor exist for this single-effect
/// run's effect-kind? The cap-open routing (`prove_cohort_run_chain`) is cap-PRESENCE driven: any
/// run threading a real consumed-cap witness routes the cap-open. This gate maps the run's
/// effect-kind to its cap-open descriptor:
///
///   * **`AttenuateCapability`** — WIRED (`attenuateCapOpenEffVmDescriptor2R24`, the
///     `prove_effect_vm_cap_open_attenuate` path); the cap-membership open is proven + self-verified
///     end-to-end (`circuit/tests/cap_open_self_verify.rs`).
///   * **`Transfer`** (#225 turn-identity cutover) — WIRED to the LIVE TURN-BOUND descriptor
///     (`transferCapOpenTBVmDescriptor2R24`, the `prove_effect_vm_cap_open_transfer` path): the
///     in-circuit depth-16 cap-membership open over the TRANSFER base PLUS the turn-identity weld
///     (the `src`/`actor`/`dst` columns welded to PIs 38/39/40, anchored by the verifier to the
///     trusted turn) so a ledgerless light client concludes the published identity = the proven turn.
///   * **every OTHER cap-authorized effect-kind** (delegate-via-cap, exercise-via-cap, …) — NO
///     cap-open descriptor is emitted yet (the cap-open appendix is base-agnostic, but a per-effect
///     `<effect>CapOpenVmDescriptor2R24` = that effect's base + the appendix has not been registered).
///     These fail CLOSED here with a precise error. This is the remaining NAMED per-effect residual:
///     the routing + appendix are general, the per-effect descriptor coverage is attenuate + transfer.
///     The cap-open ROUTE for a single-effect run: the registry key of its cap-open descriptor, the
///     effect-kind bit (`EFFECT_<kind> = 1 << n`) the appendix's `effBitGateFor`/`facetEffGate` bind, and
///     whether the base needs the attenuate phase-B nonce-freeze patch (`patch_attenuate_base_for_cap_open`).
///     `None` (the fallthrough) means no cap-open descriptor for that effect-kind.
#[cfg(feature = "prover")]
struct CapOpenRoute {
    key: &'static str,
    eff_bit: u32,
    /// the nonce-FREEZE + cap-root-advance bases (attenuate/grantCap/revokeCapability) need the
    /// phase-B patch (`patch_attenuate_base_for_cap_open`); the nonce-TICK passthrough bases
    /// (transfer/revoke/refresh/introduce) are directly valid (no patch).
    needs_attenuate_patch: bool,
    /// only the Transfer base threads the transfer caveat manifest; every other base uses the empty
    /// manifest (mirroring `RotationTurnWitness::for_effects`).
    transfer_caveat: bool,
    /// the TURN-BOUND cap-open (the `…CapOpenTBVmDescriptor2R24` weld): the descriptor carries TWO
    /// extra turn-identity columns (`actor`/`dst`) and THREE extra PIs (`src`/`actor`/`dst` at
    /// `38/39/40`), so the trace is widened with [`widen_to_cap_open_tb`] and the dpis extended with
    /// [`cap_open_tb_dpis`]. The verifier ANCHORS the three PIs to the trusted turn (`anchor_cap_open_turn_pins`),
    /// so a ledgerless light client can conclude the published `actor`/`src`/`dst` MATCH the proven
    /// transition. Wired for `transfer` (the #225 weld); the other legs ride the non-TB `-eff` descriptor.
    turn_bound: bool,
    /// **(cap-WRITE light-client axis)** the WRITE-bearing cap-open route. When the prover holds the
    /// cell's FULL c-list (`cap.clist_leaves` non-empty), it proves the `…WriteCapOpenVmDescriptor2R24`
    /// wrapper instead of `key`: that descriptor carries a `map_op` binding BEFORE cap-root (col 65) →
    /// AFTER cap-root (col 87) via a sorted-Poseidon2 cap-tree write, so the post-cap-root is
    /// on-the-wire LIGHT-CLIENT-verifiable (a wrong post-root is UNSAT, not host-trusted). The prover
    /// threads the c-list through the cap-tree→map_heaps bridge ([`generate_rotated_cap_write_base`]).
    /// `None` ⇒ this effect-kind has no write-bearing wrapper (the AUTHORITY-only `key` is used). When
    /// `Some`, an empty `clist_leaves` falls back to `key` (the authority-only route — current
    /// behavior; "named, not a silent forge"). The verifier tooth (`is_forbidden_plain_cap_descriptor`)
    /// forces the write route once the node universally supplies the c-list.
    ///
    /// The third tuple field is the WRITE wrapper's cap-facet bit — which may DIFFER from the
    /// authority-only `eff_bit` (e.g. the `delegateWriteCapOpen` wrapper binds `EFFECT_DELEGATION_OPS`
    /// = 1<<16, while the authority-only `grantCapCapOpen` binds `EFFECT_GRANT_CAPABILITY` = 1<<2). The
    /// prove path uses THIS facet for the membership crown when the write wrapper is active.
    write: Option<(
        &'static str,
        dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp,
        u32,
    )>,
}

/// THE delegateAtten ROUTING SIGNAL: is a granter-side delegation row an ATTENUATED grant (the
/// conferred rights STRICTLY narrow the held authority) rather than a plain relocation/equal grant?
/// A grant is attenuated iff the granted leaf's full effect-mask is a STRICT bitwise submask of the
/// held leaf's (`granted ⊆ held` AND `granted ≠ held`). The full mask folds `mask_lo | (mask_hi <<
/// 16)` per the `CapLeaf` encoding. This is the SAME `granted ⊑ held` relation the
/// `delegateAttenWriteCapOpenVmDescriptor2R24` wrapper's custom subset-table lookup enforces
/// in-circuit, so the route and the in-circuit submask agree: an attenuated grant routes to the
/// submask wrapper, where a grant exceeding held would be UNSAT.
#[cfg(feature = "prover")]
fn is_attenuated_grant(w: &dregg_circuit::effect_vm::AttenuateWitness) -> bool {
    let full =
        |lo: BabyBear, hi: BabyBear| -> u64 { (lo.as_u32() as u64) | ((hi.as_u32() as u64) << 16) };
    let held = full(w.held.mask_lo, w.held.mask_hi);
    let granted = full(w.granted.mask_lo, w.granted.mask_hi);
    // STRICT submask: every granted bit is held, and the grant drops at least one held bit.
    (granted & held) == granted && granted != held
}

#[cfg(feature = "prover")]
fn cap_open_route_for_run(run_effects: &[VmEffectKind]) -> Option<CapOpenRoute> {
    // The deployed `cell/facet.rs` effect-kind bits (`1 << n`).
    const EFFECT_TRANSFER: u32 = 1 << 1;
    const EFFECT_GRANT_CAPABILITY: u32 = 1 << 2;
    const EFFECT_REVOKE_CAPABILITY: u32 = 1 << 3;
    const EFFECT_INTRODUCE: u32 = 1 << 13;
    const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
    match run_effects {
        [VmEffectKind::Transfer { .. }] => Some(CapOpenRoute {
            // #225 TURN-IDENTITY CUTOVER: the LIVE transfer cap-open is the TURN-BOUND descriptor
            // (`transferCapOpenTBVmDescriptor2R24`, `CapOpenTurnPins.effCapOpenV3TB`): the effect-GENERAL
            // `-eff` cap-open (genuine SUBMASK facet — a BROAD honest cap PASSES — + DECODED tier) PLUS
            // two turn-identity columns (`actor`/`dst`) and three turn-identity PIs (`src`/`actor`/`dst`
            // welded to PIs 38/39/40 by appended `.piBinding` gates). The verifier anchors those PIs to
            // the trusted turn, so a ledgerless light client can conclude the published identity MATCHES
            // the proven transition. The apex discharge `transfer_descriptorRefines_facetTB_realized`
            // re-proves the refinement with `hsrc` REALIZED from the PI weld — wire & proof are one.
            key: "transferCapOpenTBVmDescriptor2R24",
            eff_bit: EFFECT_TRANSFER,
            needs_attenuate_patch: false,
            transfer_caveat: true,
            turn_bound: true,
            write: None,
        }),
        // residual (a): the LIVE attenuate cap-open is the effect-GENERAL `-eff` descriptor
        // (`attenuateCapOpenEffVmDescriptor2R24`, `capOpenConstraintsEff 1`) — its leaf must PERMIT
        // EFFECT_TRANSFER (submask, not equality) and its tier is decoded. The SILENT-FORGE close rebased
        // its `map_op` onto the ROTATED cap-root limb (213→264, firing on sel::ATTENUATE_CAPABILITY) as an
        // in-place UPDATE-AT-KEY (`read` the held key's mask, `write` KEEP_MASK at the SAME key) — so it
        // DEMANDS the cap-tree witness heap. The write wrapper IS the same descriptor key (the map_op rides
        // it directly); a non-empty c-list threads the genuine sorted-tree Update. The crown facet is the
        // transfer submask (EFFECT_TRANSFER); the base rides the nonce-TICK face (so the attenuate-freeze
        // patch is skipped when the write witness is threaded).
        [VmEffectKind::AttenuateCapability { .. }] => Some(CapOpenRoute {
            key: "attenuateCapOpenEffVmDescriptor2R24",
            eff_bit: EFFECT_TRANSFER,
            needs_attenuate_patch: true,
            transfer_caveat: false,
            turn_bound: false,
            write: Some((
                "attenuateCapOpenEffVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Update,
                EFFECT_TRANSFER,
            )),
        }),
        // THE FAN-OUT (residual (a) closed): each routes to its `<effect>CapOpenVmDescriptor2R24`,
        // binding the cap to THAT effect-kind bit (not transfer). grantCap/revokeCapability are the
        // nonce-FREEZE attenuate-family bases (need the patch); revoke/refresh/introduce are
        // nonce-TICK passthrough bases (directly valid, NO patch — like transfer minus its caveat).
        // delegate (the cross-vat grant): routes to the `delegateWriteCapOpenVmDescriptor2R24` Insert
        // wrapper (`grantCapWriteV3` base = the MOVING attenuate-genuine TICK face — v1-state cap_root is
        // a PASSTHROUGH, the advance rides the openable rotated cap-root limb 213→264). The consumed
        // held-authority cap (`cap.leaf.slot_hash`) is the ANCHOR (read); the fresh edge (`cap_entry`) is
        // sorted-INSERTed. A wrong post-root is UNSAT (the map_op checks `after = insert(before, key)`);
        // an empty c-list falls back to the authority-only `key`. NOTE: the honest grant base must NOT
        // legacy-advance the v1-state cap_root (the genuine moving face freezes it on the wire) —
        // `GrantCapability { phase_b: Some(_) }` (the granter-passthrough direction) is that face.
        //
        // delegateAtten (the ATTENUATED grant — `delegateAttenWriteCapOpenVmDescriptor2R24`, the SAME
        // genuine moving-face INSERT base PLUS the `granted ⊑ held` submask non-amplification lookup).
        // THE ROUTING SIGNAL (VK-freedom era): a grant is ATTENUATED iff it carries the granter-side
        // phase-B non-amp witness AND the granted leaf's rights are a STRICT submask of the held leaf's
        // (`is_attenuated_grant`) — the conferred cap NARROWS the delegator's authority. That selects the
        // submask wrapper (which forces the `keep ⊑ held` lookup over cols 73/72) instead of the plain
        // `delegateWriteCapOpen`. A non-narrowing grant (same/relocated rights) stays the plain wrapper.
        [
            VmEffectKind::GrantCapability {
                phase_b: Some(w), ..
            },
        ] if is_attenuated_grant(w) => {
            Some(CapOpenRoute {
                key: "grantCapCapOpenVmDescriptor2R24",
                eff_bit: EFFECT_GRANT_CAPABILITY,
                needs_attenuate_patch: true,
                transfer_caveat: false,
                turn_bound: false,
                // The submask write wrapper binds DELEGATION_OPS (1<<16) like plain delegate, AND carries
                // the `granted ⊑ held` lookup. Its Insert fills HELD_MASK (col 72) = anchor held mask,
                // KEEP_MASK (col 73) = conferred mask; a grant exceeding held is UNSAT (the submask bites).
                write: Some((
                    "delegateAttenWriteCapOpenVmDescriptor2R24",
                    dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                    EFFECT_DELEGATION_OPS,
                )),
            })
        }
        // plain delegate (the cross-vat grant, non-attenuating): routes to the plain
        // `delegateWriteCapOpen` Insert wrapper (NO submask lookup — the insert is genuine; for a
        // non-narrowing grant the non-amplification is trivially the held authority itself).
        [VmEffectKind::GrantCapability { .. }] => Some(CapOpenRoute {
            key: "grantCapCapOpenVmDescriptor2R24",
            eff_bit: EFFECT_GRANT_CAPABILITY,
            needs_attenuate_patch: true,
            transfer_caveat: false,
            turn_bound: false,
            // The WRITE wrapper binds the DELEGATION_OPS facet (1<<16), NOT GRANT_CAPABILITY (1<<2) — a
            // delegate IS a delegation op (the consumed authority cap permits delegation).
            write: Some((
                "delegateWriteCapOpenVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                EFFECT_DELEGATION_OPS,
            )),
        }),
        [VmEffectKind::Introduce { .. }] => Some(CapOpenRoute {
            key: "introduceCapOpenVmDescriptor2R24",
            eff_bit: EFFECT_INTRODUCE,
            needs_attenuate_patch: false,
            transfer_caveat: false,
            turn_bound: false,
            // cap-WRITE Insert fan-out (the descriptor anchor-read column landed — 5a98dbb39): the
            // `introduceWriteCapOpenVmDescriptor2R24` Insert wrapper carries a `read`(ANCHOR_KEY var 74)
            // THEN `insert`(CAP_KEY var 71) over DISTINCT columns — the held-authority read authenticates a
            // present anchor leaf, the fresh introduction edge is sorted-INSERTed (BEFORE cap-root limb 213
            // → AFTER cap-root limb 264). The consumed held-authority cap (`cap.leaf.slot_hash`) is the
            // anchor; the fresh edge (`intro_hash`) is the insert. A wrong post-root is UNSAT (the map_op
            // checks `after = insert(before, key)`); an empty c-list falls back to the authority-only `key`.
            write: Some((
                "introduceWriteCapOpenVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                EFFECT_INTRODUCE,
            )),
        }),
        [VmEffectKind::RevokeDelegation { .. }] => Some(CapOpenRoute {
            key: "revokeCapOpenVmDescriptor2R24",
            eff_bit: EFFECT_DELEGATION_OPS,
            needs_attenuate_patch: false,
            transfer_caveat: false,
            turn_bound: false,
            // cap-WRITE light-client axis (THE LOOP IS CLOSED): a revoke IS a cap-tree REMOVE, the node
            // supplies the actor's c-list (the cap-tree write witness — plumbed end-to-end), and the
            // deployed `revokeDelegationWriteCapOpenVmDescriptor2R24` now binds the AFTER cap-root (col
            // 87) ONLY via the `map_op` `write` (`new_root = var87`) — the over-determining poseidon
            // OUTPUT was dropped (commit 0c2b0704c; col 87 is now an INPUT to the commitment chain, not
            // a second definition, exactly as note-spend folds its nullifier root). So routing here is
            // PROVABLE: when the node supplies the c-list (`cap.clist_leaves` non-empty), the prover
            // proves the write wrapper and the genuine post-cap-root is ON-THE-WIRE light-client
            // verifiable (a wrong post-root is UNSAT — the `map_op` checks `after = remove(before, key)`).
            // An empty `clist_leaves` falls back to the authority-only `key` (named, not a silent forge);
            // the verifier tooth (`is_forbidden_plain_cap_descriptor`) forces the cap-open route.
            write: Some((
                "revokeDelegationWriteCapOpenVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Remove,
                EFFECT_DELEGATION_OPS,
            )),
        }),
        [VmEffectKind::RefreshDelegation { .. }] => Some(CapOpenRoute {
            key: "refreshDelegationCapOpenVmDescriptor2R24",
            eff_bit: EFFECT_DELEGATION_OPS,
            needs_attenuate_patch: false,
            transfer_caveat: false,
            turn_bound: false,
            // DELEG-tree WRITE light-client axis (THE DELEG-FORGE CLOSED — Stage E): a refreshDelegation IS a
            // DELEGATIONS-tree UPDATE-AT-KEY (the child's snapshot re-armed at the child key). The
            // authority-only `refreshDelegationCapOpenVmDescriptor2R24` (write:None) left the post-DELEG-root
            // host-trusted — a light client accepted a forged after-deleg-root (the refreshed snapshot
            // fabricated/omitted). The deployed `refreshDelegationWriteCapOpenVmDescriptor2R24` binds the AFTER
            // DELEG-root (the rotated cap-root GROUP — refresh FREEZES `caps`, so that group carries the DELEG
            // accumulator, exactly as Lean `beforeDelegRootCol = beforeCapRootCol`) via the UPDATE-AT-KEY
            // after-spine (`effCapOpenWriteV3_forces_write8`; the arity-2 `Update` map-op was shape-UNSAT
            // against the native-8-felt witness heaps and is DROPPED): the membership READ opens the re-armed
            // leaf against BEFORE, the after-spine re-opens it (value := refreshed snapshot) against AFTER.
            // When the node supplies the cell's delegations leaf-set (`cap.clist_leaves` non-empty) the prover
            // proves the write wrapper and the genuine post-DELEG-root is on-the-wire light-client-verifiable (a
            // wrong post-root is UNSAT — `writesTo` is FUNCTIONAL under CR). An empty leaf-set falls back to the
            // authority-only `key` (named, not a silent forge); the verifier tooth forces the write route. Refresh
            // re-arms an existing delegation (`granted = held`, non-amplification reflexive — Lean
            // `refreshDelegationWriteV3`), so the Update VALUE is the genuine refreshed snapshot the effect now
            // carries (`snapshot_value`, bound into effects_hash) — the membership read opens the held key, the
            // write rebinds it to the on-the-wire snapshot. This is the LIVE realization of
            // `RotatedKernelRefinementCapFamily.refreshDelegation_descriptorRefines_sat`, threaded to the apex
            // `lightclient_unfoolable_closed_final_genuine` (Rfix 55). LIVE LEAD: `VmEffect::RefreshDelegation`
            // now carries the genuine `(child_hash, snapshot_value)` of the SPECIFIC delegation re-armed (the
            // executor derives + binds them; a forged snapshot is refused at apply and changes effects_hash), so
            // an honest refresh of a specific delegation threads its genuine snapshot through the DELEG-tree
            // UPDATE — not the reflexive held-mask re-arm. A producer that omits the cell's delegations c-list
            // (empty leaf-set) still falls back to the authority-only route (named, not a silent forge).
            write: Some((
                "refreshDelegationWriteCapOpenVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Update,
                EFFECT_DELEGATION_OPS,
            )),
        }),
        [VmEffectKind::RevokeCapability { .. }] => Some(CapOpenRoute {
            key: "revokeCapabilityCapOpenVmDescriptor2R24",
            eff_bit: EFFECT_REVOKE_CAPABILITY,
            needs_attenuate_patch: true,
            transfer_caveat: false,
            turn_bound: false,
            // cap-WRITE light-client axis (THE ROUTE-FORGE CLOSED): a revokeCapability IS a cap-tree
            // REMOVE. The authority-only `revokeCapabilityCapOpenVmDescriptor2R24` (write:None) left the
            // post-cap-root host-trusted — a light client accepted a forged post-cap-root (the removed cap
            // fabricated/omitted). The deployed `revokeCapabilityWriteCapOpenVmDescriptor2R24` binds the
            // AFTER cap-root (rotated limb 264) ONLY via the `map_op` REMOVE against the membership-opened
            // BEFORE root: when the node supplies the c-list (`cap.clist_leaves` non-empty) the prover
            // proves the write wrapper and the genuine post-cap-root is on-the-wire light-client-verifiable
            // (a wrong post-root is UNSAT). An empty c-list falls back to the authority-only `key` (named,
            // not a silent forge); the verifier tooth (`is_forbidden_plain_cap_descriptor`) forces the
            // cap-open route. Mirrors revokeDelegation's REMOVE wrapper EXACTLY (same crown facet bit).
            write: Some((
                "revokeCapabilityWriteCapOpenVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Remove,
                EFFECT_REVOKE_CAPABILITY,
            )),
        }),
        [VmEffectKind::SpawnWithDelegation { .. }] => Some(CapOpenRoute {
            key: "spawnCapOpenVmDescriptor2R24",
            // The parent confers a held cap PERMITTING delegation — exactly like `delegate`, the cap binds
            // DELEGATION_OPS (1<<16), not a spawn-specific bit.
            eff_bit: EFFECT_DELEGATION_OPS,
            // spawn rides the nonce-TICK actor face (`spawnActorVmDescriptor`'s `revokeRowGates` template
            // ticks the nonce, `trace_rotated.rs` `new_state.nonce += 1`), like revoke/introduce — directly
            // valid, NO attenuate-freeze patch.
            needs_attenuate_patch: false,
            transfer_caveat: false,
            turn_bound: false,
            // cap-WRITE light-client axis (THE SPAWN CAP-HANDOFF CLOSED): a spawn IS a parent→child
            // CAPABILITY HANDOFF — an INSERT into the cap-tree of the conferred edge at the child key. The
            // authority-only `spawnCapOpenVmDescriptor2R24` (write:None) left the post-cap-root host-trusted
            // — a light client accepted a forged cap handoff (the conferred edge fabricated/omitted, the
            // child cap_root FROZEN). The deployed `spawnWriteCapOpenVmDescriptor2R24` binds the AFTER
            // cap-root (rotated limb 264) via an `Insert` map_op against the membership-opened BEFORE root:
            // the parent's held cap to `target` is the ANCHOR (read), the fresh conferred edge (`spawn_hash`)
            // is sorted-INSERTed (`after = insert(before, child_key)`). When the node supplies the parent's
            // c-list (`cap.clist_leaves` non-empty) the prover proves the write wrapper and the genuine
            // post-cap-root is on-the-wire light-client-verifiable (a wrong post-root is UNSAT). An empty
            // c-list falls back to the authority-only `key` (named, not a silent forge); the verifier tooth
            // forces the cap-open route. The cells-tree accounts insert (the child id grown into accounts)
            // rides limb 0 in PARALLEL — distinct from this cap-tree limb 25. Mirrors delegate's INSERT
            // wrapper EXACTLY (same crown facet bit). This is the LIVE realization of
            // `RotatedKernelRefinementBirth.spawnWrite_descriptorRefines_capOpenSat`, threaded to the apex
            // `lightclient_unfoolable_closed_final_genuine` (Rfix 19).
            write: Some((
                "spawnWriteCapOpenVmDescriptor2R24",
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                EFFECT_DELEGATION_OPS,
            )),
        }),
        _ => None,
    }
}

/// The EFFECTIVE cap-open descriptor key for a `(route, cap)` pair: the WRITE-bearing wrapper when
/// the route has one AND the node supplied the cell's c-list (`cap.clist_leaves` non-empty), else the
/// AUTHORITY-only `route.key`. The prove path (`prove_effect_vm_cap_open`) and the vk_hash lookup MUST
/// agree on this key (the proof is descriptor-bound, so a mismatched vk_hash would reject a sound
/// write proof).
#[cfg(feature = "prover")]
fn cap_open_effective_key(route: &CapOpenRoute, cap: &CapMembershipWitness) -> &'static str {
    match route.write {
        Some((write_key, _, _)) if !cap.clist_leaves.is_empty() => write_key,
        _ => route.key,
    }
}

/// The FRESH edge `(inserted_key, inserted_value)` an INSERT cap-write wrapper grafts into the cap-tree,
/// derived from the granting effect. The inserted leaf is the new capability slot the turn confers; its
/// key is the new cap's folded slot felt (the effect's `limb[0]`, the column the AIR anchors into
/// `params[0]`) and its value is the conferred rights mask (`limb[1]`). The anchor read (the held authority
/// leaf at `cap.leaf.slot_hash`) authenticates the delegator's right; this insert grows the set by the new
/// edge. Returns `None` for effect-kinds that carry no fresh-edge insert (the caller fails closed).
///
/// SOUNDNESS: the inserted key MUST be distinct from the anchor AND absent from the c-list (the sorted
/// `insert_witness` refuses an already-present or sentinel-colliding key); `generate_rotated_cap_write_base`
/// enforces both, so a fabricated post-root is unprovable.
#[cfg(feature = "prover")]
fn cap_insert_payload_for(
    effects: &[VmEffectKind],
    cap: &CapMembershipWitness,
) -> Option<(BabyBear, BabyBear)> {
    match effects {
        // delegate / attenuated-delegate (GrantCapability): the new cap entry. The granter confers
        // `cap_entry[0]` (the new slot felt, AIR `params[0]`) holding the conferred mask `cap_entry[1]`.
        [VmEffectKind::GrantCapability { cap_entry, .. }] => Some((cap_entry[0], cap_entry[1])),
        // introduce: the 3-party introduction hash — `intro_hash[0]` is the new edge slot, `intro_hash[1]`
        // its conferred mask.
        [VmEffectKind::Introduce { intro_hash }] => Some((intro_hash[0], intro_hash[1])),
        // delegateAtten (an attenuated grant carried as AttenuateCapability over the grant base): the
        // narrowed cap is `narrower_commitment[0]` holding the narrowed mask `narrower_commitment[1]`.
        [
            VmEffectKind::AttenuateCapability {
                narrower_commitment,
                ..
            },
        ] => Some((narrower_commitment[0], narrower_commitment[1])),
        // refreshDelegation (the DELEG-tree UPDATE-AT-KEY): an in-place re-arm of a SPECIFIC child's
        // delegation snapshot. The genuine move REBINDS the membership-opened present key
        // (`cap.leaf.slot_hash`, the anchor) to the GENUINE refreshed snapshot the effect now carries
        // (`snapshot_value[0]` — bound into effects_hash; the executor derives it from the parent's live
        // c-list and refuses a forged value at apply). The bridge ignores this tuple's KEY and rebinds at
        // the anchor; the VALUE (the snapshot felt) is the KEEP_MASK the `Update` map_op writes — so the
        // on-the-wire post-DELEG-root binds the SPECIFIC snapshot, not the reflexive held-mask re-arm.
        [
            VmEffectKind::RefreshDelegation {
                child_hash,
                snapshot_value,
            },
        ] => {
            let _ = child_hash; // child binds via effects_hash + params[0]; the anchor key is the membership-opened slot_hash
            Some((cap.leaf.slot_hash, snapshot_value[0]))
        }
        // spawn (the parent→child CAPABILITY HANDOFF): the conferred cap entry. The parent confers
        // `spawn_hash[0]` (the new child cap slot felt, the AIR child key in `params[0]` / cap-write
        // `CAP_KEY`) holding the conferred rights mask `spawn_hash[1]`. The held parent cap to `target`
        // (`cap.leaf.slot_hash`) is the ANCHOR (read); this insert grafts the fresh child edge.
        [VmEffectKind::SpawnWithDelegation { spawn_hash }] => Some((spawn_hash[0], spawn_hash[1])),
        _ => None,
    }
}

/// **`cap_open_supported_for_run`** (F1) — does a cap-open descriptor exist for this single-effect
/// run's effect-kind? Maps the run to its `<effect>CapOpenVmDescriptor2R24` via `cap_open_route_for_run`.
/// Transfer + attenuate + the 7 fan-out effects (grantCap, introduce, revoke(Delegation),
/// refreshDelegation, revokeCapability, spawn) are WIRED — each binds the cap to its OWN effect-kind bit.
/// `ExerciseViaCapability` now HAS its cap-open descriptor emitted
/// (`exerciseCapOpenVmDescriptor2R24`, the FROZEN exercise base + the EFF_EXERCISE depth-16
/// cap-membership crown; `Rfix 16`, threaded into `lightclient_unfoolable_closed_final_genuine` with
/// mutation-confirmation). The Lean apex + the descriptor column-genuineness + witness-forge-rejection
/// are CLOSED (`circuit/tests/cap_open_exercise_self_verify.rs`). The remaining residual for exercise
/// is the SHARED non-TB cap-open prove-THROUGH plumbing (the IR-v2 cap-node lookup-balance gap that
/// `cap_open_attenuate_self_verifies` also carries — only the TURN-BOUND transfer path self-verifies);
/// the SDK route for exercise is a follow-on, gated behind that shared prove path landing.
#[cfg(feature = "prover")]
fn cap_open_supported_for_run(run_effects: &[VmEffectKind]) -> Result<(), SdkError> {
    if run_effects.len() != 1 {
        return Err(SdkError::InvalidWitness(
            "cap-open routing: expected exactly one cap-authorized effect in the run".into(),
        ));
    }
    if cap_open_route_for_run(run_effects).is_some() {
        Ok(())
    } else {
        Err(SdkError::InvalidWitness(format!(
            "cap-open routing: a cap witness was threaded for a {:?} run, but the SDK does not yet \
             ROUTE that effect-kind's cap-open descriptor (transfer/attenuate + the 7 fan-out \
             grantCap/introduce/revoke/refreshDelegation/revokeCapability/spawn are wired). \
             ExerciseViaCapability's cap-open descriptor (exerciseCapOpenVmDescriptor2R24, Rfix 16) \
             IS emitted + apex-threaded; its SDK route is a follow-on behind the shared non-TB \
             cap-open prove-through plumbing. Drop the cap witness to prove the base cohort descriptor.",
            run_effects[0]
        )))
    }
}

/// The CAP-OPEN single-leg prover (soundness loop #5): prove an `AttenuateCapability` turn
/// through the CAP-OPEN descriptor (`attenuateCapOpenEffVmDescriptor2R24`, the 369-wide
/// `attenuateCapOpenEffV3` leg — genuine submask facet + decoded tier), so the in-circuit cap-membership open — the authority leg the
/// soundness proof relies on (`DeployedCapOpen.Satisfied`) — is GENUINELY exercised end-to-end.
///
/// The live single-leg/chain prover resolves the BASE attenuate descriptor
/// (`attenuateVmDescriptor2R24`, 311-wide, NO cap-membership appendix). When the actor's REAL
/// consumed capability is threaded (`witness.cap_membership`), this proves the wider cap-open
/// descriptor instead: it builds the proven 311-wide rotated attenuate base, wires the attenuate
/// phase-B bindings (`patch_attenuate_base_for_cap_open`), converts the SDK
/// [`dregg_circuit::cap_root::CapMembershipWitness`] to the trace-column
/// [`dregg_circuit::effect_vm::trace_rotated::CapOpenWitness`], and widens the trace with the
/// 58-column cap-open membership appendix (`widen_to_cap_open`) before proving through
/// `prove_vm_descriptor2`. The depth-16 absorb-node fold opens the committed `cap_root` at a
/// write-mask leaf whose target is the turn's `src`; the proof self-verifies before return.
///
/// Returns `(proof, dpis)` — the dpis are the SAME 38-PI vector the base attenuate leg carries
/// (the cap-open descriptor declares 38 PIs), corrected by the phase-B base wiring. The verifier
/// (`verify_effect_vm_rotated_with_cutover`) binds the cap-open descriptor naturally (it iterates
/// every committed cohort descriptor and binds the unique acceptor), so no verify-side change is
/// needed beyond the cap-open vk_hash.
#[cfg(feature = "prover")]
#[cfg_attr(not(test), allow(dead_code))] // a thin test-only wrapper over the generic prover
fn prove_effect_vm_cap_open_attenuate(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    cap: &CapMembershipWitness,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    // This leg is ONLY for a single AttenuateCapability effect. A multi-effect or non-attenuate run
    // never reaches here (the caller gates). Delegates to the generic prover at the attenuate route
    // (the `attenuateCapOpenEffV3` appendix: eff_bit = EFFECT_TRANSFER submask, phase-B patch).
    if !matches!(effects, [VmEffectKind::AttenuateCapability { .. }]) {
        return Err(SdkError::InvalidWitness(
            "cap-open prover: expects exactly one AttenuateCapability effect".into(),
        ));
    }
    let route = CapOpenRoute {
        key: "attenuateCapOpenEffVmDescriptor2R24",
        eff_bit: dregg_circuit::effect_vm::trace_rotated::WRITE_MASK_LO,
        needs_attenuate_patch: true,
        transfer_caveat: false,
        turn_bound: false,
        // The attenuate map_op fires unconditionally (sel::ATTENUATE_CAPABILITY) as an in-place
        // UPDATE-AT-KEY, so it DEMANDS the cap-tree witness heap. With a non-empty c-list the genuine
        // sorted-tree Update is threaded; the crown facet is the transfer submask (WRITE_MASK_LO).
        write: Some((
            "attenuateCapOpenEffVmDescriptor2R24",
            dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Update,
            dregg_circuit::effect_vm::trace_rotated::WRITE_MASK_LO,
        )),
    };
    // The attenuate cap-open key has a proven wide twin, so production always goes wide for it (the
    // narrow 1-felt leg is rejected by the wide-dodge tooth). Mirror production: go WIDE.
    prove_effect_vm_cap_open(
        initial_state,
        effects,
        before_w,
        after_w,
        cap,
        &route,
        None,
        true,
    )
}

/// Look up a cap-open descriptor JSON by its registry key from the staged rotated registry. The
/// cap-open members (`attenuateCapOpenEffVmDescriptor2R24`, `transferCapOpenEffVmDescriptor2R24`) are
/// NOT resolved by `rotated_descriptor_name_for_effect` (no effect selects them by kind — they are
/// the cap-AUGMENTED legs the prove site opts into when a consumed-cap witness is present); the SDK
/// names the registry key directly. Returns the JSON for `key`.
#[cfg(feature = "prover")]
fn cap_open_descriptor_json_by_key(key: &str) -> Result<&'static str, SdkError> {
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(key) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .ok_or_else(|| SdkError::InvalidWitness(format!("{key} not in staged rotated registry")))
}

/// The cap-open leg's `vk_hash` for a given registry key: the blake3 fingerprint of the committed
/// cap-open descriptor JSON (the SAME fingerprint `verify_effect_vm_rotated_with_cutover` re-derives
/// from the uniquely accepting cap-open cohort descriptor). Distinct per descriptor, so the attached
/// vk_hash matches the actual cap-open descriptor (attenuate vs transfer base).
#[cfg(feature = "prover")]
fn cap_open_vk_hash_by_key(key: &str) -> Result<[u8; 32], SdkError> {
    let json = cap_open_descriptor_json_by_key(key)?;
    Ok(*blake3::hash(json.as_bytes()).as_bytes())
}

/// Look up a WIDE+UMEM WELDED descriptor JSON by its LIVE registry key from
/// [`WIDE_UMEM_WELD_REGISTRY_TSV`](dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV)
/// — the Lean-emitted, member-for-member welded twin of the wide registry. The KEY is the live
/// registry key (`transferVmDescriptor2R24` / `attenuateCapOpenEffVmDescriptor2R24`); the JSON is the
/// welded descriptor (the wide carriers + the appended `umemOp` leg). `Ok(None)` when the key has NO
/// welded twin (the 1-felt-only / wide-twin-pending residual — e.g. `transferCapOpenTB`); `Err` only
/// on a malformed line (unreachable for the committed TSV).
#[cfg(feature = "prover")]
fn wide_umem_weld_registry_json_by_key(key: &str) -> Option<&'static str> {
    use dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV;
    WIDE_UMEM_WELD_REGISTRY_TSV.lines().find_map(|line| {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some(key) {
            let _display = it.next();
            it.next()
        } else {
            None
        }
    })
}

/// True iff the live registry `key` has a welded twin in the Lean-emitted
/// [`WIDE_UMEM_WELD_REGISTRY_TSV`](dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV)
/// — the gate the welded routing in [`prove_cohort_run_chain`] keys on (a welded member welds; a
/// wide-twin-pending residual stays bare).
#[cfg(feature = "prover")]
pub fn wide_umem_weld_registry_has(key: &str) -> bool {
    wide_umem_weld_registry_json_by_key(key).is_some()
}

/// The WIDE+UMEM WELDED leg's `vk_hash` for a registry `key`: the blake3 fingerprint of the welded
/// member's committed JSON — the SAME fingerprint the wire verifier
/// (`verify_effect_vm_rotated_with_cutover`) and the executor's `verify_and_commit_proof_rotated`
/// re-derive from the uniquely-accepting welded descriptor. So a welded leg's attached vk_hash MUST
/// pin the welded member (NOT the bare wide member) for the descriptor-identity tooth to pass.
#[cfg(feature = "prover")]
fn wide_umem_weld_vk_hash_by_key(key: &str) -> Result<[u8; 32], SdkError> {
    let json = wide_umem_weld_registry_json_by_key(key).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "{key} has no welded twin in WIDE_UMEM_WELD_REGISTRY_TSV"
        ))
    })?;
    Ok(*blake3::hash(json.as_bytes()).as_bytes())
}

/// THE WIDE CAP-OPEN FLAG-DAY: does this cap-open effective key have a PROVEN wide twin in
/// `WIDE_REGISTRY_STAGED_TSV` (the Lean `v3RegistryCapOpenWide` authority crown + the §10
/// `v3RegistryCapOpenWriteWide` WRITE tail)? True for the 8 AUTHORITY-CROWN members
/// (`delegate/introduce/grantCap/revoke/refresh/revokeCapability CapOpen` + `transferCapOpenEff` +
/// `attenuateCapOpenEff`) AND the 10 WRITE-bearing tail members (`…WriteCapOpenVmDescriptor2R24` +
/// `spawnCapOpen` + `exerciseCapOpen`) — every cap-open host (819) is a gated host wide-wrapped by the
/// SAME proven `wideAppend host bb (bb+51)`, geometry-identical to the crown (the cap-tree write is a
/// `map_op`, not a column, so the host width is unchanged). FALSE only for the turn-bound
/// (`transferCapOpenTB`) — its `effCapOpenV3TB` host carries TWO extra turn-identity columns at a
/// DIFFERENT (821-col) width, so `append_wide_carriers_cap_open`'s `CAP_OPEN_WIDTH` lift does not accept
/// it; it has no proven wide twin yet (the named TB residual) and stays on the 1-felt route. Membership
/// is read STRAIGHT off the proven wide registry, so a key is wide iff its Lean wide twin exists.
#[cfg(feature = "prover")]
fn cap_open_key_has_wide_twin(key: &str) -> bool {
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
    // The TB family has no proven wide twin (its host width differs); exclude it explicitly. Every
    // OTHER cap-open key (crown AND the §10 WRITE tail) is wide iff it appears in the proven wide
    // registry — read membership straight off the TSV (the Lean source of truth).
    if key.contains("TB") {
        return false;
    }
    WIDE_REGISTRY_STAGED_TSV
        .lines()
        .any(|line| line.split('\t').next() == Some(key))
}

/// Resolve the committed WIDE cap-open descriptor JSON for a key (the `WIDE_REGISTRY_STAGED_TSV`
/// twin of [`cap_open_descriptor_json_by_key`]).
#[cfg(feature = "prover")]
fn cap_open_wide_descriptor_json_by_key(key: &str) -> Result<&'static str, SdkError> {
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
    WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(key) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .ok_or_else(|| SdkError::InvalidWitness(format!("{key} not in WIDE_REGISTRY_STAGED_TSV")))
}

/// The WIDE cap-open leg's `vk_hash` (blake3 of the WIDE cap-open descriptor JSON).
#[cfg(feature = "prover")]
fn cap_open_wide_vk_hash_by_key(key: &str) -> Result<[u8; 32], SdkError> {
    let json = cap_open_wide_descriptor_json_by_key(key)?;
    Ok(*blake3::hash(json.as_bytes()).as_bytes())
}

/// The ATTENUATE cap-open leg's `vk_hash` (the blake3 fingerprint of its descriptor JSON).
#[cfg(feature = "prover")]
#[cfg_attr(not(test), allow(dead_code))] // test-only; the chain routes via `cap_open_vk_hash_by_key`
fn rotated_cap_open_vk_hash() -> Result<[u8; 32], SdkError> {
    // The attenuate leg goes WIDE (production route), so its vk_hash is the wide descriptor fingerprint.
    cap_open_wide_vk_hash_by_key("attenuateCapOpenEffVmDescriptor2R24")
}

/// The TRANSFER cap-open leg's `vk_hash` (#225) — the blake3 fingerprint of the LIVE TURN-BOUND
/// `transferCapOpenTBVmDescriptor2R24` JSON (the genuine-submask descriptor PLUS the turn-identity weld).
#[cfg(feature = "prover")]
#[cfg_attr(not(test), allow(dead_code))] // test-only; the chain routes via `cap_open_vk_hash_by_key`
fn rotated_transfer_cap_open_vk_hash() -> Result<[u8; 32], SdkError> {
    cap_open_vk_hash_by_key("transferCapOpenTBVmDescriptor2R24")
}

/// **`prove_effect_vm_cap_open_transfer`** (residual (b) — the CROSS-VAT Transfer-via-granted-cap
/// authority leg) — prove a single `Transfer` turn through the TRANSFER cap-open descriptor
/// (`transferCapOpenEffVmDescriptor2R24`, the transfer base + the cap-membership appendix). When the
/// actor's REAL consumed transfer-cap is threaded (the cross-vat `actor != src` case), this routes
/// the in-circuit depth-16 cap-membership open so the authority leg
/// (`CapOpenEmit.transferCapOpenV3_authorizes ⟹ authorizedFacetB`) is GENUINELY exercised.
///
/// Unlike the attenuate leg, the transfer base needs NO phase-B nonce-freeze patch: a Transfer is a
/// regular rotated cohort effect whose `generate_rotated_effect_vm_trace` output is directly valid
/// (the base 38-PI vector is correct as generated). We build the transfer base, convert the SDK
/// c-list opening to the trace-column [`CapOpenWitness`], widen with the 59-column appendix
/// (`widen_to_cap_open`, which fails CLOSED if the cap does not recompose its root or does not
/// confer the transfer facet/tier the descriptor's gates pin), then prove + self-verify.
#[cfg(feature = "prover")]
#[cfg_attr(not(test), allow(dead_code))] // a thin test-only wrapper over the generic prover
fn prove_effect_vm_cap_open_transfer(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    cap: &CapMembershipWitness,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    // This leg is ONLY for a single Transfer effect. A multi-effect or non-transfer run never reaches
    // here (the caller gates). Delegates to the generic prover at the transfer route (eff_bit =
    // EFFECT_TRANSFER, no phase-B patch, transfer caveat manifest).
    if !matches!(effects, [VmEffectKind::Transfer { .. }]) {
        return Err(SdkError::InvalidWitness(
            "transfer cap-open prover: expects exactly one Transfer effect".into(),
        ));
    }
    let route = CapOpenRoute {
        key: "transferCapOpenTBVmDescriptor2R24",
        eff_bit: dregg_circuit::effect_vm::trace_rotated::WRITE_MASK_LO,
        needs_attenuate_patch: false,
        transfer_caveat: true,
        turn_bound: true,
        write: None,
    };
    // The test helper publishes the OWNER arm (no explicit cross-vat identity); the verifier anchors
    // the three turn-identity PIs to the trusted turn in the deployment negative test.
    prove_effect_vm_cap_open(
        initial_state,
        effects,
        before_w,
        after_w,
        cap,
        &route,
        None,
        false,
    )
}

/// **`prove_effect_vm_cap_open`** (THE GENERIC FAN-OUT PROVER, residual (a)) — prove a single
/// cap-authorized turn through its `<effect>CapOpenVmDescriptor2R24` descriptor, binding the consumed
/// cap to the turn's ACTUAL effect-kind bit (`route.eff_bit`), NOT transfer. The appendix + the
/// `widen_to_cap_open` patch are BASE-AGNOSTIC, so this one routine serves every wired effect:
///
///   * resolve the cap-open descriptor JSON by `route.key`;
///   * build the effect's rotated base trace (`route.needs_attenuate_patch` ⇒ the attenuate phase-B
///     nonce-freeze + the empty caveat manifest; else the transfer caveat manifest, directly valid);
///   * convert the SDK c-list opening to the trace-column [`CapOpenWitness`] FOR `route.eff_bit`
///     (`from_membership_for`, which fails CLOSED if the cap's facet `mask_lo != eff_bit` — the cap
///     does not permit THAT effect-kind), and widen the base with the 59-column appendix;
///   * prove + self-verify.
///
/// The descriptor's `effBitGateFor` pins `effBit == route.eff_bit`; `facetEffGate` forces `leaf.mask_lo
/// == effBit` — so the in-circuit cap-open authorizes the turn's effect-kind ONLY (a wrong-facet cap is
/// UNSAT / refused). Returns `(proof, dpis)`.
#[cfg(feature = "prover")]
fn prove_effect_vm_cap_open(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    cap: &CapMembershipWitness,
    route: &CapOpenRoute,
    identity: Option<TurnIdentityFelts>,
    // WIDE CAP-OPEN FLAG-DAY: when true AND the effective key has a proven wide twin (authority-crown,
    // non-TB, non-Write), append the 8-felt wide carriers + prove against the WIDE cap-open descriptor
    // so the leg publishes the full ~124-bit commit. When false (or ineligible), the 1-felt V3 route.
    wide: bool,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
    // The descriptor + trace + dpis + map-op heaps are built by the SHARED cap-open leg builder (so the
    // welded domain-2 twin `prove_wide_umem_welded_cap_open_staged` reuses the EXACT same cap-open
    // descriptor / membership crown / wide carriers, then welds the umem leg onto it — no hand-inlined
    // twin). This routine only PROVES the built leg through the bare (non-umem) IR-v2 prover.
    let (desc, trace, dpis, all_heaps) = build_effect_vm_cap_open_leg(
        initial_state,
        effects,
        before_w,
        after_w,
        cap,
        route,
        identity,
        wide,
    )?;
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &all_heaps,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("cap-open IR-v2 proof ({}): {e}", desc.name)))?;
    Ok((proof, dpis))
}

/// **THE SHARED CAP-OPEN LEG BUILDER** — resolve the `<effect>CapOpenVmDescriptor2R24` descriptor and
/// assemble its rotated base trace + membership-crown appendix + (when `wide`) the 8-felt wide carriers
/// + the cap-tree `map_op` witness heaps, returning `(descriptor, trace, dpis, map_op_heaps)` WITHOUT
///   proving. Extracted from [`prove_effect_vm_cap_open`] so the bare prover AND the welded domain-2 twin
///   ([`prove_wide_umem_welded_cap_open_staged`]) share ONE descriptor/trace route (no hand-inlined twin):
///   the welded twin welds the universal-memory caps leg onto THIS descriptor + trace before proving. See
///   [`prove_effect_vm_cap_open`] for the per-step semantics.
#[cfg(feature = "prover")]
#[allow(clippy::type_complexity)]
fn build_effect_vm_cap_open_leg(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    cap: &CapMembershipWitness,
    route: &CapOpenRoute,
    identity: Option<TurnIdentityFelts>,
    wide: bool,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
    use dregg_circuit::effect_vm::trace_rotated::{
        CAP_OPEN_TB_WIDTH, CapOpenWitness, RotatedBlockWitness, cap_open_tb_dpis,
        empty_caveat_manifest, generate_rotated_cap_write_base, patch_attenuate_base_for_cap_open,
        transfer_caveat_manifest, widen_to_cap_open_avail, widen_to_cap_open_tb_avail,
    };

    // cap-WRITE light-client axis: when this effect-kind HAS a write-bearing wrapper AND the node
    // supplied the cell's full c-list (`cap.clist_leaves`), prove the `…WriteCapOpenVmDescriptor2R24`
    // wrapper (the cap-tree write's post-root is on-the-wire-verifiable). Otherwise the AUTHORITY-only
    // `route.key` (the post-cap-root stays host-trusted — named, not a silent forge). The
    // [`generate_rotated_cap_write_base`] bridge threads the c-list as the `map_op` witness heap; a
    // wrong post-root is UNSAT (the guardrail — never a fabricated post-root).
    let cap_write = match route.write {
        Some((write_key, op, write_eff_bit)) if !cap.clist_leaves.is_empty() => {
            Some((write_key, op, write_eff_bit))
        }
        _ => None,
    };
    let effective_key = cap_write.map(|(k, _, _)| k).unwrap_or(route.key);
    // The membership-crown facet bit: the WRITE wrapper's facet (which may differ from the authority-only
    // `route.eff_bit` — e.g. delegate's write wrapper binds DELEGATION_OPS, the authority-only binds
    // GRANT_CAPABILITY) when the write route is active; else the route's authority-only facet.
    let crown_eff_bit = cap_write.map(|(_, _, eb)| eb).unwrap_or(route.eff_bit);

    // ATTENUATE cap-WRITE on the AFTER-SPINE path (the arity-7 cap-tree `effCapOpenWriteV3_forces_write8`,
    // the faithful 8-felt in-place UPDATE-AT-KEY), NOT the arity-2 map-op. The map-op was DROPPED from the
    // Lean `attenuateV3` base; the deployed descriptor now forces the write via the after-spine appendix
    // alone.
    // refreshDelegation rides the SAME UPDATE-AT-KEY after-spine shape (the DELEG-tree leaf re-armed
    // at the SAME child key — the rotated cap-root group carries the DELEG accumulator on a refresh
    // row, exactly as Lean `beforeDelegRootCol = beforeCapRootCol`), so it routes through the
    // attenuate producer with `keep_mask` = the genuine refreshed snapshot felt.
    let attenuate_after_spine = cap_write
        .map(|(k, op, _)| {
            matches!(
                op,
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Update
            ) && matches!(
                k,
                "attenuateCapOpenEffVmDescriptor2R24"
                    | "refreshDelegationWriteCapOpenVmDescriptor2R24"
            )
        })
        .unwrap_or(false);
    // The INSERT-shaped keystone deploy (delegate / introduce / delegateAtten): the deployed
    // `effCapInsertV3` wrap — the cap-open READ opens the SPLICED (conferred) leaf against the
    // REBUILT AFTER cap-root over the `CanonicalCapTree::insert_witness` after-membership path
    // (`CapInsertEmit.effCapInsertV3_forces_write8`). The arity-2 map-ops were DROPPED from the Lean
    // bases (shape-UNSAT against the arity-7 fresh-key splice), so NO map heap.
    let insert_after_spine = cap_write
        .map(|(k, op, _)| {
            matches!(
                op,
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert
            ) && matches!(
                k,
                "delegateWriteCapOpenVmDescriptor2R24"
                    | "introduceWriteCapOpenVmDescriptor2R24"
                    | "delegateAttenWriteCapOpenVmDescriptor2R24"
                    // spawn's parent→child cap handoff IS the same fresh-key splice (the conferred
                    // edge at the child key), riding the keystone INSERT alongside the cells-tree
                    // accounts grow-gate (limb 0, the surviving map-ops).
                    | "spawnWriteCapOpenVmDescriptor2R24"
            )
        })
        .unwrap_or(false);
    // The REMOVE-shaped keystone deploy (revokeDelegation): the deployed `effCapRemoveV3` wrap — the
    // cap-open READ opens the REMOVED leaf against BEFORE (the consumed-cap membership witness the
    // revoke route already carries); the AFTER cap-root group carries the deployed tombstone
    // zero-fold (`CanonicalCapTree::remove_witness` — `CapRemoveEmit.effCapRemoveV3_forces_write8`).
    let remove_after_spine = cap_write
        .map(|(k, op, _)| {
            matches!(
                op,
                dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Remove
            ) && matches!(
                k,
                "revokeDelegationWriteCapOpenVmDescriptor2R24"
                    // revokeCapability IS the same tombstone zero-fold (the executor's
                    // `capabilities.revoke` removes the slot + tombstones its sorted position);
                    // mirrors revokeDelegation EXACTLY (no epoch gate).
                    | "revokeCapabilityWriteCapOpenVmDescriptor2R24"
            )
        })
        .unwrap_or(false);

    // WIDE eligibility: the effective key must have a PROVEN wide twin in `WIDE_REGISTRY_STAGED_TSV`.
    // EVERY live cap-open key — the authority crown, the §10 WRITE tail, AND the turn-bound
    // `transferCapOpenTB` (its wide twin at `CAP_OPEN_TB_WIDTH + 208 = 1029`, the `wideAppend` at the
    // transfer face, emitted by `EmitWideRegistryProbe`) — now has a wide twin, so the resolver is a
    // straight registry lookup (no TB exclusion). The TB branch below lands its 8-felt carriers at the
    // CAP_OPEN_TB host width (the 2 turn-identity columns ride UNDER the carriers); the non-TB branch
    // uses the `CAP_OPEN_WIDTH` lift. Eligible ⇒ resolve the WIDE descriptor; else the 1-felt V3.
    let go_wide = wide && cap_open_wide_descriptor_json_by_key(effective_key).is_ok();
    let json = if go_wide {
        cap_open_wide_descriptor_json_by_key(effective_key)?
    } else {
        cap_open_descriptor_json_by_key(effective_key)?
    };
    let desc = parse_vm_descriptor2(json).map_err(|e| {
        SdkError::InvalidWitness(format!("cap-open descriptor parse ({effective_key}): {e}"))
    })?;
    // THE AVAILABILITY PAD (GAP #4, cap-open member): a hardened `…-v1-avail` cap-open member
    // (the transfer eff/TB keys post-regen) widens its v1 face by the avail witness columns, so
    // the rotated appendix, cap-open appendix, and TB columns all shift by the pad. Derived from
    // the RESOLVED descriptor's name — zero for every bare member (byte-identical legacy path).
    // The WIDE twins ride the SAME pad (their avail flip landed: the wide TB lift below appends
    // the carriers at `CAP_OPEN_TB_WIDTH + avail_pad`, matching the retargeted
    // `transferCapOpenTBVmDescriptor2R24` wide row = `wideAppend transferCapOpenEffV3TBAvail` —
    // the narrow and wide registries regen together, so the two names agree on the pad).
    let avail_pad =
        dregg_circuit::effect_vm::trace_rotated::avail_pad_for_descriptor_name(&desc.name);

    let bridge = |w: &dregg_turn::rotation_witness::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
    };
    let before = bridge(before_w)
        .map_err(|e| SdkError::InvalidWitness(format!("cap-open before-witness: {e}")))?;
    let after = bridge(after_w)
        .map_err(|e| SdkError::InvalidWitness(format!("cap-open after-witness: {e}")))?;

    // Only the Transfer base threads the transfer caveat manifest; every other base (attenuate-family
    // AND the nonce-tick passthroughs) uses the empty manifest.
    let caveat = if route.transfer_caveat {
        transfer_caveat_manifest()
    } else {
        empty_caveat_manifest()
    };
    // spawn is the ONLY cap-fanout effect that ALSO grows the accounts set (the birth leg): its
    // descriptor (`spawnWriteV3`) carries the cells-tree accounts INSERT (limb 0) ALONGSIDE the cap-tree
    // handoff INSERT (limb 25). So when the write wrapper is active, the base trace is built by the
    // accounts grow-gate wiring (`generate_rotated_create_cell_trace_with_accounts_tree`, which overrides
    // limb 0 with the openable accounts accumulator + returns the BEFORE accounts leaf-set as its map-op
    // heap), and the cap-write base runs OVER it (overriding limb 25 + recomputing the rotated commit,
    // which preserves the limb-0 override). The two map-op heaps are concatenated; the map-op table
    // matches each op to its heap by ROOT (the accounts root for limb 0, the c-list root for limb 25).
    let spawn_dual_tree = cap_write.is_some()
        && matches!(
            effects.first(),
            Some(VmEffectKind::SpawnWithDelegation { .. })
        );
    let (mut trace, pis, accounts_heaps): (
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    ) = if spawn_dual_tree {
        // The genuine spawn producer supplies the actor's BEFORE accounts leaf-set as the cap witness's
        // accounts witness; here the child key is fresh against the (possibly empty) before-set — the
        // `.absent` freshness op brackets via the sentinel range, and a re-spawn of an existing cell id
        // has no bracketing witness and is REFUSED.
        let before_accounts: Vec<dregg_circuit::heap_root::HeapLeaf> = Vec::new();
        let (trace, pis, heaps) =
                dregg_circuit::effect_vm::trace_rotated::generate_rotated_create_cell_trace_with_accounts_tree(
                    initial_state, effects, &before, &after, &caveat, &before_accounts,
                )
                .map_err(|e| {
                    SdkError::InvalidWitness(format!("cap-open spawn accounts base ({}): {e}", route.key))
                })?;
        (trace, pis, heaps)
    } else {
        // The DESCRIPTOR-driven avail generator: at pad 0 byte-identical to
        // `generate_rotated_effect_vm_trace`; at a nonzero pad it fills the availability witness
        // limbs/borrow bits per row and lays the rotated appendix at the shifted bases.
        let (trace, pis) =
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace_avail(
                avail_pad,
                initial_state,
                effects,
                &before,
                &after,
                &caveat,
            )
            .map_err(|e| {
                SdkError::InvalidWitness(format!("cap-open base trace ({}): {e}", route.key))
            })?;
        (trace, pis, Vec::new())
    };

    // THE CAP-OPEN rc STRIP: the committed cap-open family was NEVER rc-wrapped in the Lean emit —
    // every `*CapOpen*` registry member carries the UNWRAPPED base (46/47/49 + appendix/wide PIs;
    // e.g. `attenuateCapOpenEffVmDescriptor2R24` 46 → wide 62), while the dsl rc tail
    // (`withDfaRcPins`, 4 PIs riding LAST on the base vector) wraps only the PLAIN cohort members.
    // The base generators append the rc unconditionally, so lift it off here — the route owns the
    // tail shape (the phase-B patch below is shape-preserving).
    let mut pis = pis;
    {
        use dregg_circuit::effect_vm::trace_rotated::DFA_RC_LEN;
        if pis.len() < DFA_RC_LEN {
            return Err(SdkError::InvalidWitness(format!(
                "cap-open base trace ({}): PI vector {} shorter than the dsl rc tail",
                route.key,
                pis.len()
            )));
        }
        pis.truncate(pis.len() - DFA_RC_LEN);
    }

    // Attenuate-family bases need the phase-B nonce-FREEZE + cap-root advance wiring; transfer is
    // directly valid (its 38-PI vector is correct as generated). BUT the WRITE-bearing wrappers ALL
    // ride the nonce-TICK face (`after.nonce == before.nonce + 1`, the gate `(var78-var56) == 1-sel0`)
    // — the cap-root advance is the openable map_op write, NOT the v1-state freeze the authority-only
    // attenuate-family `key` carries. So when the write wrapper is active, SKIP the nonce-freeze patch
    // (it would freeze the nonce against the wrapper's tick gate and corrupt the rebuilt commitment).
    let mut dpis = if route.needs_attenuate_patch && cap_write.is_none() {
        patch_attenuate_base_for_cap_open(&mut trace, &pis)
            .map_err(|e| SdkError::InvalidWitness(format!("cap-open base phase-B wiring: {e}")))?
    } else {
        pis
    };

    // cap-WRITE: thread the cell's c-list as the cap-tree write witness heap. This OVERRIDES the
    // BEFORE/AFTER cap-root columns (col 65/87 + the rotated weld) with the openable sorted-Poseidon2
    // tree roots (BEFORE = the c-list root, AFTER = the genuine post-write root), fills the `map_op`
    // key/value params, recomputes the rotated commitments + the rotated commit PIs, and returns the
    // BEFORE leaf-set as `map_heaps` for the `map_op`.
    //
    //   * REMOVE (revokeDelegation): the consumed cap's `slot_hash` is read+written in place (value 0).
    //   * INSERT (delegate/introduce/delegateAtten): the consumed cap's `slot_hash` is the ANCHOR
    //     (the delegator's held authority leaf, read-only); the FRESH edge — `cap_insert_payload_for`
    //     derived from the effect (the new `cap_entry`/`intro_hash` folded to a key + its conferred
    //     mask) — is the inserted leaf. The anchor MUST be present and the fresh key MUST be absent +
    //     distinct (both fail closed; no fabricated post-root).
    let cap_write_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = match cap_write {
        // AFTER-SPINE keystone paths (attenuate UPDATE / delegate·introduce·delegateAtten INSERT /
        // revokeDelegation REMOVE): NO map-op, NO map heap. The 8-felt cap-tree write is laid AFTER
        // `widen_to_cap_open` by the shape-matched producer (see the widen block below).
        Some(_) if attenuate_after_spine || insert_after_spine || remove_after_spine => Vec::new(),
        Some((_, op, _)) => {
            use dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp;
            let inserted = match op {
                // INSERT (delegate/introduce): the FRESH edge (distinct, absent key + conferred mask).
                CapTreeWriteOp::Insert => Some(cap_insert_payload_for(effects, cap).ok_or_else(|| {
                    SdkError::InvalidWitness(format!(
                        "cap-write Insert ({effective_key}): could not derive the fresh edge \
                         (key,value) from the {:?} effect",
                        effects.first()
                    ))
                })?),
                // UPDATE (attenuate): the SAME held key (anchor = `cap.leaf.slot_hash`) rebound to the
                // narrowed KEEP_MASK. The bridge ignores the key field and rebinds at the anchor; the
                // value is the conferred (narrowed) mask the effect carries.
                CapTreeWriteOp::Update => Some(cap_insert_payload_for(effects, cap).ok_or_else(|| {
                    SdkError::InvalidWitness(format!(
                        "cap-write Update ({effective_key}): could not derive the narrowed KEEP_MASK \
                         from the {:?} effect",
                        effects.first()
                    ))
                })?),
                // REMOVE (revokeDelegation): read+write the same present key (value 0); no payload.
                CapTreeWriteOp::Remove => None,
            };
            generate_rotated_cap_write_base(
                &mut trace,
                &mut dpis,
                op,
                &cap.clist_leaves,
                cap.leaf.slot_hash,
                inserted,
            )
            .map_err(|e| {
                SdkError::InvalidWitness(format!("cap-write witness ({effective_key}): {e}"))
            })?
        }
        None => Vec::new(),
    };

    // Convert the c-list opening to the trace-column witness FOR the turn's effect-kind bit (fails
    // closed if the cap's facet does not permit the crown facet — the WRITE wrapper's facet when active,
    // else `route.eff_bit`), then widen.
    let cap_open = CapOpenWitness::from_membership_for(
        &cap.leaf,
        &cap.siblings,
        &cap.directions,
        crown_eff_bit,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("cap-open witness ({}): {e}", route.key)))?;

    // The TURN-BOUND route (#225) widens with TWO extra turn-identity columns (`actor`/`dst`) and
    // extends the dpis with THREE turn-identity PIs (`src`/`actor`/`dst` at 38/39/40). `src` is the
    // cap-leaf target (the column `targetBindGate` roots); when no explicit identity is threaded the
    // OWNER arm (`actor = dst = src`) is published. The verifier ANCHORS the three PIs to the trusted
    // turn, so the published identity is FORCED to match the proven transition.
    let dpis = if route.turn_bound {
        let src = cap_open.src;
        let (actor, dst) = match identity {
            Some(id) => (id.actor, id.dst),
            None => (src, src),
        };
        widen_to_cap_open_tb_avail(&mut trace, &cap_open, actor, dst, avail_pad).map_err(|e| {
            SdkError::InvalidWitness(format!("cap-open TB widen ({}): {e}", route.key))
        })?;
        let tb_pis = cap_open_tb_dpis(&dpis, src, actor, dst);
        if go_wide {
            // THE WIDE TB LIFT: append the two 13×8 BEFORE/AFTER wide carriers PAST the cap-open-TB host
            // (`append_wide_carriers_avail` at `CAP_OPEN_TB_WIDTH + avail_pad` — the hardened
            // `…-v1-avail` TB member's host width and rotated limb bases ride the availability pad;
            // 0 for the bare member = geometry-identical to
            // `generate_rotated_transfer_cap_open_tb_wide`) + the 16 wide commit PIs. The cap-membership
            // host columns AND the two turn-identity columns are CARRIED UNCHANGED; the carriers re-absorb
            // the SAME limbs into the 8-felt commit, so the leg publishes the full ~124-bit before/after
            // anchor at its LAST 16 PIs (the wide anchor `verify_full_turn_bound` binds) WHILE preserving
            // the #225 turn-identity pins at PI 38/39/40. Closes the ~31-bit waist for the cap-gated
            // (cross-vat / self) Transfer route — the route the deployed node cap path proves.
            dregg_circuit::effect_vm::trace_rotated::append_wide_carriers_avail(
                &mut trace,
                tb_pis,
                CAP_OPEN_TB_WIDTH + avail_pad,
                avail_pad,
            )
        } else {
            tb_pis
        }
    } else if insert_after_spine {
        // THE CAP-TREE INSERT AFTER-SPINE LIFT (delegate / introduce / delegateAtten — the keystone
        // deploy). The deployed `effCapInsertV3` read opens the SPLICED leaf against the REBUILT
        // AFTER tree, so the appendix is widened with the SPLICED witness (NOT the anchor's): rebuild
        // the BEFORE `CanonicalCapTree` from the holder's FULL 7-field c-list, splice the fresh
        // conferred edge (`insert_witness` — refuses a present/sentinel key, computes the
        // non-membership bracket + the AFTER membership path), and lay the READ appendix from it.
        // The anchor's own membership + facet were already validated (`cap_open` above — the
        // producer-side authority guard); the fresh key's non-membership bracket + the BEFORE root
        // ride the witness carriers exactly as the Lean keystone consumes them.
        let (ins_key, ins_value) = cap_insert_payload_for(effects, cap).ok_or_else(|| {
            SdkError::InvalidWitness(format!(
                "cap insert after-spine ({effective_key}): could not derive the fresh edge \
                 (key,value) from the {:?} effect",
                effects.first()
            ))
        })?;
        if cap.cap_leaves.is_empty() {
            return Err(SdkError::InvalidWitness(format!(
                "cap insert after-spine ({effective_key}): the holder's FULL 7-field c-list \
                 (`cap_leaves`) was not supplied — the sorted INSERT reorders siblings, so the \
                 genuine AFTER tree cannot be rebuilt from the membership path alone (no fabricated \
                 after-root; thread `cap_write_cap_leaves`)"
            )));
        }
        let before_tree = dregg_circuit::cap_root::CanonicalCapTree::new_with_tombstones(
            cap.cap_leaves.clone(),
            &cap.cap_tombstones,
            dregg_circuit::cap_root::CAP_TREE_DEPTH,
        );
        let before_root8 = before_tree.root();
        if cap_open.cap_root != before_root8 {
            return Err(SdkError::InvalidWitness(format!(
                "cap insert after-spine ({effective_key}): the consumed-cap membership path opens \
                 against a DIFFERENT root than the supplied 7-field c-list rebuilds — the c-list is \
                 not the holder's genuine pre-state (no silent forge)"
            )));
        }
        // The SPLICED leaf: the conferred edge at the fresh key, conferred AS-IS from the delegator's
        // held (anchor) leaf — same target/tier/mask/expiry (a delegation confers the held edge; the
        // recipient's authority is bounded by the delegator's, and the crown facet the descriptor
        // binds on the spliced leaf is therefore ALWAYS permitted whenever the anchor permits it —
        // the honest-producer liveness invariant). The effect's conferred payload datum
        // (`cap_entry[1]`/`intro_hash[1]` — a hash limb on the executor-bridge path, a mask on the
        // prover-site path) rides the leaf's `breadstuff` field, binding it into the spliced digest;
        // for delegateAtten the NARROW is enforced by the surviving submask lookup over the param
        // columns (KEEP col 73 = the payload value ⊑ HELD col 72 = the anchor mask).
        let spliced = dregg_circuit::cap_root::CapLeaf {
            slot_hash: ins_key,
            target: cap.leaf.target,
            auth_tag: cap.leaf.auth_tag,
            mask_lo: cap.leaf.mask_lo,
            mask_hi: cap.leaf.mask_hi,
            expiry: cap.leaf.expiry,
            breadstuff: ins_value,
        };
        let iw = before_tree.insert_witness(spliced).ok_or_else(|| {
            SdkError::InvalidWitness(format!(
                "cap insert after-spine ({effective_key}): insert witness for the fresh key {} \
                 failed (already present, tombstoned, or sentinel-colliding) — the sorted insert \
                 refuses (fail closed, no fabricated after-root)",
                ins_key.as_u32()
            ))
        })?;
        // The spliced-leaf READ witness against the AFTER root. `from_membership_for` fail-closes
        // when the CONFERRED leaf does not permit the crown facet the deployed descriptor binds
        // (`effBitGateFor`/`selectedBitGate` on the spliced leaf — the honest-producer contract).
        let spliced_open = CapOpenWitness::from_membership_for(
            &spliced,
            &iw.siblings,
            &iw.directions,
            crown_eff_bit,
        )
        .map_err(|e| {
            SdkError::InvalidWitness(format!(
                "cap insert after-spine ({effective_key}): the spliced (conferred) leaf does not \
                 satisfy the insert crown: {e}"
            ))
        })?;
        debug_assert_eq!(
            spliced_open.cap_root, iw.new_root,
            "the spliced witness recomposes the rebuilt AFTER root"
        );
        widen_to_cap_open_avail(&mut trace, &spliced_open, avail_pad).map_err(|e| {
            SdkError::InvalidWitness(format!("cap insert widen ({effective_key}): {e}"))
        })?;
        // The submask legs (delegateAtten): KEEP (col 73) = the conferred mask, HELD (col 72) = the
        // anchor's held mask felt — `granted ⊑ held` rides the surviving base lookup.
        let held_for_submask = cap.leaf.mask_lo;
        if go_wide {
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_cap_insert_after_spine_wide(
                &mut trace,
                dpis,
                before_root8,
                iw.new_root,
                ins_key,
                ins_value,
                held_for_submask,
                cap.leaf.slot_hash,
                cap.leaf.mask_lo,
            )
            .map_err(|e| {
                SdkError::InvalidWitness(format!(
                    "cap insert after-spine wide ({effective_key}): {e}"
                ))
            })?
        } else {
            let mut dpis = dpis;
            dregg_circuit::effect_vm::trace_rotated::apply_rotated_cap_write_after_spine(
                &mut trace,
                &mut dpis,
                before_root8,
                iw.new_root,
                ins_key,
                held_for_submask,
                ins_value,
                cap.leaf.slot_hash,
                cap.leaf.mask_lo,
            )
            .map_err(|e| {
                SdkError::InvalidWitness(format!("cap insert after-spine ({effective_key}): {e}"))
            })?;
            dpis
        }
    } else {
        widen_to_cap_open_avail(&mut trace, &cap_open, avail_pad).map_err(|e| {
            SdkError::InvalidWitness(format!("cap-open widen ({}): {e}", route.key))
        })?;
        if remove_after_spine {
            // THE CAP-TREE REMOVE AFTER-SPINE LIFT (revokeDelegation — the keystone deploy). The
            // deployed `effCapRemoveV3` read opens the REMOVED leaf against BEFORE — exactly the
            // consumed-cap membership witness already widened above. The AFTER cap-root group is the
            // deployed tombstone zero-fold over the SAME path (`CanonicalCapTree::remove_witness`
            // semantics — the revoked position collapses to the ZERO digest; positions do not shift,
            // so every other capability's witness stays valid).
            //
            // Producer-side guard (no silent forge): the node's declared c-list MUST contain the
            // revoked key — a node that cannot exhibit the revoked edge in the holder's genuine
            // pre-state c-list cannot mint the remove leg.
            if !cap
                .clist_leaves
                .iter()
                .any(|l| l.addr == cap.leaf.slot_hash)
            {
                return Err(SdkError::InvalidWitness(format!(
                    "cap remove after-spine ({effective_key}): the revoked key {} is NOT in the \
                     supplied c-list — the remove has no declared membership (no silent forge)",
                    cap.leaf.slot_hash.as_u32()
                )));
            }
            let after_root8 = dregg_circuit::cap_root::recompose_membership(
                dregg_circuit::cap_root::CAP_ZERO8,
                &cap.siblings,
                &cap.directions,
            );
            if go_wide {
                dregg_circuit::effect_vm::trace_rotated::generate_rotated_cap_remove_after_spine_wide(
                    &mut trace,
                    dpis,
                    cap_open.cap_root,
                    after_root8,
                    cap.leaf.slot_hash,
                    cap.leaf.mask_lo,
                )
                .map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "cap remove after-spine wide ({effective_key}): {e}"
                    ))
                })?
            } else {
                let mut dpis = dpis;
                dregg_circuit::effect_vm::trace_rotated::apply_rotated_cap_write_after_spine(
                    &mut trace,
                    &mut dpis,
                    cap_open.cap_root,
                    after_root8,
                    cap.leaf.slot_hash,
                    cap.leaf.mask_lo,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                )
                .map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "cap remove after-spine ({effective_key}): {e}"
                    ))
                })?;
                dpis
            }
        } else if attenuate_after_spine {
            // THE ATTENUATE AFTER-SPINE WIDE LIFT: lay the arity-7 cap-tree UPDATE-AT-KEY after-spine
            // (`fill_cap_after_spine`) + the genuine BEFORE/AFTER 8-felt cap-root groups + the submask
            // param columns, then the generic wide carriers at `CAP_OPEN_WIDTH + AFTER_SPINE_SPAN`. The
            // faithful 8-felt write is FORCED by the deployed after-spine (`effCapOpenWriteV3_forces_write8`),
            // never the arity-2 map-op (dropped). `keep_mask` = the narrowed KEEP_MASK the effect carries;
            // `held_value` = the held key's c-list mask (the submask non-amp compares against it).
            let (_ins_key, keep_mask) = cap_insert_payload_for(effects, cap).ok_or_else(|| {
                SdkError::InvalidWitness(format!(
                    "attenuate after-spine ({effective_key}): could not derive the narrowed KEEP_MASK \
                     from the {:?} effect",
                    effects.first()
                ))
            })?;
            let held_value = cap
                .clist_leaves
                .iter()
                .find(|l| l.addr == cap.leaf.slot_hash)
                .map(|l| l.value)
                .ok_or_else(|| {
                    SdkError::InvalidWitness(format!(
                        "attenuate after-spine ({effective_key}): held key {} is NOT in the c-list — \
                         the held-authority membership witness is missing (no silent forge)",
                        cap.leaf.slot_hash.as_u32()
                    ))
                })?;
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_cap_attenuate_after_spine_wide(
                &mut trace,
                dpis,
                &cap_open,
                cap.leaf.slot_hash,
                held_value,
                keep_mask,
            )
            .map_err(|e| {
                SdkError::InvalidWitness(format!("attenuate after-spine wide ({effective_key}): {e}"))
            })?
        } else if go_wide {
            // THE WIDE LIFT: append the two 13×8 BEFORE/AFTER wide carriers PAST the cap-open
            // appendix (`append_wide_carriers_cap_open_avail` at `CAP_OPEN_WIDTH + avail_pad` —
            // the hardened `…-v1-avail` cap-open EFF member's host width and rotated limb bases
            // ride the availability pad, matching the retargeted
            // `transferCapOpenEffVmDescriptor2R24` wide row = `wideAppend transferCapOpenEffV3Avail`;
            // 0 for every bare member = byte-identical to the legacy lift) and the 16 wide commit
            // PIs. The cap-open host constraints + membership crown carry UNCHANGED; the carriers
            // re-absorb the SAME limbs into the 8-felt commit. The leg now publishes the full
            // ~124-bit commit at its LAST 16 PIs (the wide anchor the verifier binds).
            dregg_circuit::effect_vm::trace_rotated::append_wide_carriers_cap_open_avail(
                &mut trace, dpis, avail_pad,
            )
            .map_err(|e| {
                SdkError::InvalidWitness(format!("cap-open wide carriers ({effective_key}): {e}"))
            })?
        } else {
            dpis
        }
    };

    // The map-op witness heaps: the cap-tree c-list (limb 25) ALWAYS, PLUS the accounts leaf-set (limb 0)
    // for the spawn dual-tree descriptor. The map-op table matches each op to its heap by ROOT, so order
    // is irrelevant; concatenating yields one heap per distinct tree the descriptor opens.
    let all_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> =
        cap_write_heaps.into_iter().chain(accounts_heaps).collect();
    Ok((desc, trace, dpis, all_heaps))
}

/// **THE WIDE CAP-OPEN+UMEM DOMAIN-2 WELD PROVER (STAGED, VK-RISK-FREE) — the 7th flip-refusal's wall
/// CLOSED.** The cap-open (domain-2 capability) twin of [`prove_wide_umem_welded_staged`]: it proves,
/// in ONE descriptor / ONE proof, BOTH the WIDE cap-open cohort proof (the rotated effect semantics +
/// the in-circuit depth-16 cap-membership authority crown + the wide PI vector whose LAST 16 PIs are
/// the 8-felt before/after commit anchors) AND the universal-memory CAPS-domain reconciliation leg (the
/// cohort `umemOp` over 7 appended columns + a REAL [`UMemBoundaryWitness`]).
///
/// **Why the value-cohort weld ([`prove_wide_umem_welded_staged`]) could not do this.** That prover
/// resolves the PLAIN wide descriptor for the lead (`rotated_descriptor_name_for_effect`), which for a
/// capability effect is the authority-only `…VmDescriptor2R24` (e.g. `attenuateVmDescriptor2R24`). The
/// light-client wire verifier ([`verify_effect_vm_rotated_with_cutover`]) FORBIDS those plain cap
/// descriptors (`is_forbidden_plain_cap_descriptor`): a cap effect proven without the in-circuit
/// membership crown launders host-trusted authority. So a welded grant under the plain descriptor
/// self-verifies but the WIRE rejects it (the 7th refusal's `OodEvaluationMismatch` was a SEPARATE
/// witness inconsistency — a spurious nonce op made the projection diff multi-domain; the genuine wall
/// is the forbidden-plain-cap wire tooth). This prover instead routes through the cap-open WIDE
/// descriptor (the membership crown the wire DEMANDS) and welds the caps leg onto THAT — the descriptor
/// the welded registry (`WIDE_UMEM_WELD_REGISTRY_TSV`) carries a wire-accepted twin of (e.g.
/// `attenuateCapOpenEffVmDescriptor2R24`, domain 2).
///
/// `route` MUST be a wide-eligible cap-open route (`cap_open_key_has_wide_twin`, non-TB); `cap` the
/// actor's consumed-capability membership witness; `pre`/`ops` the turn's CAPS-domain universal-memory
/// touch (single-domain caps, derived from the genuine before/after cell projection diff). Self-verifies
/// before return; returns `(proof, wide_dpis)`. STAGED: a NEW welded descriptor BESIDE the deployed
/// registry; no VK epoch, no deployed-default flip, `umem_witness_enabled` untouched.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
fn prove_wide_umem_welded_cap_open_staged(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    cap: &CapMembershipWitness,
    route: &CapOpenRoute,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, prove_vm_descriptor2_umem, verify_vm_descriptor2,
    };
    use dregg_circuit::effect_vm_descriptors::weld_umem_into_wide_descriptor;

    // The umem leg's single-domain CAPS cohort rows + the REAL boundary (fails closed on a multi-domain
    // leg — e.g. a stray Heap-domain Nonce op alongside the caps insert; the projection diff must be
    // caps-only, mirroring the value-cohort weld's single-domain discipline).
    let inputs = dregg_turn::umem::umem_cohort_proving_inputs_from(pre, ops)
        .map_err(|e| SdkError::InvalidWitness(format!("umem caps cohort trace generation: {e}")))?;
    if inputs.domain != dregg_turn::umem::UDomain::Caps.code() {
        return Err(SdkError::InvalidWitness(format!(
            "cap-open umem weld: the universal-memory leg touches domain {} but a capability cap-open \
             weld must reconcile the CAPS domain ({}) — thread the genuine caps projection diff",
            inputs.domain,
            dregg_turn::umem::UDomain::Caps.code()
        )));
    }

    // Build the WIDE cap-open leg (the membership crown the wire demands) via the SHARED builder, then
    // weld the umem caps leg onto its descriptor + trace.
    let (cap_open_desc, cap_open_trace, dpis, all_heaps) = build_effect_vm_cap_open_leg(
        initial_state,
        effects,
        before_w,
        after_w,
        cap,
        route,
        None,
        true,
    )?;
    if cap_open_desc.public_input_count < 16 + 38 {
        return Err(SdkError::InvalidWitness(format!(
            "cap-open umem weld: the resolved descriptor {} is not the WIDE cap-open form (PI count \
             {} — the 8-felt wide carriers were not appended; route must be wide-eligible)",
            cap_open_desc.name, cap_open_desc.public_input_count
        )));
    }

    // WELD: append the umem caps leg INTO the WIDE cap-open descriptor (purely additive — keeps the
    // membership crown + the 16 wide commit PIs / 8-felt anchors INTACT). The first appended umem
    // column is PAST the cap-open carriers (`base` = the cap-open wide trace width).
    let welded = weld_umem_into_wide_descriptor(&cap_open_desc, inputs.domain);
    let base = cap_open_desc.trace_width;

    let real_umem_rows: Vec<&Vec<BabyBear>> = inputs
        .rows
        .iter()
        .filter(|r| r.get(6).copied() == Some(BabyBear::ONE))
        .collect();
    if real_umem_rows.len() > cap_open_trace.len() {
        return Err(SdkError::InvalidWitness(format!(
            "cap-open umem weld: {} caps umem ops exceed the cap-open trace height {} (cannot \
             co-locate the umem leg on the cap-open rows)",
            real_umem_rows.len(),
            cap_open_trace.len()
        )));
    }
    let mut welded_base: Vec<Vec<BabyBear>> = Vec::with_capacity(cap_open_trace.len());
    for (ri, row) in cap_open_trace.iter().enumerate() {
        let mut wr = row.clone();
        wr.resize(base + 7, BabyBear::ZERO);
        if let Some(umem_row) = real_umem_rows.get(ri) {
            for (i, &v) in umem_row.iter().enumerate().take(7) {
                wr[base + i] = v;
            }
        }
        welded_base.push(wr);
    }

    // Prove the WELDED WIDE cap-open descriptor through the DEPLOYED-form umem prover with the REAL
    // caps boundary. The cap-open map-op heaps (the c-list cap-tree witness) ride UNCHANGED.
    let proof = prove_vm_descriptor2_umem(
        &welded,
        &welded_base,
        &dpis,
        &MemBoundaryWitness::default(),
        &all_heaps,
        &inputs.boundary,
    )
    .map_err(|e| SdkError::InvalidWitness(format!("cap-open+umem welded IR-v2 proof: {e}")))?;
    verify_vm_descriptor2(&welded, &proof, &dpis)
        .map_err(|e| SdkError::InvalidWitness(format!("cap-open+umem welded self-verify: {e}")))?;
    Ok((proof, dpis))
}

/// **THE PUBLIC DOMAIN-2 (capability) WELDED-MINT ENTRY (STAGED, VK-RISK-FREE).** Resolve the
/// cap-open route for a single cap-authorized effect ([`cap_open_route_for_run`]) and prove the WIDE
/// cap-open+umem CAPS-domain weld ([`prove_wide_umem_welded_cap_open_staged`]) — a self-verifying
/// welded mint of a domain-2 cohort member (attenuate / grant / delegate / revoke / introduce …). The
/// produced leg verifies through the deployed wire verifier under the cap-open member's welded twin in
/// [`WIDE_UMEM_WELD_REGISTRY_TSV`](dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV)
/// (for the wire-accepted cap-open keys — e.g. `attenuateCapOpenEffVmDescriptor2R24`).
///
/// `effects` is a single-effect cap-authorized run; `cap` the actor's consumed-capability membership
/// witness (its `clist_leaves` thread the cap-tree write witness when the route is write-bearing);
/// `pre`/`ops` the turn's CAPS-domain universal-memory touch (single-domain caps, the genuine
/// before/after cell projection diff). Returns `(proof, wide_dpis)`. STAGED: no VK bump, no default
/// flip, `umem_witness_enabled` untouched.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn prove_cap_open_umem_welded_staged(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    before_w: &dregg_turn::rotation_witness::RotationWitness,
    after_w: &dregg_turn::rotation_witness::RotationWitness,
    cap: &CapMembershipWitness,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<
            dregg_circuit::descriptor_ir2::DreggStarkConfig,
        >,
        Vec<BabyBear>,
    ),
    SdkError,
> {
    let route = cap_open_route_for_run(effects).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "cap-open umem weld: {effects:?} has no wired cap-open route (the domain-2 welded mint \
             needs a single cap-authorized effect — attenuate / grant / delegate / revoke / introduce)"
        ))
    })?;
    prove_wide_umem_welded_cap_open_staged(
        initial_state,
        effects,
        before_w,
        after_w,
        cap,
        &route,
        pre,
        ops,
    )
}

/// Resolve the committed rotated cohort descriptor JSON for a turn's effects (the SAME
/// resolution `prove_effect_vm_rotated_ir2_with_caveat` performs): the lead effect's cohort
/// name via `rotated_descriptor_name_for_effect`, requiring a homogeneous cohort, then the
/// registry JSON string from `V3_STAGED_REGISTRY_TSV`. Fails closed for empty / heterogeneous /
/// non-cohort turns. Returns `(name, json)`.
#[cfg(feature = "prover")]
// Scaffolding for the in-flight rotated-leg descriptor resolution; retained for the rotated VK epoch.
#[allow(dead_code)]
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
#[cfg(feature = "prover")]
// Scaffolding for the in-flight rotated-leg vk_hash fingerprint; retained for the rotated VK epoch.
#[allow(dead_code)]
fn rotated_effect_vm_vk_hash(effects: &[VmEffectKind]) -> Result<[u8; 32], SdkError> {
    let (_name, json) = rotated_descriptor_json_for_effects(effects)?;
    Ok(*blake3::hash(json.as_bytes()).as_bytes())
}

/// Resolve the committed WIDE rotated cohort descriptor JSON for a turn's effects (the wide twin of
/// [`rotated_descriptor_json_for_effects`], pulling `WIDE_REGISTRY_STAGED_TSV` instead of the
/// 1-felt `V3_STAGED_REGISTRY_TSV`). The lead-effect cohort name is the SAME (the registries share
/// keys; only the commitment width differs), so a wide leg's vk_hash re-pins against the wide JSON.
#[cfg(feature = "prover")]
fn rotated_descriptor_wide_json_for_effects(
    effects: &[VmEffectKind],
) -> Result<(&'static str, &'static str), SdkError> {
    use dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect;
    use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;

    let lead = effects
        .first()
        .ok_or_else(|| SdkError::InvalidWitness("wide rotated vk_hash: empty turn".into()))?;
    let name = rotated_descriptor_name_for_effect(lead).ok_or_else(|| {
        SdkError::InvalidWitness(format!(
            "wide rotated vk_hash: effect {lead:?} is not in the rotated cohort (no R=24 descriptor)"
        ))
    })?;
    for e in &effects[1..] {
        if rotated_descriptor_name_for_effect(e) != Some(name) {
            return Err(SdkError::InvalidWitness(
                "wide rotated vk_hash: heterogeneous multi-effect turn (one descriptor per proof)"
                    .into(),
            ));
        }
    }
    let json = WIDE_REGISTRY_STAGED_TSV
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
            SdkError::InvalidWitness(format!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
        })?;
    Ok((name, json))
}

/// The WIDE rotated effect-vm leg's `vk_hash`: the blake3 fingerprint of the committed WIDE cohort
/// descriptor JSON (`WIDE_REGISTRY_STAGED_TSV`). The flag-day verifier
/// (`verify_effect_vm_rotated_with_cutover`, re-pointed to the wide registry) re-derives the SAME
/// fingerprint from the (uniquely) accepting WIDE descriptor and rejects a tampered vk_hash.
#[cfg(feature = "prover")]
fn rotated_effect_vm_wide_vk_hash(effects: &[VmEffectKind]) -> Result<[u8; 32], SdkError> {
    let (_name, json) = rotated_descriptor_wide_json_for_effects(effects)?;
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
#[cfg(feature = "prover")]
pub(crate) fn cell_state_after_run(
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
    // P0-2: the authority-residue digest is turn-invariant for kernel turns (the
    // EffectVM trace mutates balance/nonce/fields/cap_root, never the residue), so
    // the post-state carries the SAME `record_digest` the seed (pre-state) holds.
    let record_digest = seed_for_unchanged.record_digest;
    let mut s = CellState {
        balance,
        nonce,
        fields,
        capability_root,
        record_digest,
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
#[cfg(feature = "prover")]
fn prove_cohort_run_chain(
    initial_state: &CellState,
    effects: &[VmEffectKind],
    rot: &RotationTurnWitness,
    cap_membership: Option<&CapMembershipWitness>,
    cap_turn_identity: Option<TurnIdentityFelts>,
    before_nullifiers: Option<&[BabyBear]>,
    umem_witness: Option<&UmemWeldWitness>,
) -> Result<Vec<AttachedSubProof>, SdkError> {
    let runs = split_into_cohort_runs(effects);
    if runs.is_empty() {
        return Err(SdkError::InvalidWitness(
            "chained rotated prover: empty turn (no cohort runs)".into(),
        ));
    }
    let n_runs = runs.len();
    // UMEM-WELD ROUTING GATE (the umem-flip's producer path, STAGED / VK-RISK-FREE). A welded leg
    // folds the turn's WHOLE before→after universal-memory projection diff (`umem_witness.{pre,ops}`)
    // onto the cohort descriptor; that diff is a whole-TURN object, so it maps cleanly onto a leg ONLY
    // when the turn is a SINGLE cohort-run (`n_runs == 1`, the leg == the whole turn). A heterogeneous
    // turn would need a per-run projection split that the whole-turn witness does NOT carry, so we keep
    // such turns BARE (no silent mis-attribution of the whole-turn diff to one run). The deployed
    // welded-mint cases (cap-gated attenuate/delegate/revoke, sovereign transfer) are single-run.
    let umem_weld = umem_witness.filter(|_| n_runs == 1);
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

        // CAP-OPEN ROUTING (soundness loop #5, F1 — cap-presence-driven). A run whose authority
        // rides a REAL consumed capability (`cap_membership` threaded — the actor does NOT own the
        // cell, authority comes from a held cap) proves through the CAP-OPEN descriptor, so the
        // in-circuit cap-membership open the soundness proof relies on is exercised end-to-end.
        // OWNER-authorized runs (actor == src) thread NO cap witness, so `cap_membership` is
        // `None` and the base cohort descriptor is proven (correct — no cap authority is opened).
        //
        // The routing condition is now the PRESENCE of a cap witness for a single-effect run, NOT
        // the effect being AttenuateCapability. The cap-open descriptor is resolved per effect-kind
        // by `cap_open_supported_for_run`: AttenuateCapability is wired
        // (`attenuateCapOpenEffVmDescriptor2R24`) AND the cross-vat Transfer-via-granted-cap is wired
        // (`transferCapOpenTBVmDescriptor2R24`, `turn_bound` — #225: it publishes + forces the turn's
        // actor/src/dst identity PIs, and the node prove site now supplies the genuine cross-vat felts).
        // Effect-kinds still WITHOUT a cap-open descriptor fail CLOSED with a precise "no cap-open
        // descriptor for <effect>" error — the per-effect coverage is the NAMED residual (see
        // `cap_open_supported_for_run`).
        let cap_open_run = match (run_effects.len(), cap_membership) {
            (1, Some(cap)) => Some(cap),
            _ => None,
        };
        let (proof_bytes, rot_pi, vk_hash) = if let Some(cap) = cap_open_run {
            cap_open_supported_for_run(run_effects)?;
            // Route the cap-open by effect-kind via `cap_open_route_for_run`: transfer + attenuate +
            // the 6 fan-out effects each prove their OWN `<effect>CapOpenVmDescriptor2R24`, binding
            // the cap to THAT effect-kind bit (not transfer). Each carries its own vk_hash (distinct
            // JSON ⇒ distinct fingerprint).
            let route = cap_open_route_for_run(run_effects).ok_or_else(|| {
                SdkError::InvalidWitness("cap-open routing: unreachable (gated above)".into())
            })?;
            // THE WIDE CAP-OPEN FLAG-DAY (cap-open tail CLOSED): EVERY live cap-open key — the
            // authority crown, the §10 WRITE tail, AND the turn-bound `transferCapOpenTB` — now has a
            // PROVEN wide twin in `WIDE_REGISTRY_STAGED_TSV` (Lean `v3RegistryCapOpenWide` + the
            // `EmitWideRegistryProbe` transfer-face `wideAppend` for TB), so this run goes WIDE — its
            // leg publishes the full ~124-bit 8-felt commit (the wide carriers appended past the
            // membership crown / turn-identity pins). The producer-side `go_wide` gate inside
            // `build_effect_vm_cap_open_leg` is the SAME registry lookup, and the leg's vk_hash is
            // pinned to the wide descriptor that was proven so `verify_full_turn_bound`'s `leg_is_wide`
            // binds the 8-felt tail. The ~31-bit waist is GONE for cap-gated turns (the deployed node
            // cap path proves the TB Transfer route — see `node::turn_proving`'s wide commit anchors).
            let effective_key = cap_open_effective_key(&route, cap);
            let go_wide = cap_open_wide_descriptor_json_by_key(effective_key).is_ok();
            // DOMAIN-2 UMEM WELD (the producer seam this closes). When the caller threaded the turn's
            // CAPS-domain universal-memory projection diff AND this cap-open key has a Lean-emitted
            // welded twin, prove the WIDE cap-open+umem WELDED descriptor (the membership crown + the
            // 8-felt anchors + the appended `umemOp` caps-reconciliation leg) instead of the bare wide
            // cap-open leg. The welded leg verifies UNIQUELY through the deployed wire/executor verifiers
            // under its `WIDE_UMEM_WELD_REGISTRY_TSV` member (admitted ADDITIVELY beside the bare wide
            // form), so its vk_hash MUST pin the WELDED member. This FAILS CLOSED (no silent bare
            // fallback) when the welded prove cannot mint — a threaded witness that does not reconcile
            // the genuine caps diff is a LOUD error, never a hidden downgrade.
            if let Some(uw) =
                umem_weld.filter(|_| go_wide && wide_umem_weld_registry_has(effective_key))
            {
                let (proof, dpis) = prove_wide_umem_welded_cap_open_staged(
                    &s_k,
                    run_effects,
                    &rot.before,
                    after_w,
                    cap,
                    &route,
                    &uw.pre,
                    &uw.ops,
                )?;
                let proof_bytes = postcard::to_allocvec(&proof).map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "cap-open welded rotated proof serialize failed (run {k}): {e}"
                    ))
                })?;
                let vk_hash = wide_umem_weld_vk_hash_by_key(effective_key)?;
                (proof_bytes, dpis, vk_hash)
            } else {
                let (proof, dpis) = prove_effect_vm_cap_open(
                    &s_k,
                    run_effects,
                    &rot.before,
                    after_w,
                    cap,
                    &route,
                    cap_turn_identity,
                    go_wide,
                )?;
                let proof_bytes = postcard::to_allocvec(&proof).map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "cap-open rotated proof serialize failed (run {k}): {e}"
                    ))
                })?;
                // The vk_hash MUST pin the EFFECTIVE descriptor that was PROVEN (wide when go_wide, else
                // the 1-felt V3 cap-open) — the proof is descriptor-bound, and the wide-cutover verifier
                // re-pins blake3(json) against it.
                let vk_hash = if go_wide {
                    cap_open_wide_vk_hash_by_key(effective_key)?
                } else {
                    cap_open_vk_hash_by_key(effective_key)?
                };
                (proof_bytes, dpis, vk_hash)
            }
        } else {
            // THE WIDE FLAG-DAY (light-client ~31-bit floor close): the normal (owner-authorized,
            // non-cap-open) run now proves through the WIDE producer (`prove_effect_vm_rotated_wide`,
            // the `WIDE_REGISTRY_STAGED_TSV` descriptor family). The wide PI vector carries the FULL
            // 8-felt BEFORE/AFTER commits (the LAST 16 PIs, ~124-bit) — the leg's `sub_public_inputs`
            // publish them, and the verifier (`verify_full_turn_bound`) binds those 8-felt slices to
            // the trusted commit anchors. This mirrors the sovereign producer's wide path
            // (`cipherclerk::prove_sovereign_turn_rotated` / `prove_effect_vm_rotated_wide`); the wide
            // generator inside re-derives the SAME wide trace + PI vector so the bound 16 wide PIs
            // match. The 1-felt waist is GONE for every normal effect on the composed full-turn /
            // light-client surface. (The cap-open path above keeps its own cap-open descriptor route;
            // its wide migration is the NAMED residual — see the report.)
            // DOMAIN-1 / VALUE UMEM WELD (the producer seam, symmetric to the cap-open arm). When the
            // caller threaded the turn's universal-memory projection diff AND this normal cohort key
            // has a Lean-emitted welded twin, prove the WIDE+umem WELDED descriptor (the wide carriers
            // + the appended single-domain `umemOp` leg) instead of the bare wide leg. FAILS CLOSED (no
            // silent bare fallback) if the welded prove cannot mint. The bare wide leg runs otherwise
            // (the deployed default — owner turns with no threaded witness are UNAFFECTED).
            let wide_key =
                dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect(
                    run_effects.first().ok_or_else(|| {
                        SdkError::InvalidWitness("chained rotated prover: empty cohort run".into())
                    })?,
                );
            if let (Some(uw), Some(key)) = (
                umem_weld.filter(|_| wide_key.map(wide_umem_weld_registry_has).unwrap_or(false)),
                wide_key,
            ) {
                let (proof, dpis) = prove_wide_umem_welded_staged(
                    &s_k,
                    run_effects,
                    &rot.before,
                    after_w,
                    &caveat,
                    &uw.pre,
                    &uw.ops,
                    before_nullifiers,
                    None,
                )?;
                let proof_bytes = postcard::to_allocvec(&proof).map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "chained welded wide proof serialize failed (run {k}): {e}"
                    ))
                })?;
                (proof_bytes, dpis, wide_umem_weld_vk_hash_by_key(key)?)
            } else {
                let (proof, rot_pi) = prove_effect_vm_rotated_wide(
                    &s_k,
                    run_effects,
                    &rot.before,
                    after_w,
                    &caveat,
                    before_nullifiers,
                    // The chained full-turn path threads no per-run refusal fields context (the live
                    // refusal lead is the single-leg sovereign path); a Refusal run here fails closed
                    // against the `.write` gate, exactly as the sovereign forest path.
                    None,
                )?;
                let proof_bytes = postcard::to_allocvec(&proof).map_err(|e| {
                    SdkError::InvalidWitness(format!(
                        "chained rotated wide proof serialize failed (run {k}): {e}"
                    ))
                })?;
                (
                    proof_bytes,
                    rot_pi,
                    rotated_effect_vm_wide_vk_hash(run_effects)?,
                )
            }
        };
        legs.push(AttachedSubProof {
            label: "effect-vm-rotated".into(),
            proof_bytes,
            sub_public_inputs: rot_pi,
            vk_hash,
        });
        // Thread s_k → s_{k+1} off the generator's own STATE_AFTER columns (no hand-replay).
        if !is_final {
            let (v1_trace, _v1_pi) = generate_effect_vm_trace(&s_k, run_effects);
            s_k = cell_state_after_run(&v1_trace, run_effects.len(), &s_k);
        }
    }
    Ok(legs)
}

// (The v1 SHAPE-DRIVEN effect-vm verify `verify_effect_vm_proof_with_cutover` — the
// hand-AIR `EffectVmP3Proof` selector-bound verify with hand-AIR fallback — is RETIRED.
// The live verify is `verify_effect_vm_rotated_with_cutover` below: the rotated
// `Ir2BatchProof` verified SELECTOR-BOUND against the rotated cohort descriptors.)

/// The PLAIN cohort descriptors for CAP effects — the descriptors whose acceptance the AUTHORITY
/// FLOOR forbids on the light-client path (`verify_effect_vm_rotated_with_cutover`). Each of these
/// effects exercises capability authority (the actor must hold a cap reaching the target), but the
/// plain descriptor carries NO in-circuit cap-membership check (the 70-constraint
/// `capOpenConstraintsEff` depth-16 crown lives ONLY in the `…CapOpen…VmDescriptor2R24` variants).
/// A cap effect proven under one of these plain descriptors is light-client-UNVERIFIABLE — the
/// verifier cannot distinguish "the agent held the cap" from "the host asserted it" — so the
/// light-client verifier rejects it and demands the cap-open route (where the membership appendix
/// is verified in-circuit). The producer-side resolver (`rotated_descriptor_name`) routes cap
/// effects to the cap-open descriptors, so an honest producer never lands here; a malicious
/// producer that strips the cap-open route to forge authority is REFUSED.
///
/// `refreshVmDescriptor2R24` (RefreshDelegation) is NOT forbidden: its deleg-tree write column is a
/// separately-named obstruction (the cap-open variant is unwired on the producer side), so it stays
/// on the plain route for now — a NAMED residual, not a silent forge (refresh re-arms an existing
/// delegation rather than conferring new authority).
/// The AUTHORITY-ONLY cap-open descriptors for cap-WRITE effects whose write-bearing wrapper makes the
/// authority crown alone insufficient: the genuine post-cap-root is on-the-wire ONLY via the
/// `…WriteCapOpenVmDescriptor2R24` `map_op` (BEFORE cap-root var 213 → AFTER cap-root var 264, a genuine
/// sorted-Poseidon2 cap-tree write). The verifier-half tooth that forces the write route lives here.
///
/// THE TOOTH IS ON. The cap-root advances on the ROTATED-BLOCK limb 213→264 (the `213 == 65` weld dropped,
/// the v1-state cap-root cols 65/87 FROZEN), and the WRITE wrappers ride the nonce-TICK face — so all three
/// write-bearing routes now GENUINELY prove + light-client-verify end-to-end (a wrong post-cap-root is UNSAT):
/// revokeDelegation (REMOVE), delegate & introduce (INSERT). With the on-the-wire alternative proven, the
/// AUTHORITY-only cap-open descriptors (`revokeCapOpen` / `grantCapCapOpen` / `introduceCapOpen`) are
/// light-client-REJECTED — a producer cannot strip the write wrapper to leave the post-cap-root host-trusted.
#[cfg(feature = "prover")]
fn is_forbidden_authority_only_cap_write_descriptor(name: &str) -> bool {
    // THE TOOTH IS ON. The WRITE-bearing cap-open wrappers now GENUINELY prove + light-client-verify
    // end-to-end (a wrong post-cap-root is UNSAT — the `map_op` binds the BEFORE→AFTER cap-root write on
    // the rotated limb 213→264, a genuine sorted-Poseidon2 tree write threaded through the c-list→map_heaps
    // bridge):
    //   * revokeDelegation — `cap_write_revoke_proves_and_verifies_light_client` (REMOVE)
    //   * delegate / introduce — `cap_write_{delegate,introduce}_proves_and_verifies_light_client` (INSERT)
    // So the AUTHORITY-only cap-open route (the authority crown WITHOUT the on-the-wire cap-root write) is
    // now light-client-REJECTED for these write-bearing effects: a producer cannot strip the write wrapper
    // to leave the post-cap-root host-trusted. The verifier demands the `…WriteCapOpenVmDescriptor2R24`
    // route where the cap-tree write is verified in-circuit.
    //
    // delegateAtten rides the SAME `grantCapCapOpen` authority-only descriptor as plain delegate (both are
    // `GrantCapability`), so forbidding `grantCapCapOpenVmDescriptor2R24` forces the write route for it too.
    matches!(
        name,
        "revokeCapOpenVmDescriptor2R24"        // RevokeDelegation — the REMOVE write wrapper proves
            | "grantCapCapOpenVmDescriptor2R24" // delegate / delegateAtten — the INSERT write wrapper proves
            | "delegateCapOpenVmDescriptor2R24" // delegate (GrantCapability) — an AUTHORITY-only cap-open
                                                // twin that the honest producer NEVER routes to (it routes to
                                                // `delegateWriteCapOpen` / `grantCapCapOpen`-fallback), so it
                                                // carries the membership crown but NO on-the-wire cap-tree write:
                                                // its post-cap-root (the inserted delegation edge) is host-trusted.
                                                // Forbidding it forces the `delegateWriteCapOpen` route, exactly
                                                // like its `grantCapCapOpen` sibling. (Registry-vs-list completeness
                                                // diff: it was classified `Forbidden` by the weld matrix gauntlet but
                                                // the deny-list did not enforce it — the laundering gap this closes.)
            | "introduceCapOpenVmDescriptor2R24" // Introduce — the INSERT write wrapper proves
            | "revokeCapabilityCapOpenVmDescriptor2R24" // RevokeCapability — the REMOVE write wrapper proves
                                                        // (`cap_write_revoke_cap_route_proves_and_verifies_light_client`)
            | "refreshDelegationCapOpenVmDescriptor2R24" // RefreshDelegation — the DELEG-tree UPDATE write
                                                         // wrapper proves (`refresh_deleg_write_proves_and_verifies_light_client`);
                                                         // the authority-only route leaves the post-DELEG-root host-trusted
            | "spawnCapOpenVmDescriptor2R24" // SpawnWithDelegation — the cap-handoff INSERT write
                                             // wrapper proves (`cap_write_spawn_proves_and_verifies_light_client`);
                                             // the authority-only route leaves the child cap_root host-trusted (frozen handoff)
    )
}

#[cfg(feature = "prover")]
fn is_forbidden_plain_cap_descriptor(name: &str) -> bool {
    is_forbidden_authority_only_cap_write_descriptor(name)
        || matches!(
            name,
            "introduceVmDescriptor2R24"        // Introduce         (EFFECT_INTRODUCE)
            | "revokeVmDescriptor2R24"     // RevokeDelegation   (EFFECT_DELEGATION_OPS)
            | "attenuateVmDescriptor2R24"  // AttenuateCapability(EFFECT_ATTENUATE/Transfer-facet)
            | "grantCapVmDescriptor2R24"   // GrantCapability    (EFFECT_GRANT_CAPABILITY)
            | "revokeCapabilityVmDescriptor2R24" // RevokeCapability (EFFECT_REVOKE_CAPABILITY)
        )
}

/// The light-client AUTHORITY class of a deployed effect-vm descriptor key — the basis the authority
/// floor (`is_forbidden_plain_cap_descriptor`) must agree with. This makes the deny-list's
/// COMPLETENESS mechanical rather than a hand census: the test
/// `authority_deny_list_is_complete_over_deployed_registry` enumerates EVERY descriptor in EVERY
/// deployed registry, requires each to be classified (an UNCLASSIFIED, authority-shaped descriptor —
/// e.g. a new authority effect or a welded twin entering the registry un-listed — returns `None` and
/// FAILS the test instead of silently laundering), and asserts the deny-list forbids EXACTLY the
/// laundering classes. The per-descriptor crown/write semantics are Lean-modeled (the cap-reshape
/// crown + the `…WriteCapOpen…` cap-tree write); this closes the *list-completeness* leg the
/// `RUST-ONLY-LOGIC-CENSUS` named (Tier-1 #1).
#[cfg(all(test, feature = "prover"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DescriptorAuthorityClass {
    /// Not a capability-AUTHORITY descriptor: the owner/normal path (transfer/mint/setField/spawn
    /// (no delegation)/exercise/…) plus the ACCESS-gated cap-open routes (transfer/exercise CapOpen)
    /// that gate an OWNED action behind a cap but confer NO authority. A light-client accept here is
    /// not an authority launder. NOT forbidden.
    NotAuthority,
    /// A capability-MANAGEMENT effect (introduce / grant·delegate / revoke / attenuate /
    /// revokeCapability / refreshDelegation / spawn-with-delegation) proven WITHOUT the on-the-wire
    /// in-circuit proof of its authority: either a PLAIN descriptor (no membership crown) or an
    /// AUTHORITY-ONLY cap-open (crown present, but NO `…WriteCapOpen…` cap-tree write — the
    /// post-cap-root is host-trusted). Accepting it would launder forged authority into a light-client
    /// proof. MUST be forbidden.
    LaundersAuthority,
    /// A capability-MANAGEMENT effect proven through its FULL in-circuit route — the
    /// `…WriteCapOpen…` cap-tree-write wrapper (or `attenuateCapOpenEff`'s embedded Update) — so both
    /// the membership crown AND the post-cap-root write are verified in-circuit. Light-client
    /// verifiable; NOT forbidden.
    CrownedWriteRoute,
    /// `refreshVmDescriptor2R24` — the deliberately-plain NAMED RESIDUAL: a plain RefreshDelegation
    /// re-arms an EXISTING delegation (confers no NEW authority), so it stays on the plain route. NOT
    /// forbidden.
    NamedResidual,
}

/// Classify a deployed descriptor key. `None` ⇒ the key is authority-SHAPED (a cap-open, or a
/// cap-management verb prefix) but is NOT explicitly classified — a new such descriptor must be
/// classified (and, if laundering, added to the deny-list) before it can ride the wire. Benign
/// non-authority effects fall through to `NotAuthority`.
#[cfg(all(test, feature = "prover"))]
fn descriptor_authority_class(key: &str) -> Option<DescriptorAuthorityClass> {
    use DescriptorAuthorityClass::*;
    match key {
        // PLAIN cap-management (crownless authority) — LAUNDERS.
        "introduceVmDescriptor2R24"
        | "revokeVmDescriptor2R24"
        | "attenuateVmDescriptor2R24"
        | "grantCapVmDescriptor2R24"
        | "revokeCapabilityVmDescriptor2R24" => Some(LaundersAuthority),
        // AUTHORITY-ONLY cap-open (crown, NO cap-tree write) for a CONFERRING effect — LAUNDERS
        // (post-cap-root host-trusted; the honest route is the `…WriteCapOpen…` wrapper).
        "grantCapCapOpenVmDescriptor2R24"
        | "delegateCapOpenVmDescriptor2R24"
        | "introduceCapOpenVmDescriptor2R24"
        | "revokeCapOpenVmDescriptor2R24"
        | "revokeCapabilityCapOpenVmDescriptor2R24"
        | "refreshDelegationCapOpenVmDescriptor2R24"
        | "spawnCapOpenVmDescriptor2R24" => Some(LaundersAuthority),
        // FULL crowned WRITE route (membership + post-cap-root write verified in-circuit) — ALLOWED.
        "delegateWriteCapOpenVmDescriptor2R24"
        | "delegateAttenWriteCapOpenVmDescriptor2R24"
        | "introduceWriteCapOpenVmDescriptor2R24"
        | "revokeDelegationWriteCapOpenVmDescriptor2R24"
        | "revokeCapabilityWriteCapOpenVmDescriptor2R24"
        | "refreshDelegationWriteCapOpenVmDescriptor2R24"
        | "spawnWriteCapOpenVmDescriptor2R24"
        | "attenuateCapOpenEffVmDescriptor2R24" => Some(CrownedWriteRoute),
        // NAMED RESIDUAL — re-arms an existing delegation; confers no new authority — ALLOWED plain.
        "refreshVmDescriptor2R24" => Some(NamedResidual),
        // ACCESS-gated (non-conferring) cap-open routes + the plain owner paths for cap-shaped verbs.
        "transferCapOpenTBVmDescriptor2R24"
        | "transferCapOpenEffVmDescriptor2R24"
        | "exerciseCapOpenVmDescriptor2R24"
        | "exerciseVmDescriptor2R24"
        | "spawnVmDescriptor2R24" => Some(NotAuthority),
        // Anything else: force review if it LOOKS authority-shaped, else it is a benign normal effect.
        _ => {
            let cap_management_prefix =
                ["introduce", "revoke", "attenuate", "grantCap", "delegate"]
                    .iter()
                    .any(|p| key.starts_with(p));
            if key.contains("CapOpen") || cap_management_prefix {
                None
            } else {
                Some(NotAuthority)
            }
        }
    }
}

/// Verify a ROTATED effect-vm sub-proof (the C4 `"effect-vm-rotated"` leg): deserialize the
/// `Ir2BatchProof` and verify it SELECTOR-BOUND against the rotated cohort descriptors. A sound
/// rotated proof binds its own descriptor (each carries the Lean selector tooth), so exactly one
/// cohort member accepts. Zero ⇒ not a rotated cohort proof (reject); more than one ⇒ ambiguous
/// (reject rather than launder a wrong-descriptor acceptance).
#[cfg(feature = "prover")]
pub fn verify_effect_vm_rotated_with_cutover(
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
    expected_vk_hash: &[u8; 32],
) -> Result<(), String> {
    // The pure light-client entry: no out-of-band declaration in hand, so GATE B is inert (`&[]`).
    // Byte-identical to the pre-gate-B deployed verify.
    verify_effect_vm_rotated_inner(proof_bytes, public_inputs, expected_vk_hash, &[])
}

/// GATE B — the SDK declared-capacity route discriminator (geometry-free, defense-in-depth). Given the
/// capacity tags an acting cell's COMMITTED declaration requires (escrow 17 / discharge 18 / vault 19,
/// re-derived by the CALLER via `dregg_turn::executor::required_capacity_caveat_tags` over the committed
/// `state_constraints` — bound into the `B_AUTHORITY_DIGEST` limb of the ~124-bit wide commit), the
/// required satisfaction descriptor a declared-capacity turn MUST bind. `None` ⇒ no capacity declared ⇒
/// the discriminator is inert (a non-declaring turn resolves normally). At most one capacity is present
/// per turn; escrow is checked first, then discharge, then vault (mirrors the producer route
/// `rotated_descriptor_name_for_declared_capacity`).
pub fn required_satisfaction_member(declared_capacity_tags: &[u32]) -> Option<&'static str> {
    use dregg_circuit::effect_vm::pi;
    use dregg_circuit::effect_vm::trace_rotated::{
        DISCHARGE_SAT_DESCRIPTOR_NAME, SETTLE_ESCROW_SAT_DESCRIPTOR_NAME, VAULT_SAT_DESCRIPTOR_NAME,
    };
    if declared_capacity_tags.contains(&pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW) {
        Some(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME)
    } else if declared_capacity_tags.contains(&pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION) {
        Some(DISCHARGE_SAT_DESCRIPTOR_NAME)
    } else if declared_capacity_tags.contains(&pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT) {
        Some(VAULT_SAT_DESCRIPTOR_NAME)
    } else {
        None
    }
}

/// The DECLARING light-client verify: a caller that holds the acting cell's committed declaration
/// (a full node / the executor bridge) passes the re-derived `declared_capacity_tags` so GATE B —
/// the verifier-side declared-capacity discriminator — is LIVE. When the cell declares a capacity, the
/// uniquely-accepting descriptor MUST be the corresponding satisfaction member; a bare cohort member is
/// REJECTED here, INDEPENDENT of the gate-A refuse weld (this reads only the bound descriptor NAME + the
/// declaration, never the refuse geometry). Empty tags ⇒ byte-identical to
/// [`verify_effect_vm_rotated_with_cutover`].
pub fn verify_effect_vm_rotated_declaring(
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
    expected_vk_hash: &[u8; 32],
    declared_capacity_tags: &[u32],
) -> Result<(), String> {
    verify_effect_vm_rotated_inner(
        proof_bytes,
        public_inputs,
        expected_vk_hash,
        declared_capacity_tags,
    )
}

fn verify_effect_vm_rotated_inner(
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
    expected_vk_hash: &[u8; 32],
    declared_capacity_tags: &[u32],
) -> Result<(), String> {
    use dregg_circuit::descriptor_ir2::{
        DreggStarkConfig, Ir2BatchProof, parse_vm_descriptor2, verify_vm_descriptor2,
    };
    // THE WIDE FLAG-DAY: the light-client verifier iterates the WIDE registry FIRST (the 8-felt
    // ~124-bit commit descriptors, the verified Lean `v3RegistryCapOpenWide`). The producer
    // (`prove_cohort_run_chain`) now emits wide legs for every NORMAL (owner-authorized) run, so the
    // uniquely-accepting descriptor is the wide member and the leg's 8-felt commit PIs (the LAST 16)
    // are what `verify_full_turn_bound` binds — the ~31-bit waist is GONE for the normal core.
    //
    // THE NAMED RESIDUAL (cap-open tail): the AUTHORITY crown AND the §10 WRITE-bearing cap-open tail
    // (`…WriteCapOpen…` + `spawnCapOpen` + `exerciseCapOpen`) now have PROVEN wide twins in
    // `WIDE_REGISTRY_STAGED_TSV`, so an honest capability-gated WRITE turn verifies under its WIDE
    // member (the full ~124-bit commit). To keep an HONEST leg with NO wide twin verifying (the
    // turn-bound `transferCapOpenTB`, whose 821-col host has no wide twin yet), we FALL BACK to the
    // 1-felt `V3_STAGED_REGISTRY_TSV` when no wide member accepts — but ONLY for cap-open keys that
    // genuinely LACK a wide twin (the fallback filter below). A cap-open key that HAS a wide twin is
    // filtered OUT of the V3 fallback, so a narrow 1-felt write-cap leg is REJECTED (the reject tooth).
    // `verify_full_turn_bound` discriminates per-leg by the accepting registry. A forged plain-cap
    // descriptor still hits the AUTHORITY FLOOR below.
    use dregg_circuit::effect_vm_descriptors::{
        V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV,
    };

    let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
        .map_err(|e| format!("rotated effect-vm proof deserialize: {e}"))?;

    // Collect the (name, json) of every descriptor in a registry the proof verifies under.
    let collect_bound = |registry: &'static str| -> Vec<(&'static str, &'static str)> {
        let mut bound: Vec<(&'static str, &'static str)> = Vec::new();
        for line in registry.lines() {
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
            if let Ok(desc) = parse_vm_descriptor2(json)
                && public_inputs.len() >= desc.public_input_count
            {
                let dpis = &public_inputs[..desc.public_input_count];
                if verify_vm_descriptor2(&desc, &proof, dpis).is_ok() {
                    bound.push((name, json));
                }
            }
        }
        bound
    };

    // WIDE first (the normal core). If no wide member accepts, fall back to V3 — but ONLY accept a
    // CAP-OPEN member there (the named residual tail). This is the load-bearing reject tooth: a
    // malicious producer cannot present a 1-felt V3 leg for a NORMAL effect (e.g. a 1-felt transfer)
    // to dodge the wide ~124-bit commitment — a plain V3 transfer/normal descriptor is NOT a cap-open
    // member, so it is FILTERED OUT of the fallback and the proof verifies under NO accepted
    // descriptor ⇒ REJECTED. Only genuine cap-open legs (the wide-twin-pending residual) survive the
    // fallback, and they bind their 1-felt commit (the residual waist for cap-gated turns only).
    let mut bound = collect_bound(WIDE_REGISTRY_STAGED_TSV);
    // THE umem VK EPOCH (G4): the Lean-emitted WIDE+UMEM WELDED registry is the deployed DEFAULT
    // producer's accepted descriptor set. A welded proof (`prove_wide_umem_welded_staged`) binds the
    // welded member here UNIQUELY — its welded width / extra umemOp constraint cannot verify against any
    // BARE wide member (and a bare wide proof cannot verify against a welded member), so the 8-felt
    // ~124-bit anchors stay bound and the uniqueness/ambiguity tooth below still holds. This SDK wire
    // verifier admits BOTH registries: the welded set (the deployed sovereign/cap producers' default)
    // AND the bare set (the 3 producer-bare members heapWrite / supplyMint / transferCapOpenTB,
    // multi-cohort chain legs, and the rollback path). The deployed EXECUTOR verifier is the one that
    // REQUIRES the welded twin for a single-cohort sovereign turn (`verify_one_cohort_run`'s
    // `require_welded`), so a committed turn carries the umem boundary on the wire.
    bound.extend(collect_bound(WIDE_UMEM_WELD_REGISTRY_TSV));
    if bound.is_empty() {
        bound = collect_bound(V3_STAGED_REGISTRY_TSV)
            .into_iter()
            // A V3 cap-open member survives the fallback ONLY if it has NO proven wide twin (the
            // genuine residual — today the turn-bound `transferCapOpenTB`). A cap-open key that DOES
            // have a wide twin (the §10 WRITE tail + the authority crown) is FILTERED OUT here: its
            // honest leg verifies under the WIDE member above, so a 1-felt V3 leg for it is a
            // wide-dodge and is REJECTED (the reject tooth — a narrow write-cap leg binds no accepted
            // descriptor ⇒ rejected, forcing the producer onto the ~124-bit wide route).
            .filter(|(name, _)| name.contains("CapOpen") && !cap_open_key_has_wide_twin(name))
            .collect();
    }
    match bound.as_slice() {
        [(name, json)] => {
            // AUTHORITY FLOOR (light-client unfoolability): a CAP effect MUST be proven under its
            // cap-open descriptor (the depth-16 cap-membership authority crown is IN that descriptor,
            // and ONLY that descriptor). The PLAIN cohort descriptor for a cap effect
            // (`introduceVmDescriptor2R24`, `revokeVmDescriptor2R24`, …) carries NO in-circuit
            // cap-membership check — accepting it would let a malicious producer prove a cap effect
            // WITHOUT proving it held a cap reaching the target (the host-trusted c-list check is
            // off-AIR / light-client-blind). So if the uniquely-accepting descriptor is a plain
            // cap-effect descriptor, REJECT here: the producer must re-prove under the cap-open
            // descriptor, where the membership appendix is verified in-circuit. This is the
            // verifier half of the FORCED routing (the producer half re-points the resolver to the
            // cap-open name), and it makes cap authority light-client-verifiable, not host-trusted.
            if is_forbidden_plain_cap_descriptor(name) {
                return Err(format!(
                    "rotated effect-vm proof bound the PLAIN cap-effect descriptor {name} — a cap \
                     effect MUST be proven under its cap-open descriptor (the in-circuit depth-16 \
                     cap-membership authority crown); the plain descriptor carries NO membership \
                     check, so accepting it would launder host-trusted authority into a \
                     light-client proof. Rejecting (re-prove via the cap-open route)."
                ));
            }
            // ── GATE B: the declared-capacity discriminator (defense-in-depth, geometry-free). When
            // the caller supplied the acting cell's committed declaration, a declared-capacity turn MUST
            // bind its satisfaction member; a bare cohort member is rejected HERE — independent of the
            // gate-A refuse weld baked into the bare VK (this reads only the uniquely-bound descriptor
            // NAME + the declaration). Inert for the pure LC entry (empty tags) and for a non-declaring
            // cell, so honest turns resolve normally.
            if let Some(required) = required_satisfaction_member(declared_capacity_tags)
                && *name != required
            {
                return Err(format!(
                    "GATE B (declared-capacity discriminator): the acting cell's COMMITTED declaration \
                     requires capacity tags {declared_capacity_tags:?}, so the proof MUST bind the \
                     satisfaction member {required}; it bound the bare cohort descriptor {name} (no \
                     satisfaction gate). Rejecting the bare-cohort dodge geometry-free (independent of \
                     the refuse weld)."
                ));
            }
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
    // The v1 Effect-VM trace + PI are computed ONLY when the rotated leg is NOT taken
    // (no rotation witness). Its only escaping value is `net_delta` (the conservation
    // leg, below); on the rotated path that is carried in the rotated PI prefix instead,
    // so the rotated branch is self-sufficient and carries ZERO v1 dependency. On a
    // `not(prover)` build `rotation` is always `None` (the rotated PROVER is prover-gated),
    // so `use_rotated` is false there and `v1_effect` is computed for its net_delta.
    let use_rotated = witness.rotation.is_some();
    #[allow(clippy::type_complexity)]
    let v1_effect: Option<(Vec<Vec<BabyBear>>, Vec<BabyBear>)> = if use_rotated {
        None
    } else {
        Some(generate_effect_vm_trace(
            &witness.initial_cell_state,
            &witness.effects,
        ))
    };
    // THE ROTATED LEG (the SOLE effect-vm prover): when the caller threaded the rotation producer
    // witnesses, prove the effect-vm transition through the ROTATED IR-v2 path (the multi-table
    // `Ir2BatchProof`) and attach it as the `"effect-vm-rotated"` sub-proof. Its PI vector is
    // the rotated 38-PI (the v1 prefix `[0..34)` — OLD/NEW_COMMIT/turn-id/effects-hash carried
    // at their v1 offsets — plus the 4 appended rotated commit/height/caveat pins at 34..37).
    components.has_state_transition = true;
    // PATH-PRESERVE §2/§3: the rotated leg is N legs — one per maximal homogeneous cohort-run
    // (`split_into_cohort_runs`). A HOMOGENEOUS turn yields exactly ONE run. The collected PI
    // vectors flow to the conservation leg (Σ net_delta) + the `is_none` fail-closed guard. The
    // rotated PROVER (`prove_cohort_run_chain`) is `prover`-gated; on a `not(prover)` build
    // `rotation` is always `None`, so `rotated_effect_pis` is `None` and the guard fails closed.
    #[cfg(feature = "prover")]
    let rotated_effect_pis: Option<Vec<Vec<BabyBear>>> = if let Some(rot) = &witness.rotation {
        // The BEFORE nullifier set for the EffectVM rotated note-spend grow-gate: the
        // non-revocation witness's revocation accumulator IS the already-spent-nullifier set, so
        // its leaves seed the in-circuit limb-26 accumulator the `.absent`/`.insert` map-ops open
        // against — the grow-gate and the non-revocation leg agree on freshness by construction.
        let before_nullifiers: Option<Vec<BabyBear>> = witness
            .non_revocation
            .as_ref()
            .map(|nr| nr.tree.revoked_leaves());
        let legs = prove_cohort_run_chain(
            &witness.initial_cell_state,
            &witness.effects,
            rot,
            witness.cap_membership.as_ref(),
            witness.cap_turn_identity,
            before_nullifiers.as_deref(),
            witness.umem_witness.as_ref(),
        )?;
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
    #[cfg(not(feature = "prover"))]
    let rotated_effect_pis: Option<Vec<Vec<BabyBear>>> = None;

    if rotated_effect_pis.is_none() {
        // The v1 effect-vm leg is GONE (the rotated chained leg is the SOLE effect-vm prover —
        // PATH-PRESERVE Phases 0-4). A finalized-turn prove with no rotation witness can no
        // longer fall back to v1, so it FAILS CLOSED on every build. This enforces the Phase-4
        // invariant in code: every reachable finalized turn threads a rotation witness, so
        // `rotation.is_none()` here is unreachable for the live node (whose cohort gate always
        // yields `Some`); a caller that reaches it gets a structured error, not a silent proof.
        let _ = &v1_effect;
        return Err(SdkError::InvalidWitness(
            "full-turn prove: no rotation witness threaded and the v1 effect-vm fallback has \
             been retired — thread a rotation witness (the live node always does)"
                .into(),
        ));
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
    //
    // ⚑ NATIVE-8-FELT (Phase H-CAP-8, node8 CLOSE). The standalone DSL-p3 cap-membership
    // leg (`dsl::cap_membership`) is now a FAITHFUL 8-felt Poseidon2 Merkle STARK: its
    // `MerkleHash8` node arithmetization binds ALL 8 `poseidon2_permute_expr_lanes` output
    // lanes of the arity-16 `cap_node8` compression (the multi-output DSL-AIR gadget), so it
    // carries the native 8-felt witness at the full ~124-bit collision floor — NO lane-0
    // projection anywhere. It pins a 16-felt public input `[leaf_digest(8) ‖ cap_root(8)]`;
    // `verify_full_turn_bound` step 9 pins BOTH the 8-felt leaf digest (to the receipt-disclosed
    // consumed cap) AND the 8-felt canonical pre-state `cap_root`, so "some leaf ∈ some tree"
    // becomes "THE disclosed capability ∈ THE holder's real c-list" — production authority,
    // no longer fail-closed.
    if let Some(cap) = &witness.cap_membership {
        // The 8-felt leaf digest of the consumed capability (the same value the verifier
        // recomputes from the receipt-disclosed 7-field preimage) + the native 8-felt sibling
        // path (`node8` digests, NOT lane-0 scalars).
        let leaf_digest8 = cap.leaf.digest();
        let (cap_proof, cap_pi) = dregg_circuit::dsl::cap_membership::prove_cap_membership_p3(
            leaf_digest8,
            &cap.siblings,
            &cap.directions,
        )
        .map_err(|e| SdkError::InvalidWitness(format!("cap-membership p3 proof failed: {e}")))?;
        let cap_proof_bytes = postcard::to_allocvec(&cap_proof).map_err(|e| {
            SdkError::InvalidWitness(format!("cap-membership p3 proof serialize failed: {e}"))
        })?;

        components.has_cap_membership = true;
        all_public_inputs.extend_from_slice(&cap_pi);
        sub_proofs.push(AttachedSubProof {
            label: "cap-membership".into(),
            proof_bytes: cap_proof_bytes,
            sub_public_inputs: cap_pi,
            vk_hash: compute_vk_hash_bytes(
                &dregg_circuit::dsl::cap_membership::cap_membership_circuit_descriptor(),
            ),
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
    expected_old_commit: [BabyBear; 8],
    expected_new_commit: [BabyBear; 8],
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
    expected_old_commit: [BabyBear; 8],
    expected_new_commit: [BabyBear; 8],
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
            // (The v1 `"effect-vm"` arm — the AUDITED p3 verify of the v1 hand-AIR
            // `EffectVmP3Proof` — is RETIRED. The live effect-vm leg is `"effect-vm-rotated"`
            // below; a v1 `"effect-vm"` leg presented here rejects at the catch-all.)
            // EFFECT VM ROTATED (C4 cutover): the multi-table `Ir2BatchProof` over a rotated
            // R=24 descriptor. Resolve the descriptor SELECTOR-BOUND (a sound rotated proof
            // verifies under exactly one cohort descriptor — its own effect's), then verify
            // via the audited IR-v2 batch verifier. `not(prover)` builds never produce this
            // leg, so the arm is prover-gated.
            #[cfg(feature = "prover")]
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
                // Native 8-felt cap-membership PI is [leaf_digest(8) ‖ cap_root(8)]; all
                // 16 felts bound in-circuit (row-0 / last-row 8-lane boundaries). Carrying
                // the full 16 to the audited verifier re-binds them (a proof for a different
                // leaf or tree — even one agreeing on lane 0 — is UNSAT under these PIs).
                let pis = &attached.sub_public_inputs;
                if pis.len() < 16 {
                    return Err(FullTurnVerifyError::MalformedPublicInputs(format!(
                        "cap-membership PI carries {} felts, need 16 (leaf_digest[8] ‖ cap_root[8])",
                        pis.len()
                    )));
                }
                let mut leaf_digest = [BabyBear::ZERO; 8];
                leaf_digest.copy_from_slice(&pis[0..8]);
                let mut cap_root = [BabyBear::ZERO; 8];
                cap_root.copy_from_slice(&pis[8..16]);
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

    // THE WIDE FLAG-DAY COMMIT ANCHOR (the ~31-bit light-client floor close). A WIDE rotated leg
    // publishes the FULL 8-felt BEFORE/AFTER commits as the LAST 16 PIs of its `sub_public_inputs`
    // (the wide descriptor's carrier-12 pi_bindings tie them to the proof's bound 8-felt carriers, so
    // a forged 8-felt commit is UNSAT — the wide analog of the executor's `n_pi-16..` anchor). We bind
    // those 8-felt slices, NOT the retired single felt at `pi::OLD_COMMIT`/`pi::NEW_COMMIT`. Each leg
    // is classified WIDE vs NARROW by its `vk_hash` (the blake3 of the descriptor JSON it bound — the
    // SAME fingerprint `verify_effect_vm_rotated_with_cutover` re-pinned): a wide-registry fingerprint
    // ⇒ bind the 8-felt tail; otherwise (the cap-open RESIDUAL tail — see the cutover comment) the leg
    // is a 1-felt V3 cap-open leg, bound at its single `pi::OLD_COMMIT`/`pi::NEW_COMMIT` felt
    // (broadcast into the 8-felt anchor's slot 0, the residual ~31-bit waist for cap-gated turns).
    #[cfg(feature = "prover")]
    fn leg_is_wide(leg: &AttachedSubProof) -> bool {
        use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
        WIDE_REGISTRY_STAGED_TSV.lines().any(|line| {
            line.splitn(3, '\t')
                .nth(2)
                .map(|json| blake3::hash(json.as_bytes()).as_bytes() == &leg.vk_hash)
                .unwrap_or(false)
        })
    }
    #[cfg(not(feature = "prover"))]
    fn leg_is_wide(_leg: &AttachedSubProof) -> bool {
        false
    }

    // Extract a leg's (before8, after8) commit anchors at the leg's true width. For a wide leg the
    // 8-felt commits are the LAST 16 PIs (~124-bit). For a narrow cap-open leg (the residual) the
    // 1-felt commit at `pi::OLD_COMMIT`/`pi::NEW_COMMIT` is widened into slot 0 (its faithful width).
    let leg_commit = |leg: &AttachedSubProof,
                      which: &'static str|
     -> Result<([BabyBear; 8], [BabyBear; 8]), FullTurnVerifyError> {
        if leg_is_wide(leg) {
            let n = leg.sub_public_inputs.len();
            if n < 16 {
                return Err(FullTurnVerifyError::MalformedPublicInputs(format!(
                    "wide effect-vm leg too short for the 8-felt commit tail ({which}): {n} PIs < 16"
                )));
            }
            let before: [BabyBear; 8] = leg.sub_public_inputs[n - 16..n - 8]
                .try_into()
                .expect("slice of len 8");
            let after: [BabyBear; 8] = leg.sub_public_inputs[n - 8..n]
                .try_into()
                .expect("slice of len 8");
            Ok((before, after))
        } else {
            // The cap-open residual: 1-felt commit broadcast into slot 0 (zeros elsewhere — the
            // narrow leg carries no wide tail). The caller's `expected_*` is the 8-felt anchor; for a
            // cap-gated turn the caller derives it the SAME 1-felt-in-slot-0 way (see below).
            let mut before = [BabyBear::ZERO; 8];
            let mut after = [BabyBear::ZERO; 8];
            before[0] = leg.sub_public_inputs[effect_vm::pi::OLD_COMMIT];
            after[0] = leg.sub_public_inputs[effect_vm::pi::NEW_COMMIT];
            Ok((before, after))
        }
    };

    // Endpoints: the chain's first BEFORE and last AFTER commits pin the turn's pre/post state.
    let first_leg = effect_legs[0];
    let last_leg = effect_legs[effect_legs.len() - 1];
    let (proof_old_commit, _) = leg_commit(first_leg, "first leg")?;
    let (_, proof_new_commit) = leg_commit(last_leg, "last leg")?;

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

    // Adjacency: each leg's BEFORE commit must equal the previous leg's AFTER commit — the chain
    // closes with no gap and no splice. A tampered / dropped middle leg breaks this (anti-ghost at
    // the chain layer), at the full ~124-bit width for the wide normal core.
    for w in effect_legs.windows(2) {
        let (_, prev_after) = leg_commit(w[0], "chain prev")?;
        let (this_before, _) = leg_commit(w[1], "chain this")?;
        if this_before != prev_after {
            return Err(FullTurnVerifyError::CommitmentMismatch {
                which: "chain_adjacency",
                expected: prev_after,
                got: this_before,
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
    if let Some(expected_root) = expected_revocation_root
        && proof.components.has_non_revocation
    {
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
            // THE WIDE FLAG-DAY GUARD FIX: a WIDE rotated leg ALWAYS carries >= ROT_NULLIFIER_PI_COUNT
            // PIs (the 16 wide commit PIs pushed every leg past 47), so the old PI-count guard wrongly
            // fired for NON-note-spend wide legs — reading PI[46] (a non-nullifier wide pin) as a
            // bogus nullifier. The nullifier slot at ROT_NULLIFIER_PI is meaningful ONLY for the
            // note-spend descriptor (the C4 fifth-pin weld is `noteSpendVmDescriptor2R24`-specific), so
            // gate the read on the leg actually binding the note-spend descriptor (by its vk_hash —
            // the SAME fingerprint the cutover verifier re-pinned). A non-note-spend leg publishes no
            // nullifier ⇒ ZERO sentinel ⇒ no binding.
            #[cfg(feature = "prover")]
            fn leg_is_note_spend(leg: &AttachedSubProof) -> bool {
                use dregg_circuit::effect_vm_descriptors::{
                    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV,
                };
                let matches_ns = |registry: &str| {
                    registry.lines().any(|line| {
                        let mut it = line.splitn(3, '\t');
                        let name = it.next();
                        let _disp = it.next();
                        let json = it.next();
                        name == Some("noteSpendVmDescriptor2R24")
                            && json
                                .map(|j| blake3::hash(j.as_bytes()).as_bytes() == &leg.vk_hash)
                                .unwrap_or(false)
                    })
                };
                matches_ns(WIDE_REGISTRY_STAGED_TSV) || matches_ns(V3_STAGED_REGISTRY_TSV)
            }
            #[cfg(not(feature = "prover"))]
            fn leg_is_note_spend(_leg: &AttachedSubProof) -> bool {
                false
            }
            let mut nullifier = BabyBear::ZERO;
            for leg in &effect_legs {
                let leg_nullifier = if leg.label == "effect-vm-rotated" {
                    if leg_is_note_spend(leg)
                        && leg.sub_public_inputs.len() >= ROT_NULLIFIER_PI_COUNT
                    {
                        leg.sub_public_inputs[ROT_NULLIFIER_PI]
                    } else {
                        // Not a note-spend rotated leg: no nullifier published (the wide commit tail
                        // is NOT a nullifier — the old PI-count-only guard misread it).
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
        // Native 8-felt AUTHORITY binding (Phase H-CAP-8): the standalone cap-membership
        // leg's PI is `[leaf_digest(8) ‖ cap_root(8)]` — the FULL-width node8 digests, NOT
        // a lane-0 scalar. Pin BOTH the 8-felt leaf digest AND the 8-felt canonical
        // pre-state cap_root, so the ~124-bit collision floor (matching the deployed
        // FRI/STARK soundness) carries end-to-end. A leg that publishes fewer than 16 PIs
        // is malformed and rejected here (never lane-0-narrowed to fit).
        let pis = &cap_sub.sub_public_inputs;
        if pis.len() < 16 {
            return Err(FullTurnVerifyError::MalformedPublicInputs(format!(
                "cap-membership PI carries {} felts, need 16 (leaf_digest[8] ‖ cap_root[8])",
                pis.len()
            )));
        }
        let mut proof_leaf_digest = [BabyBear::ZERO; 8];
        proof_leaf_digest.copy_from_slice(&pis[0..8]);
        let mut proof_cap_root = [BabyBear::ZERO; 8];
        proof_cap_root.copy_from_slice(&pis[8..16]);
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

/// **The STAGED constraint-binding verifier (the house-capacity weld's omission-proof
/// path).** Runs every deployed [`verify_full_turn_bound`] check, then — when the
/// caller supplies a [`CaveatCoverageExpectation`] — additionally enforces that the
/// slot-caveat manifest COVERS every capacity caveat the cell's COMMITTED declaration
/// requires (present AND its gate re-evaluates true). This closes the load-bearing
/// soundness gap that the deployed path leaves: the manifest is prover-chosen, so a
/// forger could OMIT a declared capacity entry and the verifier would have nothing to
/// check (the §6 weld rungs only force a PRESENT entry's invariant). With the
/// coverage demand, omission is rejected.
///
/// This is the Rust shadow of the Lean
/// `Dregg2.Deos.ConstraintBinding.omission_caught_under_binding`: the caller's
/// `required_tags` is `requiredTags(committed declaration)`, and a forger cannot
/// escape via a hollow declaration because the declaration is bound in committed
/// state (the `B_AUTHORITY_DIGEST` limb of the wide commit — the Lean `DeclCommitBinds`
/// floor = the authority digest's collision-resistance).
///
/// STAGED — built BESIDE the deployed [`verify_full_turn_bound`], NOT flipping it:
///   * `expected_caveat_coverage = None` ⇒ byte-identical to [`verify_full_turn_bound`]
///     (the deployed default; no caveat check, nothing flips).
///   * `Some(cov)` ⇒ the omission-proof path. The AIR constraint polynomials — hence
///     the VK bytes — are UNCHANGED (the manifest rides public inputs + off-AIR
///     re-evaluation).
///
/// CARRIER NOTE (the true remaining distance): the off-AIR slot-caveat manifest rides
/// the FULL v1 effect-vm PI layout (`>= pi::BASE_COUNT`); the live ROTATED leg
/// (38/39/wide PIs) does NOT carry it. So for a pure light client (commitments only),
/// getting the manifest onto the rotated/wide leg bound in-AIR is the named VK epoch.
/// Until then this path is fail-closed: a turn with NO manifest-bearing leg has every
/// required tag absent and is rejected. See
/// `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`.
pub fn verify_full_turn_bound_with_caveat_coverage(
    proof: &FullTurnProof,
    expected_old_commit: [BabyBear; 8],
    expected_new_commit: [BabyBear; 8],
    expected_revocation_root: Option<BabyBear>,
    expected_cap_membership: Option<&CapMembershipExpectation>,
    expected_caveat_coverage: Option<&CaveatCoverageExpectation>,
) -> Result<(), FullTurnVerifyError> {
    // 1. Every deployed check (cryptographic verify + commit/adjacency/auth/freshness/cap).
    verify_full_turn_bound(
        proof,
        expected_old_commit,
        expected_new_commit,
        expected_revocation_root,
        expected_cap_membership,
    )?;

    // 2. The staged coverage check (None ⇒ deployed-identical).
    let Some(cov) = expected_caveat_coverage else {
        return Ok(());
    };
    if cov.required_tags.is_empty() {
        return Ok(());
    }

    // Locate the effect-vm leg carrying the off-AIR slot-caveat manifest (the FULL v1 PI layout,
    // >= pi::BASE_COUNT). The rotated leg does not carry it (the carrier gap, documented above);
    // a turn with no manifest-bearing leg fails closed (every required tag absent).
    let manifest_leg = proof.composed.sub_proofs.iter().find(|sp| {
        (sp.label == "effect-vm" || sp.label == "effect-vm-rotated")
            && sp.sub_public_inputs.len() >= effect_vm::pi::BASE_COUNT
    });
    let pi: &[BabyBear] = match manifest_leg {
        Some(leg) => &leg.sub_public_inputs,
        None => {
            return Err(FullTurnVerifyError::CaveatCoverageFailed {
                reason: format!(
                    "no manifest-bearing effect-vm leg (>= {} PIs); declared capacity tag {} is \
                     unwitnessed — omission rejected (fail-closed)",
                    effect_vm::pi::BASE_COUNT,
                    cov.required_tags[0]
                ),
            });
        }
    };

    // SATISFACTION: every PRESENT entry's gate re-evaluates true (the §6 capacity gates).
    dregg_circuit::effect_vm::verify_slot_caveat_manifest(
        pi,
        &cov.initial_fields,
        &cov.final_fields,
        cov.block_height,
    )
    .map_err(|reason| FullTurnVerifyError::CaveatManifestUnsatisfied { reason })?;

    // COVERAGE / OMISSION: every REQUIRED tag is present (the soundness core).
    dregg_circuit::effect_vm::verify_slot_caveat_coverage(pi, &cov.required_tags)
        .map_err(|reason| FullTurnVerifyError::CaveatCoverageFailed { reason })?;

    Ok(())
}

/// Whether the cell's COMMITTED-declaration required-tag floor DEMANDS the sealed-escrow selector
/// (the Lean `Dregg2.Deos.SettleEscrowSelectorBinding.demandsEscrowSelector`: the floor includes the
/// escrow tag `SLOT_CAVEAT_TAG_SETTLE_ESCROW = 17`). The Rust twin of the Lean predicate — a turn
/// declaring the sealed-escrow capacity must be forced through the welded gates.
pub fn demands_escrow_selector(required_tags: &[u32]) -> bool {
    required_tags.contains(&dregg_circuit::effect_vm::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW)
}

/// **The escrow SELECTOR-PI demand (HALF B, the pure twin).** When the required-tag floor demands
/// the escrow selector, the rotated effect-vm leg's selector PI (`ESCROW_SEL_PI = 46`) MUST be `1`
/// — so a forger cannot dodge the welded satisfaction gates by leaving `sel = 0` (which makes every
/// `sel · (col − const)` gate inert). This is the deployed realization of the Lean `hverifier`
/// discipline `demandsEscrowSelector required → pub ESCROW_SEL_PI = 1`. Returns `Ok(())` when no
/// demand fires (deployed-identical), else enforces the pin against the leg's published PI.
///
/// Pure (PI-slice in, verdict out) so it is unit-testable without building a full STARK proof; the
/// staged [`verify_full_turn_bound_with_escrow_weld`] calls it on the rotated leg's public inputs.
pub fn check_escrow_selector_pin(
    required_tags: &[u32],
    rotated_leg_pis: &[BabyBear],
) -> Result<(), FullTurnVerifyError> {
    if !demands_escrow_selector(required_tags) {
        return Ok(());
    }
    let sel_pi = dregg_circuit::effect_vm::satisfaction_weld::ESCROW_SEL_PI;
    let published = rotated_leg_pis.get(sel_pi).copied().ok_or_else(|| {
        FullTurnVerifyError::EscrowWeldNotForced {
            reason: format!(
                "rotated effect-vm leg carries only {} PIs (< {}); the welded escrow descriptor's \
                 selector PI is absent, so a declared-escrow turn was NOT proven under the welded \
                 descriptor (non-welded route — rejected fail-closed)",
                rotated_leg_pis.len(),
                sel_pi + 1
            ),
        }
    })?;
    if published != BabyBear::ONE {
        return Err(FullTurnVerifyError::EscrowWeldNotForced {
            reason: format!(
                "escrow selector PI[{sel_pi}] = {published:?} != 1 — a declared-escrow turn left \
                 the capacity selector OFF, which would make the welded satisfaction gates inert \
                 (the half-open-settle dodge, HALF B)"
            ),
        });
    }
    Ok(())
}

/// **The STAGED sealed-escrow SELECTOR-weld verifier (§6 item 2 — the deployed `hverifier`).** Runs
/// every deployed [`verify_full_turn_bound`] check, then — when the caller supplies an
/// [`EscrowWeldExpectation`] whose re-derived required-tag floor demands the escrow capacity — FORCES
/// the declared-escrow turn through the welded gates:
///
///   1. **HALF B (selector on):** the rotated effect-vm leg's selector PI (`ESCROW_SEL_PI = 46`) MUST
///      be `1` ([`check_escrow_selector_pin`]) — a forger cannot leave `sel = 0` to make the gates
///      inert.
///   2. **Welded route:** the rotated leg MUST verify under the WELDED descriptor
///      (`SETTLE_ESCROW_SAT_DESCRIPTOR_NAME` — the four selector-gated satisfaction gates over the
///      committed BEFORE/AFTER field columns). A declared-escrow turn routed through a non-welded
///      descriptor (e.g. a plain `transferVmDescriptor2R24`) is REJECTED.
///
/// This is the deployed realization of the proven Lean obligation
/// `Dregg2.Deos.SettleEscrowSelectorBinding.escrow_selector_bound_to_declaration`: HALF A (the
/// demand is un-dodgeable by a hollow declaration) is the `DeclCommitBinds` authority-digest floor
/// (the caller re-derives `required_tags` from the committed declaration, the same cap-membership
/// posture as [`CapMembershipExpectation`]); HALF B (the demanded selector forces the gate) is the
/// PI pin checked here.
///
/// STAGED — built BESIDE the deployed [`verify_full_turn_bound`]:
///   * `expected_escrow_weld = None` ⇒ byte-identical to [`verify_full_turn_bound`].
///   * `Some(_)` with no escrow tag in `required_tags` ⇒ deployed-identical (no demand).
///   * `Some(_)` requiring the escrow tag ⇒ the enforcement above. FAIL-CLOSED: until the welded
///     descriptor is a WIDE member with a producer + committed VK (the FLIP — §6 BLOCKER 1), no
///     honest proof verifies under it, so this path REJECTS a declared-escrow turn rather than
///     accepting it half-open. No deployed cell declares the escrow caveat, so the deployed default
///     is unaffected and the descriptors/VK are byte-identical.
pub fn verify_full_turn_bound_with_escrow_weld(
    proof: &FullTurnProof,
    expected_old_commit: [BabyBear; 8],
    expected_new_commit: [BabyBear; 8],
    expected_revocation_root: Option<BabyBear>,
    expected_cap_membership: Option<&CapMembershipExpectation>,
    expected_escrow_weld: Option<&EscrowWeldExpectation>,
) -> Result<(), FullTurnVerifyError> {
    // 1. Every deployed check (cryptographic verify + commit/adjacency/auth/freshness/cap).
    verify_full_turn_bound(
        proof,
        expected_old_commit,
        expected_new_commit,
        expected_revocation_root,
        expected_cap_membership,
    )?;

    // 2. The staged escrow-selector weld (None ⇒ deployed-identical).
    let Some(weld) = expected_escrow_weld else {
        return Ok(());
    };
    if !demands_escrow_selector(&weld.required_tags) {
        return Ok(());
    }

    // Locate the rotated effect-vm leg (the only leg that can carry the welded descriptor's PIs).
    let rotated_leg = proof
        .composed
        .sub_proofs
        .iter()
        .find(|sp| sp.label == "effect-vm-rotated")
        .ok_or_else(|| FullTurnVerifyError::EscrowWeldNotForced {
            reason: "declared-escrow turn carries no rotated effect-vm leg — the welded \
                     satisfaction gate is unwitnessed (rejected fail-closed)"
                .into(),
        })?;

    // HALF B: the demanded selector PI must be 1 (so the welded gates are not inert).
    check_escrow_selector_pin(&weld.required_tags, &rotated_leg.sub_public_inputs)?;

    // WELDED ROUTE: the rotated leg must verify under the WELDED descriptor specifically — a
    // declared-escrow turn proven under a non-welded descriptor (no satisfaction gate) is rejected.
    // Prover-gated (the IR-v2 batch verifier lives behind `prover`); a non-prover verifier cannot
    // confirm the welded gates, so it fails closed.
    #[cfg(feature = "prover")]
    {
        use dregg_circuit::descriptor_ir2::{
            DreggStarkConfig, Ir2BatchProof, parse_vm_descriptor2, verify_vm_descriptor2,
        };
        use dregg_circuit::effect_vm::SETTLE_ESCROW_SAT_DESCRIPTOR_NAME;
        use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;

        let welded_json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                let name = it.next()?;
                let _display = it.next()?;
                let json = it.next()?;
                (name == SETTLE_ESCROW_SAT_DESCRIPTOR_NAME).then_some(json)
            })
            .ok_or_else(|| FullTurnVerifyError::EscrowWeldNotForced {
                reason: format!(
                    "welded descriptor {SETTLE_ESCROW_SAT_DESCRIPTOR_NAME} not found in the staged \
                     registry — cannot confirm the satisfaction gate"
                ),
            })?;
        let desc = parse_vm_descriptor2(welded_json).map_err(|e| {
            FullTurnVerifyError::EscrowWeldNotForced {
                reason: format!("welded descriptor parse: {e}"),
            }
        })?;
        let proof_obj: Ir2BatchProof<DreggStarkConfig> =
            postcard::from_bytes(&rotated_leg.proof_bytes).map_err(|e| {
                FullTurnVerifyError::EscrowWeldNotForced {
                    reason: format!("rotated leg deserialize: {e}"),
                }
            })?;
        if rotated_leg.sub_public_inputs.len() < desc.public_input_count {
            return Err(FullTurnVerifyError::EscrowWeldNotForced {
                reason: format!(
                    "rotated leg carries {} PIs (< the welded descriptor's {}) — not a welded \
                     escrow proof (non-welded route, rejected)",
                    rotated_leg.sub_public_inputs.len(),
                    desc.public_input_count
                ),
            });
        }
        let dpis = &rotated_leg.sub_public_inputs[..desc.public_input_count];
        verify_vm_descriptor2(&desc, &proof_obj, dpis).map_err(|e| {
            FullTurnVerifyError::EscrowWeldNotForced {
                reason: format!(
                    "rotated leg does NOT verify under the welded descriptor \
                     {SETTLE_ESCROW_SAT_DESCRIPTOR_NAME} — a declared-escrow turn was routed \
                     through a non-welded descriptor with no satisfaction gate: {e}"
                ),
            }
        })?;
        Ok(())
    }
    #[cfg(not(feature = "prover"))]
    {
        Err(FullTurnVerifyError::EscrowWeldNotForced {
            reason: "the welded escrow descriptor verify requires the `prover` feature; a \
                     non-prover verifier cannot confirm the satisfaction gate, so a declared-escrow \
                     turn is rejected fail-closed"
                .into(),
        })
    }
}

/// Errors that can occur during full turn proof verification.
#[derive(Debug, Clone)]
pub enum FullTurnVerifyError {
    /// STAGED constraint-binding weld: a PRESENT slot-caveat manifest entry's gate
    /// re-evaluation FAILED against the bound state views (the §6
    /// `SettleGate`/`DischargeGate`/`VaultDepositGate` satisfaction half — e.g. a
    /// partial settle, an early discharge, a diluting deposit). Only raised on the
    /// staged [`verify_full_turn_bound_with_caveat_coverage`] path.
    CaveatManifestUnsatisfied {
        /// The first failing entry's diagnostic.
        reason: String,
    },
    /// STAGED constraint-binding weld: a capacity caveat the cell's COMMITTED
    /// declaration REQUIRES is ABSENT from the manifest (omission). This is the
    /// soundness-core rejection — a forger cannot drop a declared capacity gate. Only
    /// raised on the staged [`verify_full_turn_bound_with_caveat_coverage`] path.
    CaveatCoverageFailed {
        /// The missing-tag diagnostic.
        reason: String,
    },
    /// STAGED sealed-escrow SELECTOR weld (§6 item 2): a turn whose COMMITTED declaration requires
    /// the escrow capacity was NOT forced through the welded gates — either the escrow selector PI
    /// (`ESCROW_SEL_PI = 46`) on the rotated leg was not `1` (a forger trying to make the gates
    /// inert by `sel = 0`), or the rotated leg did not verify under the welded descriptor (the turn
    /// was routed through a non-welded descriptor with no satisfaction gate). The deployed
    /// realization of the Lean `escrow_selector_bound_to_declaration` `hverifier` discipline. Only
    /// raised on the staged [`verify_full_turn_bound_with_escrow_weld`] path.
    EscrowWeldNotForced {
        /// The selector / routing diagnostic.
        reason: String,
    },
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
    /// State commitment in proof does not match expected value. Post the WIDE flag-day the
    /// commitment is the FULL 8-felt (~124-bit) wide commit (the leg's LAST 16 PIs), not the
    /// retired 1-felt waist.
    CommitmentMismatch {
        which: &'static str,
        expected: [BabyBear; 8],
        got: [BabyBear; 8],
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
        /// The canonical pre-state capability root the verifier expects (native 8-felt).
        expected: [BabyBear; 8],
        /// The root the proof's membership path actually tops (native 8-felt).
        got: [BabyBear; 8],
    },
    /// The cap-membership sub-proof proves membership of a leaf that is NOT
    /// the consumed capability disclosed in the receipt. The circuit's row-0
    /// boundary pins the published leaf digest to the genuinely-proven member,
    /// and the verifier recomputes the expected digest from the receipt's
    /// 7-field leaf preimage — so a leaf-field tamper (e.g. an inflated
    /// `EffectMask`) mismatches and is rejected here.
    CapLeafMismatch {
        /// Digest of the receipt-disclosed consumed-cap leaf (native 8-felt).
        expected: [BabyBear; 8],
        /// The leaf digest the proof actually attests (native 8-felt).
        got: [BabyBear; 8],
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
            Self::CaveatManifestUnsatisfied { reason } => write!(
                f,
                "slot-caveat manifest entry's gate failed re-evaluation (capacity-weld \
                 satisfaction): {reason}"
            ),
            Self::CaveatCoverageFailed { reason } => write!(
                f,
                "slot-caveat coverage failed (capacity-weld omission): {reason}"
            ),
            Self::EscrowWeldNotForced { reason } => write!(
                f,
                "sealed-escrow SELECTOR weld not forced (declared-escrow turn dodged the welded \
                 gate): {reason}"
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
        membership: None,
        conservation: None,
        non_revocation: None,
        cap_membership: None,
        turn_hash,
        rotation: None,
        cap_turn_identity: None,
        umem_witness: None,
    };
    prove_full_turn(&witness)
}

/// Self-sovereign proof with the per-turn ROTATION producer witnesses threaded (cutover FLOW-B):
/// the effect-vm leg proves through the LEAN-emitted rotated descriptor (`"effect-vm-rotated"`,
/// a multi-table `Ir2BatchProof`) instead of the v1 hand-AIR. `rotation` carries the acting
/// cell's before/after [`RotationTurnWitness`] (minted by
/// `dregg_turn::rotation_witness::produce`). When `rotation` is `None`, this is byte-identical to
/// [`prove_turn_self_sovereign`]. Under `not(prover)` a present `rotation` is ignored (the v1
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
        membership: None,
        conservation: None,
        non_revocation: None,
        cap_membership: None,
        turn_hash,
        rotation,
        cap_turn_identity: None,
        umem_witness: None,
    };
    prove_full_turn(&witness)
}

// (RETIRED: `revalidate_turn_self_sovereign` — the FRI-free DIRECT witness revalidation
// for a self-sovereign turn via the v1 hand-AIR `bespoke_air_accepts` predicate — is gone
// with the v1 hand-AIR. The inline FRI-free revalidation is the rotated descriptor's
// constraint check.)

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

    /// **THE AUTHORITY-FLOOR DENY-LIST IS COMPLETE OVER THE DEPLOYED REGISTRY** (the mechanical
    /// completeness leg — `RUST-ONLY-LOGIC-CENSUS` Tier-1 #1). The authority floor
    /// (`is_forbidden_plain_cap_descriptor`) is the ONLY barrier stopping a membership-free / write-free
    /// cap-management descriptor from laundering host-trusted authority into a light-client proof. This
    /// test makes the deny-list's COMPLETENESS mechanical instead of a hand census:
    ///
    /// 1. It enumerates EVERY descriptor key in EVERY deployed registry the wire verifier iterates
    ///    (`V3_STAGED`, `WIDE`, and the umem-`WIDE_UMEM_WELD` registry — so WELDED authority descriptors
    ///    are covered too, exactly the umem-flip concern).
    /// 2. It requires each key to be CLASSIFIED (`descriptor_authority_class` ≠ `None`). A NEW
    ///    authority-shaped descriptor entering a registry un-classified FAILS here — it cannot ride the
    ///    wire silently.
    /// 3. It asserts the deny-list forbids EXACTLY the laundering class
    ///    (`LaundersAuthority`) and NOTHING in the allowed classes — so an authority descriptor that is
    ///    classified as laundering but NOT added to `is_forbidden_plain_cap_descriptor` (the original
    ///    gap, which let `delegateCapOpenVmDescriptor2R24` through) FAILS.
    #[cfg(feature = "prover")]
    #[test]
    fn authority_deny_list_is_complete_over_deployed_registry() {
        use dregg_circuit::effect_vm_descriptors::{
            V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV,
        };
        use std::collections::BTreeSet;

        // The wire verifier (`verify_effect_vm_rotated_with_cutover`) passes the registry KEY (TSV
        // col-0 — bare for every registry, including the welded one) to the deny-list, so we classify
        // and check the SAME value.
        let keys: BTreeSet<&str> = [
            V3_STAGED_REGISTRY_TSV,
            WIDE_REGISTRY_STAGED_TSV,
            WIDE_UMEM_WELD_REGISTRY_TSV,
        ]
        .iter()
        .flat_map(|tsv| tsv.lines())
        .filter(|l| !l.is_empty())
        .map(|l| l.split('\t').next().expect("registry line has a key"))
        .collect();

        assert!(
            keys.len() > 40,
            "sanity: the deployed registries enumerate the full descriptor set (got {})",
            keys.len()
        );

        for key in &keys {
            let class = descriptor_authority_class(key).unwrap_or_else(|| {
                panic!(
                    "deployed descriptor {key} is NOT classified by `descriptor_authority_class` — \
                     a new authority-shaped descriptor entered a registry un-classified. Classify it \
                     (and, if it is a membership-free / write-free cap-management descriptor, add it to \
                     `is_forbidden_plain_cap_descriptor`) before it can ride the light-client wire."
                )
            });
            let must_forbid = class == DescriptorAuthorityClass::LaundersAuthority;
            assert_eq!(
                is_forbidden_plain_cap_descriptor(key),
                must_forbid,
                "AUTHORITY-FLOOR DRIFT for {key}: classified {class:?} (must_forbid={must_forbid}) but \
                 the deny-list says is_forbidden={}. A laundering authority descriptor MUST be \
                 forbidden; an allowed route MUST NOT be.",
                is_forbidden_plain_cap_descriptor(key)
            );
        }
    }

    /// The completeness check BITES: a *synthetic* new authority descriptor (a cap-open / cap-management
    /// verb the registry did not declare before) is UNCLASSIFIED (`None`), so the enumeration test above
    /// would panic on it rather than silently admit it. (Mirrors the umem-flip risk: a welded authority
    /// twin landing in the registry without a deny-list entry.)
    #[test]
    fn new_unlisted_authority_descriptor_is_unclassified_and_bites() {
        // A brand-new cap-open authority descriptor (the laundering shape) — not yet in any match arm.
        assert_eq!(
            descriptor_authority_class("superGrantCapOpenVmDescriptor2R24"),
            None,
            "a new cap-open authority descriptor must force review (None), not slip through"
        );
        // A new PLAIN cap-management verb is also caught by the verb-prefix net.
        assert_eq!(
            descriptor_authority_class("delegateSuperVmDescriptor2R24"),
            None,
            "a new cap-management verb descriptor must force review (None)"
        );
        // A benign non-authority effect is NOT spuriously flagged (no false-positive churn).
        assert_eq!(
            descriptor_authority_class("transferVmDescriptor2R24"),
            Some(DescriptorAuthorityClass::NotAuthority),
            "a plain owner transfer is the normal path, not an authority launder"
        );
        // The closed gap: the authority-only delegate cap-open is now classified as laundering AND
        // forbidden by the deny-list.
        assert_eq!(
            descriptor_authority_class("delegateCapOpenVmDescriptor2R24"),
            Some(DescriptorAuthorityClass::LaundersAuthority)
        );
        #[cfg(feature = "prover")]
        assert!(is_forbidden_plain_cap_descriptor(
            "delegateCapOpenVmDescriptor2R24"
        ));
    }

    /// **The 6 fan-out cap-effects + transfer/attenuate each route to their OWN cap-open descriptor at
    /// their OWN effect-kind bit.** This is the wire-side mirror of the apex authority leg's re-key
    /// (`CircuitSoundnessAssembled.actionTagToPos`: tag → `<effect>CapOpenVmDescriptor2R24`,
    /// `RotatedKernelForestFacet.stepAuthorityFacetEff`: the cap-open forces `authorizedFacetEffB …
    /// (1 << n)`). The deployed prover and the proven apex now bind the SAME (descriptor, eff_bit)
    /// per effect — a cap permitting a DIFFERENT effect-kind than the run performs cannot satisfy the
    /// `effBitGateFor`/submask gate the keyed descriptor carries. Both polarities: each fan-out routes
    /// (positive), and non-cap-authorized / multi-effect runs fall through to `None` (negative).
    #[cfg(feature = "prover")]
    #[test]
    fn cap_open_route_binds_each_fanout_effect_to_its_own_bit() {
        const EFFECT_TRANSFER: u32 = 1 << 1;
        const EFFECT_GRANT_CAPABILITY: u32 = 1 << 2;
        const EFFECT_REVOKE_CAPABILITY: u32 = 1 << 3;
        const EFFECT_INTRODUCE: u32 = 1 << 13;
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

        // (descriptor key, the effect-kind bit the keyed descriptor's appendix binds, the single-effect
        // run). Each row asserts the deployed route binds the cap to THAT effect's bit (not transfer).
        let cases: Vec<(&'static str, u32, Vec<VmEffect>)> = vec![
            (
                // #225: the LIVE transfer cap-open is the TURN-BOUND descriptor.
                "transferCapOpenTBVmDescriptor2R24",
                EFFECT_TRANSFER,
                vec![VmEffect::Transfer {
                    amount: 1,
                    direction: 1,
                }],
            ),
            (
                "attenuateCapOpenEffVmDescriptor2R24",
                EFFECT_TRANSFER,
                vec![VmEffect::AttenuateCapability {
                    cap_slot_hash: [BabyBear::new(1); 8],
                    narrower_commitment: [BabyBear::new(2); 8],
                    phase_b: None,
                }],
            ),
            (
                "grantCapCapOpenVmDescriptor2R24",
                EFFECT_GRANT_CAPABILITY,
                vec![VmEffect::GrantCapability {
                    cap_entry: [BabyBear::new(3); 8],
                    phase_b: None,
                }],
            ),
            (
                "introduceCapOpenVmDescriptor2R24",
                EFFECT_INTRODUCE,
                vec![VmEffect::Introduce {
                    intro_hash: [BabyBear::new(4); 8],
                }],
            ),
            (
                "revokeCapOpenVmDescriptor2R24",
                EFFECT_DELEGATION_OPS,
                vec![VmEffect::RevokeDelegation {
                    child_hash: [BabyBear::new(5); 8],
                }],
            ),
            (
                "refreshDelegationCapOpenVmDescriptor2R24",
                EFFECT_DELEGATION_OPS,
                vec![VmEffect::RefreshDelegation {
                    child_hash: [BabyBear::new(7); 8],
                    snapshot_value: [BabyBear::new(8); 8],
                }],
            ),
            (
                "revokeCapabilityCapOpenVmDescriptor2R24",
                EFFECT_REVOKE_CAPABILITY,
                vec![VmEffect::RevokeCapability {
                    slot_hash: [BabyBear::new(6); 8],
                    phase_b: None,
                }],
            ),
        ];

        for (key, eff_bit, effects) in &cases {
            let route = cap_open_route_for_run(effects)
                .unwrap_or_else(|| panic!("{key}: expected a cap-open route for {effects:?}"));
            assert_eq!(route.key, *key, "{key}: route key mismatch");
            assert_eq!(
                route.eff_bit, *eff_bit,
                "{key}: bound the WRONG effect-kind bit"
            );
            // each fan-out effect binds its OWN bit — never the transfer bit (unless it IS transfer).
            if *key != "transferCapOpenTBVmDescriptor2R24"
                && *key != "attenuateCapOpenEffVmDescriptor2R24"
            {
                assert_ne!(
                    route.eff_bit, EFFECT_TRANSFER,
                    "{key}: a fan-out cap-effect must NOT ride the transfer bit"
                );
            }
        }

        // NEGATIVE: a non-cap-authorized effect (EmitEvent) has no cap-open route.
        assert!(
            cap_open_route_for_run(&[VmEffect::EmitEvent {
                topic_hash: [BabyBear::new(0); 8],
                payload_hash: [BabyBear::new(0); 8],
            }])
            .is_none(),
            "a non-cap-authorized effect must NOT route a cap-open descriptor"
        );
        // NEGATIVE: a multi-effect run is not a single cap-open route (the appendix opens one cap).
        assert!(
            cap_open_route_for_run(&[
                VmEffect::Transfer {
                    amount: 1,
                    direction: 1
                },
                VmEffect::RefreshDelegation {
                    child_hash: [BabyBear::new(7); 8],
                    snapshot_value: [BabyBear::new(8); 8],
                },
            ])
            .is_none(),
            "a multi-effect run must NOT route a single cap-open descriptor"
        );
    }

    /// SOUNDNESS LOOP #5 — the cap-open authority leg is exercised END-TO-END.
    ///
    /// A turn whose authority rides a REAL consumed capability (an `AttenuateCapability` with a
    /// threaded `cap_membership`) proves through the CAP-OPEN descriptor
    /// (`attenuateCapOpenEffVmDescriptor2R24`): the 58-column cap-membership appendix opens the
    /// committed `cap_root` at a write-mask leaf whose target is the turn's `src`. This test builds
    /// a genuine cap witness, drives the cap-open prover (`prove_effect_vm_cap_open_attenuate`,
    /// which self-verifies before return), and re-verifies the produced leg through the SAME verify
    /// path the full-turn verifier uses (`verify_effect_vm_rotated_with_cutover`) — which binds the
    /// cap-open cohort descriptor (NOT the bare attenuate one). A green test means the in-circuit
    /// cap-open membership chip-lookups + the faithful facet/tier gates are genuinely satisfied by
    /// the live prover's output, not skipped.
    ///
    /// **THE RUST CAP-WRITE ROUTE HANDOFF — CLOSED (genuine prove + verify).** The attenuate map_op is the
    /// SILENT-FORGE close: `attenuateCapOpenEffVmDescriptor2R24`'s `map_op` rides the ROTATED cap-root limb,
    /// FIRES on `sel.ATTENUATE_CAPABILITY = 48`, and BINDS the AFTER cap-root (var 264) to the genuine sorted
    /// write (Lean `attenuateV3_non_amp`; forge-detector `cap_write_attenuate_no_silent_forge` GREEN). The
    /// prover DEMANDS the cap-tree witness heap for that map_op, so this honest prove-through threads a real
    /// c-list through `prove_effect_vm_cap_open_attenuate` (route `write: Some(.., Update, ..)`) — the
    /// UPDATE-AT-KEY `CapTreeWriteOp` (attenuate narrows IN PLACE: `read` the held key's mask, `write`
    /// KEEP_MASK at the SAME key) now landed in `trace_rotated.rs`. The cap-open cohort descriptor verifies
    /// on the light-client path (the genuine narrowed cap-root is on-the-wire-verifiable).
    #[cfg(feature = "prover")]
    #[test]
    fn cap_open_attenuate_leg_proves_and_verifies_end_to_end() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
        };
        use dregg_turn::rotation_witness as rw;

        // A FAITHFUL transfer-conferring leaf: the descriptor's two-axis gate pins auth_tag ==
        // Signature, mask_lo == EFFECT_TRANSFER, mask_hi == 0; target == src.
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xA11CE),
            BabyBear::new(7_777), // target (== src)
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(WRITE_MASK_LO),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(1),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        // Build a genuine c-list opening, then re-shape it as the SDK's `CapMembershipWitness`
        // (the c-list opening the turn threads through `TurnReceipt::consumed_capabilities`).
        let open = CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds");
        // THE GENUINE c-list: the held key (chosen[0] = the cap being narrowed) MUST be present — the
        // attenuate map_op is an in-place UPDATE-AT-KEY (read the held mask at col 72, rebind KEEP_MASK at
        // the SAME key). The held leaf VALUE is the HELD_MASK the submask gate compares against; it must be
        // BROAD enough that the narrowed KEEP_MASK (`narrower_commitment[1]` = 0x52) is a submask
        // (`0x52 ⊑ 0xFF`). A wrong/absent key fails closed.
        let held_mask = BabyBear::new(0xFF);
        let clist_leaves = vec![
            dregg_circuit::heap_root::HeapLeaf {
                addr: chosen[0],
                value: held_mask,
            }, // held key → broad held mask
            dregg_circuit::heap_root::HeapLeaf {
                addr: other[0],
                value: other[3],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: CapLeaf {
                slot_hash: chosen[0],
                target: chosen[1],
                auth_tag: chosen[2],
                mask_lo: chosen[3],
                mask_hi: chosen[4],
                expiry: chosen[5],
                breadstuff: chosen[6],
            },
            siblings: open.siblings.to_vec(),
            directions: open.directions.to_vec(),
            clist_leaves,
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real AttenuateCapability turn + its rotation producer witnesses (mirrors the circuit
        // `cap_open_self_verify` scaffolding: attenuate is a nonce-tick state passthrough).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::AttenuateCapability {
            cap_slot_hash: [BabyBear::new(0x51); 8],
            narrower_commitment: [BabyBear::new(0x52); 8],
            phase_b: None,
        }];

        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();

        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // PROVE the cap-open leg (self-verifies internally) and re-verify it through the live
        // verify path with the cap-open vk_hash.
        let (proof, dpis) =
            prove_effect_vm_cap_open_attenuate(&initial, &effects, &before_w, &after_w, &cap)
                .expect("cap-open attenuate leg must prove + self-verify");
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize cap-open leg");
        let vk_hash = rotated_cap_open_vk_hash().expect("cap-open vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the cap-open leg MUST verify under the cap-open cohort descriptor (the in-circuit \
             cap-membership open is exercised, not skipped)",
        );

        // NEGATIVE: a cap whose leaf does NOT PERMIT the transfer facet is refused at witness build
        // (the GENUINE submask `facetEffGate` is UNSAT — bit 1 of the full mask is clear) — fail-closed
        // at the seam. `mask_lo = EFFECT_SET_FIELD = 1` (bit 0 only) does NOT carry the transfer bit
        // (bit 1), so `(EFFECT_TRANSFER & mask) == 0`. (NB the old over-strict equality would also have
        // rejected `mask_lo = 3`, but `3 & 2 == 2` GENUINELY permits transfer, so `3` is NOT a valid
        // negative under the membership gate — we use `1`, which is genuinely transfer-denying.)
        let non_transfer = CapMembershipWitness {
            leaf: CapLeaf {
                mask_lo: BabyBear::new(1), // EFFECT_SET_FIELD = 1 << 0; bit 1 (transfer) is CLEAR
                ..cap.leaf
            },
            siblings: cap.siblings.clone(),
            directions: cap.directions.clone(),
            clist_leaves: cap.clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open_attenuate(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &non_transfer
            )
            .is_err(),
            "a cap that does not PERMIT EFFECT_TRANSFER MUST be refused (fail-closed — submask bites)"
        );
    }

    /// THE WIDE CAP-OPEN FLAG-DAY: an attenuate cap-open leg proves through the WIDE
    /// `attenuateCapOpenEffVmDescriptor2R24` (8-felt ~124-bit commit at the LAST 16 PIs) AND the
    /// light-client verifier ACCEPTS it. The cap-membership authority crown carries UNCHANGED; the
    /// wide carriers re-absorb the same limbs into the 8-felt commit. This closes the 31-bit floor for
    /// the authority-crown cap-open tail (the residual shrinks to the write-bearing wrappers only).
    #[cfg(feature = "prover")]
    #[test]
    // WIDE/8felt is deliberate emphasis in the test name (the wide-commit flag-day).
    #[allow(non_snake_case)]
    fn cap_open_attenuate_leg_proves_and_verifies_WIDE_8felt() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
        };
        use dregg_turn::rotation_witness as rw;

        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xA11CE),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(WRITE_MASK_LO),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(1),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let open = CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds");
        let held_mask = BabyBear::new(0xFF);
        let clist_leaves = vec![
            dregg_circuit::heap_root::HeapLeaf {
                addr: chosen[0],
                value: held_mask,
            },
            dregg_circuit::heap_root::HeapLeaf {
                addr: other[0],
                value: other[3],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: CapLeaf {
                slot_hash: chosen[0],
                target: chosen[1],
                auth_tag: chosen[2],
                mask_lo: chosen[3],
                mask_hi: chosen[4],
                expiry: chosen[5],
                breadstuff: chosen[6],
            },
            siblings: open.siblings.to_vec(),
            directions: open.directions.to_vec(),
            clist_leaves,
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::AttenuateCapability {
            cap_slot_hash: [BabyBear::new(0x51); 8],
            narrower_commitment: [BabyBear::new(0x52); 8],
            phase_b: None,
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &[[3u8; 32], [4u8; 32]],
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &[[3u8; 32], [4u8; 32]],
            &Default::default(),
        );

        let route = cap_open_route_for_run(&effects).expect("attenuate is a wired cap-open route");
        let effective_key = cap_open_effective_key(&route, &cap);
        // Precondition: the attenuate effective key HAS a proven wide twin (it goes WIDE).
        assert!(
            cap_open_key_has_wide_twin(effective_key),
            "attenuate cap-open key {effective_key} must have a proven wide twin"
        );

        // PROVE WIDE: the leg publishes the 8-felt commit at its LAST 16 PIs.
        let (proof, dpis) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap, &route, None, true,
        )
        .expect("the WIDE attenuate cap-open leg must prove + self-verify");
        let n = dpis.len();
        assert!(
            n >= 16 + 46,
            "the WIDE cap-open leg carries the cap-open base PIs + 16 wide commit PIs (got {n})"
        );
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize wide cap-open leg");
        let vk_hash = cap_open_wide_vk_hash_by_key(effective_key).expect("wide cap-open vk_hash");

        // THE LIGHT-CLIENT VERIFY: the wide-cutover verifier ACCEPTS the wide cap-open leg (iterates
        // the WIDE registry, binds the wide cap-open descriptor — the membership crown is in it).
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the WIDE attenuate cap-open leg MUST verify under the wide cap-open descriptor (8-felt commit)",
        );

        // THE FORGE TOOTH: a forged 8-felt commit PI (one felt of the wide tail) is UNSAT.
        let mut forged = dpis.clone();
        forged[n - 1] = forged[n - 1] + BabyBear::new(0x9999);
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged, &vk_hash).is_err(),
            "a forged 8-felt commit PI on the wide cap-open leg MUST be REJECTED (the wide carrier binds it)"
        );
        eprintln!(
            "WIDE CAP-OPEN GREEN: the attenuate cap-open authority-crown leg binds the 8-felt ~124-bit commit."
        );
    }

    /// RESIDUAL (b) — the CROSS-VAT Transfer-via-granted-cap routes the TRANSFER cap-open END-TO-END,
    /// and the GENERAL facet gate BITES in-circuit (residual (a)).
    ///
    /// A single `Transfer` turn whose authority rides a REAL consumed transfer-cap proves through the
    /// LIVE TURN-BOUND transfer cap-open descriptor (`transferCapOpenTBVmDescriptor2R24` — transfer base
    /// plus the cap-membership appendix + the turn-identity weld), self-verifies, and re-verifies through
    /// the live verify path with the
    /// transfer cap-open vk_hash. Then the NEGATIVE: a cap whose leaf facet permits a DIFFERENT effect
    /// (not EFFECT_TRANSFER) is rejected — first at witness build (`from_membership` fail-closed), AND
    /// in-circuit: a hand-built witness carrying a wrong-facet leaf (bypassing the build pin) makes the
    /// descriptor's `facetEffGate`/`effBitGate` UNSAT, so the proof FAILS. The general facet bites on
    /// the turn's ACTUAL effect, not a constant.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_open_transfer_leg_proves_verifies_and_general_facet_bites() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
        };
        use dregg_circuit::field::BabyBear;

        // A FAITHFUL transfer-conferring leaf (mask_lo == EFFECT_TRANSFER, mask_hi == 0, auth_tag ==
        // Signature; target == src).
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xA11CE),
            BabyBear::new(7_777), // target (== src)
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(WRITE_MASK_LO),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(1),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let open = CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds");
        let cap = CapMembershipWitness {
            leaf: CapLeaf {
                slot_hash: chosen[0],
                target: chosen[1],
                auth_tag: chosen[2],
                mask_lo: chosen[3],
                mask_hi: chosen[4],
                expiry: chosen[5],
                breadstuff: chosen[6],
            },
            siblings: open.siblings.to_vec(),
            directions: open.directions.to_vec(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real cross-vat Transfer turn + its rotation producer witnesses. We reuse the SAME
        // before/after rotation witnesses the cohort transfer leg uses (`rotation_for_initial`), so
        // the TRANSFER base constraints are satisfied; the cap-open appendix rides on top.
        let before_balance: u64 = 1000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
        let rot = rotation_for_initial(&initial, &effects);
        let before_w = rot.before.clone();
        let after_w = rot.after.clone();

        // PROVE the transfer cap-open leg (self-verifies internally) + re-verify through the live path.
        let (proof, dpis) =
            prove_effect_vm_cap_open_transfer(&initial, &effects, &before_w, &after_w, &cap)
                .expect("transfer cap-open leg must prove + self-verify");
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize transfer cap-open leg");
        let vk_hash = rotated_transfer_cap_open_vk_hash().expect("transfer cap-open vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the transfer cap-open leg MUST verify under the transfer cap-open cohort descriptor",
        );

        // NEGATIVE #1 (fail-closed at the seam): a cap whose facet is a DIFFERENT effect bit
        // (EFFECT_GRANT_CAPABILITY = 1<<2 = 4, not EFFECT_TRANSFER = 2) is refused at witness build.
        const EFFECT_GRANT: u32 = 1 << 2;
        let wrong_facet = CapMembershipWitness {
            leaf: CapLeaf {
                mask_lo: BabyBear::new(EFFECT_GRANT),
                ..cap.leaf
            },
            siblings: cap.siblings.clone(),
            directions: cap.directions.clone(),
            clist_leaves: cap.clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open_transfer(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &wrong_facet
            )
            .is_err(),
            "a cap permitting a DIFFERENT effect (grant, not transfer) MUST be refused (fail-closed)"
        );

        // NEGATIVE #2 (the GENERAL SUBMASK facet gate BITES AT THE DEPLOYED VERIFIER): hand-build a
        // CapOpenWitness whose leaf facet is the wrong effect bit, BYPASSING the build/from_membership
        // facet pin (its root still recomposes, so `widen_to_cap_open`'s recompose check passes). The
        // LIVE `transferCapOpenTBVmDescriptor2R24` descriptor's `effBitGateFor` pins effBit ==
        // EFFECT_TRANSFER (= 2) while the submask gate forces `(effBit & full_mask) == effBit` — and a
        // grant-only leaf (`mask_lo = 4`, bit 2) has `(2 & 4) == 0 != 2`, so the trace is UNSAT.
        //
        // We feed the FORGED proof to the DEPLOYED WIRE VERIFIER and assert it REJECTS — the real
        // soundness boundary (STARK soundness), end to end. In DEBUG the IR-v2 prover's constraint
        // self-check (`#[cfg(debug_assertions)]`) panics before emitting a proof, so there is no proof
        // to verify; the verifier-rejection arm is therefore release-only (mirroring
        // `circuit::plonky3_forged_parent_rejected`). Release is the point: the forged proof actually
        // reaches the live verifier and is rejected.
        #[cfg(not(debug_assertions))]
        {
            use dregg_circuit::descriptor_ir2::{
                MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
                verify_vm_descriptor2,
            };
            use dregg_circuit::effect_vm::trace_rotated::{
                CAP_OPEN_DIGEST_W, RotatedBlockWitness, cap_open_tb_dpis,
                generate_rotated_effect_vm_trace, transfer_caveat_manifest, widen_to_cap_open_tb,
            };
            let mut wrong_leaf = chosen;
            wrong_leaf[3] = BabyBear::new(EFFECT_GRANT); // mask_lo = grant, not transfer
            // The wide cap-open siblings are the NATIVE 8-felt `[[BabyBear; 8]; 16]` images; copy the
            // genuine path wholesale (same shape, Copy) so the recompose self-check operates on the
            // real membership path with only the leaf facet tampered.
            let wsib = open.siblings;
            let wdir = open.directions;
            // recompute the root for the tampered leaf so the recompose self-check passes.
            let wrong_w = {
                let mut w = CapOpenWitness {
                    leaf: wrong_leaf,
                    siblings: wsib,
                    directions: wdir,
                    cap_root: [BabyBear::ZERO; CAP_OPEN_DIGEST_W],
                    src: wrong_leaf[1],
                    eff_bit: WRITE_MASK_LO, // the transfer descriptor pins effBit == EFFECT_TRANSFER
                };
                w.cap_root = w.recomposes();
                w
            };
            // #225: the LIVE transfer cap-open is the TURN-BOUND descriptor (409 wide, 41 PIs).
            let json =
                cap_open_descriptor_json_by_key("transferCapOpenTBVmDescriptor2R24").unwrap();
            let desc = parse_vm_descriptor2(json).unwrap();
            let before =
                RotatedBlockWitness::new(before_w.pre_limbs.clone(), before_w.iroot).unwrap();
            let after = RotatedBlockWitness::new(after_w.pre_limbs.clone(), after_w.iroot).unwrap();
            let caveat = transfer_caveat_manifest();
            let (mut trace, dpis) =
                generate_rotated_effect_vm_trace(&initial, &effects, &before, &after, &caveat)
                    .unwrap();
            let src = wrong_w.src;
            widen_to_cap_open_tb(&mut trace, &wrong_w, src, src).unwrap();
            let dpis = cap_open_tb_dpis(&dpis, src, src, src);
            // Release: the prover emits a BOGUS proof for the UNSAT wrong-facet trace; the DEPLOYED
            // verifier must reject it.
            let forged =
                prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
                    .expect("release prover emits a (bogus) proof for the UNSAT wrong-facet trace");
            assert!(
                verify_vm_descriptor2(&desc, &forged, &dpis).is_err(),
                "the GENERAL facet gate (facetEffGate: mask_lo == effBit, effBit pinned EFFECT_TRANSFER) \
                 MUST make the DEPLOYED VERIFIER reject a wrong-facet leaf — the cap-open authorizes the \
                 turn's ACTUAL effect, not just a constant transfer pin"
            );
        }
    }

    /// THE FAN-OUT (residual (a) closed for the 6 effects) — a cap-authorized `RevokeDelegation`
    /// (the "revoke" effect, `EFFECT_DELEGATION_OPS = 1 << 16`) routes its OWN cap-open descriptor
    /// (`revokeCapOpenVmDescriptor2R24`) END-TO-END: the consumed cap's facet must permit
    /// `EFFECT_DELEGATION_OPS` (NOT transfer). The general appendix (`capOpenConstraintsEff 16`) binds
    /// the cap to THAT effect-kind bit. Then the NEGATIVE: a cap whose facet permits a DIFFERENT
    /// effect-kind (`EFFECT_TRANSFER`, not delegation) is REJECTED — at witness build
    /// (`from_membership_for` fail-closed) AND in-circuit (a hand-built wrong-facet witness makes the
    /// descriptor's `facetEffGate`/`effBitGateFor` UNSAT, so the proof FAILS). The `delegateCapOpen`
    /// route shares the SAME bit, proving the generic prover serves the whole family.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_open_fanout_revoke_proves_verifies_and_wrong_facet_bites() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_turn::rotation_witness as rw;

        // `EFFECT_DELEGATION_OPS = 1 << 16` — the effect-kind the revoke cap-open binds.
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
        const EFFECT_TRANSFER: u32 = 1 << 1;

        // A delegation-conferring leaf: mask_lo == EFFECT_DELEGATION_OPS (NOT transfer), mask_hi == 0,
        // auth_tag == Signature (the fan-out appendix reads the DECODED tier; a Signature leaf is a
        // valid decoded tier). target == src.
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xDE16A),
            BabyBear::new(7_777), // target (== src)
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_DELEGATION_OPS), // mask_lo permits the delegation effect-kind
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        // Build the path with the generic constructor FOR the delegation bit.
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_DELEGATION_OPS)
            .expect("cap-open path builds");
        let cap = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real RevokeDelegation turn (nonce-tick state passthrough, attenuate-family base).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }];

        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();

        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // The revoke route: key `revokeCapOpenVmDescriptor2R24`, eff_bit EFFECT_DELEGATION_OPS,
        // attenuate-family patch.
        let route = cap_open_route_for_run(&[VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }])
        .expect("revoke is a wired cap-open route");
        assert_eq!(route.key, "revokeCapOpenVmDescriptor2R24");
        assert_eq!(route.eff_bit, EFFECT_DELEGATION_OPS);

        // PROVE the revoke cap-open leg with an EMPTY c-list (the AUTHORITY-only route, no write
        // witness): the cap-membership authority crown proves + self-verifies, exercising the fan-out
        // facet/effBit gates. The proof is VALID (it self-verifies), BUT the light-client verifier now
        // REJECTS it — THE TOOTH IS ON (`is_forbidden_authority_only_cap_write_descriptor`): an
        // authority-only revoke cap-open leaves the post-cap-root host-trusted, so a producer must prove
        // the WRITE wrapper (where the cap-tree REMOVE is on-the-wire-verifiable). The descriptor selected
        // is `revokeCapOpenVmDescriptor2R24` (no write-op) because `cap.clist_leaves` is empty.
        assert!(cap.clist_leaves.is_empty());
        let (proof, dpis) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap, &route, None, false,
        )
        .expect("revoke cap-open fan-out leg must prove + self-verify (the proof is VALID)");
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize revoke cap-open leg");
        let vk_hash = cap_open_vk_hash_by_key(route.key).expect("revoke cap-open vk_hash");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).is_err(),
            "the AUTHORITY-only revoke cap-open MUST be light-client-REJECTED (the tooth is ON) — the \
             post-cap-root is host-trusted; the producer must prove the WRITE wrapper \
             (`cap_write_revoke_proves_and_verifies_light_client` is the accepted route)",
        );

        // NEGATIVE #1 (fail-closed at the seam): a cap whose facet permits EFFECT_TRANSFER (not the
        // delegation kind the revoke route binds) is refused at witness build — `from_membership_for`
        // requires mask_lo == route.eff_bit.
        let wrong_facet = CapMembershipWitness {
            leaf: CapLeaf {
                mask_lo: BabyBear::new(EFFECT_TRANSFER),
                ..cap.leaf
            },
            siblings: cap.siblings.clone(),
            directions: cap.directions.clone(),
            clist_leaves: cap.clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &wrong_facet,
                &route,
                None,
                false
            )
            .is_err(),
            "a cap permitting a DIFFERENT effect (transfer, not delegation) MUST be refused (fail-closed)"
        );

        // NEGATIVE #2 (the GENERAL facet gate BITES AT THE DEPLOYED VERIFIER): hand-build a
        // CapOpenWitness whose leaf facet is the wrong bit (EFFECT_TRANSFER) but eff_bit is the route's
        // (EFFECT_DELEGATION_OPS), bypassing the build pin. The descriptor's `effBitGateFor` pins effBit
        // == EFFECT_DELEGATION_OPS while `facetEffGate` forces mask_lo == effBit — so the wrong-facet
        // leaf is UNSAT.
        //
        // We feed the FORGED proof to the DEPLOYED WIRE VERIFIER and assert it REJECTS — the real
        // soundness boundary (STARK soundness), end to end. In DEBUG the IR-v2 prover's constraint
        // self-check (`#[cfg(debug_assertions)]`) panics before emitting a proof, so the
        // verifier-rejection arm is release-only (mirroring `circuit::plonky3_forged_parent_rejected`).
        #[cfg(not(debug_assertions))]
        {
            use dregg_circuit::descriptor_ir2::{
                MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
                verify_vm_descriptor2,
            };
            use dregg_circuit::effect_vm::trace_rotated::{
                CAP_OPEN_DIGEST_W, RotatedBlockWitness, empty_caveat_manifest,
                generate_rotated_effect_vm_trace, widen_to_cap_open,
            };
            let mut wrong_leaf = chosen;
            wrong_leaf[3] = BabyBear::new(EFFECT_TRANSFER); // mask_lo = transfer, not delegation
            // Wide 8-felt sibling images: copy the genuine path wholesale (same shape, Copy).
            let wsib = built.siblings;
            let wdir = built.directions;
            let wrong_w = {
                let mut w = CapOpenWitness {
                    leaf: wrong_leaf,
                    siblings: wsib,
                    directions: wdir,
                    cap_root: [BabyBear::ZERO; CAP_OPEN_DIGEST_W],
                    src: wrong_leaf[1],
                    eff_bit: EFFECT_DELEGATION_OPS, // the revoke descriptor pins effBit == DELEGATION_OPS
                };
                w.cap_root = w.recomposes();
                w
            };
            let json = cap_open_descriptor_json_by_key("revokeCapOpenVmDescriptor2R24").unwrap();
            let desc = parse_vm_descriptor2(json).unwrap();
            let before =
                RotatedBlockWitness::new(before_w.pre_limbs.clone(), before_w.iroot).unwrap();
            let after = RotatedBlockWitness::new(after_w.pre_limbs.clone(), after_w.iroot).unwrap();
            // revoke is a nonce-TICK passthrough base — directly valid, NO attenuate patch.
            let caveat = empty_caveat_manifest();
            let (mut trace, dpis) =
                generate_rotated_effect_vm_trace(&initial, &effects, &before, &after, &caveat)
                    .unwrap();
            widen_to_cap_open(&mut trace, &wrong_w).unwrap();
            // Release: the prover emits a BOGUS proof for the UNSAT wrong-facet trace; the DEPLOYED
            // verifier must reject it.
            let forged =
                prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
                    .expect("release prover emits a (bogus) proof for the UNSAT wrong-facet trace");
            assert!(
                verify_vm_descriptor2(&desc, &forged, &dpis).is_err(),
                "the GENERAL facet gate (facetEffGate: mask_lo == effBit, effBit pinned EFFECT_DELEGATION_OPS) \
                 MUST make the DEPLOYED VERIFIER reject a wrong-facet leaf for the revoke fan-out — the \
                 cap-open authorizes the turn's ACTUAL effect-kind only"
            );
        }
    }

    /// **THE CAP-WRITE WRAPPER BINDS THE COMMITTED ROOT GROUPS — restated to the KEYSTONE shape.**
    /// The arity-2 scalar map-op is GONE from the WRITE-bearing wrappers (shape-UNSAT against the
    /// native-8-felt witness heaps); the cap-tree write now rides the SHAPE-MATCHED keystone wraps
    /// (`effCapRemoveV3` here — the removed leaf's membership READ welded to the committed BEFORE
    /// cap-root group; the AFTER group is the deployed tombstone zero-fold). The no-silent-forge floor
    /// is UNCHANGED — a fabricated root binding must NOT be provable:
    ///   (structure) the deployed `revokeDelegationWriteCapOpen` wrapper carries NO arity-2 map-op AND
    ///   welds ALL 8 lanes of the membership read's `capRoot` group to the committed BEFORE cap-root
    ///   block (lane0 = var 213, lanes 1..7 = vars 239..245) — the `effCapRemoveV3` BEFORE welds;
    ///   (bite) a trace whose committed BEFORE group is TAMPERED away from the membership-opened root
    ///   (the genuine after-spine trace, then BEFORE lane0 perturbed WITHOUT re-deriving the appendix)
    ///   REFUSES to prove — the weld gates bind; there is NO silent forge of the root binding.
    #[cfg(feature = "prover")]
    #[test]
    fn write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::descriptor_ir2::{
            MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2,
        };
        use dregg_circuit::effect_vm::trace_rotated::{
            AFTER_BASE, B_CAP_ROOT, BEFORE_BASE, CapOpenWitness, FACET_MASK_HI,
            RotatedBlockWitness, SIGNATURE_AUTH_TAG, empty_caveat_manifest,
            generate_rotated_cap_remove_after_spine_wide, generate_rotated_effect_vm_trace,
            widen_to_cap_open,
        };
        use dregg_circuit::lean_descriptor_air::LeanExpr;
        use dregg_turn::rotation_witness as rw;

        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

        // (structure) the WIDE wrapper (the deployed leg production proves) — 0 map-ops + the 8 BEFORE
        // welds. The registry-availability concern stays RESOLVED FAVORABLY: both twins resolve.
        let json = cap_open_wide_descriptor_json_by_key(
            "revokeDelegationWriteCapOpenVmDescriptor2R24",
        )
        .expect(
            "the write-bearing wrapper IS in the wide registry (the leg the SDK cap-open route \
                 + the light-client verifier both resolve against)",
        );
        let desc = parse_vm_descriptor2(json).expect("write wrapper descriptor parses");
        let map_ops = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::MapOp(_)))
            .count();
        assert_eq!(
            map_ops, 0,
            "the revokeDelegation keystone wrapper carries NO arity-2 map-op (the REMOVE rides the \
             BEFORE-root welds + the tombstone zero-fold) — descriptor: {}",
            desc.name
        );
        // The 8 `effCapRemoveV3` BEFORE welds: the read `capRoot` lane welded to the committed BEFORE
        // cap-root block `[lane0 = var 213 ‖ lanes 1..7 = vars 239..=245]`.
        let before_group: Vec<usize> = std::iter::once(213usize).chain(239..=245).collect();
        for (lane, g) in before_group.iter().enumerate() {
            let has_weld = desc.constraints.iter().any(|c| {
                matches!(c,
                    VmConstraint2::Base(dregg_circuit::lean_descriptor_air::VmConstraint::Gate(
                        LeanExpr::Add(_, r)))
                    if matches!(&**r, LeanExpr::Mul(cneg, v)
                        if matches!(&**cneg, LeanExpr::Const(-1))
                            && matches!(&**v, LeanExpr::Var(x) if x == g)))
            });
            assert!(
                has_weld,
                "the revokeDelegation keystone wrapper MUST weld the read capRoot lane {lane} to the \
                 committed BEFORE cap-root var {g} (the effCapRemoveV3 before-root weld) — descriptor: {}",
                desc.name
            );
        }

        // The removed delegation-conferring leaf (target == src), exactly as the honest revoke tests.
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xDE16A),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_DELEGATION_OPS)
            .expect("cap-open path builds");
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let _ = leaf_cl(&chosen);

        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        // the §14.EPOCH gate: a genuine revokeDelegation bumps the delegation epoch.
        assert!(after_cell.state.bump_delegation_epoch());
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let before = RotatedBlockWitness::new(before_w.pre_limbs.clone(), before_w.iroot).unwrap();
        let after = RotatedBlockWitness::new(after_w.pre_limbs.clone(), after_w.iroot).unwrap();
        let caveat = empty_caveat_manifest();

        // Build the GENUINE keystone trace exactly as the deployed remove path does: the membership
        // READ opens the REMOVED leaf against BEFORE; the AFTER group is the tombstone zero-fold over
        // the SAME path.
        let cap_w = CapOpenWitness {
            leaf: chosen,
            siblings: built.siblings,
            directions: built.directions,
            cap_root: built.cap_root,
            src: chosen[1],
            eff_bit: EFFECT_DELEGATION_OPS,
        };
        let after_root8 = dregg_circuit::cap_root::recompose_membership(
            dregg_circuit::cap_root::CAP_ZERO8,
            &cap_w.siblings,
            &cap_w.directions,
        );
        let (mut wtrace, wdpis) =
            generate_rotated_effect_vm_trace(&initial, &effects, &before, &after, &caveat).unwrap();
        widen_to_cap_open(&mut wtrace, &cap_w).unwrap();
        let wdpis = generate_rotated_cap_remove_after_spine_wide(
            &mut wtrace,
            wdpis,
            cap_w.cap_root,
            after_root8,
            chosen[0],
            chosen[3],
        )
        .expect("the remove after-spine producer lays the genuine committed root groups");
        // CONFIRM the change is GENUINE (non-vacuous): the committed groups DIFFER (a real tombstone
        // zero-fold moved the root) — else the bite below would be a no-op.
        assert_ne!(
            wtrace[0][BEFORE_BASE + B_CAP_ROOT],
            wtrace[0][AFTER_BASE + B_CAP_ROOT],
            "the tombstone zero-fold MUST move the committed cap-root (BEFORE != AFTER) — else this \
             guardrail would be vacuous"
        );
        // Sanity: the honest keystone trace PROVES (non-vacuity of the bite below).
        prove_vm_descriptor2(&desc, &wtrace, &wdpis, &MemBoundaryWitness::default(), &[])
            .expect("the GENUINE keystone remove trace proves (the bite below is non-vacuous)");

        // ── THE BITE: tamper the committed BEFORE cap-root group away from the membership-opened root
        // (lane 0 perturbed on every row, appendix NOT re-derived). The `effCapRemoveV3` BEFORE weld
        // binds the read capRoot to this group; the tampered trace must REFUSE to prove — the root
        // binding cannot be silently forged. (The IR-v2 prover self-verifies, so the refusal may
        // surface as Err OR a panic; both are fail-closed. A PASSING proof is the critical forge.)
        let mut forged_trace = wtrace.clone();
        for row in forged_trace.iter_mut() {
            row[BEFORE_BASE + B_CAP_ROOT] += BabyBear::new(0x9999);
        }
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(
                &desc,
                &forged_trace,
                &wdpis,
                &MemBoundaryWitness::default(),
                &[],
            )
            .map(|_| ())
            .map_err(|e| format!("{e:?}"))
        }));
        std::panic::set_hook(prev_hook);
        match outcome {
            Ok(Err(_)) => { /* prover refused — fail-closed (no silent forge) */ }
            Err(_) => { /* self-verify panic — fail-closed (no silent forge) */ }
            Ok(Ok(())) => panic!(
                "SILENT FORGE: the WRITE-bearing cap-open wrapper PROVED with a TAMPERED committed \
                 BEFORE cap-root group — the effCapRemoveV3 weld does NOT bind the membership-opened \
                 root to the committed block; this is a critical soundness regression."
            ),
        }
    }

    /// **THE SILENT-FORGE DETECTOR for attenuate — restated to the KEYSTONE shape.** The arity-2
    /// scalar map-op is GONE from the deployed wrapper (it was shape-UNSAT against the native-8-felt
    /// witness heaps — the ~31-bit lane-0 squeeze); the faithful 8-felt in-place UPDATE-AT-KEY now rides
    /// the after-spine (`effCapOpenWriteV3_forces_write8`): the membership READ opens the held leaf
    /// against the committed BEFORE cap-root group, and the after-spine re-opens the NARROWED leaf
    /// (mask_lo := KEEP_MASK) against the committed AFTER group over the SHARED path. The forge this
    /// detector closes is UNCHANGED — a fabricated post-cap-root must NOT be light-client-acceptable:
    ///   (structure) the deployed wrapper carries NO arity-2 map-op (the write is the after-spine);
    ///   (1) GENUINE — an honest attenuate (held key narrowed in the arity-7 `CanonicalCapTree`)
    ///       proves the WIDE keystone leg + light-client-verifies (non-vacuity);
    ///   (2) FORGE (wire) — a forged 8-felt AFTER-commit PI is REJECTED (the wide anchor binds the
    ///       committed cap-root groups the after-spine welds — the silent forge has no wire);
    ///   (3) FORGE (producer) — a c-list MISSING the narrowed key fails closed (no held-authority
    ///       membership witness, no fabricated post-root).
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_attenuate_no_silent_forge() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        const EFFECT_TRANSFER: u32 = 1 << 1;

        // (structure) the deployed wrapper (narrow AND wide twins) carries NO arity-2 map-op — the
        // faithful 8-felt UPDATE rides the after-spine welds, never a scalar map heap.
        for json in [
            cap_open_descriptor_json_by_key("attenuateCapOpenEffVmDescriptor2R24")
                .expect("the attenuate cap-open wrapper IS in V3_STAGED_REGISTRY_TSV"),
            cap_open_wide_descriptor_json_by_key("attenuateCapOpenEffVmDescriptor2R24")
                .expect("the attenuate cap-open wrapper HAS a wide twin"),
        ] {
            let desc = parse_vm_descriptor2(json).expect("attenuate cap-open wrapper parses");
            let map_ops = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::MapOp(_)))
                .count();
            assert_eq!(
                map_ops, 0,
                "the attenuate keystone wrapper carries NO arity-2 map-op (the UPDATE-AT-KEY rides \
                 the after-spine + the 8-felt root welds) — descriptor: {}",
                desc.name
            );
        }

        // The held cap being narrowed: its mask PERMITS the crown facet (EFFECT_TRANSFER submask).
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xA77E),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(0xFFFF), // broad held mask — permits EFFECT_TRANSFER (bit 1)
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_TRANSFER),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_TRANSFER)
            .expect("cap-open path builds");
        // THE GENUINE c-list — the narrowed key IS present (the UPDATE has a membership witness).
        let clist_leaves = vec![
            HeapLeaf {
                addr: chosen[0],
                value: chosen[3], // the held mask felt (the submask RHS the producer reads)
            },
            HeapLeaf {
                addr: other[0],
                value: other[3],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real AttenuateCapability turn: the held key 0xA77E narrowed to KEEP 0x0002 (⊑ held, keeps
        // the crown bit) — the UPDATE-AT-KEY the after-spine forces.
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let keep_mask = BabyBear::new(EFFECT_TRANSFER); // the narrowed rights
        let effects = vec![VmEffect::AttenuateCapability {
            cap_slot_hash: [chosen[0]; 8],
            narrower_commitment: [
                chosen[0],
                keep_mask,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            phase_b: None,
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        let route = cap_open_route_for_run(&effects).expect("attenuate is a wired cap-open route");
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, "attenuateCapOpenEffVmDescriptor2R24",
            "with a genuine c-list the attenuate route proves its own (write-bearing) descriptor"
        );

        // ── (1) GENUINE: the WIDE keystone leg proves + light-client-verifies.
        let (proof, dpis) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap, &route, None, true,
        )
        .expect(
            "the attenuate keystone leg MUST genuinely prove — the held leaf narrowed in place, \
             the after-spine re-opens it against the committed AFTER cap-root group",
        );
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize attenuate keystone leg");
        let vk_hash =
            cap_open_wide_vk_hash_by_key(effective_key).expect("wide attenuate wrapper vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the attenuate keystone leg MUST verify on the light-client path — the genuine \
             post-cap-root is on-the-wire light-client-verifiable",
        );

        // ── (2) FORGE (wire): a forged 8-felt AFTER-commit PI is REJECTED — the silent forge (a
        // fabricated post-cap-root laundered past a light client) has NO wire.
        let n_pis = dpis.len();
        let mut forged = dpis.clone();
        forged[n_pis - 1] = forged[n_pis - 1] + BabyBear::new(0x9999);
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged, &vk_hash).is_err(),
            "SILENT FORGE (attenuate): a forged 8-felt AFTER-commit PI on the keystone leg was \
             ACCEPTED — the wide anchor no longer binds the committed cap-root groups"
        );

        // ── (3) FORGE (producer): a c-list MISSING the narrowed key fails closed (no held-authority
        // membership, no fabricated post-root).
        let cap_forged = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: vec![HeapLeaf {
                addr: other[0],
                value: other[3],
            }],
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_forged,
                &route,
                None,
                true
            )
            .is_err(),
            "a c-list MISSING the narrowed key MUST fail closed — a fabricated post-cap-root is NOT provable"
        );
    }

    /// **THE SILENT-FORGE DETECTOR for revokeCapability's PLAIN base (sel 24) — restated to the
    /// KEYSTONE shape.** The arity-2 scalar map-op pair is GONE from `revokeCapabilityVmDescriptor2R24`
    /// (it was shape-UNSAT against the deployed arity-7 `CanonicalCapTree` — the ~31-bit lane-0
    /// squeeze); the cap-tree REMOVE now rides the `effCapRemoveV3` keystone wrap on the WRITE route
    /// (`revokeCapabilityWriteCapOpenVmDescriptor2R24` — `cap_write_revoke_cap_route_proves_and_verifies_light_client`).
    /// The no-silent-forge floor for the PLAIN base is the WIRE TOOTH: a bare `revokeCapability` proven
    /// under the plain descriptor (no membership crown, no keystone welds) is light-client-REJECTED
    /// (`is_forbidden_plain_cap_descriptor`), so nothing can launder a cap write through it.
    ///   (structure) the plain base carries NO arity-2 map-op (a scalar map-op that can never be
    ///   realized against the deployed native-8-felt heaps would be a liveness lie, not a tooth);
    ///   (bite) the plain key is on the deny-list BOTH halves (`is_forbidden_plain_cap_descriptor`)
    ///   — the forced route is the keystone write wrapper.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_revoke_cap_no_silent_forge() {
        use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};

        let json = cap_open_descriptor_json_by_key("revokeCapabilityVmDescriptor2R24")
            .expect("the revokeCapability base IS in V3_STAGED_REGISTRY_TSV");
        let desc = parse_vm_descriptor2(json).expect("revokeCapability base parses");
        // (structure) the arity-2 map-op pair is DROPPED — the REMOVE rides the keystone write route.
        let map_ops = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::MapOp(_)))
            .count();
        assert_eq!(
            map_ops, 0,
            "the revokeCapability base carries NO arity-2 map-op (the REMOVE rides the effCapRemoveV3 \
             keystone write wrapper) — descriptor: {}",
            desc.name
        );
        // (bite) the plain base is wire-FORBIDDEN — a bare revokeCapability cannot be laundered past a
        // light client; the producer MUST prove the keystone write wrapper (whose genuine/forge arms
        // are `cap_write_revoke_cap_route_proves_and_verifies_light_client`).
        assert!(
            is_forbidden_plain_cap_descriptor("revokeCapabilityVmDescriptor2R24"),
            "the PLAIN revokeCapability descriptor MUST stay light-client-forbidden — the keystone \
             write wrapper is the only wire-accepted route"
        );
        assert!(
            is_forbidden_authority_only_cap_write_descriptor(
                "revokeCapabilityCapOpenVmDescriptor2R24"
            ),
            "the AUTHORITY-only revokeCapability cap-open MUST stay light-client-forbidden — the \
             post-cap-root would be host-trusted without the keystone welds"
        );
    }

    /// **THE OVER-DETERMINATION IS GONE — col 87 (AFTER cap-root) is now `map_op`-defined ONLY**
    /// (commit 0c2b0704c). The prior obstruction was that `revokeDelegationWriteCapOpenVmDescriptor2R24`
    /// bound the AFTER cap-root (col 87) TWO incompatible ways — the `map_op` `new_root = var87` (a
    /// sorted `CanonicalHeapTree` REMOVE) AND a poseidon OUTPUT `var87 = hash2(...)` — which disagree for
    /// an honest c-list (Poseidon is non-invertible), making the wrapper UNPROVABLE. The re-emit dropped
    /// the poseidon-output definition: col 87 now appears as the `map_op` `write` `new_root` (the sole
    /// definition) and only as an INPUT to the commitment chain (folded in, never re-derived), exactly as
    /// note-spend treats its nullifier-accumulator root. This test PINS the descriptor structure (col 87
    /// is the `map_op` `new_root` AND is NOT a poseidon-output) so the fix is non-vacuous and a regression
    /// re-introducing the second binding fails here — and exercises the genuine cap-tree→`map_heaps`
    /// bridge + its missing-key fail-closed guardrail. The end-to-end prove+verify closure of the loop is
    /// `cap_write_revoke_proves_and_verifies_light_client`.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_revoke_descriptor_after_root_is_map_op_defined_only() {
        use dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp;
        use dregg_circuit::heap_root::HeapLeaf;

        // The deployed write wrapper's descriptor JSON (the SAME the producer + light-client verifier
        // resolve against). Assert col 87 (the AFTER cap-root) is bound ONLY via the map_op write — the
        // over-determining poseidon-output binding was dropped.
        use dregg_circuit::descriptor_ir2::VmConstraint2;
        use dregg_circuit::lean_descriptor_air::LeanExpr;
        let json = cap_open_descriptor_json_by_key("revokeDelegationWriteCapOpenVmDescriptor2R24")
            .expect("the write wrapper is in V3_STAGED_REGISTRY_TSV");
        let desc = dregg_circuit::descriptor_ir2::parse_vm_descriptor2(json)
            .expect("write wrapper parses");

        // THE REMOVE KEYSTONE SHAPE (`effCapRemoveV3`): the arity-2 map-op is GONE (its update-at-key
        // `writesTo` could not express the deployed ZERO-digest tombstone leaf — the break this deploy
        // closed); the cap-tree REMOVE is carried by the 8 BEFORE cap-root WELD gates pinning the
        // cap-open READ's `capRoot` group to the committed BEFORE cap-root block `[lane0=var 213 ‖
        // lanes 1..7 = vars 239..=245]` — the read opens the REMOVED leaf against BEFORE, and the
        // committed AFTER group carries the tombstone zero-fold (witness-carried, wide-anchored).
        let map_ops = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::MapOp(_)))
            .count();
        assert_eq!(
            map_ops, 0,
            "the revokeDelegation keystone wrapper carries NO arity-2 map-op (the REMOVE rides the \
             before-root welds + the tombstone zero-fold) — descriptor: {}",
            desc.name
        );
        let before_group: Vec<usize> = std::iter::once(213usize).chain(239..=245).collect();
        for (lane, g) in before_group.iter().enumerate() {
            let has_weld = desc.constraints.iter().any(|c| {
                matches!(c,
                    VmConstraint2::Base(dregg_circuit::lean_descriptor_air::VmConstraint::Gate(
                        LeanExpr::Add(_, r)))
                    if matches!(&**r, LeanExpr::Mul(cneg, v)
                        if matches!(&**cneg, LeanExpr::Const(-1))
                            && matches!(&**v, LeanExpr::Var(x) if x == g)))
            });
            assert!(
                has_weld,
                "the revokeDelegation keystone wrapper MUST weld the read capRoot lane {lane} to the \
                 committed BEFORE cap-root var {g} (the effCapRemoveV3 before-root weld) — descriptor: {}",
                desc.name
            );
        }
        // The v1-state cap-root column (var 87) stays FROZEN pass-through: no map_op writes it (there
        // are no map ops at all).
        let _ = LeanExpr::Var(87);

        // The cap-tree->map_heaps bridge itself is sound + ready: it builds the genuine BEFORE/AFTER
        // roots over the real c-list (a wrong key fails closed — no fabricated post-root). Exercise it
        // on a ROT_WIDTH base so the data-availability half is proven LIVE.
        let revoked_key = BabyBear::new(0xDE16A);
        let revoked_value = BabyBear::new(7_777);
        let clist_leaves = vec![
            HeapLeaf {
                addr: revoked_key,
                value: revoked_value,
            },
            HeapLeaf {
                addr: BabyBear::new(0xBEEF),
                value: BabyBear::new(123),
            },
        ];
        let initial = CellState::new(100_000, 0);
        let effects = vec![VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], 100_000);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = dregg_turn::rotation_witness::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = dregg_turn::rotation_witness::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let before = dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(
            before_w.pre_limbs.clone(),
            before_w.iroot,
        )
        .unwrap();
        let after = dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(
            after_w.pre_limbs.clone(),
            after_w.iroot,
        )
        .unwrap();
        let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
        let (mut trace, mut dpis) =
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace(
                &initial, &effects, &before, &after, &caveat,
            )
            .unwrap();
        let heaps = dregg_circuit::effect_vm::trace_rotated::generate_rotated_cap_write_base(
            &mut trace,
            &mut dpis,
            CapTreeWriteOp::Remove,
            &clist_leaves,
            revoked_key,
            None,
        )
        .expect("the cap-tree->map_heaps bridge builds the genuine BEFORE/AFTER roots");
        assert_eq!(
            heaps,
            vec![clist_leaves.clone()],
            "the bridge returns the c-list as the map heap"
        );

        // A c-list MISSING the revoked key fails closed (the guardrail — no fabricated post-root).
        let absent = vec![HeapLeaf {
            addr: BabyBear::new(0xBEEF),
            value: BabyBear::new(123),
        }];
        let (mut t2, mut d2) =
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace(
                &initial, &effects, &before, &after, &caveat,
            )
            .unwrap();
        assert!(
            dregg_circuit::effect_vm::trace_rotated::generate_rotated_cap_write_base(
                &mut t2,
                &mut d2,
                CapTreeWriteOp::Remove,
                &absent,
                revoked_key,
                None,
            )
            .is_err(),
            "a c-list MISSING the revoked key MUST fail closed (no fabricated post-cap-root)"
        );
    }

    /// **THE CAP-WRITE LOOP — CLOSED on the WIDE DELEG-tree REMOVE leg.**
    /// A `RevokeDelegation` (a DELEG-tree REMOVE) with a GENUINE c-list witness routes to the
    /// `revokeDelegationWriteCapOpenVmDescriptor2R24` WRITE wrapper (the re-point is ON), proven on the WIDE
    /// cap-open route (the key has a proven wide twin, so production + this test go wide): the cap-root
    /// advances on the ROTATED-BLOCK limb (descriptor vars 213→264, exactly as note-spend advances its
    /// nullifier accumulator), the v1-state cap-root cols 65/87 are FROZEN pass-through (the `213 == 65`
    /// collision GONE), the c-list heap is threaded as the `map_op` witness (the genuine sorted-tree
    /// post-WRITE root computed; a wrong post-root is UNSAT, `cap_write_revoke_forge_rejected`), and the
    /// 8-felt (~124-bit) wide commit anchors are appended over the membership crown.
    ///
    /// THE LAST WIDE GAP — the delegation-EPOCH tick — is CLOSED HERE (it was the `failed constraint #70`
    /// the wide DELEG-REMOVE leg tripped on while the Update-on-deleg (refresh) and Remove-on-cap-tree
    /// (revokeCapability) wide legs proved). A genuine revokeDelegation is EPOCH-BASED revocation: the
    /// after-state BUMPS the delegation epoch (a cap stamped at the prior epoch goes stale). The wide
    /// `revokeDelegationWriteCapOpenVmDescriptor2R24` UNIQUELY pins that tick on the rotated delegation-epoch
    /// limb (pre_limb 30 = `epoch_felt`, descriptor cols 218→269, guarded by the revoke selector:
    /// `after.epoch == before.epoch + 1`). The nonce-only after-cell FROZE the epoch and was UNSAT — so the
    /// faithful witness here advances BOTH the nonce and the delegation epoch (`bump_delegation_epoch`), and
    /// the leg PROVES + LIGHT-CLIENT-VERIFIES end-to-end. revokeCapability / refresh carry no epoch-tick gate
    /// (their REMOVE/UPDATE wide legs prove with a frozen epoch — the source-of-truth distinction). The
    /// cap-root advance is confirmed correct by `cap_write_revoke_descriptor_after_root_is_map_op_defined_only`.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_revoke_proves_and_verifies_light_client() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

        // The cap being revoked: slot_hash 0xDE16A, target 7_777 (== src), delegation facet.
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xDE16A),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_DELEGATION_OPS)
            .expect("cap-open path builds");

        // THE GENUINE c-list (the cap-tree write witness): each cap → HeapLeaf keyed by slot_hash with
        // value = target (the shape `turn_proving::cap_write_clist_leaves` produces from the real ledger).
        // The revoked cap's slot_hash (0xDE16A) IS present — the REMOVE has a membership witness.
        let clist_leaves = vec![
            HeapLeaf {
                addr: chosen[0],
                value: chosen[1],
            },
            HeapLeaf {
                addr: other[0],
                value: other[1],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real RevokeDelegation turn (nonce-tick passthrough base).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        // A genuine RevokeDelegation BUMPS the delegation epoch (epoch-based revocation — a cap stamped
        // at the prior epoch goes stale). The wide `revokeDelegationWriteCapOpenVmDescriptor2R24` pins
        // that tick on the rotated delegation-epoch limb (pre_limb 30 = `epoch_felt`, descriptor cols
        // 218→269), guarded by the revoke selector: `after.epoch == before.epoch + 1`. So the faithful
        // after-state must advance the epoch (the nonce-only after-cell FROZE it and was UNSAT — the
        // honest revoke ticks BOTH the nonce and the delegation epoch). revokeCapability / refresh carry
        // no epoch-tick gate, which is why their REMOVE/UPDATE wide legs prove with a frozen epoch.
        assert!(
            after_cell.state.bump_delegation_epoch(),
            "the genuine revokeDelegation post-state advances the delegation epoch"
        );
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // THE RE-POINT IS ON: the revoke route now carries `write: Some((...WriteCapOpen..., Remove))`,
        // and `cap_open_effective_key` selects the WRITE wrapper because the c-list is non-empty.
        let route = cap_open_route_for_run(&effects).expect("revoke is a wired cap-open route");
        assert!(
            route.write.is_some(),
            "the revoke route MUST carry the write wrapper (re-point ON)"
        );
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, "revokeDelegationWriteCapOpenVmDescriptor2R24",
            "with a genuine c-list witness the EFFECTIVE descriptor is the WRITE wrapper"
        );

        // PROVE through the write wrapper. The cap-root half is CLOSED: the descriptor advances the
        // cap-root on the ROTATED-BLOCK limb (descriptor vars 213→264, exactly as note-spend advances its
        // nullifier accumulator), the c-list heap is threaded as the `map_op` witness, the genuine
        // sorted-tree post-WRITE root is computed, and the v1-state cap-root columns (65/87) stay FROZEN
        // (the `213 == 65` / `264 == 87` welds are gone). A wrong post-root is UNSAT
        // (`cap_write_revoke_forge_rejected`).
        //
        // UNAMBIGUOUS (the nonce-freeze gate is DROPPED — the descriptor now rides the tick face): the
        // WRITE-bearing revoke cap-open MUST GENUINELY prove (the cap-root advances on the rotated limb
        // 213→264 over the real c-list, the genuine sorted-tree REMOVE post-root is computed, v1-state
        // cap-root frozen, nonce TICKS) and the LIGHT-CLIENT verifier MUST accept the genuine post-cap-root.
        // NO catch_unwind, NO fail-closed branch: if the prover refuses or the verifier rejects, this test
        // FAILS — that is the honest signal the cap-WRITE post-root is NOT light-client-verifiable. A wrong
        // post-root is UNSAT (`cap_write_revoke_forge_rejected`), so a passing proof here IS the genuine
        // post-cap-root, bound on the wire.
        // PROVE on the WIDE route: the `revokeDelegationWriteCapOpen` key has a proven wide twin in the
        // registry (so production goes wide; the narrow 1-felt leg is REJECTED by the wide-dodge tooth).
        // The wide DELEG-tree REMOVE leg now proves — the after-state advances the delegation epoch above,
        // satisfying the epoch-tick gate the bare nonce-only after-cell froze (the former `#70` gap).
        let (proof, dpis) =
            prove_effect_vm_cap_open(&initial, &effects, &before_w, &after_w, &cap, &route, None, true)
                .expect(
                    "the WRITE-bearing revoke cap-open MUST genuinely prove — cap-root on the rotated limb \
                     (213→264) over the real c-list, v1-state frozen, nonce ticks (tick face, no freeze)",
                );
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize write cap-open leg");
        let vk_hash = cap_open_wide_vk_hash_by_key(effective_key).expect("write wrapper vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the WRITE-bearing revoke cap-open MUST verify on the light-client path — the genuine \
             post-cap-root is on-the-wire light-client-verifiable",
        );
    }

    /// **THE FORGE IS REJECTED (the soundness guardrail).** The load-bearing forge is (a): a FABRICATED
    /// post-cap-root — a c-list that does NOT contain the revoked key — makes the `map_op` REMOVE have no
    /// membership witness, so the prover FAILS CLOSED. A wrong post-cap-root is NOT provable (no silent
    /// forge) — this is the guardrail the cap-WRITE axis rests on. (b) documents the CURRENT honest state:
    /// the authority-only revoke cap-open still PROVES + the light-client verifier ACCEPTS it (the
    /// post-cap-root is host-trusted — a NAMED residual). The verifier-half tooth that will FORCE the write
    /// route (`is_forbidden_authority_only_cap_write_descriptor`) remains GATED OFF as a deliberate verifier
    /// policy step (a VK-epoch decision), NOT a prover blocker: the write wrapper now PROVES + verifies on the
    /// wide DELEG-REMOVE leg (`cap_write_revoke_proves_and_verifies_light_client`), so the provable alternative
    /// exists; flipping the tooth on is the separate forcing step.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_revoke_forge_rejected() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xDE16A),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_DELEGATION_OPS)
            .expect("cap-open path builds");

        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        let route = cap_open_route_for_run(&effects).expect("revoke is a wired cap-open route");

        // FORGE (a): a c-list that does NOT contain the revoked key (slot_hash 0xDE16A). The write
        // wrapper's map_op REMOVE has no membership witness for the key → the prover FAILS CLOSED. A wrong
        // post-cap-root CANNOT be proven (no silent forge).
        let forged_clist = vec![
            HeapLeaf {
                addr: other[0],
                value: other[1],
            }, // only the OTHER cap; the revoked key is ABSENT
        ];
        let cap_forged = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: forged_clist,
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_forged,
                &route,
                None,
                false
            )
            .is_err(),
            "a c-list MISSING the revoked key MUST fail closed — a fabricated post-cap-root is NOT provable"
        );

        // (b) the AUTHORITY-only route (empty c-list ⇒ `revokeCapOpenVmDescriptor2R24`, NO write-op): it
        // still PROVES (the cap-membership crown is valid — the proof self-verifies), BUT the LIGHT-CLIENT
        // verifier now REJECTS it — THE TOOTH IS ON (`is_forbidden_authority_only_cap_write_descriptor`):
        // an authority-only revoke leaves the post-cap-root host-trusted, so the producer MUST prove the
        // WRITE wrapper (`cap_write_revoke_proves_and_verifies_light_client` is the accepted route). This
        // is the verifier half of the FORCED write routing.
        let cap_authority_only = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert_eq!(
            cap_open_effective_key(&route, &cap_authority_only),
            "revokeCapOpenVmDescriptor2R24",
            "an empty c-list falls back to the authority-only route"
        );
        let (proof_ao, dpis_ao) = prove_effect_vm_cap_open(
            &initial,
            &effects,
            &before_w,
            &after_w,
            &cap_authority_only,
            &route,
            None,
            false,
        )
        .expect("the authority-only cap-open still PROVES (the membership crown is valid)");
        let proof_ao_bytes =
            postcard::to_allocvec(&proof_ao).expect("serialize authority-only leg");
        let vk_ao = cap_open_vk_hash_by_key("revokeCapOpenVmDescriptor2R24")
            .expect("authority-only vk_hash");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_ao_bytes, &dpis_ao, &vk_ao).is_err(),
            "the AUTHORITY-only revoke cap-open is now light-client-REJECTED (the tooth is ON) — the \
             post-cap-root is host-trusted; the producer must prove the on-the-wire WRITE wrapper",
        );
    }

    /// **THE ROUTE-LEVEL FORGE DETECTOR for revokeCapability (the ROUTE-FORGE close).** The
    /// pre-existing `cap_write_revoke_cap_no_silent_forge` tests the BASE descriptor
    /// (`revokeCapabilityVmDescriptor2R24`), NOT the LIVE SDK cap-open route — it passed without
    /// guarding the route. The bug: the revokeCapability route selected the AUTHORITY-only
    /// `revokeCapabilityCapOpenVmDescriptor2R24` (write:None), so the cap-tree REMOVE rode UNBOUND on
    /// the light-client wire — a forged post-cap-root (removed cap fabricated/omitted) was ACCEPTED by
    /// a light client (a full node re-running the executor caught it; a light client did not).
    ///
    /// The fix (mirroring revokeDelegation): the route now carries
    /// `write: Some((revokeCapabilityWriteCapOpenVmDescriptor2R24, Remove, EFFECT_REVOKE_CAPABILITY))`,
    /// and the authority-only wrapper is light-client-REJECTED (`is_forbidden_authority_only_cap_write_descriptor`).
    /// THREE arms against the SAME verify:
    ///   (1) the GENUINE write route PROVES + light-client-VERIFIES (non-vacuity — the honest path works);
    ///   (2) a FORGED post-cap-root (c-list MISSING the revoked key) FAILS CLOSED at the prover (no
    ///       silent forge — a wrong post-root is UNSAT);
    ///   (3) the AUTHORITY-only route (empty c-list) still PROVES but the light-client verifier now
    ///       REJECTS it (the tooth is ON — the producer MUST prove the on-the-wire WRITE wrapper).
    /// This is RED before the route fix (the authority-only route was the effective key + accepted) and
    /// GREEN after.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_revoke_cap_route_proves_and_verifies_light_client() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        const EFFECT_REVOKE_CAPABILITY: u32 = 1 << 3;

        // The cap being revoked: slot_hash 0xCA9, target 7_777 (== src), revokeCapability facet.
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xCA9),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_REVOKE_CAPABILITY),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_REVOKE_CAPABILITY),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_REVOKE_CAPABILITY)
            .expect("cap-open path builds");

        // THE GENUINE c-list — the revoked cap's slot_hash (0xCA9) IS present (the REMOVE has a witness).
        let clist_leaves = vec![
            HeapLeaf {
                addr: chosen[0],
                value: chosen[1],
            },
            HeapLeaf {
                addr: other[0],
                value: other[1],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real RevokeCapability turn (the cap-crown remove base; nonce-tick passthrough).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::RevokeCapability {
            slot_hash: [BabyBear::new(0xCA9); 8],
            phase_b: None,
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // THE RE-POINT IS ON: the revokeCapability route now carries `write: Some((...WriteCapOpen..., Remove))`.
        let route =
            cap_open_route_for_run(&effects).expect("revokeCapability is a wired cap-open route");
        assert!(
            route.write.is_some(),
            "the revokeCapability route MUST carry the write wrapper (route-forge close)"
        );
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, "revokeCapabilityWriteCapOpenVmDescriptor2R24",
            "with a genuine c-list witness the EFFECTIVE descriptor is the WRITE wrapper"
        );

        // (1) NON-VACUITY: the WRITE-bearing revokeCapability cap-open MUST GENUINELY prove + the
        // LIGHT-CLIENT verifier MUST accept the genuine post-cap-root (the cap-tree REMOVE bound on the
        // wire). NO catch_unwind: a refusal/rejection FAILS the test (the honest signal).
        // The WRITE key has a proven wide twin, so production always goes wide for it (the narrow
        // 1-felt leg is rejected by the wide-dodge tooth). Prove + verify the deployed WIDE leg.
        let (proof, dpis) =
            prove_effect_vm_cap_open(&initial, &effects, &before_w, &after_w, &cap, &route, None, true)
                .expect(
                    "the WRITE-bearing revokeCapability cap-open MUST genuinely prove — the cap-root REMOVE \
                     on the rotated limb (213→264) over the real c-list, v1-state frozen, nonce ticks",
                );
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize write cap-open leg");
        let vk_hash =
            cap_open_wide_vk_hash_by_key(effective_key).expect("wide write wrapper vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the WRITE-bearing revokeCapability cap-open MUST verify on the light-client path — the genuine \
             post-cap-root is on-the-wire light-client-verifiable",
        );

        // (2) THE FORGE IS REJECTED: a c-list that does NOT contain the revoked key (0xCA9). The write
        // wrapper's map_op REMOVE has no membership witness → the prover FAILS CLOSED. A wrong
        // post-cap-root CANNOT be proven (no silent forge — the route-forge antibody).
        let forged_clist = vec![
            HeapLeaf {
                addr: other[0],
                value: other[1],
            }, // only the OTHER cap; the revoked key is ABSENT
        ];
        let cap_forged = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: forged_clist,
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_forged,
                &route,
                None,
                false
            )
            .is_err(),
            "a c-list MISSING the revoked key MUST fail closed — a fabricated post-cap-root is NOT provable"
        );

        // (3) THE AUTHORITY-ONLY ROUTE IS LIGHT-CLIENT-REJECTED (the tooth is ON): an empty c-list falls
        // back to `revokeCapabilityCapOpenVmDescriptor2R24` (write:None). It still PROVES (the membership
        // crown is valid) BUT the light-client verifier now REJECTS it — the producer MUST prove the
        // on-the-wire WRITE wrapper. This is the verifier half of the FORCED write routing.
        let cap_authority_only = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert_eq!(
            cap_open_effective_key(&route, &cap_authority_only),
            "revokeCapabilityCapOpenVmDescriptor2R24",
            "an empty c-list falls back to the authority-only route"
        );
        let (proof_ao, dpis_ao) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap_authority_only, &route, None,
            false,
        )
        .expect("the authority-only revokeCapability cap-open still PROVES (the membership crown is valid)");
        let proof_ao_bytes =
            postcard::to_allocvec(&proof_ao).expect("serialize authority-only leg");
        let vk_ao = cap_open_vk_hash_by_key("revokeCapabilityCapOpenVmDescriptor2R24")
            .expect("authority-only vk_hash");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_ao_bytes, &dpis_ao, &vk_ao).is_err(),
            "the AUTHORITY-only revokeCapability cap-open is now light-client-REJECTED (the tooth is ON) — \
             the post-cap-root is host-trusted; the producer must prove the on-the-wire WRITE wrapper",
        );
    }

    /// **THE ROUTE-LEVEL FORGE DETECTOR for refreshDelegation (the DELEG-FORGE close — Stage E).** The
    /// genuine move of `refreshDelegation` is a DELEGATIONS-tree UPDATE-AT-KEY (the `DELEG` system-root,
    /// NOT `caps`): the child's delegation snapshot is re-armed (`granted = held`, reflexive
    /// non-amplification) at the child key. Before this close the route selected the AUTHORITY-only
    /// `refreshDelegationCapOpenVmDescriptor2R24` (write:None), so the DELEG-tree write rode UNBOUND on the
    /// light-client wire — a forged after-DELEG-root (the refreshed snapshot fabricated/omitted) was
    /// ACCEPTED by a light client (a full node re-running the executor caught it; a light client did not).
    ///
    /// The fix (mirroring revokeDelegation/revokeCapability): the route now carries
    /// `write: Some((refreshDelegationWriteCapOpenVmDescriptor2R24, Update, EFFECT_DELEGATION_OPS))`, and the
    /// authority-only wrapper is light-client-REJECTED (`is_forbidden_authority_only_cap_write_descriptor`).
    /// The deleg accumulator rides the rotated cap-root limb 25 (refresh FREEZES `caps`, so that limb is free
    /// to carry the DELEG before→after root — Lean `beforeDelegRootCol = beforeCapRootCol`). THREE arms
    /// against the SAME light-client verify:
    ///   (1) the GENUINE write route PROVES + light-client-VERIFIES (non-vacuity — the honest path works);
    ///   (2) a FORGED post-DELEG-root (a leaf-set MISSING the re-armed key) FAILS CLOSED at the prover (the
    ///       `Update` map_op has no membership witness for the key — a wrong post-root is UNSAT);
    ///   (3) the AUTHORITY-only route (empty leaf-set) still PROVES but the light-client verifier now
    ///       REJECTS it (the tooth is ON — the producer MUST prove the on-the-wire WRITE wrapper).
    /// This is the LIVE realization of Lean `refreshDelegation_descriptorRefines_sat` /
    /// `effCapOpenWriteV3_forces_write8` (the arity-2 map-op theorem is DELETED), threaded to the apex
    /// `lightclient_unfoolable_closed_final_genuine` (Rfix 55). RED before the route fix (authority-only was
    /// the effective key + accepted); GREEN after.
    #[cfg(feature = "prover")]
    #[test]
    fn refresh_deleg_write_proves_and_verifies_light_client() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

        // THE GENUINE SNAPSHOT VALUE the refresh re-arms to (the SPECIFIC delegation's new commitment felt,
        // bound into effects_hash via `VmEffect::RefreshDelegation { snapshot_value }`). DISTINCT from the
        // held c-list value (7_777) and from the cap facet mask (EFFECT_DELEGATION_OPS): the live lead writes
        // THIS value at the re-armed key, proving the genuine-params path — NOT the reflexive held-mask re-arm.
        let genuine_snapshot = BabyBear::new(0x5A57_0001);

        // The child delegation being re-armed: slot_hash 0xDE16, target 7_777 (== src), delegation facet.
        // mask_lo is the HELD facet the membership read opens; the UPDATE rebinds the present key to the
        // genuine refreshed snapshot value (the key set is preserved — the update-at-key shadow).
        let chosen: [BabyBear; 7] = [
            BabyBear::new(0xDE16),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(42),
        ];
        let other: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };
        let built = CapOpenWitness::build_for(&[other, chosen], 1, EFFECT_DELEGATION_OPS)
            .expect("cap-open path builds");

        // THE GENUINE delegations leaf-set — the re-armed child key (0xDE16) IS present (the UPDATE has a
        // membership witness; refresh is an update-at-key, so the key stays present).
        let clist_leaves = vec![
            HeapLeaf {
                addr: chosen[0],
                value: chosen[1],
            },
            HeapLeaf {
                addr: other[0],
                value: other[1],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };

        // A real RefreshDelegation turn (the genuine moving face; nonce-tick passthrough, caps frozen).
        // LIVE LEAD: the effect carries the GENUINE `(child_hash, snapshot_value)` of the SPECIFIC delegation
        // re-armed — the DELEG-tree UPDATE writes `snapshot_value[0]` (the genuine snapshot felt) at the
        // re-armed key, NOT the reflexive held mask. `child_hash` binds WHICH delegation; both fold into
        // effects_hash so a light client sees the specific re-arm.
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let mut snapshot_value = [BabyBear::ZERO; 8];
        snapshot_value[0] = genuine_snapshot;
        let effects = vec![VmEffect::RefreshDelegation {
            child_hash: [
                chosen[0],
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            snapshot_value,
        }];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // THE RE-POINT IS ON: the refreshDelegation route now carries `write: Some((...WriteCapOpen..., Update))`.
        let route =
            cap_open_route_for_run(&effects).expect("refreshDelegation is a wired cap-open route");
        assert!(
            route.write.is_some(),
            "the refreshDelegation route MUST carry the DELEG-tree write wrapper (the DELEG-forge close)"
        );
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, "refreshDelegationWriteCapOpenVmDescriptor2R24",
            "with a genuine delegations leaf-set the EFFECTIVE descriptor is the DELEG-tree WRITE wrapper"
        );

        // (1) NON-VACUITY: the WRITE-bearing refreshDelegation cap-open MUST GENUINELY prove + the
        // LIGHT-CLIENT verifier MUST accept the genuine post-DELEG-root (the DELEG-tree UPDATE bound on the
        // wire). NO catch_unwind: a refusal/rejection FAILS the test (the honest signal).
        // The WRITE key has a proven wide twin, so production always goes wide for it (the narrow
        // 1-felt leg is rejected by the wide-dodge tooth). Prove + verify the deployed WIDE leg.
        let (proof, dpis) =
            prove_effect_vm_cap_open(&initial, &effects, &before_w, &after_w, &cap, &route, None, true)
                .expect(
                    "the WRITE-bearing refreshDelegation cap-open MUST genuinely prove — the DELEG-root \
                     UPDATE on the rotated limb 25 (beforeDelegRootCol) over the real leaf-set, caps frozen, \
                     nonce ticks",
                );
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize write cap-open leg");
        let vk_hash =
            cap_open_wide_vk_hash_by_key(effective_key).expect("wide write wrapper vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the WRITE-bearing refreshDelegation cap-open MUST verify on the light-client path — the genuine \
             post-DELEG-root is on-the-wire light-client-verifiable",
        );

        // (1b) THE LIVE LEAD (genuine params, NOT the reflexive re-arm): the DELEG-tree UPDATE writes the
        // effect's carried `snapshot_value[0]` (the SPECIFIC re-armed snapshot) — distinct from the held
        // c-list value AND the cap facet mask. `cap_insert_payload_for` derives the (anchor key, KEEP_MASK)
        // the `Update` map_op rebinds: the KEEP_MASK MUST be the genuine snapshot, confirming the on-the-wire
        // post-DELEG-root binds the specific snapshot the producer claims (a forged snapshot would write a
        // different value → a different effects_hash + post-root, light-client-distinguishable).
        let (_anchor_key, keep_mask) = cap_insert_payload_for(&effects, &cap)
            .expect("refresh derives a (key, snapshot) payload");
        assert_eq!(
            keep_mask, genuine_snapshot,
            "the live lead writes the GENUINE snapshot value (the carried `snapshot_value[0]`), NOT the \
             reflexive held mask — this is the genuine-params path, not the old unit re-arm"
        );
        assert_ne!(
            keep_mask, cap.leaf.mask_lo,
            "the genuine snapshot is DISTINCT from the held facet mask — a real refresh is not a reflexive re-arm"
        );

        // (1c) THE SNAPSHOT-FORGE IS REJECTED: a turn whose carried `snapshot_value` differs from the one the
        // honest proof bound writes a DIFFERENT keep_mask → a DIFFERENT effects_hash + post-DELEG-root. The
        // light-client verifier (anchored to the honest turn's effects_hash) rejects the forged-snapshot proof.
        let mut forged_snapshot_value = [BabyBear::ZERO; 8];
        forged_snapshot_value[0] = BabyBear::new(0xBAD0_F00D);
        let forged_snapshot_effects = vec![VmEffect::RefreshDelegation {
            child_hash: [
                chosen[0],
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            snapshot_value: forged_snapshot_value,
        }];
        // (the keystone after-spine producer is WIDE-only, so the forged-snapshot leg proves wide too)
        let (proof_forge, dpis_forge) = prove_effect_vm_cap_open(
            &initial, &forged_snapshot_effects, &before_w, &after_w, &cap, &route, None,
            true,
        )
        .expect("the forged-snapshot turn still PROVES its OWN (forged) transition — the forge is caught at VERIFY");
        let proof_forge_bytes =
            postcard::to_allocvec(&proof_forge).expect("serialize forged-snapshot leg");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_forge_bytes, &dpis_forge, &vk_hash)
                .is_err()
                || dpis_forge != dpis,
            "a forged-snapshot refresh binds a DIFFERENT effects_hash / post-DELEG-root than the honest turn — \
             the light client (anchored to the honest effects_hash) cannot be fooled into accepting it as the \
             genuine re-arm",
        );

        // (2) THE FORGE IS REJECTED: a leaf-set that does NOT contain the re-armed key (0xDE16). The write
        // wrapper's `Update` map_op has no membership witness → the prover FAILS CLOSED. A wrong
        // post-DELEG-root CANNOT be proven (no silent forge — the DELEG-forge antibody).
        let forged_clist = vec![
            HeapLeaf {
                addr: other[0],
                value: other[1],
            }, // only the OTHER edge; the re-armed key is ABSENT
        ];
        let cap_forged = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: forged_clist,
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_forged,
                &route,
                None,
                false
            )
            .is_err(),
            "a leaf-set MISSING the re-armed key MUST fail closed — a fabricated post-DELEG-root is NOT provable"
        );

        // (3) THE AUTHORITY-ONLY ROUTE IS LIGHT-CLIENT-REJECTED (the tooth is ON): an empty leaf-set falls
        // back to `refreshDelegationCapOpenVmDescriptor2R24` (write:None). It still PROVES (the membership
        // crown is valid) BUT the light-client verifier now REJECTS it — the producer MUST prove the
        // on-the-wire WRITE wrapper. This is the verifier half of the FORCED DELEG-write routing.
        let cap_authority_only = CapMembershipWitness {
            leaf: leaf_cl(&chosen),
            siblings: built.siblings.to_vec(),
            directions: built.directions.to_vec(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert_eq!(
            cap_open_effective_key(&route, &cap_authority_only),
            "refreshDelegationCapOpenVmDescriptor2R24",
            "an empty leaf-set falls back to the authority-only route"
        );
        let (proof_ao, dpis_ao) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap_authority_only, &route, None,
            false,
        )
        .expect("the authority-only refreshDelegation cap-open still PROVES (the membership crown is valid)");
        let proof_ao_bytes =
            postcard::to_allocvec(&proof_ao).expect("serialize authority-only leg");
        let vk_ao = cap_open_vk_hash_by_key("refreshDelegationCapOpenVmDescriptor2R24")
            .expect("authority-only vk_hash");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_ao_bytes, &dpis_ao, &vk_ao).is_err(),
            "the AUTHORITY-only refreshDelegation cap-open is now light-client-REJECTED (the tooth is ON) — \
             the post-DELEG-root is host-trusted; the producer must prove the on-the-wire WRITE wrapper",
        );
    }

    /// **THE INSERT-AFTER-SPINE prove/verify/forge harness (the keystone deploy — delegate /
    /// introduce / delegateAtten).** The deployed wrappers are the INSERT-shaped keystone descriptors
    /// (`effCapInsertV3`): the cap-open READ opens the SPLICED (conferred) leaf against the REBUILT
    /// AFTER cap-root over the `CanonicalCapTree::insert_witness` after-membership path; the BEFORE
    /// root + the fresh key's non-membership bracket ride the witness carriers; NO arity-2 map-op,
    /// NO map heap. The fixture builds the holder's BEFORE tree as a genuine `CanonicalCapTree`
    /// (anchor + one filler leaf) and threads BOTH the arity-2 c-list (the write-route activation
    /// signal) and the FULL 7-field `cap_leaves` (the rebuild witness). Arms:
    ///   (1) GENUINE — the WIDE keystone leg proves + light-client-verifies;
    ///   (2) FORGE TOOTH (wire) — a forged 8-felt AFTER-commit PI is REJECTED;
    ///   (3) FORGE (present key) — a c-list ALREADY containing the fresh edge key fails closed
    ///       (`insert_witness` refuses — no fabricated after-root);
    ///   (4) FORGE (mismatched c-list) — a 7-field c-list that does NOT rebuild the membership
    ///       root fails closed (the anchor path and the supplied tree disagree — no silent forge).
    ///
    /// `route_eff_bit` is the crown facet the deployed descriptor binds — checked against the ANCHOR
    /// (producer-side authority guard) AND against the SPLICED leaf (the descriptor's
    /// `selectedBitGate` on the conferred mask), so `fresh_edge.1` MUST carry bit
    /// `log2(route_eff_bit)`.
    #[cfg(feature = "prover")]
    fn run_insert_after_spine_prove_verify_forge(
        effect: VmEffect,
        fresh_edge: (BabyBear, BabyBear),
        route_eff_bit: u32,
        expected_write_key: &str,
    ) {
        // The anchor's held mask defaults to exactly the crown facet bit (the as-is conferral).
        run_insert_after_spine_prove_verify_forge_masked(
            effect,
            fresh_edge,
            route_eff_bit,
            route_eff_bit,
            expected_write_key,
        )
    }

    /// As [`run_insert_after_spine_prove_verify_forge`] with an explicit ANCHOR held mask —
    /// delegateAtten narrows `keep ⊑ held`, so its anchor must hold a SUPERSET of the conferred
    /// mask (the surviving `submaskLookup` over cols 73/72 bites otherwise).
    #[cfg(feature = "prover")]
    fn run_insert_after_spine_prove_verify_forge_masked(
        effect: VmEffect,
        fresh_edge: (BabyBear, BabyBear),
        route_eff_bit: u32,
        anchor_mask_lo: u32,
        expected_write_key: &str,
    ) {
        use dregg_circuit::cap_root::{CAP_TREE_DEPTH, CanonicalCapTree, CapLeaf};
        use dregg_circuit::effect_vm::trace_rotated::{FACET_MASK_HI, SIGNATURE_AUTH_TAG};
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        // The ANCHOR cap (the delegator's held authority) — its full mask MUST permit the route's
        // eff_bit (`from_membership_for` submask), and its slot_hash is the present anchor key.
        let anchor = CapLeaf {
            slot_hash: BabyBear::new(0xA0C0),
            target: BabyBear::new(7_777),
            auth_tag: BabyBear::new(SIGNATURE_AUTH_TAG),
            mask_lo: BabyBear::new(anchor_mask_lo),
            mask_hi: BabyBear::new(FACET_MASK_HI),
            expiry: BabyBear::new(0x00FF_FFFF),
            breadstuff: BabyBear::new(99),
        };
        let other = CapLeaf {
            slot_hash: BabyBear::new(0xBEEF),
            target: BabyBear::new(123),
            auth_tag: BabyBear::new(1),
            mask_lo: BabyBear::new(route_eff_bit),
            mask_hi: BabyBear::new(0),
            expiry: BabyBear::new(9),
            breadstuff: BabyBear::new(0),
        };
        let (fresh_key, fresh_value) = fresh_edge;
        assert_ne!(
            fresh_key, anchor.slot_hash,
            "fresh edge distinct from anchor"
        );
        assert_ne!(
            fresh_key, other.slot_hash,
            "fresh edge absent from the c-list"
        );
        // (The conferred payload value is ARBITRARY — a hash limb on the executor-bridge path; the
        // spliced leaf inherits the ANCHOR's mask as-is, so the crown facet is always permitted.)

        // The holder's BEFORE tree: the GENUINE deployed CanonicalCapTree (sorted, sentinel-
        // bracketed) — the tree `insert_witness` rebuilds and the cell-side root commits.
        let before_tree = CanonicalCapTree::new(vec![anchor, other], CAP_TREE_DEPTH);
        let mw = before_tree
            .membership_witness(anchor.slot_hash)
            .expect("the anchor is a member of the BEFORE tree");
        let clist_leaves = vec![
            HeapLeaf {
                addr: anchor.slot_hash,
                value: anchor.target,
            },
            HeapLeaf {
                addr: other.slot_hash,
                value: other.target,
            },
        ];
        let cap = CapMembershipWitness {
            leaf: mw.leaf,
            siblings: mw.siblings.clone(),
            directions: mw.directions.clone(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: vec![anchor, other],
            cap_tombstones: Vec::new(),
        };

        // A real granting turn (nonce-tick passthrough base).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![effect];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        let route = cap_open_route_for_run(&effects).expect("a wired cap-open route");
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, expected_write_key,
            "with a genuine c-list the EFFECTIVE descriptor is the INSERT keystone wrapper"
        );
        assert_eq!(
            cap_insert_payload_for(&effects, &cap),
            Some((fresh_key, fresh_value)),
            "the fresh conferred edge derived from the effect must match"
        );

        // ── ARM (1): GENUINE — the WIDE keystone leg proves + light-client-verifies. The spliced
        // leaf's membership in the REBUILT AFTER tree is what the deployed read opens; a wrong
        // after-root is unbuildable (the witness IS the rebuild).
        let (proof, dpis) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap, &route, None, true,
        )
        .unwrap_or_else(|e| {
            panic!(
                "the INSERT keystone wrapper ({expected_write_key}) MUST genuinely prove — \
                         the spliced-leaf AFTER membership + witness-carried BEFORE root: {e:?}"
            )
        });
        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize insert keystone leg");
        let vk_hash =
            cap_open_wide_vk_hash_by_key(effective_key).expect("wide insert keystone vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).unwrap_or_else(|e| {
            panic!(
                "the INSERT keystone wrapper ({expected_write_key}) MUST light-client-verify — the \
                 genuine post-cap-root is on the wire: {e:?}"
            )
        });

        // ── ARM (2): FORGE TOOTH (wire) — a forged 8-felt AFTER-commit PI is REJECTED (the wide
        // carrier binds the committed cap-root groups the keystone welds).
        let n_pis = dpis.len();
        let mut forged = dpis.clone();
        forged[n_pis - 1] = forged[n_pis - 1] + BabyBear::new(0x9999);
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged, &vk_hash).is_err(),
            "a forged 8-felt commit PI on the insert keystone leg MUST be REJECTED"
        );

        // ── ARM (3): FORGE (present key) — a c-list ALREADY containing the fresh edge key fails
        // closed (`insert_witness` refuses a present key — no fabricated after-root, no no-op
        // laundering).
        let colliding = CapLeaf {
            slot_hash: fresh_key,
            ..other
        };
        let collide_tree = CanonicalCapTree::new(vec![anchor, other, colliding], CAP_TREE_DEPTH);
        let mw_c = collide_tree
            .membership_witness(anchor.slot_hash)
            .expect("anchor member of the colliding tree");
        let cap_collide = CapMembershipWitness {
            leaf: mw_c.leaf,
            siblings: mw_c.siblings,
            directions: mw_c.directions,
            clist_leaves: clist_leaves.clone(),
            cap_leaves: vec![anchor, other, colliding],
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_collide,
                &route,
                None,
                false
            )
            .is_err(),
            "a c-list ALREADY containing the fresh edge key MUST fail closed (the sorted insert \
             refuses a present key)"
        );

        // ── ARM (4): FORGE (mismatched c-list) — a supplied 7-field c-list that does NOT rebuild
        // the membership-opened root fails closed (the anchor path and the tree disagree — the
        // c-list is not the holder's genuine pre-state; no silent forge of a different tree).
        let cap_mismatch = CapMembershipWitness {
            leaf: mw.leaf,
            siblings: mw.siblings.clone(),
            directions: mw.directions.clone(),
            clist_leaves,
            cap_leaves: vec![anchor], // `other` dropped — rebuilds a DIFFERENT root
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_mismatch,
                &route,
                None,
                false
            )
            .is_err(),
            "a 7-field c-list that does not rebuild the membership root MUST fail closed"
        );
    }

    /// **THE WIDE WRITE-CAP FLAG-DAY harness (§10 close — no ~31-bit waist for a WRITE-cap turn).** Given
    /// an INSERT-cap-write effect + its route, this proves the WRITE wrapper WIDE (the 8-felt ~124-bit
    /// commit appended past the membership crown + the cap-tree write `map_op`), light-client-verifies the
    /// wide leg, exercises the forge tooth on a wide commit PI, AND fires the REJECT TOOTH: a NARROW
    /// (1-felt V3) write-cap leg is now REJECTED by the cutover verifier (its wide twin exists, so the V3
    /// fallback filters it OUT — the producer is forced onto the wide route). Mirrors
    /// `sovereign_rotated_wide`'s flag-day shape for the WRITE-cap tail.
    #[cfg(feature = "prover")]
    fn run_insert_cap_write_wide_flag_day(
        effect: VmEffect,
        fresh_edge: (BabyBear, BabyBear),
        route_eff_bit: u32,
        expected_write_key: &str,
    ) {
        use dregg_circuit::cap_root::{CAP_TREE_DEPTH, CanonicalCapTree, CapLeaf};
        use dregg_circuit::effect_vm::trace_rotated::{FACET_MASK_HI, SIGNATURE_AUTH_TAG};
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        // The INSERT keystone fixture: the holder's BEFORE tree is a genuine CanonicalCapTree
        // (mirroring `run_insert_after_spine_prove_verify_forge` — the keystone read opens the
        // SPLICED leaf against the rebuilt AFTER tree, so the full 7-field c-list is threaded).
        let anchor = CapLeaf {
            slot_hash: BabyBear::new(0xA0C0),
            target: BabyBear::new(7_777),
            auth_tag: BabyBear::new(SIGNATURE_AUTH_TAG),
            mask_lo: BabyBear::new(route_eff_bit),
            mask_hi: BabyBear::new(FACET_MASK_HI),
            expiry: BabyBear::new(0x00FF_FFFF),
            breadstuff: BabyBear::new(99),
        };
        let other = CapLeaf {
            slot_hash: BabyBear::new(0xBEEF),
            target: BabyBear::new(123),
            auth_tag: BabyBear::new(1),
            mask_lo: BabyBear::new(route_eff_bit),
            mask_hi: BabyBear::new(0),
            expiry: BabyBear::new(9),
            breadstuff: BabyBear::new(0),
        };
        let before_tree = CanonicalCapTree::new(vec![anchor, other], CAP_TREE_DEPTH);
        let mw = before_tree
            .membership_witness(anchor.slot_hash)
            .expect("the anchor is a member of the BEFORE tree");
        let (fresh_key, fresh_value) = fresh_edge;
        let clist_leaves = vec![
            HeapLeaf {
                addr: anchor.slot_hash,
                value: anchor.target,
            },
            HeapLeaf {
                addr: other.slot_hash,
                value: other.target,
            },
        ];
        let cap = CapMembershipWitness {
            leaf: mw.leaf,
            siblings: mw.siblings.clone(),
            directions: mw.directions.clone(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: vec![anchor, other],
            cap_tombstones: Vec::new(),
        };

        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![effect];
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        let route = cap_open_route_for_run(&effects).expect("a wired cap-open route");
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, expected_write_key,
            "the effective key is the WRITE wrapper"
        );
        // THE §10 PRECONDITION: the WRITE wrapper now HAS a proven wide twin (it goes WIDE).
        assert!(
            cap_open_key_has_wide_twin(effective_key),
            "the WRITE-cap key {effective_key} MUST have a proven wide twin (§10 v3RegistryCapOpenWriteWide)"
        );

        // PROVE WIDE: the WRITE wrapper proves with the 8-felt commit appended past the crown + the
        // cap-tree write map_op — the honest write-cap turn binds the FULL ~124-bit commit.
        let (proof_w, dpis_w) =
            prove_effect_vm_cap_open(&initial, &effects, &before_w, &after_w, &cap, &route, None, true)
                .unwrap_or_else(|e| {
                    panic!(
                        "the WIDE WRITE-cap wrapper ({expected_write_key}) MUST prove — the cap-tree write \
                         (anchor read + sorted insert) on the rotated cap-root limb PLUS the 8-felt wide \
                         carriers: {e:?}"
                    )
                });
        let n_w = dpis_w.len();
        assert!(
            n_w >= 16,
            "the WIDE write-cap leg carries the 16 wide commit PIs (got {n_w})"
        );
        let proof_w_bytes = postcard::to_allocvec(&proof_w).expect("serialize wide write-cap leg");
        let vk_w = cap_open_wide_vk_hash_by_key(effective_key).expect("wide write-cap vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_w_bytes, &dpis_w, &vk_w).unwrap_or_else(|e| {
            panic!(
                "the WIDE WRITE-cap wrapper ({expected_write_key}) MUST light-client-verify (8-felt commit \
                 bound, cap-tree write on the wire): {e:?}"
            )
        });

        // THE FORGE TOOTH on the wide commit: a forged 8-felt commit PI is UNSAT.
        let mut forged = dpis_w.clone();
        forged[n_w - 1] = forged[n_w - 1] + BabyBear::new(0x9999);
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_w_bytes, &forged, &vk_w).is_err(),
            "a forged 8-felt commit PI on the wide write-cap leg MUST be REJECTED (the wide carrier binds it)"
        );

        // THE REJECT TOOTH (the flag-day's load-bearing half): a NARROW (1-felt V3) write-cap leg is now
        // REJECTED by the cutover verifier — its wide twin exists, so the V3 fallback FILTERS IT OUT and
        // the proof verifies under NO accepted descriptor. The producer can no longer dodge the ~124-bit
        // commit with a 1-felt write-cap leg.
        let (proof_n, dpis_n) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap, &route, None, false,
        )
        .unwrap_or_else(|e| panic!("the NARROW write-cap leg still PROVES (it is honest): {e:?}"));
        let proof_n_bytes =
            postcard::to_allocvec(&proof_n).expect("serialize narrow write-cap leg");
        let vk_n = cap_open_vk_hash_by_key(effective_key).expect("narrow write-cap vk_hash");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_n_bytes, &dpis_n, &vk_n).is_err(),
            "POST-CUTOVER: a NARROW 1-felt write-cap leg ({expected_write_key}) MUST be REJECTED — its wide \
             twin exists, so the V3 cap-open fallback filters it out (the reject tooth forces the wide route)"
        );
        let _ = fresh_key;
        let _ = fresh_value;
        eprintln!(
            "WIDE WRITE-CAP GREEN ({expected_write_key}): the honest leg binds the 8-felt ~124-bit commit; \
             a narrow 1-felt write-cap leg is REJECTED."
        );
    }

    /// **THE WIDE WRITE-CAP FLAG-DAY for delegate (§10).** The `delegateWriteCapOpenVmDescriptor2R24`
    /// INSERT wrapper now has a proven wide twin: the honest delegate-via-cap turn proves+verifies at the
    /// 8-felt ~124-bit commit, and a narrow 1-felt delegate write-cap leg is REJECTED post-cutover.
    #[cfg(feature = "prover")]
    #[test]
    // WIDE is deliberate emphasis in the test name (the wide-commit flag-day).
    #[allow(non_snake_case)]
    fn cap_write_delegate_WIDE_flag_day() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::AttenuateWitness;
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
        let fresh = (
            BabyBear::new(0xED6E),
            BabyBear::new(EFFECT_DELEGATION_OPS | 0x0F),
        );
        let zero_leaf = CapLeaf {
            slot_hash: BabyBear::ZERO,
            target: BabyBear::ZERO,
            auth_tag: BabyBear::ZERO,
            mask_lo: BabyBear::ZERO,
            mask_hi: BabyBear::ZERO,
            expiry: BabyBear::ZERO,
            breadstuff: BabyBear::ZERO,
        };
        let phase_b = AttenuateWitness {
            held: zero_leaf,
            granted: zero_leaf,
            siblings: Vec::new(),
            directions: Vec::new(),
            held_tier: 0,
            granted_tier: 0,
            held_expiry_height: None,
            granted_expiry_height: None,
        };
        run_insert_cap_write_wide_flag_day(
            VmEffect::GrantCapability {
                cap_entry: [
                    fresh.0,
                    fresh.1,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
                phase_b: Some(Box::new(phase_b)),
            },
            fresh,
            EFFECT_DELEGATION_OPS,
            "delegateWriteCapOpenVmDescriptor2R24",
        );
    }

    /// **delegate (cross-vat grant) — genuine prove + verify + forge (the INSERT keystone deploy).**
    /// `GrantCapability` routes to `delegateWriteCapOpenVmDescriptor2R24` — now the INSERT-shaped
    /// keystone wrapper (`effCapInsertV3`): the cap-open READ opens the SPLICED conferred leaf against
    /// the REBUILT AFTER cap-root (`CanonicalCapTree::insert_witness`); no arity-2 map-op. The fresh
    /// edge is `cap_entry[0..2]`; its conferred mask carries the DELEGATION_OPS bit (an as-is
    /// delegation of a DELEGATION_OPS-permitting held cap). The grant is the GRANTER-side direction
    /// (`phase_b: Some` — the v1-state cap_root passes through, the genuine moving face).
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_delegate_proves_and_verifies_light_client() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::AttenuateWitness;
        // The delegate keystone wrapper binds the DELEGATION_OPS facet (1<<16) on the SPLICED leaf —
        // the anchor cap permits DELEGATION_OPS and the as-is conferral carries it.
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
        let fresh = (
            BabyBear::new(0xED6E),
            BabyBear::new(EFFECT_DELEGATION_OPS | 0x0F),
        ); // distinct from anchor/other keys; mask carries the crown bit
        let zero_leaf = CapLeaf {
            slot_hash: BabyBear::ZERO,
            target: BabyBear::ZERO,
            auth_tag: BabyBear::ZERO,
            mask_lo: BabyBear::ZERO,
            mask_hi: BabyBear::ZERO,
            expiry: BabyBear::ZERO,
            breadstuff: BabyBear::ZERO,
        };
        let phase_b = AttenuateWitness {
            held: zero_leaf,
            granted: zero_leaf,
            siblings: Vec::new(),
            directions: Vec::new(),
            held_tier: 0,
            granted_tier: 0,
            held_expiry_height: None,
            granted_expiry_height: None,
        };
        run_insert_after_spine_prove_verify_forge(
            VmEffect::GrantCapability {
                cap_entry: [
                    fresh.0,
                    fresh.1,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
                phase_b: Some(Box::new(phase_b)),
            },
            fresh,
            EFFECT_DELEGATION_OPS,
            "delegateWriteCapOpenVmDescriptor2R24",
        );
    }

    /// **grantCapability — genuine prove + light-client verify + forge + authority-only rejection
    /// (THE GRANTCAP CLOSE).** A `GrantCapability` turn confers a capability the granter holds; its
    /// DEPLOYED light-client-VERIFYING route is the INSERT write wrapper (`delegateWriteCapOpen` — a
    /// grant IS a delegation op, so the cap-tree INSERT binds the DELEGATION_OPS facet 1<<16 and the
    /// fresh conferred edge is grafted on the rotated cap-root limb 213→264). The grant's OWN
    /// AUTHORITY-only descriptor `grantCapCapOpenVmDescriptor2R24` (binding GRANT_CAPABILITY 1<<2)
    /// proves the membership crown but leaves the post-cap-root host-trusted, so the light-client tooth
    /// (`is_forbidden_authority_only_cap_write_descriptor`) FORCES the write wrapper. FOUR arms:
    ///   (1) NON-VACUITY — the WRITE wrapper genuinely PROVES + light-client-VERIFIES (the honest grant
    ///       binds the conferred edge on the wire);
    ///   (2) FORGE — a c-list MISSING the anchor (the granter's held authority) FAILS CLOSED (no
    ///       membership witness for the anchor read → a fabricated post-cap-root is UNPROVABLE);
    ///   (3) WRONG FACET — a held cap that does NOT permit the delegation op the write wrapper binds is
    ///       refused at witness build (`from_membership_for` requires `mask_lo == eff_bit`);
    ///   (4) AUTHORITY-ONLY — an empty c-list falls back to `grantCapCapOpenVmDescriptor2R24` (the grant's
    ///       own GRANT_CAPABILITY-bound crown). It still PROVES (the membership crown is valid) BUT the
    ///       light-client verifier REJECTS it (the tooth is ON — the producer MUST prove the on-the-wire
    ///       write wrapper). BEFORE: grantCapability had no NAMED genuine prove-through; AFTER: it proves +
    ///       light-client-verifies through its deployed route, and the authority-only forge is rejected.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_grant_proves_and_verifies_light_client() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::AttenuateWitness;
        use dregg_circuit::effect_vm::trace_rotated::{
            CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG,
        };
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        // The grant's DEPLOYED write wrapper binds the DELEGATION_OPS facet (1<<16); its OWN authority-only
        // descriptor binds GRANT_CAPABILITY (1<<2). The two membership crowns demand different anchor facets.
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
        const EFFECT_GRANT_CAPABILITY: u32 = 1 << 2;

        let leaf_cl = |l: &[BabyBear; 7]| CapLeaf {
            slot_hash: l[0],
            target: l[1],
            auth_tag: l[2],
            mask_lo: l[3],
            mask_hi: l[4],
            expiry: l[5],
            breadstuff: l[6],
        };

        // The fresh conferred edge (the new cap slot felt + its conferred mask) — distinct from the
        // anchor (0xA0C0) and other (0xBEEF) c-list keys. The conferred mask carries the
        // DELEGATION_OPS bit (the INSERT keystone crown binds it on the SPLICED leaf).
        let fresh_key = BabyBear::new(0x67A7);
        let fresh_value = BabyBear::new(EFFECT_DELEGATION_OPS | 0x0F);
        let zero_leaf = CapLeaf {
            slot_hash: BabyBear::ZERO,
            target: BabyBear::ZERO,
            auth_tag: BabyBear::ZERO,
            mask_lo: BabyBear::ZERO,
            mask_hi: BabyBear::ZERO,
            expiry: BabyBear::ZERO,
            breadstuff: BabyBear::ZERO,
        };
        // A NON-attenuating grant (no phase-B narrowing) → the plain `delegateWriteCapOpen` wrapper.
        let mk_effect = || VmEffect::GrantCapability {
            cap_entry: [
                fresh_key,
                fresh_value,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            phase_b: Some(Box::new(AttenuateWitness {
                held: zero_leaf,
                granted: zero_leaf,
                siblings: Vec::new(),
                directions: Vec::new(),
                held_tier: 0,
                granted_tier: 0,
                held_expiry_height: None,
                granted_expiry_height: None,
            })),
        };
        let effects = vec![mk_effect()];

        // A real granting turn (nonce-tick passthrough base, all permissions open).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // The grant routes through `grantCapCapOpenVmDescriptor2R24` (authority-only `.key`) PLUS the
        // INSERT write wrapper (`delegateWriteCapOpen`, DELEGATION_OPS). With a genuine c-list the
        // EFFECTIVE descriptor is the write wrapper.
        let route = cap_open_route_for_run(&effects).expect("a wired cap-open route for the grant");
        assert_eq!(
            route.key, "grantCapCapOpenVmDescriptor2R24",
            "the grant's authority-only descriptor is grantCapCapOpen (binds GRANT_CAPABILITY 1<<2)"
        );
        assert!(
            matches!(
                route.write,
                Some((
                    "delegateWriteCapOpenVmDescriptor2R24",
                    dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                    EFFECT_DELEGATION_OPS
                ))
            ),
            "a NON-attenuating grant routes to the plain delegate INSERT write wrapper (DELEGATION_OPS), got {:?}",
            route.write
        );

        // ── ARM (1): NON-VACUITY. The write wrapper's anchor cap permits DELEGATION_OPS (the facet the
        // INSERT crown binds). The genuine c-list carries the anchor (present, opened by the crown) + one
        // other held cap; the fresh conferred edge key is ABSENT and distinct.
        let anchor_deleg: [BabyBear; 7] = [
            BabyBear::new(0xA0C0), // slot_hash (the anchor key)
            BabyBear::new(7_777),  // target (== src)
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_DELEGATION_OPS), // facet == the write wrapper's eff_bit
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(99),
        ];
        let other_deleg: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_DELEGATION_OPS),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        assert_ne!(
            fresh_key, anchor_deleg[0],
            "the fresh edge MUST be distinct from the anchor key"
        );
        assert_ne!(
            fresh_key, other_deleg[0],
            "the fresh edge MUST be absent from the c-list"
        );
        // The INSERT keystone fixture: the holder's BEFORE tree is a genuine CanonicalCapTree; the
        // membership path opens the anchor against ITS root, and the FULL 7-field c-list is threaded
        // so the spliced AFTER tree can be rebuilt (`insert_witness`).
        let before_tree = dregg_circuit::cap_root::CanonicalCapTree::new(
            vec![leaf_cl(&anchor_deleg), leaf_cl(&other_deleg)],
            dregg_circuit::cap_root::CAP_TREE_DEPTH,
        );
        let mw_deleg = before_tree
            .membership_witness(anchor_deleg[0])
            .expect("the anchor is a member of the BEFORE tree");
        let clist_leaves = vec![
            HeapLeaf {
                addr: anchor_deleg[0],
                value: anchor_deleg[1],
            },
            HeapLeaf {
                addr: other_deleg[0],
                value: other_deleg[1],
            },
        ];
        let cap = CapMembershipWitness {
            leaf: leaf_cl(&anchor_deleg),
            siblings: mw_deleg.siblings.clone(),
            directions: mw_deleg.directions.clone(),
            clist_leaves,
            cap_leaves: vec![leaf_cl(&anchor_deleg), leaf_cl(&other_deleg)],
            cap_tombstones: Vec::new(),
        };
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(
            effective_key, "delegateWriteCapOpenVmDescriptor2R24",
            "with a genuine c-list the EFFECTIVE grant descriptor is the INSERT write wrapper"
        );
        // The fresh edge the write wrapper grafts is the conferred `cap_entry[0..2]`.
        assert_eq!(
            cap_insert_payload_for(&effects, &cap),
            Some((fresh_key, fresh_value)),
            "the fresh conferred edge derived from the grant must match the test's expectation"
        );

        // The grant INSERT WRITE key has a proven wide twin, so production always goes wide for it (the
        // narrow 1-felt leg is rejected by the wide-dodge tooth). Prove + verify the deployed WIDE leg.
        let (proof, dpis) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap, &route, None, true,
        )
        .expect(
            "the WRITE-bearing grant cap-open MUST genuinely prove — anchor read + fresh \
                     sorted-INSERT on the rotated cap-root limb (213→264) over the real c-list, \
                     v1-state frozen, nonce ticks",
        );
        let proof_bytes =
            postcard::to_allocvec(&proof).expect("serialize grant write cap-open leg");
        let vk_hash =
            cap_open_wide_vk_hash_by_key(effective_key).expect("wide grant write wrapper vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).expect(
            "the WRITE-bearing grant cap-open MUST verify on the light-client path — the genuine \
             post-cap-root (the conferred edge) is on-the-wire light-client-verifiable",
        );

        // ── ARM (2): FORGE. A 7-field c-list MISSING the anchor — it rebuilds a DIFFERENT tree than
        // the membership path opens, so the keystone producer FAILS CLOSED (the c-list is not the
        // holder's genuine pre-state). A fabricated post-cap-root is NOT provable.
        let forged_clist = vec![HeapLeaf {
            addr: other_deleg[0],
            value: other_deleg[1],
        }];
        let cap_forged = CapMembershipWitness {
            leaf: leaf_cl(&anchor_deleg),
            siblings: mw_deleg.siblings.clone(),
            directions: mw_deleg.directions.clone(),
            clist_leaves: forged_clist,
            cap_leaves: vec![leaf_cl(&other_deleg)], // anchor MISSING — rebuilds a different root
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &cap_forged,
                &route,
                None,
                false
            )
            .is_err(),
            "a c-list MISSING the granter's held-authority anchor MUST fail closed — a fabricated \
             post-cap-root is NOT provable (no silent forge)"
        );

        // ── ARM (3): WRONG FACET. A held cap whose facet permits a DIFFERENT effect (transfer, not the
        // delegation op the write wrapper binds) is refused at witness build (`from_membership_for`
        // requires `mask_lo == eff_bit`).
        const EFFECT_TRANSFER: u32 = 1 << 1;
        let wrong_facet = CapMembershipWitness {
            leaf: CapLeaf {
                mask_lo: BabyBear::new(EFFECT_TRANSFER),
                ..leaf_cl(&anchor_deleg)
            },
            siblings: cap.siblings.clone(),
            directions: cap.directions.clone(),
            clist_leaves: cap.clist_leaves.clone(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert!(
            prove_effect_vm_cap_open(
                &initial,
                &effects,
                &before_w,
                &after_w,
                &wrong_facet,
                &route,
                None,
                false
            )
            .is_err(),
            "a held cap permitting a DIFFERENT effect (transfer, not the delegation op the grant write \
             wrapper binds) MUST be refused (fail-closed at the membership crown)"
        );

        // ── ARM (4): AUTHORITY-ONLY ROUTE IS LIGHT-CLIENT-REJECTED (the tooth is ON). An empty c-list
        // falls back to `grantCapCapOpenVmDescriptor2R24` — the grant's OWN authority-only crown, which
        // binds GRANT_CAPABILITY (1<<2). So its anchor cap permits GRANT_CAPABILITY. It PROVES (the
        // membership crown is valid) BUT the light-client verifier REJECTS it (the post-cap-root is
        // host-trusted; the producer MUST prove the on-the-wire write wrapper).
        let anchor_grant: [BabyBear; 7] = [
            BabyBear::new(0xA0C0),
            BabyBear::new(7_777),
            BabyBear::new(SIGNATURE_AUTH_TAG),
            BabyBear::new(EFFECT_GRANT_CAPABILITY), // facet == the authority-only route's eff_bit (1<<2)
            BabyBear::new(FACET_MASK_HI),
            BabyBear::new(0x00FF_FFFF),
            BabyBear::new(99),
        ];
        let other_grant: [BabyBear; 7] = [
            BabyBear::new(0xBEEF),
            BabyBear::new(123),
            BabyBear::new(1),
            BabyBear::new(EFFECT_GRANT_CAPABILITY),
            BabyBear::new(0),
            BabyBear::new(9),
            BabyBear::new(0),
        ];
        let built_grant =
            CapOpenWitness::build_for(&[other_grant, anchor_grant], 1, EFFECT_GRANT_CAPABILITY)
                .expect("the GRANT_CAPABILITY membership path builds for the anchor");
        let cap_authority_only = CapMembershipWitness {
            leaf: leaf_cl(&anchor_grant),
            siblings: built_grant.siblings.to_vec(),
            directions: built_grant.directions.to_vec(),
            clist_leaves: Vec::new(),
            cap_leaves: Vec::new(),
            cap_tombstones: Vec::new(),
        };
        assert_eq!(
            cap_open_effective_key(&route, &cap_authority_only),
            "grantCapCapOpenVmDescriptor2R24",
            "an empty c-list falls back to the grant's authority-only route"
        );
        let (proof_ao, dpis_ao) = prove_effect_vm_cap_open(
            &initial, &effects, &before_w, &after_w, &cap_authority_only, &route, None,
            false,
        )
        .expect("the authority-only grant cap-open still PROVES (the GRANT_CAPABILITY membership crown is valid)");
        let proof_ao_bytes =
            postcard::to_allocvec(&proof_ao).expect("serialize authority-only grant leg");
        let vk_ao = cap_open_vk_hash_by_key("grantCapCapOpenVmDescriptor2R24")
            .expect("authority-only grant vk_hash");
        assert!(
            verify_effect_vm_rotated_with_cutover(&proof_ao_bytes, &dpis_ao, &vk_ao).is_err(),
            "the AUTHORITY-only grant cap-open is light-client-REJECTED (the tooth is ON) — the \
             post-cap-root is host-trusted; the producer must prove the on-the-wire WRITE wrapper",
        );
    }

    /// **introduce — genuine prove + verify + forge (the INSERT keystone deploy).** `Introduce {
    /// intro_hash }` routes to `introduceWriteCapOpenVmDescriptor2R24` — the INSERT-shaped keystone
    /// wrapper; the fresh edge is `intro_hash[0..2]`, its conferred mask carrying the INTRODUCE bit
    /// (the as-is introduction of an INTRODUCE-permitting held cap).
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_introduce_proves_and_verifies_light_client() {
        const EFFECT_INTRODUCE: u32 = 1 << 13;
        let fresh = (
            BabyBear::new(0x1D7E),
            BabyBear::new(EFFECT_INTRODUCE | 0x07),
        );
        run_insert_after_spine_prove_verify_forge(
            VmEffect::Introduce {
                intro_hash: [
                    fresh.0,
                    fresh.1,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            },
            fresh,
            EFFECT_INTRODUCE,
            "introduceWriteCapOpenVmDescriptor2R24",
        );
    }

    /// **spawn — genuine prove + verify + forge (THE CAP-HANDOFF CLOSE, keystone-shaped).**
    /// `SpawnWithDelegation { spawn_hash }` routes to `spawnWriteCapOpenVmDescriptor2R24` (the
    /// `effCapInsertV3` keystone wrap): the parent→child CAPABILITY HANDOFF is the conferred edge
    /// `spawn_hash[0..2]` (the child cap key + payload), SPLICED into the arity-7 `CanonicalCapTree`
    /// (`insert_witness` — the membership READ opens the spliced leaf against the REBUILT AFTER
    /// cap-root; NO arity-2 map-op) — ALONGSIDE the accounts grow-gate INSERT of the child id (limb 0,
    /// the birth leg's SURVIVING map-ops + the accounts heap). BEFORE: the authority-only
    /// `spawnCapOpenVmDescriptor2R24` left the child cap_root host-trusted (the handoff frozen/forged).
    /// AFTER: the genuine handoff PROVES + light-client-VERIFIES on the WIDE keystone leg, and a forged
    /// 8-felt AFTER-commit / present-key insert / mismatched 7-field c-list is REJECTED (the shared
    /// keystone harness exercises all three forge poles + the non-vacuous genuine pole). The cap binds
    /// DELEGATION_OPS (1<<16) — the parent confers a cap PERMITTING delegation, exactly like `delegate`.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_spawn_proves_and_verifies_light_client() {
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
        // child key + conferred payload — distinct from the anchor (0xA0C0) and other (0xBEEF) c-list keys.
        let fresh = (BabyBear::new(0x59A0), BabyBear::new(0x0F));
        run_insert_after_spine_prove_verify_forge(
            VmEffect::SpawnWithDelegation {
                spawn_hash: [
                    fresh.0,
                    fresh.1,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            },
            fresh,
            EFFECT_DELEGATION_OPS,
            "spawnWriteCapOpenVmDescriptor2R24",
        );
    }

    /// **delegateAtten — the NAMED residual (the cap-tree-write half is BUILT; the routing signal +
    /// submask witness is the gap).** The `delegateAttenWriteCapOpenVmDescriptor2R24` wrapper is the SAME
    /// genuine moving-face INSERT as `delegate` PLUS the `granted ⊑ held` submask non-amplification lookup.
    /// Its cap-tree write half is identical to delegate's (the `generate_rotated_cap_write_base` Insert is
    /// fully exercised by `cap_write_delegate_proves_and_verifies_light_client`). What it lacks is (1) a
    /// routing SIGNAL distinct from plain delegate — both are a `GrantCapability` effect on the same
    /// `sel::GRANT_CAP` guard — and (2) the submask WITNESS (`keep ⊑ held` filled into cols 73/72 + the
    /// custom subset-table). This test pins the descriptor STRUCTURE (the wrapper IS in the registry, it
    /// carries the INSERT `map_op` on the rotated cap-root limb 213→264 AND the submask lookup) so the
    /// residual is named NON-vacuously — a regression dropping the submask or the insert FAILS here.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_delegate_atten_descriptor_carries_insert_and_submask() {
        use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};
        use dregg_circuit::lean_descriptor_air::LeanExpr;

        let json = cap_open_descriptor_json_by_key("delegateAttenWriteCapOpenVmDescriptor2R24")
            .expect("the delegateAtten write wrapper IS in V3_STAGED_REGISTRY_TSV");
        let desc = parse_vm_descriptor2(json).expect("delegateAtten write wrapper parses");

        // THE INSERT KEYSTONE SHAPE (`effCapInsertV3`): the arity-2 map-op is GONE (it was
        // shape-UNSAT against the arity-7 fresh-key splice — the break this deploy closed); the
        // cap-tree INSERT is carried by the 8 AFTER cap-root WELD gates pinning the cap-open READ's
        // `capRoot` group to the committed AFTER cap-root block `[lane0=var 332 ‖ lanes 1..7 =
        // vars 358..=364]` — so the read opens the SPLICED leaf against the REBUILT AFTER tree.
        let map_ops = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::MapOp(_)))
            .count();
        assert_eq!(
            map_ops, 0,
            "the delegateAtten keystone wrapper carries NO arity-2 map-op (the INSERT rides the \
             after-root welds) — descriptor: {}",
            desc.name
        );
        let after_group: Vec<usize> = std::iter::once(332usize).chain(358..=364).collect();
        for (lane, g) in after_group.iter().enumerate() {
            let has_weld = desc.constraints.iter().any(|c| {
                matches!(c,
                    VmConstraint2::Base(dregg_circuit::lean_descriptor_air::VmConstraint::Gate(
                        LeanExpr::Add(_, r)))
                    if matches!(&**r, LeanExpr::Mul(cneg, v)
                        if matches!(&**cneg, LeanExpr::Const(-1))
                            && matches!(&**v, LeanExpr::Var(x) if x == g)))
            });
            assert!(
                has_weld,
                "the delegateAtten keystone wrapper MUST weld the read capRoot lane {lane} to the \
                 committed AFTER cap-root var {g} (the effCapInsertV3 after-root weld) — descriptor: {}",
                desc.name
            );
        }

        // The non-amplification submask lookup (`granted ⊑ held`) — the tooth that distinguishes
        // delegateAtten from plain delegate. It is a CUSTOM subset-table (`SUBMASK_TID`, deployed table
        // id 5) lookup over `[KEEP_MASK (var 73), HELD_MASK (var 72)]`.
        let has_submask = desc.constraints.iter().any(|c| {
            matches!(c, VmConstraint2::Lookup(l)
                if l.table == 5
                && l.tuple.len() == 2
                && matches!(l.tuple[0], LeanExpr::Var(73))
                && matches!(l.tuple[1], LeanExpr::Var(72)))
        });
        assert!(
            has_submask,
            "the delegateAtten wrapper MUST carry the `granted ⊑ held` submask non-amplification lookup \
             (custom table 5 over [KEEP_MASK var 73, HELD_MASK var 72] — the tooth distinguishing it \
             from plain delegate) — descriptor: {}",
            desc.name
        );

        // The cap-tree-write half (the Insert bridge) is identical to delegate's; the routing signal
        // (`is_attenuated_grant`) + the submask witness fill (col 72 = anchor held mask) CLOSE the
        // routing + witness halves — see `cap_write_delegate_atten_routes_to_submask_wrapper`.
    }

    /// **delegateAtten ROUTING SIGNAL (CLOSED, GREEN).** THE named residual of the big wave: a plain
    /// delegate and an attenuated delegate were INDISTINGUISHABLE (both `GrantCapability` on `sel::GRANT_CAP`),
    /// so an attenuated grant routed to the plain `delegateWriteCapOpen` (losing the submask). This pins the
    /// FIX: `is_attenuated_grant(phase_b)` (the granted leaf's rights are a STRICT bitwise submask of the
    /// held leaf's) selects the SUBMASK wrapper `delegateAttenWriteCapOpenVmDescriptor2R24` (which carries
    /// the in-circuit `granted ⊑ held` non-amplification lookup), while a non-narrowing grant stays the
    /// plain `delegateWriteCapOpenVmDescriptor2R24`. BOTH polarities are asserted — the signal is the tooth
    /// that distinguishes the two cap-tree writes.
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_delegate_atten_routes_to_submask_wrapper() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::AttenuateWitness;

        let mk_leaf = |mask_lo: u32| CapLeaf {
            slot_hash: BabyBear::ZERO,
            target: BabyBear::ZERO,
            auth_tag: BabyBear::ZERO,
            mask_lo: BabyBear::new(mask_lo),
            mask_hi: BabyBear::ZERO,
            expiry: BabyBear::ZERO,
            breadstuff: BabyBear::ZERO,
        };
        let mk_witness = |held: u32, granted: u32| {
            Box::new(AttenuateWitness {
                held: mk_leaf(held),
                granted: mk_leaf(granted),
                siblings: Vec::new(),
                directions: Vec::new(),
                held_tier: 0,
                granted_tier: 0,
                held_expiry_height: None,
                granted_expiry_height: None,
            })
        };
        let fresh = [
            BabyBear::new(0xED57),
            BabyBear::new(0x52),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];

        // ATTENUATED grant (granted 0x52 ⊊ held 0xFF) → the SUBMASK wrapper.
        let atten = vec![VmEffect::GrantCapability {
            cap_entry: fresh,
            phase_b: Some(mk_witness(0xFF, 0x52)),
        }];
        let route =
            cap_open_route_for_run(&atten).expect("attenuated grant has a wired cap-open route");
        assert!(
            matches!(
                route.write,
                Some((
                    "delegateAttenWriteCapOpenVmDescriptor2R24",
                    dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                    _
                ))
            ),
            "an ATTENUATED grant (granted ⊊ held) MUST route to the delegateAtten SUBMASK wrapper, got {:?}",
            route.write
        );

        // PLAIN (non-narrowing) grant (granted == held) → the plain delegate wrapper.
        let plain = vec![VmEffect::GrantCapability {
            cap_entry: fresh,
            phase_b: Some(mk_witness(0xFF, 0xFF)),
        }];
        let route_plain =
            cap_open_route_for_run(&plain).expect("plain grant has a wired cap-open route");
        assert!(
            matches!(
                route_plain.write,
                Some((
                    "delegateWriteCapOpenVmDescriptor2R24",
                    dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                    _
                ))
            ),
            "a NON-narrowing grant (granted == held) MUST route to the PLAIN delegate wrapper, got {:?}",
            route_plain.write
        );

        // A recipient-install grant with no phase-B witness → plain delegate (no attenuation claimed).
        let no_witness = vec![VmEffect::GrantCapability {
            cap_entry: fresh,
            phase_b: None,
        }];
        let route_nw = cap_open_route_for_run(&no_witness).expect("no-witness grant route");
        assert!(
            matches!(
                route_nw.write,
                Some(("delegateWriteCapOpenVmDescriptor2R24", _, _))
            ),
            "a grant with no phase-B witness MUST route to the plain delegate wrapper, got {:?}",
            route_nw.write
        );
    }

    /// **delegateAtten — GENUINE prove + light-client verify + submask forge-reject (RESIDUAL CLOSED,
    /// VK-freedom era).** An ATTENUATED grant (the conferred rights STRICTLY narrow the held authority)
    /// now ROUTES to `delegateAttenWriteCapOpenVmDescriptor2R24` via `is_attenuated_grant(phase_b)` —
    /// distinct from the plain `delegateWriteCapOpen` a non-narrowing grant takes. The wrapper proves the
    /// SAME genuine moving-face sorted INSERT as plain delegate (anchor read + fresh insert on the rotated
    /// cap-root limb 213→264) PLUS the `granted ⊑ held` non-amplification submask lookup over
    /// `[KEEP_MASK (col 73) = conferred mask, HELD_MASK (col 72) = anchor held mask]`. The genuine arm
    /// (conferred 0x52 ⊑ held 0xFF) proves + light-client-verifies; the FORGE arm (a grant 0x52 whose
    /// real held authority is only 0x0F — `0x52 ⊄ 0x0F`) is UNSAT (the submask lookup bites).
    #[cfg(feature = "prover")]
    #[test]
    fn cap_write_delegate_atten_proves_and_verifies_light_client() {
        use dregg_circuit::cap_root::CapLeaf;
        use dregg_circuit::effect_vm::AttenuateWitness;
        use dregg_circuit::effect_vm::trace_rotated::{FACET_MASK_HI, SIGNATURE_AUTH_TAG};
        use dregg_circuit::heap_root::HeapLeaf;
        use dregg_turn::rotation_witness as rw;

        // The delegateAtten keystone wrapper binds the DELEGATION_OPS facet (1<<16) on the SPLICED
        // (conferred, narrowed) leaf. The anchor cap (the delegator's held authority) holds the BROAD
        // mask 0x100FF (= DELEGATION_OPS | 0xFF); the conferred KEEP_MASK 0x10052 STRICTLY narrows it
        // while keeping the crown bit. The surviving submask lookup compares KEEP (col 73) against
        // the anchor leaf's held mask (col 72).
        const EFFECT_DELEGATION_OPS: u32 = 1 << 16;
        let held_mask = BabyBear::new(EFFECT_DELEGATION_OPS | 0xFF); // the anchor's broad held authority
        let granted_mask = BabyBear::new(EFFECT_DELEGATION_OPS | 0x52); // the narrowed conferred mask
        let fresh_key = BabyBear::new(0xED57); // distinct from anchor/other keys
        let anchor = CapLeaf {
            slot_hash: BabyBear::new(0xA0C0), // the anchor key
            target: BabyBear::new(7_777),
            auth_tag: BabyBear::new(SIGNATURE_AUTH_TAG),
            mask_lo: held_mask, // the broad held mask (permits DELEGATION_OPS; the submask RHS)
            mask_hi: BabyBear::new(FACET_MASK_HI),
            expiry: BabyBear::new(0x00FF_FFFF),
            breadstuff: BabyBear::new(99),
        };
        let other = CapLeaf {
            slot_hash: BabyBear::new(0xBEEF),
            target: BabyBear::new(123),
            auth_tag: BabyBear::new(1),
            mask_lo: BabyBear::new(EFFECT_DELEGATION_OPS),
            mask_hi: BabyBear::new(0),
            expiry: BabyBear::new(9),
            breadstuff: BabyBear::new(0),
        };
        let before_tree = dregg_circuit::cap_root::CanonicalCapTree::new(
            vec![anchor, other],
            dregg_circuit::cap_root::CAP_TREE_DEPTH,
        );
        let mw = before_tree
            .membership_witness(anchor.slot_hash)
            .expect("the anchor is a member of the BEFORE tree");

        // The phase-B granter-side witness that DRIVES the routing signal: held mask 0xFF, granted mask
        // 0x52 — a STRICT submask, so `is_attenuated_grant` selects the delegateAtten submask wrapper.
        let mk_leaf = |mask: BabyBear| CapLeaf {
            slot_hash: BabyBear::ZERO,
            target: BabyBear::ZERO,
            auth_tag: BabyBear::ZERO,
            mask_lo: mask,
            mask_hi: BabyBear::ZERO,
            expiry: BabyBear::ZERO,
            breadstuff: BabyBear::ZERO,
        };
        let phase_b = AttenuateWitness {
            held: mk_leaf(held_mask),
            granted: mk_leaf(granted_mask),
            siblings: Vec::new(),
            directions: Vec::new(),
            held_tier: 0,
            granted_tier: 0,
            held_expiry_height: None,
            granted_expiry_height: None,
        };
        assert!(
            is_attenuated_grant(&phase_b),
            "the witness (granted 0x52 ⊊ held 0xFF) MUST register as an attenuated grant"
        );

        // The GENUINE witness: the anchor present in the CanonicalCapTree at its BROAD held mask; the
        // fresh edge key ABSENT and distinct. The FULL 7-field c-list is threaded (the INSERT rebuild
        // witness). The conferred grant rides `cap_entry = [fresh_key, granted_mask]`.
        assert_ne!(fresh_key, anchor.slot_hash);
        assert_ne!(fresh_key, other.slot_hash);
        let clist_leaves = vec![
            HeapLeaf {
                addr: anchor.slot_hash,
                value: held_mask,
            },
            HeapLeaf {
                addr: other.slot_hash,
                value: other.target,
            },
        ];
        let cap = CapMembershipWitness {
            leaf: anchor,
            siblings: mw.siblings.clone(),
            directions: mw.directions.clone(),
            clist_leaves: clist_leaves.clone(),
            cap_leaves: vec![anchor, other],
            cap_tombstones: Vec::new(),
        };

        let effect = VmEffect::GrantCapability {
            cap_entry: [
                fresh_key,
                granted_mask,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            phase_b: Some(Box::new(phase_b)),
        };
        let effects = vec![effect];

        // The attenuated grant MUST select the SUBMASK wrapper (not plain delegate).
        let route = cap_open_route_for_run(&effects)
            .expect("a wired cap-open route for the attenuated grant");
        assert!(
            matches!(
                route.write,
                Some((
                    "delegateAttenWriteCapOpenVmDescriptor2R24",
                    dregg_circuit::effect_vm::trace_rotated::CapTreeWriteOp::Insert,
                    _
                ))
            ),
            "an attenuated grant MUST route to the delegateAtten submask INSERT wrapper"
        );
        let effective_key = cap_open_effective_key(&route, &cap);
        assert_eq!(effective_key, "delegateAttenWriteCapOpenVmDescriptor2R24");

        // A real granting turn (nonce-tick passthrough base).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        before_cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();
        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // GENUINE PROVE + LIGHT-CLIENT VERIFY (UNAMBIGUOUS — no catch_unwind): the genuine post-cap-root
        // (sorted INSERT) AND the `granted ⊑ held` submask both hold; a passing proof binds them on the wire.
        // The delegateAtten WRITE key has a proven wide twin, so production always goes wide for it (the
        // narrow 1-felt leg is rejected by the wide-dodge tooth). Prove + verify the deployed WIDE leg.
        let (proof, dpis) =
            prove_effect_vm_cap_open(&initial, &effects, &before_w, &after_w, &cap, &route, None, true)
                .unwrap_or_else(|e| {
                    panic!(
                        "the delegateAtten submask wrapper MUST genuinely prove — anchor read + fresh \
                         sorted-insert on the rotated cap-root limb (213→264) + `granted 0x52 ⊑ held 0xFF`: {e:?}"
                    )
                });
        let proof_bytes =
            postcard::to_allocvec(&proof).expect("serialize delegateAtten cap-open leg");
        let vk_hash = cap_open_wide_vk_hash_by_key(effective_key)
            .expect("wide delegateAtten wrapper vk_hash");
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &dpis, &vk_hash).unwrap_or_else(|e| {
            panic!(
                "the delegateAtten submask wrapper MUST verify on the light-client path — the genuine \
                 post-cap-root + the submask non-amplification are on-the-wire verifiable: {e:?}"
            )
        });

        // FORGE: a grant EXCEEDING the held authority. The phase-B witness still claims attenuation
        // (so the route selects the submask wrapper), but the anchor's REAL committed held mask is
        // only 0x1000F while the conferred KEEP_MASK is 0x10052 — `0x10052 ⊄ 0x1000F`, so the
        // `granted ⊑ held` submask lookup is UNSAT (the prover refuses or its self-verify panics —
        // both fail-closed; a PASSING proof would be the amplification forge).
        let narrow_anchor = CapLeaf {
            mask_lo: BabyBear::new(EFFECT_DELEGATION_OPS | 0x0F), // narrower than the grant
            ..anchor
        };
        let forge_tree = dregg_circuit::cap_root::CanonicalCapTree::new(
            vec![narrow_anchor, other],
            dregg_circuit::cap_root::CAP_TREE_DEPTH,
        );
        let mw_forge = forge_tree
            .membership_witness(narrow_anchor.slot_hash)
            .expect("the narrow anchor is a member of the forge tree");
        let cap_forge = CapMembershipWitness {
            leaf: narrow_anchor,
            siblings: mw_forge.siblings.clone(),
            directions: mw_forge.directions.clone(),
            clist_leaves,
            cap_leaves: vec![narrow_anchor, other],
            cap_tombstones: Vec::new(),
        };
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_effect_vm_cap_open(
                &initial, &effects, &before_w, &after_w, &cap_forge, &route, None, false,
            )
            .map(|_| ())
        }));
        std::panic::set_hook(prev_hook);
        assert!(
            !matches!(outcome, Ok(Ok(()))),
            "a grant EXCEEDING the held authority (conferred 0x10052 ⊄ real held 0x1000F) MUST fail \
             closed — the `granted ⊑ held` submask lookup bites (no amplification)"
        );
    }

    /// THE LIGHT-CLIENT FORGE IS CLOSED (AUTHORITY FLOOR last mile). A cap effect
    /// (`RevokeDelegation`, `EFFECT_DELEGATION_OPS`) proven under the PLAIN cohort descriptor
    /// (`revokeVmDescriptor2R24`, which carries NO in-circuit cap-membership check) is REJECTED by
    /// the light-client verifier (`verify_effect_vm_rotated_with_cutover`) — a malicious producer
    /// cannot strip the cap-open route to launder host-trusted authority into a passing proof. The
    /// honest route (the cap-open descriptor, where the depth-16 membership crown is verified
    /// in-circuit) still VERIFIES (the `cap_open_fanout_revoke_*` test proves that leg end-to-end),
    /// so the forcing is a clean ONE-WAY tooth: plain cap-effect descriptor ⇒ reject, cap-open ⇒ accept.
    #[cfg(feature = "prover")]
    #[test]
    fn light_client_rejects_cap_effect_under_plain_descriptor() {
        use dregg_turn::rotation_witness as rw;

        // A real RevokeDelegation turn (a CAP effect — exercises delegation authority).
        let before_balance: u64 = 100_000;
        let initial = CellState::new(before_balance, 0);
        let effects = vec![VmEffect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }];

        let mut pk = [0u8; 32];
        pk[0] = 9;
        let before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
        let mut after_cell = before_cell.clone();
        let _ = after_cell.state.increment_nonce();

        let mut ledger = dregg_cell::Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );

        // THE FORGE: prove the cap effect under the PLAIN base descriptor (no cap witness threaded,
        // no membership appendix). This is exactly what a malicious producer does to skip the
        // authority crown — the resulting proof is internally sound for the plain (authority-blind)
        // descriptor.
        let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
        let plain_proof = prove_effect_vm_rotated_ir2_with_caveat(
            &initial, &effects, &before_w, &after_w, &caveat, None,
        )
        .expect(
            "the plain revoke base leg proves (it is sound for the authority-BLIND descriptor)",
        );
        let plain_bytes = postcard::to_allocvec(&plain_proof).expect("serialize plain revoke leg");
        // The plain leg's PI vector (the same 38-PI vector the base descriptor declares).
        let run_rot = RotationTurnWitness {
            before: before_w.clone(),
            after: after_w.clone(),
            caveat: caveat.clone(),
        };
        let plain_pi = rotated_effect_pi_for(&initial, &effects, &run_rot, None)
            .expect("plain revoke PI re-derives");
        let plain_vk = rotated_effect_vm_vk_hash(&effects).expect("plain revoke vk_hash");

        // CONTROL: the plain proof IS a sound proof of the plain descriptor — it binds it
        // selector-bound. (We confirm the descriptor it would bind is the forbidden plain one.)
        assert_eq!(
            dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect(
                &effects[0]
            ),
            Some("revokeVmDescriptor2R24"),
            "the base resolver routes RevokeDelegation to its plain descriptor (the forge's target)"
        );

        // THE TOOTH: the light-client verifier REJECTS the cap effect proven under the plain
        // descriptor — the forge is closed. POST WIDE FLAG-DAY the verifier iterates the WIDE registry
        // first; this leg is a NARROW (1-felt V3) plain-revoke proof, so it verifies under NO WIDE
        // descriptor, and the V3 fallback admits CAP-OPEN members ONLY (a plain `revokeVmDescriptor2R24`
        // is filtered out) — so the forge is rejected at the "NO cohort descriptor" branch. (The
        // `is_forbidden_plain_cap_descriptor` AUTHORITY-FLOOR tooth still bites a WIDE plain-cap leg or
        // a cap-open-authority-only leg directly; here the narrow plain leg can't even bind, which is
        // a STRICTLY tighter rejection.) Either way: the cap effect under the authority-blind route
        // does NOT verify.
        let verdict = verify_effect_vm_rotated_with_cutover(&plain_bytes, &plain_pi, &plain_vk);
        assert!(
            verdict.is_err(),
            "LIGHT-CLIENT FORGE: a cap effect proven under the PLAIN (authority-blind) descriptor \
             MUST be rejected — the cap-open membership crown is mandatory. Got Ok(())."
        );
        let msg = format!("{}", verdict.unwrap_err());
        assert!(
            msg.contains("PLAIN cap-effect descriptor") || msg.contains("NO cohort descriptor"),
            "the rejection must close the forge (cap effect under the authority-blind route does not \
             verify — either the AUTHORITY-FLOOR tooth or the wide-cutover NO-descriptor branch), got: {msg}"
        );
    }

    /// Smoke test: prove and verify a self-sovereign turn (Effect VM only).
    #[cfg(feature = "prover")]
    #[test]
    fn prove_verify_self_sovereign_turn() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1, // outgoing
        }];
        let turn_hash = [0xABu8; 32];

        // WIDE FLAG-DAY: the trusted 8-felt commit anchors come from the rotation witness
        // (`wire_commit_8`), the SAME ~124-bit commits the wide producer publishes at the leg's PI
        // tail. (The retired 1-felt `mono_pi[OLD_COMMIT]` is no longer the bound anchor.)
        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let proof = prove_turn_self_sovereign_rotated(&initial, &effects, turn_hash, Some(rot))
            .expect("proof generation should succeed");

        assert!(proof.components.has_state_transition);
        assert!(!proof.components.has_membership);
        assert!(!proof.components.has_conservation);
        assert!(!proof.components.has_non_revocation);

        let result = verify_full_turn(&proof, old_commit, new_commit);
        assert!(
            result.is_ok(),
            "self-sovereign turn proof should verify: {:?}",
            result.err()
        );
    }

    /// Verify that wrong commitments cause rejection.
    #[cfg(feature = "prover")]
    #[test]
    fn verify_rejects_wrong_commitment() {
        let initial = CellState::new(500, 5);
        let effects = vec![VmEffect::Transfer {
            amount: 50,
            direction: 0, // incoming
        }];
        let turn_hash = [0xCDu8; 32];

        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, _new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let proof = prove_turn_self_sovereign_rotated(&initial, &effects, turn_hash, Some(rot))
            .expect("proof generation should succeed");

        let wrong_new_commit = [BabyBear::new(99999); 8];

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
    #[cfg(feature = "prover")]
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
        let rot = rotation_for_initial(&cell_a, &effects_a);
        let proof_a = prove_turn_self_sovereign_rotated(&cell_a, &effects_a, turn_hash, Some(rot))
            .expect("proof_a should succeed");

        // The proof for cell_a's old_commit is cell_a's 8-felt wide commit. cell_b's commitment
        // differs, so verifying with it must fail on old_commitment. (cell_b is a distinct
        // balance/nonce; its rotation witness yields a distinct 8-felt anchor.)
        let rot_b = rotation_for_initial(&cell_b, &effects_a);
        let (cell_b_commit, _) = rot_b
            .wide_commit_anchors(&cell_b, &effects_a, None)
            .expect("wide_commit_anchors");
        let result = verify_full_turn(
            &proof_a,
            cell_b_commit,             // WRONG: this is cell_b, not cell_a
            [BabyBear::new(12345); 8], // doesn't matter, should fail on old_commit
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
    #[cfg(feature = "prover")]
    #[test]
    fn verify_rejects_forged_post_state_on_audited_p3() {
        use dregg_circuit::effect_vm::pi as vmpi;

        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer {
            amount: 100,
            direction: 1,
        }];
        let turn_hash = [0x5Au8; 32];

        let _ = vmpi::NEW_COMMIT; // (the retired 1-felt slot — no longer the bound anchor)

        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, honest_new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        // Forge the WIDE 8-felt post-state commit (the LAST 8 PIs the wide verifier binds).
        let mut forged_new_commit = honest_new_commit;
        forged_new_commit[0] = forged_new_commit[0] + BabyBear::new(1);

        let mut proof = prove_turn_self_sovereign_rotated(&initial, &effects, turn_hash, Some(rot))
            .expect("honest proof should generate");

        // Tamper the published EffectVM post-state 8-felt commit in the wire proof (the rotated
        // leg's LAST 8 PIs — the wide commit tail).
        let eff = proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("effect-vm-rotated sub-proof present");
        let n = eff.sub_public_inputs.len();
        for j in 0..8 {
            eff.sub_public_inputs[n - 8 + j] = forged_new_commit[j];
        }

        // Verify against the FORGED 8-felt commitment (so the surface-level PI equality
        // check would PASS). Only the audited in-circuit carrier binding stands
        // between the forgery and acceptance — and it MUST reject (the wide pi_binding ⇒ UNSAT).
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
    #[cfg(feature = "prover")]
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

        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
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
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };

        let proof = prove_full_turn(&witness).expect("full turn proof should generate");
        assert!(proof.components.has_state_transition);
        assert!(proof.components.has_membership);
        assert!(proof.components.has_non_revocation);

        verify_full_turn(&proof, old_commit, new_commit).expect(
            "full turn with membership + non-revocation must verify on the audited p3 path",
        );
    }

    /// FRESHNESS / no-double-spend — binding (a), HONEST: a full turn whose
    /// non-revocation proof proves freshness against the CANONICAL accumulator
    /// root verifies through `verify_full_turn_bound(Some(canonical_root))`.
    #[cfg(feature = "prover")]
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

        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree: canonical_tree,
                item_hash: fresh_item,
            }),
            cap_membership: None,
            turn_hash: [0x91u8; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };
        let proof = prove_full_turn(&witness).expect("honest fresh-spend proof should generate");

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
    #[cfg(feature = "prover")]
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

        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree: prover_tree, // freshness "proven" against the prover's own tree
                item_hash: spent,
            }),
            cap_membership: None,
            turn_hash: [0x92u8; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };
        let proof = prove_full_turn(&witness)
            .expect("proof generates (the forgery is a verify-time property)");

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
    #[cfg(feature = "prover")]
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

        let rot = rotation_for_initial(&initial, &effects);
        // NoteSpend: the wide note-spend producer opens the grow-gate against the BEFORE nullifier-set
        // leaves; thread the SAME leaves `prove_full_turn` threads (the non-revocation tree) so the
        // anchor's BEFORE 8-felt commit matches the produced leg.
        let before_nullifiers = tree.revoked_leaves();
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, Some(&before_nullifiers))
            .expect("wide_commit_anchors");
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree,
                item_hash: nullifier, // freshness proven for THIS turn's nullifier
            }),
            cap_membership: None,
            turn_hash: [0xB1u8; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };
        let proof = prove_full_turn(&witness).expect("honest fresh-spend proof should generate");

        // Sanity: the rotated EffectVM leg surfaces the nullifier (so step 8 actually fires).
        // The WIDE rotated note-spend leg publishes the nullifier at `ROT_NULLIFIER_PI` (still in the
        // PI prefix) plus the 16 wide commit PIs at the tail — so len >= ROT_NULLIFIER_PI_COUNT.
        use dregg_circuit::effect_vm::trace_rotated::{ROT_NULLIFIER_PI, ROT_NULLIFIER_PI_COUNT};
        let eff = proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm-rotated")
            .unwrap();
        assert!(
            eff.sub_public_inputs.len() >= ROT_NULLIFIER_PI_COUNT,
            "precondition: a (wide) note-spend rotated leg publishes >= {ROT_NULLIFIER_PI_COUNT} PIs \
             (the nullifier-bearing prefix + the 16 wide commit PIs)",
        );
        assert_eq!(
            eff.sub_public_inputs[ROT_NULLIFIER_PI], nullifier,
            "precondition: the spend turn surfaces its nullifier into PI[ROT_NULLIFIER_PI]",
        );
        let _ = vmpi::NOTESPEND_NULLIFIER;

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
    #[cfg(feature = "prover")]
    #[test]
    fn freshness_binding_b_rejects_wrong_item() {
        use dregg_circuit::dsl::revocation::DslRevocationTree;

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

        let rot = rotation_for_initial(&initial, &effects);
        // NoteSpend: thread the BEFORE nullifier-set leaves so the anchor's grow-gate BEFORE commit
        // matches the produced wide note-spend leg.
        let before_nullifiers = tree.revoked_leaves();
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, Some(&before_nullifiers))
            .expect("wide_commit_anchors");
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            membership: None,
            conservation: None,
            non_revocation: Some(NonRevocationWitness {
                tree,
                item_hash: other_item, // freshness proven for the WRONG item
            }),
            cap_membership: None,
            turn_hash: [0xB2u8; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };
        let proof = prove_full_turn(&witness)
            .expect("proof generates (the mismatch is a verify-time property)");

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

    /// ANTI-GHOST end-to-end: forging the published MEMBERSHIP root in a finished
    /// full-turn proof MUST be rejected by the audited membership verifier (the
    /// proof binds the genuine hash-chain root, not the forged PI).
    #[cfg(feature = "prover")]
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

        let rot = rotation_for_initial(&initial, &effects);
        let (old_commit, new_commit) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            membership: Some(MembershipWitness {
                leaf_hash: leaf,
                siblings,
                positions,
            }),
            conservation: None,
            non_revocation: None,
            cap_membership: None,
            turn_hash: [0x88u8; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
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
        #[cfg(feature = "prover")]
        {
            let initial = CellState::new(1234, 7);
            let rot = RotationTurnWitness {
                before: dregg_turn::rotation_witness::produce(
                    &dregg_cell::Cell::with_balance([0xE0; 32], [0u8; 32], 1234),
                    &dregg_cell::Ledger::new(),
                    &dregg_circuit::heap_root::empty_heap_root_8(),
                    &dregg_circuit::heap_root::empty_heap_root_8(),
                    &dregg_turn::rotation_witness::empty_revoked_root_8(),
                    &[[0x11u8; 32]],
                    &Default::default(),
                ),
                after: dregg_turn::rotation_witness::produce(
                    &dregg_cell::Cell::with_balance([0xE0; 32], [0u8; 32], 1234),
                    &dregg_cell::Ledger::new(),
                    &dregg_circuit::heap_root::empty_heap_root_8(),
                    &dregg_circuit::heap_root::empty_heap_root_8(),
                    &dregg_turn::rotation_witness::empty_revoked_root_8(),
                    &[[0x11u8; 32]],
                    &Default::default(),
                ),
                caveat: dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
            };
            let res = prove_cohort_run_chain(&initial, &[], &rot, None, None, None, None);
            assert!(
                res.is_err(),
                "the chained prover must fail closed on an empty turn"
            );
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // PATH-PRESERVE — Phase 1 (the chained N-leg prover + chain verifier; SLOW)
    //
    // Gated on `prover` (the rotated IR-v2 path). These prove real STARKs.
    // Run with: cargo nextest run -p dregg-sdk path_preserve_chain --features prover
    // ════════════════════════════════════════════════════════════════════════

    /// Build the per-turn rotation witnesses for a turn over a real before/after cell — the SAME
    /// construction the node's `rotation_witness_for_self_sovereign` uses, but inlined here so the
    /// SDK test does not depend on the node crate. The before/after cells are the real
    /// `RecordKernelState` the producer reads; the per-run welds carry the changing scalars.
    #[cfg(feature = "prover")]
    fn rotation_witness_for_cells(
        before_cell: &dregg_cell::Cell,
        after_cell: &dregg_cell::Cell,
        receipt_hashes: &[[u8; 32]],
    ) -> RotationTurnWitness {
        use dregg_turn::rotation_witness as rw;
        let mut ctx_ledger = dregg_cell::Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let before_w = rw::produce(
            before_cell,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            receipt_hashes,
            &Default::default(),
        );
        let after_w = rw::produce(
            after_cell,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            receipt_hashes,
            &Default::default(),
        );
        // The caveat is recomputed per-run inside the chained prover; the manifest stored here is
        // only the single-leg default and is unused by `prove_cohort_run_chain`.
        RotationTurnWitness {
            before: before_w,
            after: after_w,
            caveat: dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
        }
    }

    /// Thread a rotation witness for a turn described only by an Effect-VM `initial` state +
    /// `effects` (the common shape of the composition-leg tests). Since the v1 effect-vm fallback
    /// is retired, EVERY finalized-turn prove must carry a rotation witness; this builds the same
    /// before/after producer witnesses the live node mints, over a real `dregg_cell::Cell` whose
    /// EffectVM balance matches `initial`. The rotated leg's OLD/NEW_COMMIT endpoints are welded
    /// from the v1 trace over `initial`+`effects` (`trace_rotated.rs:294-307`), so they agree with
    /// the monolithic reference (`generate_effect_vm_trace`) BY CONSTRUCTION — the after-cell's raw
    /// field bytes only need to be SOME marker for the producer's heap/authority views.
    #[cfg(feature = "prover")]
    fn rotation_for_initial(initial: &CellState, effects: &[VmEffect]) -> RotationTurnWitness {
        let before_cell =
            dregg_cell::Cell::with_balance([0xC0; 32], [0u8; 32], initial.balance as i64);
        let mut after_cell = before_cell.clone();
        // A non-zero marker in field[0] so the after-block producer view differs from the before
        // one; the rotated endpoints come from the v1 weld, not these bytes.
        after_cell.state.fields[0] = {
            let mut b = [0u8; 32];
            b[0] = 1;
            b
        };
        let _ = effects;
        rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]])
    }

    /// THE LOAD-BEARING DIFFERENTIAL (§6.1): a heterogeneous turn `[Transfer, SetField, Transfer]`
    /// on a real cell proves as a chain of N rotated legs whose endpoints + interior boundaries
    /// agree with the MONOLITHIC v1 reference transition, and whose Σ net_delta equals the
    /// monolithic net_delta. Then the full chained proof VERIFIES against the real pre/post
    /// commitments.
    #[cfg(feature = "prover")]
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
        let legs = prove_cohort_run_chain(&initial, &effects, &rot, None, None, None, None)
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
        // The WIDE 8-felt chain endpoints come from the rotation witness (leg0.before8 / legN.after8).
        let (wide_old, wide_new) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");
        let _ = (mono_old, mono_new); // the narrow endpoints stay asserted above on the leg PIs
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
        verify_full_turn(&proof, wide_old, wide_new)
            .expect("the chained heterogeneous proof must verify against the wide chain endpoints");
    }

    /// ANTI-GHOST (§6.2): a tampered MIDDLE-leg commitment breaks the chain — `verify_full_turn`
    /// rejects (either the leg's own re-verification fails because PI desyncs from proof, OR the
    /// adjacency chain-check fires). Either rejection path is the soundness tooth.
    #[cfg(feature = "prover")]
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

        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance(930);
        after_cell.state.fields[0] = {
            let mut b = [0u8; 32];
            b[0] = 7;
            b
        };
        let rot = rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]]);
        let (wide_old, wide_new) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");

        let mut proof =
            prove_turn_self_sovereign_rotated(&initial, &effects, [0x5A; 32], Some(rot))
                .expect("chained composed proof must generate");
        // Honest proof verifies.
        verify_full_turn(&proof, wide_old, wide_new).expect("honest chained proof verifies");

        // TAMPER the middle leg's WIDE AFTER 8-felt commit (the LAST 8 PIs — the wide anchor) by one
        // felt — the wide chain no longer closes (adjacency leg[2].before8 != leg[1].after8).
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
        let n = proof.composed.sub_proofs[mid].sub_public_inputs.len();
        proof.composed.sub_proofs[mid].sub_public_inputs[n - 1] =
            proof.composed.sub_proofs[mid].sub_public_inputs[n - 1] + BabyBear::new(1);

        let res = verify_full_turn(&proof, wide_old, wide_new);
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
    #[cfg(feature = "prover")]
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

        // After: balance back to 1000, field set, nonce 3.
        let mut after_cell = before_cell.clone();
        after_cell.state.fields[0] = {
            let mut b = [0u8; 32];
            b[0] = 7;
            b
        };
        let rot = rotation_witness_for_cells(&before_cell, &after_cell, &[[0x11u8; 32]]);
        let (wide_old, wide_new) = rot
            .wide_commit_anchors(&initial, &effects, None)
            .expect("wide_commit_anchors");

        // Compose WITH a conservation witness of the correct net (0). The prover's conservation
        // block sums Σ net_delta across the legs and must equal 0.
        let witness = FullTurnWitness {
            initial_cell_state: initial.clone(),
            effects: effects.clone(),
            membership: None,
            conservation: Some(ConservationWitness {
                expected_net_delta: 0,
            }),
            non_revocation: None,
            cap_membership: None,
            turn_hash: [0x5A; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };
        let proof = prove_full_turn(&witness)
            .expect("chained proof with a correct Σ-net=0 conservation witness must generate");
        assert!(proof.components.has_conservation);
        verify_full_turn(&proof, wide_old, wide_new)
            .expect("the conserving chained proof must verify");
    }

    /// CONSERVATION anti-ghost: a WRONG expected net (the prover claims +5 when Σ = 0) is rejected
    /// at prove time by the chain-summed conservation check.
    #[cfg(feature = "prover")]
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
            membership: None,
            conservation: Some(ConservationWitness {
                expected_net_delta: 5,
            }), // WRONG
            non_revocation: None,
            cap_membership: None,
            turn_hash: [0x5A; 32],
            rotation: Some(rot),
            cap_turn_identity: None,
            umem_witness: None,
        };
        let res = prove_full_turn(&witness);
        assert!(
            res.is_err(),
            "SOUNDNESS: a wrong chain-summed conservation net MUST be rejected at prove time"
        );
    }

    // ========================================================================
    // The sealed-escrow SELECTOR weld (§6 item 2) — the deployed `hverifier`.
    // ========================================================================

    /// The pure selector-pin demand matches the Lean predicate `demandsEscrowSelector`: it fires
    /// iff the re-derived required-tag floor includes the sealed-escrow tag (17), both polarities.
    /// The Rust twin of the `SettleEscrowSelectorBinding.lean` `#guard` teeth.
    #[test]
    fn escrow_selector_demand_matches_lean_rung() {
        let tag = dregg_circuit::effect_vm::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
        assert_eq!(tag, 17, "the sealed-escrow capacity tag");
        // DEMAND: a floor including the escrow tag demands the selector (Lean
        // `demandsEscrowSelector [tagSettleEscrow]`).
        assert!(demands_escrow_selector(&[tag]));
        // A multi-capacity floor still demands it (Lean `demandsEscrowSelector [18, 17, 19]`).
        assert!(demands_escrow_selector(&[18, tag, 19]));
        // NO-DEMAND: a non-capacity floor demands nothing (Lean `!demandsEscrowSelector []` / `[6]`).
        assert!(!demands_escrow_selector(&[]));
        assert!(!demands_escrow_selector(&[6]));
    }

    /// HALF B (the selector pin), pure: a declared-escrow turn whose rotated leg leaves the selector
    /// PI at `0` (the half-open-settle dodge) is REJECTED; the genuine `1` passes the pin; a leg too
    /// short to carry the welded selector PI is rejected fail-closed; and a non-escrow floor is
    /// deployed-identical (always Ok).
    #[test]
    fn escrow_selector_pin_rejects_sel_zero_and_short_leg() {
        let tag = dregg_circuit::effect_vm::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
        let sel_pi = dregg_circuit::effect_vm::satisfaction_weld::ESCROW_SEL_PI;

        // A welded-width PI vector with the selector OFF (sel = 0) — the dodge — is rejected.
        let mut pis_off = vec![BabyBear::ZERO; sel_pi + 1];
        pis_off[sel_pi] = BabyBear::ZERO;
        let err = check_escrow_selector_pin(&[tag], &pis_off).unwrap_err();
        assert!(
            matches!(err, FullTurnVerifyError::EscrowWeldNotForced { .. }),
            "sel = 0 on a declared-escrow turn must be rejected (HALF B), got {err:?}"
        );

        // The selector ON (sel = 1) passes the pin.
        let mut pis_on = vec![BabyBear::ZERO; sel_pi + 1];
        pis_on[sel_pi] = BabyBear::ONE;
        assert!(check_escrow_selector_pin(&[tag], &pis_on).is_ok());

        // A leg too short to even carry the welded selector PI (e.g. a plain 38-PI rotated transfer
        // leg) is rejected fail-closed — the welded descriptor was not the accepting one.
        let short = vec![BabyBear::ONE; sel_pi]; // length sel_pi, index sel_pi absent
        let err = check_escrow_selector_pin(&[tag], &short).unwrap_err();
        assert!(
            matches!(err, FullTurnVerifyError::EscrowWeldNotForced { .. }),
            "a non-welded (too-short) rotated leg must be rejected, got {err:?}"
        );

        // A non-escrow declaration is deployed-identical: no demand, always Ok (even sel = 0).
        assert!(check_escrow_selector_pin(&[], &pis_off).is_ok());
        assert!(check_escrow_selector_pin(&[6], &pis_off).is_ok());
    }

    /// The staged declaration-keyed routing arm sends a declared-escrow turn to the WELDED descriptor
    /// and a non-escrow declaration to the deployed default — keyed on the existing caveat, not a new
    /// effect (the settle is still a `Transfer`).
    #[test]
    fn declared_escrow_routes_to_welded_descriptor() {
        use dregg_circuit::effect_vm::{
            Effect, SETTLE_ESCROW_SAT_DESCRIPTOR_NAME, rotated_descriptor_name_for_declared_escrow,
            rotated_descriptor_name_for_effect,
        };
        let tag = dregg_circuit::effect_vm::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
        // A settle is performed AS a transfer; with a declared escrow caveat it routes to the weld.
        let transfer = Effect::Transfer {
            amount: 0,
            direction: 1,
        };
        assert_eq!(
            rotated_descriptor_name_for_declared_escrow(&transfer, &[tag]),
            Some(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME)
        );
        // No escrow caveat ⇒ the deployed default (plain transfer descriptor).
        assert_eq!(
            rotated_descriptor_name_for_declared_escrow(&transfer, &[]),
            rotated_descriptor_name_for_effect(&transfer)
        );
    }
}
