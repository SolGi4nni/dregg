//! Full-turn STARK proving on the node's finalized-turn commit path.
//!
//! This module makes the public claim — *every committed state transition is
//! proven* — TRUE for the running node. When the devnet enables full-turn
//! proving, [`crate::blocklace_sync::execute_finalized_turn`] calls
//! [`prove_and_verify_finalized_turn`] for each finalized turn:
//!
//! 1. **Prove.** The turn's effects (projected onto the actor cell) are
//!    marshalled into the Effect VM encoding via the cipherclerk's existing
//!    [`AgentCipherclerk::convert_effects_to_vm`] marshaller, and a real
//!    `FullTurnProof` (a composed STARK over the Effect-VM AIR) is generated
//!    with [`dregg_sdk::prove_turn_self_sovereign`].
//!
//! 2. **Verify → accept.** The freshly generated proof is *re-verified*
//!    against the actor cell's pre-state commitment (`old_commit`) and the
//!    proven post-state commitment (`new_commit`) using
//!    [`dregg_sdk::verify_full_turn`] — the same verifier remote peers use.
//!    Acceptance is **gated** on this check: if the proof does not verify
//!    against the expected commitments, the turn is *not* accepted as proven
//!    (the caller surfaces a rejection).
//!
//! The anti-ghost property is exercised in this module's tests: a turn whose
//! post-state commitment is forged (any felt off by one) is **REJECTED** by
//! `verify_full_turn`, because the Effect-VM AIR binds the new commitment at
//! its boundary row and the verifier checks it against the caller's expected
//! value (`CommitmentMismatch`).
//!
//! ## Soundness scope (honest)
//!
//! The Effect VM proves the actor cell's `(balance, nonce, fields, cap_root)`
//! transition. `old_commit` is the actor cell's pre-execution
//! `CellState::compute_commitment` and `new_commit` is read from the AIR's
//! boundary public input (the prover cannot forge it without producing an
//! invalid trace). This is the per-cell whole-turn binding the SDK FullTurn
//! phase established; it is the load-bearing commit-path leg the public claim
//! rests on. Cross-cell / multi-root aggregation is the Silver→Gold vision and
//! is tracked separately — it does not weaken what is proven here.
//!
//! ## FRESHNESS / no-double-spend (the LIVE binding this module wires)
//!
//! A finalized turn that SPENDS a note (carries an [`dregg_turn::Effect::NoteSpend`])
//! is routed through [`prove_and_verify_finalized_turn_freshness`] instead of the
//! plain self-sovereign path. That function attaches a **non-revocation** sub-proof
//! whose sorted-Merkle tree is built from the node's CANONICAL spent-nullifier set
//! (the persisted [`dregg_persist::Store`] nullifier set, folded into the field the
//! Effect-VM uses), and then verifies the composed proof through
//! [`dregg_sdk::verify_full_turn_bound`] with `expected_revocation_root` pinned to
//! that canonical root. This makes the SDK's two no-double-spend teeth FIRE on the
//! live commit path:
//!
//! - **binding (a)** [`FullTurnVerifyError::RevocationRootMismatch`]: the freshness
//!   proof must be against THE canonical nullifier set the node maintains — a
//!   prover-chosen (empty/stale) accumulator is rejected;
//! - **binding (b)** [`FullTurnVerifyError::NullifierMismatch`]: the item proved
//!   fresh must be THIS turn's spent nullifier, not some other item.
//!
//! ### Accumulator reconciliation (PolynomialAccumulator vs sorted-Merkle)
//!
//! The node has two distinct "absence" structures for two distinct sets:
//! `NodeState::revocation_accumulator` (a `PolynomialAccumulator` over revoked
//! capability-token hashes) and the persisted note-nullifier set (double-spend
//! prevention for `NoteSpend`). They are NOT the same set. The circuit's
//! non-revocation AIR ([`dregg_circuit::dsl::revocation`]) is a fixed-capacity
//! sorted-Merkle tree, so for note-spend freshness we make the **sorted-Merkle
//! tree derived from the persisted nullifier set** the canonical structure the
//! verifier pins. The derived root is a deterministic function of the node's
//! authoritative set (built here via [`canonical_revocation_root_for_set`]), so a
//! peer/light-client re-deriving it from the same set obtains the same root: the
//! verifier's `revocation_root` check is against the node's REAL set, never a
//! prover-chosen tree.
//!
//! ### Capacity bound (honest)
//!
//! The audited non-revocation circuit is hardwired to
//! [`dregg_circuit::dsl::revocation::TREE_DEPTH`] (`= 4`, a 16-leaf tree, so at
//! most `16 - 2 = 14` revoked entries after the two sentinels). When the canonical
//! nullifier set exceeds that capacity, a single fixed-depth proof cannot cover it
//! WITHOUT a deeper circuit (a circuit change, out of scope here). Rather than
//! silently truncate the canonical set (which would be UNSOUND — it could omit the
//! very nullifier being re-spent), [`canonical_revocation_root_for_set`] returns
//! `Err(RevocationCapacityExceeded)` and the spend turn is committed but carries NO
//! freshness-bound proof, logged loudly as a real limitation. Closing this needs a
//! depth-parameterized non-revocation AIR (tracked, not faked).
//!
//! ## AUTHORITY leg — WIRED (cap Phase D; the former blocker here is CLOSED)
//!
//! A capability-gated turn (receipt carries [`dregg_turn::TurnReceipt::consumed_capabilities`],
//! the cap Phase C executor witness) is routed through
//! [`prove_and_verify_finalized_turn_capability`], which attaches a
//! **cap-membership** sub-proof — the consumed capability's 7-field leaf proven
//! a sorted-Poseidon2-Merkle member of the holder's pre-state openable
//! `capability_root` (cap Phase A) — and gates acceptance on
//! [`dregg_sdk::verify_full_turn_bound`] with a [`dregg_sdk::CapMembershipExpectation`]
//! pinning BOTH the leg's root (to the node's CANONICAL pre-state capability
//! root) and its leaf digest (to the receipt-disclosed consumed-cap preimage).
//! The two former gaps are gone: the cap_root IS an openable membership root
//! the circuit seeds from (Phase A), and the executor DOES thread the consumed
//! witness (Phase C) — so the leg is a real binding, not a free body-fact wire.

use dregg_circuit::dsl::revocation::{DslRevocationTree, TREE_DEPTH};
use dregg_circuit::effect_vm::fold_bytes32_to_bb;
use dregg_circuit::field::BabyBear;
use dregg_circuit::{CellState, generate_effect_vm_trace};
use dregg_sdk::{
    AgentCipherclerk, CapMembershipExpectation, CapMembershipWitness, FullTurnProof,
    FullTurnVerifyError, FullTurnWitness, NonRevocationWitness, prove_full_turn,
    prove_turn_self_sovereign_rotated, verify_full_turn_bound,
};
use dregg_types::CellId;

/// Maximum number of revoked entries the audited non-revocation circuit can
/// authenticate in a single proof: the sorted-Merkle tree is hardwired to
/// [`TREE_DEPTH`] (`= 4`, a `2^4 = 16`-leaf tree) and reserves two leaves for the
/// `SENTINEL_MIN`/`SENTINEL_MAX` ordering sentinels, leaving `16 - 2 = 14`.
///
/// This is a CIRCUIT capacity, not a node policy: building the canonical tree at
/// any other depth would not match the verifier's AIR. See the module-level
/// "Capacity bound" note.
pub const MAX_REVOCATION_TREE_ENTRIES: usize = (1usize << TREE_DEPTH) - 2;

/// Widen a single-felt commitment into the 8-felt anchor the wide verifier compares against for a
/// NARROW (v1 / cap-open) effect-vm leg: the verifier broadcasts such a leg's 1-felt commit into
/// slot 0 with the remaining felts zero (`verify_full_turn_bound`'s `leg_commit`), so the caller's
/// expected anchor for a non-rotated proof is the matching `[felt, 0, …, 0]`.
fn wide_from_felt(felt: BabyBear) -> [BabyBear; 8] {
    let mut wide = [BabyBear::ZERO; 8];
    wide[0] = felt;
    wide
}

/// A finalized turn that carries a real, re-verified full-turn STARK proof.
#[derive(Clone, Debug)]
pub struct ProvenFinalizedTurn {
    /// The composed full-turn proof (Effect-VM STARK), ready for wire transmission.
    pub proof: FullTurnProof,
    /// The actor cell's pre-execution 8-felt wide state commitment.
    pub old_commit: [BabyBear; 8],
    /// The proven post-execution 8-felt wide state commitment.
    pub new_commit: [BabyBear; 8],
}

impl ProvenFinalizedTurn {
    /// Serialized proof bytes (the wire form attached to the committed turn).
    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof.proof_bytes
    }
}

/// Errors from the full-turn proving + verify→accept leg.
#[derive(Debug)]
pub enum FullTurnProvingError {
    /// Proof generation failed (invalid witness).
    Prove(dregg_sdk::SdkError),
    /// The freshly generated proof did NOT verify against the expected
    /// pre/post commitments. Acceptance is gated on this: a turn whose proof
    /// does not verify is not accepted as proven.
    Verify(FullTurnVerifyError),
    /// The canonical spent-nullifier set is larger than the audited
    /// non-revocation circuit's fixed capacity ([`MAX_REVOCATION_TREE_ENTRIES`]).
    /// A single fixed-depth freshness proof cannot soundly cover it (omitting any
    /// entry could hide a double-spend), so the freshness-bound proof is NOT
    /// produced for this turn. Closing this needs a depth-parameterized
    /// non-revocation AIR.
    RevocationCapacityExceeded { have: usize, max: usize },
    /// The turn was routed to the freshness path but the prover could not build a
    /// non-membership witness — the spent nullifier is ALREADY in the canonical
    /// set (a genuine double-spend the executor should also have rejected) or the
    /// witness was otherwise unconstructible. The turn carries no freshness proof.
    NullifierAlreadyRevoked,
    /// The receipt's consumed-capability witness (cap Phase C) does not open to
    /// the node's CANONICAL pre-state `capability_root` for the holder — its
    /// membership path is broken or tops a different (non-canonical) tree. A
    /// cap-membership leg proven from it could only bind a wrong root, so the
    /// capability path REFUSES rather than attach a leg the bound verifier
    /// would (correctly) reject.
    ConsumedCapWitnessInvalid { reason: String },
}

impl std::fmt::Display for FullTurnProvingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Prove(e) => write!(f, "full-turn proof generation failed: {e}"),
            Self::Verify(e) => write!(f, "full-turn proof verification failed: {e}"),
            Self::RevocationCapacityExceeded { have, max } => write!(
                f,
                "canonical nullifier set ({have}) exceeds the non-revocation circuit capacity \
                 ({max}); freshness-bound proof not produced (needs a deeper non-revocation AIR)"
            ),
            Self::NullifierAlreadyRevoked => write!(
                f,
                "spent nullifier is already in the canonical revocation set (double-spend) — \
                 no non-membership witness exists"
            ),
            Self::ConsumedCapWitnessInvalid { reason } => write!(
                f,
                "consumed-capability witness does not open to the canonical pre-state \
                 capability_root: {reason} — no sound cap-membership leg exists"
            ),
        }
    }
}

impl std::error::Error for FullTurnProvingError {}

/// Prove a finalized NON-SPEND turn and gate acceptance on the proof verifying.
///
/// This is the self-sovereign path: it carries ONLY the Effect-VM state-transition
/// leg (no authorization / membership / non-revocation sub-proofs), which is the
/// correct trust model for an owner-authorized turn that spends no note. A turn
/// that spends a note (`NoteSpend`) must instead go through
/// [`prove_and_verify_finalized_turn_freshness`] so the no-double-spend bindings
/// fire; the caller branches on [`spent_nullifiers`].
///
/// FLOW-B ROTATION: when the caller threads the per-turn rotation producer witnesses
/// (built by [`rotation_witness_for_self_sovereign`] from the REAL before/after cells +
/// ledger), the effect-vm leg proves through the LEAN-emitted rotated descriptor — the live
/// node turn proves ROTATED. PATH-PRESERVE §4 (the non-synthetic-cell lift): the prover seeds
/// `initial_vm_state` from the REAL cell (decoded from the rotation witness's welded limbs via
/// [`dregg_sdk::RotationTurnWitness::before_cell_state`]), so a FIELD-BEARING / cap-holding cell
/// rotates too — the v1-prefix OLD_COMMIT and the rotated OLD_COMMIT are the same real-cell object
/// by construction. The witness is built whenever the cell is representable (the lifted gate:
/// balance/nonce match the captured pre-state); otherwise the caller passes `None` and the
/// byte-identical v1 leg runs.
///
/// `pre_balance` / `pre_nonce` are the actor cell's state captured **before**
/// the executor mutated the ledger (the pre-state the proof's `old_commit`
/// binds to). `effects` are the turn's effects (the caller passes
/// `turn.call_forest.total_effects()` cloned).
///
/// Returns the proven turn on success, or [`FullTurnProvingError`] if proving
/// fails or — critically — if the freshly generated proof does not verify
/// against the expected commitments (the verify→accept leg).
/// Build the per-turn ROTATION producer witnesses for the self-sovereign FLOW-B path from the
/// REAL before/after actor cells + a turn-context ledger snapshot. PATH-PRESERVE §4 (the lift):
/// returns `Some` whenever the cell is REPRESENTABLE — balance/nonce match the node's captured
/// `(pre_balance, pre_nonce)`. The rotated block's welded scalars
/// (`r0↔balance_lo · r1↔nonce · r2↔balance_hi · r3..r10↔fields[0..8] · cap_root`) are filled from
/// the REAL cell, and the prover now seeds `initial_vm_state` from that same witness (so the
/// v1-prefix OLD_COMMIT equals the rotated OLD_COMMIT for a field-bearing / cap-holding cell too).
/// A balance/nonce that disagrees with the captured scalars means an inconsistent pre-state
/// capture (would mis-pin OLD_COMMIT) — return `None` and let the byte-identical v1 leg run.
///
/// The non-spend self-sovereign turn carries no note, so the nullifier root is the empty root
/// on both blocks (mirrors the C1 sovereign path). `cells_root` rides a single-cell ledger
/// snapshot of the actor (the turn-invariant context shared by the before/after blocks);
/// `iroot` rides the receipt-hash log.
pub fn rotation_witness_for_self_sovereign(
    pre_balance: u64,
    pre_nonce: u64,
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    receipt_hashes: &[[u8; 32]],
    effects: &[dregg_turn::Effect],
) -> Option<dregg_sdk::RotationTurnWitness> {
    rotation_witness_for_self_sovereign_impl(
        pre_balance,
        pre_nonce,
        before_cell,
        after_cell,
        receipt_hashes,
        effects,
    )
}

/// Public entry: build the per-turn ROTATION producer witnesses for the CAPABILITY-GATED FLOW-B
/// path from the REAL before/after actor cells + the canonical pre-state `capability_root` the
/// commit path captured. The live commit path (`blocklace_sync::execute_finalized_turn`) calls this
/// with the real `full_turn_pre_cell` so the rotated AUTHORITY DIGEST r23 binds the real cell — see
/// [`rotation_witness_for_capability_turn`]. Returns `None` (⇒ the caller keeps the v1 cap leg) when
/// the cell cannot be faithfully represented by the v1 capability pre-state.
#[allow(clippy::too_many_arguments)]
pub fn rotation_witness_for_capability(
    pre_balance: u64,
    pre_nonce: u64,
    pre_capability_root: BabyBear,
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    receipt_hashes: &[[u8; 32]],
    effects: &[dregg_turn::Effect],
) -> Option<dregg_sdk::RotationTurnWitness> {
    rotation_witness_for_capability_turn(
        pre_balance,
        pre_nonce,
        pre_capability_root,
        before_cell,
        after_cell,
        receipt_hashes,
        effects,
    )
}

/// Build the rotation witness for a CAP-LESS finalized turn whose actor cell the node does NOT
/// hand us directly (the FRESHNESS / freshness-bearing arms — `prove_and_verify_finalized_turn_*`
/// receive only `(agent, pre_balance, pre_nonce)`, not the `Cell`). Synthesize the cap-less
/// self-sovereign actor cell from those scalars (the SAME synthetic pre-state the v1 leg proves
/// over: `CellState::new(pre_balance, pre_nonce)` — empty c-list ⇒ empty cap root, zero fields)
/// and route it through [`rotation_witness_for_self_sovereign_impl`]. The synthetic cell carries
/// the actor's real `CellId` (`Cell::remote_stub_with_id_and_balance`), so the single-cell
/// `cells_root` matches; its welded scalars (balance/nonce/fields/cap_root) are OVERRIDDEN per-row
/// from the v1 sub-trace by `trace_rotated::fill_block`, so the after-state (the spend's balance
/// credit + nonce tick) flows from the v1 trace itself — no hand-replay of the executor. The same
/// cell is before AND after: the turn-INVARIANT limbs (`cells_root`/map roots/lifecycle/epoch/
/// authority digest) are identical for a single-cell cap-less self-spend; the per-row welds carry
/// the rest. Returns `None` (⇒ the caller keeps the v1 leg) iff the synthetic-shape / cohort gate
/// rejects — e.g. the turn is not a single rotated-cohort member.
///
/// Used to CLOSE the C4 note-spend boundary: with the rotated note-spend descriptor exposing the
/// nullifier at PI[38] (`EffectVmEmitRotationV3.noteSpendV3`), a single-spend NoteSpend turn now
/// proves ROTATED and `verify_full_turn` step 8 reads the nullifier from the rotated leg.
fn rotation_witness_for_cap_less_turn(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: &[dregg_turn::Effect],
    receipt_hashes: &[[u8; 32]],
) -> Option<dregg_sdk::RotationTurnWitness> {
    // SINGLE-SPEND GATE (mirrors `trace_rotated::generate_rotated_effect_vm_trace`): the rotated
    // note-spend leg faithfully covers exactly ONE spend row (the first-row nullifier pin + the
    // single freshness slot). A turn with >1 NoteSpend must NOT commit to the rotated path — the
    // rotated trace generator would refuse it (no second nullifier pin ⇒ the 2nd spend escapes
    // the freshness check). Returning `None` here keeps the v1 leg (where a 2nd distinct
    // nullifier is UNSAT), rather than committing to a rotated prove that errors. (For a non-spend
    // cohort turn this count is 0 ≠ 1, so the cohort gate below decides; only an exactly-one-spend
    // note-spend turn passes both this and the cohort gate.)
    let spend_count = effects
        .iter()
        .filter(|e| matches!(e, dregg_turn::Effect::NoteSpend { .. }))
        .count();
    if spend_count > 1 {
        return None;
    }

    // The cap-less synthetic actor cell — the SAME pre-state shape `CellState::new` builds. Carry
    // the actor's real id so `cells_root` matches; set the runtime nonce; balance from the scalar.
    let mut cell = dregg_cell::Cell::remote_stub_with_id_and_balance(*agent, pre_balance as i64);
    cell.state.set_nonce(pre_nonce);
    // before == after: per-row welds (fill_block) carry the spend's post-state from the v1 trace;
    // the turn-invariant limbs are identical for a single-cell cap-less self-spend.
    rotation_witness_for_self_sovereign_impl(
        pre_balance,
        pre_nonce,
        &cell,
        &cell,
        receipt_hashes,
        effects,
    )
}

fn rotation_witness_for_self_sovereign_impl(
    pre_balance: u64,
    pre_nonce: u64,
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    receipt_hashes: &[[u8; 32]],
    effects: &[dregg_turn::Effect],
) -> Option<dregg_sdk::RotationTurnWitness> {
    use dregg_turn::rotation_witness as rw;

    // REPRESENTABILITY GATE (PATH-PRESERVE §4.1 — the non-synthetic-cell lift). The prover entry
    // now seeds `initial_vm_state` from THIS witness's before-block (`RotationTurnWitness::
    // before_cell_state`), decoded from the welded limbs the rotated leg uses — so the v1-prefix
    // OLD_COMMIT and the rotated OLD_COMMIT are the SAME object regardless of whether the cell
    // carries non-zero fields or a non-empty c-list (the welds copy `fold_bytes32_to_bb(fields)` +
    // the canonical cap root; the authority residue + fields[8..16] ride the witness-carried r23).
    // The gate therefore stops being "is this cell PRISTINE (zero fields, empty c-list)?" and
    // becomes "can the Effect-VM `CellState` losslessly hold this cell, AND does the node's captured
    // (pre_balance, pre_nonce) match the cell?" — the only cross-input the prover entry takes
    // separately from the witness. A balance/nonce that disagrees with the captured scalars means
    // the node's pre-state capture is inconsistent (would mis-pin OLD_COMMIT), so refuse → the
    // byte-identical v1 leg runs. Field-bearing / cap-holding ordinary cells now PASS (they no
    // longer fall to v1), which is the whole point of the lift.
    let cell_is_representable =
        before_cell.state.balance() == pre_balance as i64 && before_cell.state.nonce() == pre_nonce;
    if !cell_is_representable {
        return None;
    }

    // The turn-context ledger snapshot: a single-cell ledger holding the actor (the same
    // cells_root the C1 sovereign path uses; the before/after blocks share it).
    let mut ctx_ledger = dregg_cell::Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    // The non-spend self-sovereign turn spends no note → the empty nullifier root.
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];

    // COHORT GATE (PATH-PRESERVE §1/§4 Shape-1 cutover): the rotated effect-vm prover
    // (`prove_effect_vm_rotated_ir2_with_caveat`) proves exactly ONE cohort descriptor per call and
    // fails CLOSED on an empty / non-cohort effect, and `prove_full_turn` now routes EVERY rotation
    // witness through `prove_cohort_run_chain` (the N-leg chain). So the gate no longer demands a
    // HOMOGENEOUS turn — a HETEROGENEOUS turn (one actor doing >1 distinct cohort effect, e.g.
    // Transfer + SetField) is split by `split_into_cohort_runs` into maximal homogeneous cohort-runs,
    // each proven as its OWN rotated leg, and the verifier chains them (leg_k.OLD == leg_{k-1}.NEW).
    // The gate now only requires that EVERY vm-effect resolves to SOME rotated R=24 cohort descriptor
    // (a non-cohort effect — NoOp / non-graduated — would make a run's per-run rotated prove FAIL
    // closed, so such turns keep the byte-identical v1 leg), AND that the projection is NON-EMPTY
    // (Shape 3: an empty actor projection is a no-op transition the rotated path cannot prove —
    // `convert_effects_to_vm` injects no NoOp, so this is the only empty-guard). A HOMOGENEOUS turn
    // yields ONE run, byte-identical to the prior single rotated leg for the existing fleet.
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(&before_cell.id(), effects);
    let all_cohort = !vm_effects.is_empty()
        && vm_effects.iter().all(|e| {
            dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect(e).is_some()
        });
    if !all_cohort {
        return None;
    }

    // v12 CARRIER MATERIAL (STEP-2.5, the cipherclerk thread mirrored): a factory turn's AFTER
    // commitment publishes the installed child VK on octet 88..95 (non-zero); every non-factory
    // lead keeps the zero `Default` octet. The BEFORE block always keeps the zero octet (the
    // child is BORN by this turn).
    let after_material = match effects.first() {
        Some(dregg_turn::Effect::CreateCellFromFactory { params, .. }) => {
            dregg_cell::commitment::RotationCarrierMaterial {
                child_vk: params.program_vk,
                contract_hash: None,
            }
        }
        _ => dregg_cell::commitment::RotationCarrierMaterial::default(),
    };

    let before_w = rw::produce(
        before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        receipt_hashes,
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = rw::produce(
        after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        receipt_hashes,
        &after_material,
    );

    Some(dregg_sdk::RotationTurnWitness::for_effects(
        before_w,
        after_w,
        &vm_effects,
    ))
}

/// Build the per-turn ROTATION producer witnesses for the CAPABILITY-GATED FLOW-B path from the
/// REAL before/after actor cells + the canonical pre-state `capability_root` the cap-membership
/// leg binds. This is the AUTHORITY analog of [`rotation_witness_for_self_sovereign_impl`]: a
/// capability-gated turn's rotated leg proves over an `initial_vm_state` the prover now seeds from
/// the REAL cell (PATH-PRESERVE §4 — decoded from this witness's welded limbs via
/// [`dregg_sdk::RotationTurnWitness::before_cell_state`], real cap root + real fields[0..8]), so a
/// FIELD-BEARING cap-holding cell rotates too — the welded scalars
/// (`r0↔balance_lo · r1↔nonce · r2↔balance_hi · r3..r10↔fields[0..8] · cap_root`) and the v1-prefix
/// OLD_COMMIT are the same real-cell object by construction.
///
/// CRITICAL (the brief's core requirement — do NOT launder a zero-pk stub): the rotated AUTHORITY
/// DIGEST limb `r23 = compute_authority_digest_felt(before_cell)` is WITNESS-CARRIED (it is NOT
/// overridden by the per-row v1-state weld), so it folds the REAL cell's identity (`public_key` /
/// `id` / `token_id`), permissions, VK, delegate, delegation snapshot (the c-list-derived cap
/// leaves), and program into the rotated OLD/NEW-commit pins (PI 34/35). A cap-less synthetic stub
/// (`Cell::remote_stub_with_id_and_balance`) carries a ZERO public key and empty permissions/program,
/// so its r23 would be UNFAITHFUL — a faithful capability rotation REQUIRES the real cell the node
/// holds in its ledger at the turn's pre-state. We take it directly (the call site passes
/// `full_turn_pre_cell`), never synthesize it.
///
/// REPRESENTABILITY GATE (PATH-PRESERVE §4.1; returns `None` ⇒ graceful v1 fallback): admits the
/// cell when `balance == pre_balance`, `nonce == pre_nonce`, AND the cell's CANONICAL capability
/// root equals `pre_capability_root` (the value the cap-membership leg's `CapRootMismatch` tooth
/// binds AND the seeded EffectVm row's `cap_root` column carries — they must coincide so the
/// membership leg opens the SAME tree the state-transition leg attests over). The lift DROPS the
/// former zero-FIELDS demand — a field-bearing cap-holding cell now rotates (its real fields[0..8]
/// flow through the seeded `initial_vm_state`; fields[8..16] + the authority residue ride the
/// witness-carried r23). Any divergence ⇒ `None` and the byte-identical v1 cap leg runs.
fn rotation_witness_for_capability_turn(
    pre_balance: u64,
    pre_nonce: u64,
    pre_capability_root: BabyBear,
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
    receipt_hashes: &[[u8; 32]],
    effects: &[dregg_turn::Effect],
) -> Option<dregg_sdk::RotationTurnWitness> {
    use dregg_turn::rotation_witness as rw;

    // REPRESENTABILITY GATE (PATH-PRESERVE §4.1 — the non-synthetic-cell lift, capability path).
    // The prover entry seeds `initial_vm_state` from THIS witness's before-block
    // (`RotationTurnWitness::before_cell_state`), so the v1-prefix OLD_COMMIT and the rotated
    // OLD_COMMIT are the SAME object even when the cell carries non-zero fields (the welds copy the
    // real `fold_bytes32_to_bb(fields)`; fields[8..16] + the authority residue ride the
    // witness-carried r23). So we DROP the zero-fields requirement. We KEEP balance/nonce matching
    // the node's captured (pre_balance, pre_nonce) — the prover entry's separate cross-input — and,
    // crucially, KEEP `cell_cap_root == pre_capability_root`: the cap-membership leg binds
    // `pre_capability_root` (its `CapRootMismatch` tooth) and the seeded EffectVm row's `cap_root`
    // column now equals `cell_cap_root`, so the two must coincide for the membership leg to open the
    // SAME tree the state-transition leg attests over. Any divergence ⇒ refuse → the byte-identical
    // v1 cap leg runs. (Unlike the self-sovereign gate this never required an EMPTY cap root — a
    // cap-gated turn's whole point is a non-empty c-list; the lift only removes the zero-FIELDS
    // demand, so field-bearing cap-holding cells now rotate.)
    let cell_cap_root =
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities);
    let cell_matches_v1_prestate = before_cell.state.balance() == pre_balance as i64
        && before_cell.state.nonce() == pre_nonce
        && cell_cap_root == pre_capability_root;
    if !cell_matches_v1_prestate {
        return None;
    }

    // The turn-context ledger snapshot: a single-cell ledger holding the REAL actor (the same
    // cells_root shape the C1 sovereign path uses; the before/after blocks share it).
    let mut ctx_ledger = dregg_cell::Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    // A capability-gated turn carries no note in the cohort case routed here → the empty nullifier
    // root (a cap-gated turn that ALSO spends fails the cohort gate below — its lead effect is not a
    // single rotated note-spend member — and falls back to the v1 leg, which keeps the freshness
    // tooth).
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];

    // COHORT GATE (PATH-PRESERVE §1/§4 Shape-1 cutover — identical to the self-sovereign builder):
    // `prove_full_turn` routes EVERY rotation witness through the N-leg chain (`prove_cohort_run_chain`),
    // so a HETEROGENEOUS cap-gated turn (the actor doing >1 distinct cohort effect under one consumed
    // capability) is split into maximal homogeneous cohort-runs, each proven as its OWN rotated leg,
    // and the verifier chains them. The cap-membership leg + its root/leaf teeth are UNCHANGED and run
    // ALONGSIDE the chained effect legs. So the gate no longer demands homogeneity — it only requires
    // that EVERY vm-effect resolves to SOME rotated R=24 cohort descriptor (a non-cohort effect would
    // make a run's per-run rotated prove FAIL closed ⇒ keep the v1 cap leg) AND that the projection is
    // NON-EMPTY (the cross-cell-SetField case projects to an empty actor transition, a no-op the
    // rotated path cannot prove ⇒ v1). A HOMOGENEOUS cap turn yields ONE run, byte-identical to before.
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(&before_cell.id(), effects);
    let all_cohort = !vm_effects.is_empty()
        && vm_effects.iter().all(|e| {
            dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect(e).is_some()
        });
    if !all_cohort {
        return None;
    }

    // The SetField/BridgeMint nonce-tick seam is CLOSED (model-found, then fixed in-circuit): the
    // rotated `setFieldVmDescriptor2-{0..7}R24` + `mintVmDescriptor2R24` descriptors now carry the
    // tick-modelling `(after_nonce − before_nonce) − (1 − selector)` gate (Lean
    // `EffectVmEmitRotationV3.{setFieldTickFace,mintTickFace}` — the SAME `−(1 − selector)` term
    // `transferVmDescriptor2R24` / `noteSpendVmDescriptor2R24` carry), matching the runtime
    // `new_state.nonce += 1` the trace generator writes on every non-NoOp row. So a SetField /
    // BridgeMint actor turn proves ROTATED (the descriptor is SAT on the ticked trace, and a forged
    // nonce delta is UNSAT — `setFieldTick_rejects_wrong_nonce_delta` / `mintTick_rejects_wrong_nonce_delta`).
    // No broken-descriptor fallback remains: EVERY cohort effect rotates.

    // v12 CARRIER MATERIAL (STEP-2.5, the cipherclerk thread mirrored — see the self-sovereign
    // builder above): a factory lead carries the installed child VK on the AFTER octet; every
    // other lead keeps the zero `Default`.
    let after_material = match effects.first() {
        Some(dregg_turn::Effect::CreateCellFromFactory { params, .. }) => {
            dregg_cell::commitment::RotationCarrierMaterial {
                child_vk: params.program_vk,
                contract_hash: None,
            }
        }
        _ => dregg_cell::commitment::RotationCarrierMaterial::default(),
    };

    let before_w = rw::produce(
        before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        receipt_hashes,
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = rw::produce(
        after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        receipt_hashes,
        &after_material,
    );

    Some(dregg_sdk::RotationTurnWitness::for_effects(
        before_w,
        after_w,
        &vm_effects,
    ))
}

pub fn prove_and_verify_finalized_turn(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
    rotation: Option<dregg_sdk::RotationTurnWitness>,
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // 1. Marshal the turn's effects onto the actor cell in the Effect-VM
    //    encoding (reuses the cipherclerk's canonical marshaller so the node
    //    proves exactly what the cipherclerk would sign).
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(agent, effects);

    // SHAPE-3 INVARIANT (PATH-PRESERVE §1/§7 Phase 0 — CORRECTED against HEAD; the doc's §1/§8
    // premise that this projector "returns an EMPTY vm_effects" is STALE). The FullTurnProof-path
    // projector `AgentCipherclerk::convert_effects_to_vm` DOES inject a sentinel
    // `VmEffect::NoOp` when no effect touches the actor (`sdk/src/cipherclerk.rs:5876-5877`:
    // `if vm_effects.is_empty() { vm_effects.push(VmEffect::NoOp); }`), so `vm_effects` is NEVER
    // empty here — a `debug_assert!(!is_empty())` would be VACUOUS. The real Shape-3 case is a
    // `[NoOp]`-ONLY projection (a cross-cell / no-actor-effect turn): `rotated_descriptor_name_for_effect(&NoOp)`
    // is `None` (`trace_rotated.rs:467`), so the cohort gate refuses it and the builder hands us
    // `rotation == None` — the v1 leg then proves the trivial old==new no-op. That is the CORRECT
    // routing; a `[NoOp]`-only turn is NOT a rotated state transition. The LOAD-BEARING invariant
    // (non-vacuous) is therefore: the rotated path is taken ONLY for a projection carrying a real
    // (non-NoOp) effect — if a lone-NoOp turn ever arrives WITH a rotation witness, the rotated leg
    // would attest a fictional cohort transition, so we make THAT regression loud.
    debug_assert!(
        rotation.is_none()
            || vm_effects
                .iter()
                .any(|e| !matches!(e, dregg_circuit::effect_vm::Effect::NoOp)),
        "PATH-PRESERVE Shape-3: prove_and_verify_finalized_turn reached with a ROTATION witness \
         for a NoOp-only actor projection — a no-actor-effect turn cannot rotate (the cohort gate \
         must have refused it ⇒ rotation==None). agent={agent:?}, effects={effects:?}, \
         vm_effects={vm_effects:?}"
    );

    // 2. Build the actor cell's pre-execution Effect-VM state. The old
    //    commitment the proof binds to is this state's commitment.
    //
    //    PATH-PRESERVE §4 (the non-synthetic-cell lift): when a rotation witness is threaded, the
    //    rotated leg's OLD_COMMIT is the v1 prefix `generate_effect_vm_trace` emits from THIS
    //    `initial_vm_state` (the rotated welds then override `r0..r10`/`cap_root` from that same v1
    //    state block — `trace_rotated.rs:294-307`). So `initial_vm_state` must carry the REAL cell's
    //    balance/nonce/fields[0..8]/cap_root, NOT a synthetic zero-field `CellState::new`, else a
    //    field-bearing / cap-holding cell's rotated OLD_COMMIT would attest a fictional zero-field
    //    cell that a light client re-deriving from the real cell could never reproduce (an ARGUS
    //    regression). We seed it from `rotation.before_cell_state()`, decoded from the SAME welded
    //    limbs the rotated leg uses, so the agreement is by construction (§4.2). Without a rotation
    //    witness (the byte-identical v1 fallback / `not(recursion)`), `CellState::new` seeds the
    //    cap-less zero-field synthetic state the v1 self-sovereign leg has always proven over.
    let initial_vm_state = match &rotation {
        Some(rot) => rot
            .before_cell_state()
            .map_err(FullTurnProvingError::Prove)?,
        None => CellState::new(pre_balance, pre_nonce as u32),
    };

    // 3. Derive the proven post-state commitment from the AIR boundary public
    //    input. The prover cannot forge this without an invalid trace.
    let (_trace, pi) = generate_effect_vm_trace(&initial_vm_state, &vm_effects);

    // WIDE FLAG-DAY: the trusted 8-felt (~124-bit) commit anchors `verify_full_turn` binds. When a
    // rotation witness is threaded (the wide leg), they are the rotation's `wire_commit_8` before/after
    // anchors (the SAME commits the wide producer publishes at the leg's PI tail). Without one (the
    // byte-identical v1 / narrow leg) the verifier broadcasts the leg's 1-felt commit into slot 0, so
    // we match by widening the same single felts the v1 leg attests at `pi::OLD_COMMIT`/`pi::NEW_COMMIT`.
    let (old_commit, new_commit) = match &rotation {
        Some(rot) => rot
            .wide_commit_anchors(&initial_vm_state, &vm_effects, None)
            .map_err(FullTurnProvingError::Prove)?,
        None => (
            wide_from_felt(initial_vm_state.state_commitment),
            wide_from_felt(pi[dregg_circuit::effect_vm::pi::NEW_COMMIT]),
        ),
    };

    // 4. Generate the real composed full-turn STARK proof. When the caller threaded the
    //    per-turn rotation producer witnesses (FLOW-B), the effect-vm leg proves through the
    //    LEAN-emitted rotated descriptor; otherwise the byte-identical v1 leg runs.
    let proof =
        prove_turn_self_sovereign_rotated(&initial_vm_state, &vm_effects, turn_hash, rotation)
            .map_err(FullTurnProvingError::Prove)?;

    // 5. VERIFY → ACCEPT leg. Re-verify the proof against the expected
    //    pre/post commitments using the same verifier a remote peer runs.
    //    Acceptance is gated on this returning Ok.
    dregg_sdk::verify_full_turn(&proof, old_commit, new_commit)
        .map_err(FullTurnProvingError::Verify)?;

    Ok(ProvenFinalizedTurn {
        proof,
        old_commit,
        new_commit,
    })
}

/// Extract the raw 32-byte nullifiers of every `NoteSpend` in a turn's effects
/// (including those nested inside `ExerciseViaCapability`), in order.
///
/// A turn with at least one entry here is a SPEND turn and is routed through the
/// freshness path. The current freshness circuit attests ONE nullifier per proof;
/// the caller proves the first and (when several are present) the rest ride the
/// per-cell Effect-VM binding (multi-nullifier batching is a circuit extension).
pub fn spent_nullifiers(effects: &[dregg_turn::Effect]) -> Vec<[u8; 32]> {
    fn collect(effect: &dregg_turn::Effect, out: &mut Vec<[u8; 32]>) {
        match effect {
            dregg_turn::Effect::NoteSpend { nullifier, .. } => out.push(nullifier.0),
            dregg_turn::Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    for e in effects {
        collect(e, &mut out);
    }
    out
}

/// Pick the consumed-capability witness whose HOLDER is the actor cell — the
/// breadstuff authorization surface, where the actor's own c-list held the
/// consumed authority. This is the routing predicate for the AUTHORITY /
/// cap-membership path (cap Phase D): a receipt carrying such a witness routes
/// through [`prove_and_verify_finalized_turn_capability`], binding the leg
/// against the ACTOR's canonical pre-state cap root.
///
/// Bearer-delegation witnesses (`holder != actor`) are picked by the sibling
/// [`bearer_consumed_cap`]; they route through
/// [`prove_and_verify_finalized_turn_capability_holder`], binding the leg against
/// the DELEGATOR's canonical pre-state cap root.
pub fn actor_consumed_cap<'a>(
    consumed: &'a [dregg_turn::ConsumedCapWitness],
    agent: &CellId,
) -> Option<&'a dregg_turn::ConsumedCapWitness> {
    consumed.iter().find(|w| w.holder == *agent)
}

/// Pick the consumed-capability witness whose HOLDER is NOT the actor cell — a
/// BEARER-delegation witness, where some OTHER cell (the delegator) held the
/// consumed authority and signed a delegation the actor exercised this turn.
///
/// This is the routing predicate for the bearer AUTHORITY leg: such a receipt
/// routes through [`prove_and_verify_finalized_turn_capability_holder`] with the
/// DELEGATOR's (`holder`'s) canonical pre-state cap root — recomputed by the node
/// from its own authoritative pre-execution ledger (see
/// [`delegator_pre_state_cap_roots`]), never taken from the receipt — so the
/// authority leg PROVES the delegated cap was real (not merely that the witness
/// is internally consistent). Returns the FIRST bearer witness; a single turn
/// exercising several distinct delegators is a multi-bearer extension (the first
/// is proven through the authority leg, the rest ride the v1 fallback until the
/// circuit batches multiple cap-membership legs).
pub fn bearer_consumed_cap<'a>(
    consumed: &'a [dregg_turn::ConsumedCapWitness],
    agent: &CellId,
) -> Option<&'a dregg_turn::ConsumedCapWitness> {
    consumed.iter().find(|w| w.holder != *agent)
}

/// Snapshot the canonical pre-state `capability_root` of every cell that a
/// bearer (`SignedDelegation`) authorization in `forest` names as its delegator,
/// keyed by the delegator cell's `CellId`. Captured from the node's
/// authoritative PRE-execution `ledger` (BEFORE any effect mutates a c-list), so
/// a bearer turn's AUTHORITY leg can bind the DELEGATOR's real pre-state cap root
/// — the value the executor's Phase-C witness records as its `cap_root` "as it
/// was in scope at authorization time" — without trusting the receipt.
///
/// The delegator is resolved exactly as the executor resolves it
/// (`cell.public_key() == delegator_pk`), so the keyed `CellId` matches the
/// witness's `holder` (`delegator_cell.id()`). The anonymous `StarkDelegation`
/// path names no concrete delegator cell (and the executor records no holder
/// witness for it), so it contributes nothing here. Only walked when full-turn
/// proving is enabled; an empty map for a turn with no bearer authorization.
pub fn delegator_pre_state_cap_roots(
    forest: &dregg_turn::CallForest,
    ledger: &dregg_cell::Ledger,
) -> std::collections::HashMap<CellId, [BabyBear; 8]> {
    use dregg_turn::{Authorization, DelegationProofData};
    let mut out = std::collections::HashMap::new();
    for tree in forest.iter_dfs() {
        if let Authorization::Bearer(proof) = &tree.action.authorization
            && let DelegationProofData::SignedDelegation { delegator_pk, .. } =
                &proof.delegation_proof
        {
            // Resolve the delegator cell by public key (the executor's own
            // lookup), then snapshot its pre-state canonical cap root — the FULL
            // native 8-felt openable root (`_8`, the ~124-bit faithful root the
            // cap-membership leg binds), NOT a lane-0 squeeze.
            if let Some((id, cell)) = ledger.iter().find(|(_, c)| c.public_key() == delegator_pk) {
                out.entry(*id).or_insert_with(|| {
                    dregg_cell::compute_canonical_capability_root_8(&cell.capabilities).limbs()
                });
            }
        }
    }
    out
}

/// Fold a raw 32-byte note nullifier into the BabyBear field element the
/// Effect-VM uses for `PI[NOTESPEND_NULLIFIER]`.
///
/// This is the SAME fold the cipherclerk's `convert_effects_to_vm` applies to a
/// `NoteSpend` nullifier (`dregg_circuit::effect_vm::fold_bytes32_to_bb`), so the
/// canonical revocation tree's leaves and the queried `item_hash` live in the
/// same field as the Effect-VM nullifier the verifier's binding-(b) tooth checks.
pub fn nullifier_to_field(nullifier: &[u8; 32]) -> BabyBear {
    fold_bytes32_to_bb(nullifier)
}

/// Build the canonical [`DslRevocationTree`] from the node's authoritative
/// spent-nullifier set (the raw 32-byte nullifiers), folding each into the
/// Effect-VM field. Returns the tree (whose `root()` is the canonical revocation
/// root) or [`FullTurnProvingError::RevocationCapacityExceeded`] when the set is
/// too large for the fixed-depth circuit.
///
/// The set passed in is the previously-spent nullifiers — i.e. it must EXCLUDE
/// the nullifier of the turn currently being proven (freshness = "not yet in the
/// set"). The caller is responsible for capturing the set before recording this
/// turn's spend.
pub fn canonical_revocation_tree_for_set(
    previously_spent: &[[u8; 32]],
) -> Result<DslRevocationTree, FullTurnProvingError> {
    if previously_spent.len() > MAX_REVOCATION_TREE_ENTRIES {
        return Err(FullTurnProvingError::RevocationCapacityExceeded {
            have: previously_spent.len(),
            max: MAX_REVOCATION_TREE_ENTRIES,
        });
    }
    let leaves: Vec<BabyBear> = previously_spent.iter().map(nullifier_to_field).collect();
    Ok(DslRevocationTree::new(leaves, TREE_DEPTH))
}

/// Canonical revocation root for a spent-nullifier set: the root of the
/// sorted-Merkle tree the audited non-revocation circuit authenticates against,
/// derived deterministically from the node's authoritative set. A peer/light
/// client re-deriving from the same set obtains the same root.
#[allow(dead_code)] // Retained light-client/peer revocation-root re-derivation helper.
pub fn canonical_revocation_root_for_set(
    previously_spent: &[[u8; 32]],
) -> Result<BabyBear, FullTurnProvingError> {
    Ok(canonical_revocation_tree_for_set(previously_spent)?.root())
}

/// Prove a finalized SPEND turn and gate acceptance on the freshness-bound
/// verifier (`verify_full_turn_bound` with the canonical revocation root pinned).
///
/// This is the no-double-spend path. In addition to the Effect-VM post-state
/// binding [`prove_and_verify_finalized_turn`] establishes, it:
///
/// 1. builds the canonical [`DslRevocationTree`] from `previously_spent` (the
///    node's authoritative set of nullifiers spent BEFORE this turn);
/// 2. attaches a non-revocation sub-proof of freshness for `spent_nullifier`
///    (this turn's nullifier, folded into the Effect-VM field);
/// 3. verifies through [`verify_full_turn_bound`] with `expected_revocation_root`
///    pinned to the canonical root — so the SDK's binding-(a)
///    ([`FullTurnVerifyError::RevocationRootMismatch`]) and binding-(b)
///    ([`FullTurnVerifyError::NullifierMismatch`]) teeth FIRE on the live path.
///
/// `spent_nullifier` is the raw 32-byte nullifier of THIS turn's `NoteSpend`
/// (the executor already rejected a genuine double-spend; this proof attests
/// freshness against the canonical set so a light client can re-check it).
///
/// Returns the proven turn, or:
/// - [`FullTurnProvingError::RevocationCapacityExceeded`] if the canonical set is
///   too large for the fixed-depth circuit (turn carries no freshness proof);
/// - [`FullTurnProvingError::NullifierAlreadyRevoked`] if the nullifier is already
///   in the canonical set (double-spend; no non-membership witness);
/// - [`FullTurnProvingError::Prove`] / [`FullTurnProvingError::Verify`] on the
///   usual proving / verify-gate failures.
#[allow(clippy::too_many_arguments)]
pub fn prove_and_verify_finalized_turn_freshness(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
    spent_nullifier: &[u8; 32],
    previously_spent: &[[u8; 32]],
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // Canonical revocation tree from the node's authoritative set (built from the
    // set BEFORE this turn's nullifier is recorded — freshness is non-membership).
    let tree = canonical_revocation_tree_for_set(previously_spent)?;
    let canonical_root = tree.root();
    let item_hash = nullifier_to_field(spent_nullifier);

    // A genuine double-spend has no non-membership witness; refuse rather than
    // attach an unsound/absent proof. (The executor's NullifierSet should already
    // have rejected this turn; this is defence in depth.)
    if tree.contains(&item_hash) {
        return Err(FullTurnProvingError::NullifierAlreadyRevoked);
    }

    // Same Effect-VM marshalling + pre-state as the self-sovereign path.
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(agent, effects);
    // SHAPE-3 INVARIANT (PATH-PRESERVE §1/§7 Phase 0 — CORRECTED; see the canonical note in
    // `prove_and_verify_finalized_turn`: the projector injects a NoOp sentinel so `vm_effects` is
    // NEVER empty). The freshness path is a SPEND turn — `NoteSpend` projects UNCONDITIONALLY
    // (`cipherclerk.rs:5524`, no actor guard) — so a real (non-NoOp) effect is present a fortiori
    // and the NoOp sentinel is never the lone element here. The non-vacuous invariant: a `[NoOp]`-only
    // projection (which cannot occur for a spend) must never carry a rotation witness.
    debug_assert!(
        vm_effects
            .iter()
            .any(|e| !matches!(e, dregg_circuit::effect_vm::Effect::NoOp)),
        "PATH-PRESERVE Shape-3: prove_and_verify_finalized_turn_freshness reached with a NoOp-only \
         projection — a spend turn must project a real NoteSpend effect. agent={agent:?}, \
         effects={effects:?}, vm_effects={vm_effects:?}"
    );
    let initial_vm_state = CellState::new(pre_balance, pre_nonce as u32);
    let (_trace, pi) = generate_effect_vm_trace(&initial_vm_state, &vm_effects);

    // FLOW-B ROTATION (C4 close): a single-spend NoteSpend turn now ROTATES — the rotated
    // note-spend descriptor (`noteSpendVmDescriptor2R24`) exposes the spent nullifier at PI[38]
    // (`EffectVmEmitRotationV3.noteSpendV3`), so the rotated leg carries the no-double-spend
    // binding `verify_full_turn` step 8 reads. Build the rotation witness from the cap-less
    // synthetic actor cell (the SAME pre-state the v1 leg proves over); the builder's
    // synthetic-shape/cohort gate returns `None` (⇒ keep the v1 leg) for any turn it cannot
    // faithfully rotate (e.g. a multi-spend turn, which the rotated generator also refuses —
    // the single-nullifier freshness shape stays the invariant on BOTH legs).
    let rotation =
        rotation_witness_for_cap_less_turn(agent, pre_balance, pre_nonce, effects, &[turn_hash]);

    // WIDE FLAG-DAY: the trusted 8-felt commit anchors `verify_full_turn_bound` binds — the rotation's
    // wide chain endpoints when the spend rotates (the wide leg), else the v1 leg's single felts
    // broadcast into slot 0 (the narrow leg the verifier widens the same way). This is a NoteSpend turn,
    // so the wide note-spend producer opens the limb-26 grow-gate against the BEFORE nullifier-set
    // leaves — thread the SAME canonical-tree leaves `prove_full_turn` threads (from the non-revocation
    // witness), so the published 8-felt commit matches. Derived before the witness MOVES `tree`/`rotation`.
    let before_nullifiers = tree.revoked_leaves();
    let (old_commit, new_commit) = match &rotation {
        Some(rot) => rot
            .wide_commit_anchors(&initial_vm_state, &vm_effects, Some(&before_nullifiers))
            .map_err(FullTurnProvingError::Prove)?,
        None => (
            wide_from_felt(initial_vm_state.state_commitment),
            wide_from_felt(pi[dregg_circuit::effect_vm::pi::NEW_COMMIT]),
        ),
    };

    // Compose the full-turn proof WITH the non-revocation leg.
    let witness = FullTurnWitness {
        initial_cell_state: initial_vm_state,
        effects: vm_effects,
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: Some(NonRevocationWitness { tree, item_hash }),
        cap_membership: None,
        turn_hash,
        rotation,
        cap_turn_identity: None,
        umem_witness: None,
    };
    let proof = prove_full_turn(&witness).map_err(FullTurnProvingError::Prove)?;

    // VERIFY → ACCEPT leg, BOUND to the canonical revocation root. Acceptance is
    // gated on this Ok: a freshness proof against any other (prover-chosen) root,
    // or for any item other than this turn's nullifier, is rejected here.
    verify_full_turn_bound(&proof, old_commit, new_commit, Some(canonical_root), None)
        .map_err(FullTurnProvingError::Verify)?;

    Ok(ProvenFinalizedTurn {
        proof,
        old_commit,
        new_commit,
    })
}

/// Prove a finalized CAPABILITY-GATED turn (cap Phase D — the AUTHORITY payoff)
/// and gate acceptance on the cap-membership-bound verifier.
///
/// `consumed` is the receipt's Phase-C [`dregg_turn::ConsumedCapWitness`] whose
/// `holder` is the ACTOR cell (`agent`) — the breadstuff surface, where the
/// actor's own c-list held the consumed authority. In addition to the Effect-VM
/// post-state binding, this:
///
/// 1. checks (defence in depth) that the receipt witness's membership path
///    opens to `pre_capability_root` — the node's CANONICAL pre-state
///    capability root for the holder, recomputed from the authoritative
///    pre-execution c-list (NOT taken from the receipt) — refusing with
///    [`FullTurnProvingError::ConsumedCapWitnessInvalid`] otherwise;
/// 2. seeds the Effect-VM pre-state with that same canonical root
///    ([`CellState::with_capability_root`], cap Phase A) so `old_commit` binds
///    the very tree the membership leg opens;
/// 3. attaches the **cap-membership** sub-proof (the consumed cap's 7-field
///    leaf ∈ the openable sorted-Poseidon2 `capability_root`, proven through
///    the audited p3 path);
/// 4. verifies through [`verify_full_turn_bound`] with a
///    [`CapMembershipExpectation`] pinning the leg's root to the canonical
///    pre-state cap root ([`FullTurnVerifyError::CapRootMismatch`] tooth) and
///    its leaf digest to the receipt-disclosed preimage
///    ([`FullTurnVerifyError::CapLeafMismatch`] tooth).
///
/// A capability-gated turn that ALSO spends a note keeps its freshness leg:
/// pass `spent_nullifier` + `previously_spent` and the non-revocation sub-proof
/// is attached and bound exactly as in
/// [`prove_and_verify_finalized_turn_freshness`] (no-degrade: cap routing never
/// drops the no-double-spend teeth).
///
/// FLOW-B ROTATION (C7 close): when the caller threads the per-turn rotation producer witnesses
/// (built by [`rotation_witness_for_capability_turn`] from the REAL before/after cells +
/// `pre_capability_root`), the effect-vm leg proves through the LEAN-emitted rotated descriptor —
/// the live capability-gated node turn proves ROTATED, and the rotated commit pins (PI 34/35) fold
/// the REAL authority digest r23. The cap-membership leg + its root/leaf teeth are UNCHANGED and run
/// ALONGSIDE the rotated leg (`prove_full_turn` composes both), so a cap OVER-GRANT (granted ⊄ held)
/// is still REFUSED on the rotated path. When `rotation` is `None` (the builder's gate rejected the
/// turn, or proving disabled) the byte-identical v1 leg runs — same graceful fallback discipline as
/// the note-spend arm.
#[allow(clippy::too_many_arguments)]
pub fn prove_and_verify_finalized_turn_capability(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    pre_capability_root: BabyBear,
    actor_cap_root_8: [BabyBear; 8],
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
    consumed: &dregg_turn::ConsumedCapWitness,
    spent_nullifier: Option<&[u8; 32]>,
    previously_spent: &[[u8; 32]],
    rotation: Option<dregg_sdk::RotationTurnWitness>,
    cap_trees: CapWriteTreeWitness,
    umem_witness: Option<dregg_sdk::UmemWeldWitness>,
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // BREADSTUFF (actor-held) path: the cap's HOLDER is the actor, so the
    // AUTHORITY leg binds against the ACTOR's own canonical pre-state cap root.
    // `pre_capability_root` (SCALAR lane-0) seeds the EffectVm state-transition
    // leg's `cap_root` column; `actor_cap_root_8` (the FULL native 8-felt openable
    // root) is what the cap-membership leg / `CapMembershipExpectation` binds — on
    // the actor-held path holder == actor, so it IS the actor's own 8-felt root.
    // The bearer generalisation (`..._holder`) takes a distinct holder root.
    prove_and_verify_finalized_turn_capability_holder(
        agent,
        pre_balance,
        pre_nonce,
        pre_capability_root,
        actor_cap_root_8,
        effects,
        turn_hash,
        consumed,
        spent_nullifier,
        previously_spent,
        rotation,
        cap_trees,
        umem_witness,
    )
}

/// **(cap-WRITE light-client axis)** Build the openable cap-tree leaf-set for a cell's FULL c-list —
/// the sorted-Poseidon2 `HeapLeaf` set the WRITE-bearing cap-open wrappers' `map_op` opens against
/// (BEFORE cap-root → AFTER cap-root). Each ACTIVE capability becomes a leaf keyed by its
/// `slot_hash` (the SAME felt the cap-leaf carries) with its `target` as the presence value (the
/// revoke `map_op` reads this value then writes 0 in place). Tombstoned (revoked) slots are omitted.
/// This is the cell's GENUINE c-list — the prover threads it as the cap-tree write witness so a
/// wrong post-root is UNSAT (the no-silent-forge guardrail).
pub fn cap_write_clist_leaves(cell: &dregg_cell::Cell) -> Vec<dregg_circuit::heap_root::HeapLeaf> {
    cell.capabilities
        .iter()
        .map(|cap| {
            let leaf = dregg_cell::cap_ref_to_leaf(cap);
            dregg_circuit::heap_root::HeapLeaf {
                addr: leaf.slot_hash,
                value: leaf.target,
            }
        })
        .collect()
}

/// **(cap-WRITE light-client axis, the INSERT/REMOVE keystone deploy)** The FULL cap-tree write
/// witness bundle for a cell: the arity-2 openable leaf-set (`clist_leaves` — the map-op tree the
/// non-rewired write wrappers open), the FULL 7-field LIVE c-list (`cap_leaves` — the arity-7
/// `CanonicalCapTree` the INSERT-shaped keystone wrappers rebuild to splice a fresh conferred edge),
/// and the tombstoned slot keys (`cap_tombstones` — the ghost positions the rebuilt roots preserve,
/// cell-side byte-identity). This is the cell's GENUINE pre-state; the prover threads it so a wrong
/// post-root is unprovable (no fabricated after-root).
#[derive(Clone, Debug, Default)]
pub struct CapWriteTreeWitness {
    pub clist_leaves: Vec<dregg_circuit::heap_root::HeapLeaf>,
    pub cap_leaves: Vec<dregg_circuit::cap_root::CapLeaf>,
    pub cap_tombstones: Vec<BabyBear>,
}

/// Build the [`CapWriteTreeWitness`] from a cell's genuine pre-state (see
/// [`cap_write_clist_leaves`] for the arity-2 half).
pub fn cap_write_tree_witness(cell: &dregg_cell::Cell) -> CapWriteTreeWitness {
    CapWriteTreeWitness {
        clist_leaves: cap_write_clist_leaves(cell),
        cap_leaves: cell
            .capabilities
            .iter()
            .map(dregg_cell::cap_ref_to_leaf)
            .collect(),
        cap_tombstones: cell
            .capabilities
            .tombstoned_slots()
            .map(dregg_circuit::cap_root::slot_hash)
            .collect(),
    }
}

/// **THE DOMAIN-2 (CAPS) UMEM WELD WITNESS PRODUCER (the umem-flip's node-side seam).** Build the
/// per-turn universal-memory weld witness ([`dregg_sdk::UmemWeldWitness`]) from the REAL before/after
/// actor cells the commit path holds — the GENUINE record-kernel projection diff
/// (`project_record_kernel_state(before) → project_diff_ops(pre, post)`) — and return it ONLY when the
/// diff is a NON-EMPTY, single-domain CAPS change (the shape
/// [`prove_wide_umem_welded_cap_open_staged`] reconciles). A turn whose actor projection diff is empty
/// (no caps change), heap-domain (a value move, NOT a cap-open weld), or spans multiple domains gets
/// `None` ⇒ the caller keeps the BARE wide cap-open leg (the deployed default). This is the witness
/// the loud-probe threads to mint the DOMAIN-2 welded form through the deployed cap path; the deployed
/// commit site (`blocklace_sync`) passes `None` until the gated VK epoch flips it on.
pub fn caps_umem_weld_witness(
    before_cell: &dregg_cell::Cell,
    after_cell: &dregg_cell::Cell,
) -> Option<dregg_sdk::UmemWeldWitness> {
    use dregg_turn::umem::{UDomain, project_diff_ops, project_record_kernel_state};
    let pre = project_record_kernel_state(before_cell);
    let post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&pre, &post);
    if ops.is_empty() {
        return None;
    }
    // Single-domain CAPS discipline (the cap-open weld reconciles domain 2 only — the producer fails
    // closed otherwise, so we refuse to thread a witness it could not mint from).
    if ops.iter().any(|op| op.key.domain() != UDomain::Caps) {
        return None;
    }
    Some(dregg_sdk::UmemWeldWitness { pre, ops })
}

/// Prove a finalized CAPABILITY-GATED turn binding the AUTHORITY (cap-membership)
/// leg against a HOLDER pre-state cap root that may differ from the ACTOR's
/// EffectVm-seed root — the BEARER-delegation generalisation (cap Phase D).
///
/// `pre_capability_root` seeds the actor's EffectVm pre-state (`old_commit`) and
/// the rotation witness — it is the ACTOR's canonical pre-state cap root.
/// `holder_cap_root` is the cap HOLDER's (the delegator's, for a bearer turn)
/// canonical pre-state cap root the cap-membership leg opens against and the
/// verifier pins (`CapRootMismatch` tooth). For the breadstuff/actor-held path
/// the two coincide (holder == actor) and this is byte-identical to the v1
/// `prove_and_verify_finalized_turn_capability`.
///
/// SOUNDNESS (the bearer authority leg): a bearer-delegated turn (the consumed
/// cap's `holder` is the DELEGATOR, not the actor) now PROVES the authority leg
/// — the disclosed delegated cap is a sorted-Poseidon2 member of the DELEGATOR's
/// real pre-state c-list (`holder_cap_root`, recomputed by the node from its own
/// authoritative pre-execution ledger, NEVER taken from the receipt). A bearer
/// turn whose delegator did NOT actually hold the cap is REJECTED here (the
/// witness's recorded `cap_root` will not equal the node-derived `holder_cap_root`,
/// or — for a fabricated path — `verify_full_turn_bound`'s `CapRootMismatch`
/// fires). The actor's state-transition leg is bound independently to the actor's
/// own `old_commit`/`new_commit`, so the two legs together attest "the actor's
/// state evolved correctly AND the delegated authority it exercised was real."
#[allow(clippy::too_many_arguments)]
pub fn prove_and_verify_finalized_turn_capability_holder(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    pre_capability_root: BabyBear,
    holder_cap_root: [BabyBear; 8],
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
    consumed: &dregg_turn::ConsumedCapWitness,
    spent_nullifier: Option<&[u8; 32]>,
    previously_spent: &[[u8; 32]],
    rotation: Option<dregg_sdk::RotationTurnWitness>,
    cap_trees: CapWriteTreeWitness,
    umem_witness: Option<dregg_sdk::UmemWeldWitness>,
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // Defence in depth: the receipt witness must be internally consistent AND
    // open to the CANONICAL pre-state capability root the node itself derived for
    // the cap's HOLDER (the delegator on the bearer path; the actor on the
    // breadstuff path). (verify_full_turn_bound re-checks the root equality
    // cryptographically; refusing here avoids minting a proof the bound verifier
    // must reject.)
    if !consumed.verify() {
        return Err(FullTurnProvingError::ConsumedCapWitnessInvalid {
            reason: "membership path does not recompute the witness's own cap_root".into(),
        });
    }
    // FULL native 8-felt equality (the ~124-bit faithful root, NOT a lane-0
    // squeeze): lift the witness's recorded `[u32; 8]` cap root per-lane into the
    // field and compare it against the node-derived `[BabyBear; 8]` holder root.
    if consumed.cap_root.map(BabyBear::new) != holder_cap_root {
        return Err(FullTurnProvingError::ConsumedCapWitnessInvalid {
            reason: format!(
                "witness cap_root {:?} != canonical pre-state holder capability_root {:?} \
                 (the cap was NOT a member of the holder's authoritative pre-state c-list)",
                consumed.cap_root, holder_cap_root
            ),
        });
    }

    // Optional freshness leg (a cap-gated turn that also spends a note).
    let non_revocation = match spent_nullifier {
        Some(nf) => {
            let tree = canonical_revocation_tree_for_set(previously_spent)?;
            let item_hash = nullifier_to_field(nf);
            if tree.contains(&item_hash) {
                return Err(FullTurnProvingError::NullifierAlreadyRevoked);
            }
            Some((tree, item_hash))
        }
        None => None,
    };
    let canonical_revocation_root = non_revocation.as_ref().map(|(tree, _)| tree.root());

    // Effect-VM pre-state, seeded with the ACTOR's REAL canonical capability root
    // (cap Phase A) — `pre_capability_root`. NOTE the actor/holder split: the
    // EffectVm state-transition leg attests the ACTOR's evolution, so it is seeded
    // from the ACTOR's pre-state cap root; the cap-membership leg attests that the
    // consumed cap is a member of the HOLDER's c-list, so it opens against
    // `holder_cap_root`. On the breadstuff/actor-held path holder == actor and the
    // two roots coincide. On the bearer path they DIFFER — and that is sound
    // because `verify_full_turn_bound` does NOT cross-bind the cap-membership leg's
    // `cap_root` to the EffectVm row (it pins the leg to the caller-supplied
    // `CapMembershipExpectation.cap_root` only), so the two legs are independent.
    //
    // PATH-PRESERVE §4 (the non-synthetic-cell lift): with a rotation witness threaded the rotated
    // leg's OLD_COMMIT is the v1 prefix emitted from THIS `initial_vm_state`, so it must carry the
    // REAL cell's fields[0..8] (not the zero fields `with_capability_root` seeds) for a field-bearing
    // cap-holding cell's rotated OLD_COMMIT to faithfully represent it. We seed from
    // `rotation.before_cell_state()` (decoded from the same welded limbs the rotated leg uses) so the
    // agreement holds by construction; that decode carries the actor's real cap_root. Without a
    // rotation witness the byte-identical `with_capability_root` (zero fields, actor cap root) v1 cap
    // leg runs.
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(agent, effects);
    // SHAPE-3 INVARIANT (PATH-PRESERVE §1/§7 Phase 0 — CORRECTED; see the canonical note in
    // `prove_and_verify_finalized_turn`: the projector injects a NoOp sentinel so `vm_effects` is
    // NEVER empty). A cap-gated turn whose effects touch ONLY other cells (e.g. a cross-cell
    // SetField) projects to `[NoOp]` on the actor; the cohort builder refuses it (NoOp resolves to
    // no descriptor) and hands `rotation == None` ⇒ the v1 cap leg proves the trivial no-op. The
    // non-vacuous invariant: the rotated cap path is taken ONLY for a projection carrying a real
    // (non-NoOp) effect — a lone-NoOp turn arriving WITH a rotation witness would mis-attest a
    // cohort transition, so we make THAT regression loud.
    debug_assert!(
        rotation.is_none()
            || vm_effects
                .iter()
                .any(|e| !matches!(e, dregg_circuit::effect_vm::Effect::NoOp)),
        "PATH-PRESERVE Shape-3: prove_and_verify_finalized_turn_capability reached with a ROTATION \
         witness for a NoOp-only actor projection — a no-actor-effect cap turn cannot rotate. \
         agent={agent:?}, effects={effects:?}, vm_effects={vm_effects:?}"
    );
    let initial_vm_state = match &rotation {
        Some(rot) => rot
            .before_cell_state()
            .map_err(FullTurnProvingError::Prove)?,
        None => CellState::with_capability_root(pre_balance, pre_nonce as u32, pre_capability_root),
    };
    let (_trace, pi) = generate_effect_vm_trace(&initial_vm_state, &vm_effects);

    // WIDE FLAG-DAY — THE CAP-OPEN TAIL CLOSED. A capability-gated turn threads `cap_membership`
    // (below), so `prove_cohort_run_chain` routes the run through the CAP-OPEN producer
    // (`prove_effect_vm_cap_open`). EVERY live cap-open key — the authority crown, the §10 WRITE tail,
    // AND the turn-bound `transferCapOpenTB` (the route THIS deployed cap path proves) — now has a
    // PROVEN wide twin in `WIDE_REGISTRY_STAGED_TSV`, so the cap-open leg publishes the FULL 8-felt
    // (~124-bit) BEFORE/AFTER commit at its LAST 16 PIs (the wide carriers appended past the membership
    // crown / turn-identity pins). `verify_full_turn_bound`'s `leg_is_wide` (keyed on the wide-registry
    // fingerprint the leg's vk_hash pins) binds those 8-felt slices — so the trusted anchor here must be
    // the GENUINE wide chain endpoints, NOT the 1-felt-in-slot-0 form. We derive them exactly as the
    // owner-authorized path does (`rotation.wide_commit_anchors`, generate-only, the SAME wide carriers
    // the producer absorbs), threading the BEFORE nullifier-set leaves for a cap-turn that also spends.
    // The ~31-bit waist is GONE for cap-gated turns. (Without a rotation witness the retired v1 cap leg
    // runs and the verifier broadcasts its 1-felt commit into slot 0 — matched by `wide_from_felt`.)
    let before_nullifiers: Vec<BabyBear> = non_revocation
        .as_ref()
        .map(|(tree, _)| tree.revoked_leaves())
        .unwrap_or_default();
    let (old_commit, new_commit) = match &rotation {
        Some(rot) => rot
            .wide_commit_anchors(&initial_vm_state, &vm_effects, Some(&before_nullifiers))
            .map_err(FullTurnProvingError::Prove)?,
        None => (
            wide_from_felt(initial_vm_state.state_commitment),
            wide_from_felt(pi[dregg_circuit::effect_vm::pi::NEW_COMMIT]),
        ),
    };

    // #225 TURN-IDENTITY (cross-vat close): derive the genuine `(actor, src, dst)` single-felt
    // identity from the REAL turn so a cap-gated transfer where the cap HOLDER/actor (`agent`)
    // differs from the cap's TARGET (`src` — the cell being moved) publishes its true identity.
    //
    // CONVENTION (precision-critical — must byte-match what `verify_vm_descriptor2` anchors into
    // PIs 38/39/40 via `anchor_cap_open_turn_pins`): the single-felt cell projection is
    // `dregg_circuit::cap_root::fold_bytes32(cell_id.as_bytes())`
    // (`circuit/src/cap_root.rs:194` = `hash_many(&BabyBear::encode_hash(bytes))`).
    //   - `src`   = the consumed cap's `leaf.target` — ALREADY the rooted value: the cap-leaf
    //               `target` is `fold_bytes32(cap.target.as_bytes())` (`cell/src/commitment.rs:506`),
    //               folded to `consumed.leaf_target` (`turn/src/executor/authorize.rs:1045`,
    //               `leaf.target.as_u32()`). The SDK cap-open route reads exactly this as
    //               `cap_open.src = leaf.target` (`circuit/.../trace_rotated.rs:1149`), so we re-use
    //               the felt verbatim rather than re-folding.
    //   - `actor` = the turn's actor / cap holder (`agent`), under the SAME `fold_bytes32` projection.
    //   - `dst`   = the transfer's recipient cell (`Effect::Transfer.to`), SAME projection.
    // NB: this is `cap_root::fold_bytes32` (Poseidon2 `encode_hash`), NOT the distinct
    // `effect_vm::fold_bytes32_to_bb` Horner fold — they are different functions; using the latter
    // for actor/dst would make an honest cross-vat proof's PIs disagree with the anchor and REJECT.
    //
    // On the OWNER arm (`agent == src cell` and `to == src cell`, a cap in the actor's own c-list)
    // this yields `actor == dst == src`, byte-identical to the prior `None` default — so the owner
    // path is unchanged. `dst` falls back to `src` when the turn carries no Transfer recipient.
    let cap_turn_identity = {
        use dregg_circuit::cap_root::fold_bytes32;
        let src = BabyBear::new(consumed.leaf_target);
        let actor = fold_bytes32(agent.as_bytes());
        let dst = effects
            .iter()
            .find_map(|e| match e {
                dregg_turn::Effect::Transfer { to, .. } => Some(fold_bytes32(to.as_bytes())),
                _ => None,
            })
            .unwrap_or(src);
        Some(dregg_sdk::TurnIdentityFelts { actor, src, dst })
    };

    // Compose the full-turn proof WITH the cap-membership leg (+ freshness when
    // the turn also spends).
    let witness = FullTurnWitness {
        initial_cell_state: initial_vm_state,
        effects: vm_effects,
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: non_revocation
            .map(|(tree, item_hash)| NonRevocationWitness { tree, item_hash }),
        // cap-WRITE light-client axis: thread the holder's FULL c-list as the cap-tree write witness.
        // When non-empty AND the effect routes a write wrapper (e.g. RevokeDelegation → the cap-tree
        // REMOVE), the SDK proves the `…WriteCapOpenVmDescriptor2R24` so the post-cap-root is on the
        // wire (light-client-verifiable). Empty ⇒ the authority-only cap-open (current behavior).
        cap_membership: Some(CapMembershipWitness::from_consumed_with_trees(
            consumed,
            cap_trees.clist_leaves,
            cap_trees.cap_leaves,
            cap_trees.cap_tombstones,
        )),
        turn_hash,
        rotation,
        cap_turn_identity,
        // DOMAIN-2 UMEM WELD (the producer seam this closes): when the caller threads the turn's
        // genuine CAPS-domain projection diff, the cap-open leg mints the WIDE cap-open+umem WELDED
        // form (the membership crown + the 8-felt anchors + the appended caps `umemOp` leg) that the
        // deployed executor admits ADDITIVELY. `None` (the deployed default) ⇒ the bare wide cap-open
        // leg — owner/cap turns that thread no witness are UNAFFECTED, no VK committed.
        umem_witness,
    };
    let proof = prove_full_turn(&witness).map_err(FullTurnProvingError::Prove)?;

    // VERIFY → ACCEPT leg, BOUND to the canonical pre-state capability root and
    // the receipt-disclosed consumed-cap leaf (and, for a spend, the canonical
    // revocation root). Acceptance is gated on this Ok: a membership path into
    // any other (prover-chosen / spliced) tree, or for any leaf other than the
    // disclosed consumed capability, is rejected here.
    let expectation = CapMembershipExpectation {
        leaf: consumed.cap_leaf(),
        cap_root: holder_cap_root,
    };
    verify_full_turn_bound(
        &proof,
        old_commit,
        new_commit,
        canonical_revocation_root,
        Some(&expectation),
    )
    .map_err(FullTurnProvingError::Verify)?;

    Ok(ProvenFinalizedTurn {
        proof,
        old_commit,
        new_commit,
    })
}

/// Config-store key under which a finalized turn's proof bytes are persisted,
/// keyed by the turn hash (hex). Lets an operator / API surface the attached
/// proof for any committed turn.
pub fn turn_proof_config_key(turn_hash_hex: &str) -> String {
    format!("full_turn_proof:{turn_hash_hex}")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A committed transfer turn carries a proof that VERIFIES against the
    /// expected pre/post commitments (the verify→accept leg succeeds).
    #[test]
    fn committed_turn_carries_verifying_proof() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1000;
        let pre_nonce: u64 = 0;

        // The REAL before/after cells the live commit path holds: Alice sends 100 to Bob, so from
        // Alice's actor-cell perspective this is an outgoing transfer (balance debits by 100). The
        // agent id IS the cell's id on the live path, so the effect's `from` + the proving `agent`
        // are `before_cell.id()`.
        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        let alice = before_cell.id();
        let amount: u64 = 100;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let turn_hash = [0x11u8; 32];
        let receipt_hashes = [[0x11u8; 32]];

        // Thread the per-turn ROTATION witness (the live node always does — under `recursion` the v1
        // effect-vm leg is retired, so a finalized turn proves through the rotated descriptor).
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "a cap-less transfer turn must yield a rotation witness"
        );
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .expect("finalized turn should prove and self-verify");

        // The proof is real (non-empty wire bytes) and re-verifies.
        assert!(!proven.proof_bytes().is_empty());
        assert!(proven.proof.components.has_state_transition);
        assert_eq!(proven.proof.turn_hash, turn_hash);

        // Independent re-verification against the carried commitments.
        dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit)
            .expect("carried proof must re-verify against carried commitments");
    }

    /// ANTI-GHOST: a turn whose post-state commitment is FORGED (off by one
    /// felt) is REJECTED. The Effect-VM AIR binds the new commitment at its
    /// boundary; `verify_full_turn` checks it against the expected value and
    /// returns `CommitmentMismatch`.
    #[test]
    fn forged_post_state_is_rejected() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1000;
        let pre_nonce: u64 = 0;

        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        let alice = before_cell.id();
        let amount: u64 = 100;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let turn_hash = [0x22u8; 32];
        let receipt_hashes = [[0x11u8; 32]];

        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .expect("honest turn should prove");

        // Forge the post-state commitment: claim a DIFFERENT new state than
        // the one the proof actually attests (perturb slot 0 of the 8-felt anchor).
        let mut forged_new_commit = proven.new_commit;
        forged_new_commit[0] = forged_new_commit[0] + BabyBear::new(1);
        assert_ne!(forged_new_commit, proven.new_commit);

        let result =
            dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, forged_new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: forged post-state commitment MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "new_commitment");
            }
            other => panic!("expected new_commitment mismatch, got {other:?}"),
        }
    }

    /// ANTI-GHOST (pre-state): forging the OLD commitment (claiming the turn
    /// started from a different cell state than it did) is also REJECTED.
    #[test]
    fn forged_pre_state_is_rejected() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 777;
        let pre_nonce: u64 = 3;

        let mut before_cell =
            dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        before_cell.state.set_nonce(pre_nonce);
        let alice = before_cell.id();
        let amount: u64 = 50;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let turn_hash = [0x33u8; 32];
        let receipt_hashes = [[0x11u8; 32]];

        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .expect("honest turn should prove");

        let mut forged_old_commit = proven.old_commit;
        forged_old_commit[0] = forged_old_commit[0] + BabyBear::new(1);
        let result =
            dregg_sdk::verify_full_turn(&proven.proof, forged_old_commit, proven.new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: forged pre-state commitment MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "old_commitment");
            }
            other => panic!("expected old_commitment mismatch, got {other:?}"),
        }
    }

    /// FLOW-B LIVE TURN (the node self-sovereign commit path, ROTATED): build a REAL cap-less
    /// actor `Cell` (the shape the self-sovereign path serves), apply a transfer to get the
    /// post-state cell, build the per-turn rotation witnesses via
    /// [`rotation_witness_for_self_sovereign`] (the SAME call `blocklace_sync` makes), prove the
    /// finalized turn with `Some(rotation)`, and confirm (a) the verify→accept gate passes and
    /// (b) the composed proof carries the `"effect-vm-rotated"` leg — i.e. the live node turn
    /// proved through the LEAN-emitted rotated descriptor, not the v1 hand-AIR.
    #[test]
    fn flow_b_self_sovereign_turn_proves_rotated() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1_000;
        let pre_nonce: u64 = 0;

        // The REAL before-cell: a fresh cap-less sovereign cell with a balance (zero fields,
        // empty c-list — exactly what the synthetic-shaped gate admits). In the live node path
        // the agent id IS the cell's id (the cell is looked up BY the agent id), so the effect's
        // `from` + the proving `agent` must be `before_cell.id()`, not an unrelated raw id.
        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        let alice = before_cell.id();
        // The after-cell: the transfer debits alice's balance by the amount.
        let amount: u64 = 100;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let turn_hash = [0x5Au8; 32];
        let receipt_hashes = [[0x11u8; 32]];

        // Build the rotation witness via the node's own builder (the synthetic-shaped + cohort
        // gates must BOTH pass for a cap-less transfer).
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "a cap-less transfer turn must yield a rotation witness (synthetic-shaped + cohort)"
        );

        // Prove the finalized turn ROTATED + gate acceptance (the live commit-path call).
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .expect("the rotated self-sovereign turn must prove + verify");

        // The composed proof must carry the ROTATED effect-vm leg (not the v1 `"effect-vm"`).
        let labels: Vec<&str> = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "the live node turn must prove through the rotated descriptor; sub-proofs = {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must NOT be present on the rotated turn; sub-proofs = {labels:?}"
        );
    }

    /// FLOW-B NON-SYNTHETIC CELL PROVES ROTATED (PATH-PRESERVE §4 — the lift). This test was the
    /// INVERSE before Phase 3: a field-bearing cell used to fall back to v1 (`rotation.is_none()`)
    /// because the synthetic `CellState::new` pre-state could not represent it. Phase 3 seeds
    /// `initial_vm_state` from the REAL cell (decoded from the rotation witness's welded limbs, the
    /// SAME felts the rotated leg welds), so the v1-prefix OLD_COMMIT and the rotated OLD_COMMIT are
    /// the same object — and a field-bearing cell now yields a rotation witness whose composed proof
    /// VERIFIES rotated against the real cell's commitment.
    #[test]
    fn flow_b_non_synthetic_cell_proves_rotated() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1_000;
        let pre_nonce: u64 = 0;

        // A REAL field-bearing cell: non-zero `fields[0]` (the shape the OLD gate refused). In the
        // live node path the agent id IS the cell's id, so the effect's `from` + the proving `agent`
        // are `before_cell.id()`.
        let mut before_cell =
            dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        before_cell.state.set_field(0, [0x07u8; 32]);
        let alice = before_cell.id();
        // The transfer debits alice's balance by the amount (+ the runtime nonce tick).
        let amount: u64 = 100;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let turn_hash = [0x6Bu8; 32];
        let receipt_hashes = [[0x11u8; 32]];

        // The lifted REPRESENTABILITY gate must now ADMIT the field-bearing cell.
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "PATH-PRESERVE §4: a field-bearing cell must now yield a rotation witness (lifted gate)"
        );

        // Prove the finalized turn ROTATED + gate acceptance (the live commit-path call). The
        // verify→accept leg pins OLD/NEW to the real (field-bearing) cell's commitment.
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .expect("the rotated NON-SYNTHETIC self-sovereign turn must prove + verify");

        // It must carry the ROTATED leg (not the v1 `"effect-vm"`).
        let labels: Vec<&str> = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "the non-synthetic node turn must prove through the rotated descriptor; sub-proofs = {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must NOT be present on the rotated non-synthetic turn; sub-proofs = {labels:?}"
        );

        // Independent re-verification against the carried commitments (a light client's path):
        // OLD_COMMIT is the REAL field-bearing cell's commitment, reproducible from the real cell.
        dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit).expect(
            "the non-synthetic rotated proof must re-verify against the real-cell commitments",
        );
    }

    /// ANTI-GHOST (PATH-PRESERVE §4): the non-synthetic rotated turn's commitments are LOAD-BEARING
    /// — forging the post-state commitment (the proven NEW_COMMIT off by one felt) is REJECTED, so a
    /// field-bearing cell's rotated proof cannot attest a fictional post-state. This is the §6.2
    /// tooth specialized to the lifted (non-synthetic) path.
    #[test]
    fn flow_b_non_synthetic_forged_post_state_is_rejected() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1_000;
        let pre_nonce: u64 = 0;

        let mut before_cell =
            dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        before_cell.state.set_field(0, [0x07u8; 32]);
        let alice = before_cell.id();
        let amount: u64 = 100;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &[[0x11u8; 32]],
            &effects,
        )
        .expect("field-bearing cell yields a rotation witness (lifted gate)");

        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            [0x6Cu8; 32],
            Some(rotation),
        )
        .expect("honest non-synthetic rotated turn must prove");

        // Forge the post-state commitment the verifier is asked to accept (perturb slot 0).
        let mut forged_new_commit = proven.new_commit;
        forged_new_commit[0] = forged_new_commit[0] + BabyBear::new(1);
        assert_ne!(forged_new_commit, proven.new_commit);
        let result =
            dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, forged_new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: a forged post-state commitment on the non-synthetic rotated leg MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "new_commitment");
            }
            other => panic!("expected new_commitment mismatch, got {other:?}"),
        }
    }

    // ──────────────────────────────────────────────────────────────────────
    // PATH-PRESERVE Phase 4 — HETEROGENEOUS turns rotate as an N-leg chain
    // ──────────────────────────────────────────────────────────────────────

    /// PATH-PRESERVE §1/§4 (Shape-1, the live cutover): a HETEROGENEOUS turn — one actor doing >1
    /// distinct cohort effect (Transfer THEN SetField on its own cell) — now proves ROTATED as a
    /// CHAIN of legs instead of falling to the v1 effect-vm leg. The lifted cohort gate
    /// (`rotation_witness_for_self_sovereign`) admits it (every vm-effect resolves to SOME rotated
    /// cohort), `prove_full_turn` routes it through `prove_cohort_run_chain` (splitting into the
    /// maximal homogeneous runs `[Transfer] | [SetField]`, threading the interior boundary state),
    /// and the chained verifier checks endpoints + adjacency. Asserts: the composed proof carries
    /// >= 2 `"effect-vm-rotated"` legs and ZERO `"effect-vm"` (v1) legs, and the verify->accept gate
    /// > passes against the real-cell commitments. This is the live-path evidence the heterogeneous
    /// > shape no longer takes the v1 fallback (unblocking C7).
    #[test]
    fn flow_b_heterogeneous_turn_proves_rotated_chain() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1_000;
        let pre_nonce: u64 = 0;

        // The REAL actor cell (the agent id IS the cell id on the live path).
        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        let alice = before_cell.id();
        // The after-cell only feeds the turn-INVARIANT limbs (cells_root/lifecycle/epoch/r23) of the
        // final run's after-block — the per-run welds carry the changing balance/nonce/fields — so a
        // clone of the before-cell (same single-cell invariant view) is the faithful after-block.
        let after_cell = before_cell.clone();

        // HETEROGENEOUS: an outgoing Transfer (cohort `transferVmDescriptor2R24`) THEN a SetField on
        // the actor's OWN cell (cohort `setFieldVmDescriptor2-0R24`). The actor's Effect-VM
        // projection is `[Transfer{dir:1}, SetField{slot:0}]` — two DISTINCT cohorts ⇒ two runs.
        let effects = vec![
            dregg_turn::Effect::Transfer {
                from: alice,
                to: bob,
                amount: 100,
            },
            dregg_turn::Effect::SetField {
                cell: alice,
                index: 0,
                value: [0x09u8; 32],
            },
        ];
        let turn_hash = [0x7Au8; 32];
        let receipt_hashes = [[0x11u8; 32]];

        // Sanity: the projection really IS heterogeneous (two distinct cohort descriptors).
        let vm_effects = AgentCipherclerk::convert_effects_to_vm(&alice, &effects);
        assert_eq!(
            vm_effects.len(),
            2,
            "Transfer + self-SetField must project to a 2-effect actor transition"
        );
        let names: Vec<Option<&str>> = vm_effects
            .iter()
            .map(dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect)
            .collect();
        assert!(
            names[0].is_some() && names[1].is_some() && names[0] != names[1],
            "the two effects must resolve to DISTINCT rotated cohort descriptors, got {names:?}"
        );

        // The LIFTED gate must now ADMIT this heterogeneous turn (the old gate returned None).
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "PATH-PRESERVE §1: a heterogeneous all-cohort turn must now yield a rotation witness \
             (the lifted cohort gate)"
        );

        // Prove the finalized turn ROTATED (the live commit-path call) + gate acceptance.
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .expect("the heterogeneous turn must prove as an N-leg rotated chain + verify");

        // The composed proof must carry >= 2 ROTATED legs (one per cohort-run) and NO v1 leg.
        let labels: Vec<&str> = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        let rotated_legs = labels.iter().filter(|l| **l == "effect-vm-rotated").count();
        assert!(
            rotated_legs >= 2,
            "a heterogeneous turn must carry >= 2 chained rotated legs (one per cohort-run); \
             sub-proofs = {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "ZERO v1 effect-vm legs on the heterogeneous rotated chain; sub-proofs = {labels:?}"
        );

        // Independent re-verification against the carried commitments (a light client's chain-check):
        // first.OLD == old_commit, last.NEW == new_commit, interior adjacency closes.
        dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit).expect(
            "the chained heterogeneous proof must re-verify against the real-cell commitments",
        );
    }

    /// PATH-PRESERVE §6.2 ANTI-GHOST (the chain): a TAMPERED interior chain leg is REJECTED. We
    /// prove the same heterogeneous Transfer+SetField chain, then corrupt the FIRST leg's published
    /// NEW_COMMIT PI (off by one felt). Two independent teeth catch it and either rejection is the
    /// anti-ghost (§6.2: "a tamper that desyncs PI from proof fails there first — assert either
    /// rejection path"):
    ///   * step 3 (per-leg crypto re-verify): the rotated leg is selector-bound to its PIs, so a PI
    ///     that no longer matches the committed trace verifies under NO cohort descriptor
    ///     (`SubProofInvalid`) — the leg itself is UNSAT against the forged PI;
    ///   * step 4 (chain adjacency): even if a leg's PI/proof stayed self-consistent, the broken
    ///     NEW would fail `leg_1.OLD == leg_0.NEW` (`CommitmentMismatch{chain_adjacency}`).
    ///
    /// So a spliced/forged middle state cannot launder a fictional intermediate transition onto the
    /// rotated chain.
    #[test]
    fn flow_b_heterogeneous_chain_tampered_leg_is_rejected() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1_000;
        let pre_nonce: u64 = 0;

        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        let alice = before_cell.id();
        let after_cell = before_cell.clone();

        let effects = vec![
            dregg_turn::Effect::Transfer {
                from: alice,
                to: bob,
                amount: 100,
            },
            dregg_turn::Effect::SetField {
                cell: alice,
                index: 0,
                value: [0x09u8; 32],
            },
        ];
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &[[0x11u8; 32]],
            &effects,
        )
        .expect("heterogeneous all-cohort turn yields a rotation witness");

        let mut proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            [0x7Bu8; 32],
            Some(rotation),
        )
        .expect("honest heterogeneous chain must prove");

        // Locate the chain's FIRST rotated leg and corrupt its NEW_COMMIT PI (offset 4) by one felt.
        // Adjacency (leg_1.OLD == leg_0.NEW) then breaks.
        let new_commit_off = dregg_circuit::effect_vm::pi::NEW_COMMIT;
        let first_rotated = proven
            .proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("the heterogeneous proof carries a rotated leg");
        first_rotated.sub_public_inputs[new_commit_off] += BabyBear::new(1);

        // The chained verifier rejects: the corrupted leg is UNSAT against its forged PI (step 3)
        // OR — if it stayed self-consistent — its broken NEW fails chain adjacency (step 4). Either
        // is the anti-ghost: the chain does not close on a fictional intermediate state.
        let result =
            dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit);
        match result {
            Err(FullTurnVerifyError::SubProofInvalid { index, label, .. }) => {
                assert_eq!(index, 0, "the tampered first leg is the rejected sub-proof");
                assert_eq!(
                    label, "effect-vm-rotated",
                    "the rejected leg is the corrupted rotated chain leg"
                );
            }
            Err(FullTurnVerifyError::CommitmentMismatch { which, .. }) => {
                assert!(
                    which == "chain_adjacency" || which == "new_commitment",
                    "a tampered first-leg NEW must fail adjacency (or the endpoint), got which={which}"
                );
            }
            Ok(()) => panic!(
                "ANTI-GHOST (chain): a tampered interior leg NEW_COMMIT was ACCEPTED — the rotated \
                 chain laundered a fictional intermediate state!"
            ),
            Err(other) => panic!(
                "expected SubProofInvalid (step-3 crypto) or CommitmentMismatch (step-4 chain), \
                 got {other:?}"
            ),
        }
    }

    /// ARGUS fidelity rung 3 (node leg-iterate): a tampered NON-LEAD chain leg is REFUSED at the
    /// node's verify->accept gate — the verifier checks EVERY cohort leg, not just the lead. The
    /// node's gate is `dregg_sdk::verify_full_turn` (the same one the heterogeneous chain proves
    /// through, and the same one a remote peer / light client runs); since PATH-PRESERVE it COLLECTS
    /// all `"effect-vm-rotated"` legs, re-verifies each cryptographically (step 3) and chain-checks
    /// endpoints + adjacency (step 4). This test is the missing witness: the prior anti-ghost test
    /// (`flow_b_heterogeneous_chain_tampered_leg_is_rejected`) tampered the LEAD leg (index 0); a
    /// lead-only verifier would have caught THAT but SLIPPED a forged tail. Here we corrupt the
    /// SECOND (non-lead) rotated leg and assert the rejection lands on THAT leg (not index 0) — so a
    /// forged interior/tail cohort cannot ride a valid lead onto the chain.
    #[test]
    // NON_LEAD is deliberate emphasis in the test name (the non-lead-leg rejection witness).
    #[allow(non_snake_case)]
    fn flow_b_heterogeneous_chain_tampered_NON_LEAD_leg_is_rejected() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 1_000;
        let pre_nonce: u64 = 0;

        let before_cell = dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        let alice = before_cell.id();
        let after_cell = before_cell.clone();

        // HETEROGENEOUS: Transfer THEN self-SetField — two distinct cohorts ⇒ two chained legs.
        let effects = vec![
            dregg_turn::Effect::Transfer {
                from: alice,
                to: bob,
                amount: 100,
            },
            dregg_turn::Effect::SetField {
                cell: alice,
                index: 0,
                value: [0x09u8; 32],
            },
        ];
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &[[0x11u8; 32]],
            &effects,
        )
        .expect("heterogeneous all-cohort turn yields a rotation witness");

        let mut proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            [0x7Cu8; 32],
            Some(rotation),
        )
        .expect("honest heterogeneous chain must prove");

        // Locate EVERY rotated leg in sub-proof order; there must be >= 2 (one per cohort run).
        let rotated_indices: Vec<usize> = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .enumerate()
            .filter(|(_, sp)| sp.label == "effect-vm-rotated")
            .map(|(i, _)| i)
            .collect();
        assert!(
            rotated_indices.len() >= 2,
            "the heterogeneous turn must carry >= 2 chained rotated legs; got {rotated_indices:?}"
        );
        let lead_idx = rotated_indices[0];
        let non_lead_idx = rotated_indices[1];

        // Corrupt the NON-LEAD (second) leg's NEW_COMMIT PI (offset 4) by one felt. For a wide leg
        // this desyncs the PI from the committed trace (step-3 crypto rejects THIS leg); for a narrow
        // leg the last-leg endpoint / adjacency tooth bites (step-4). Either way the rejection must
        // land on the non-lead leg — a lead-only verifier would have ACCEPTED this forged tail.
        let new_commit_off = dregg_circuit::effect_vm::pi::NEW_COMMIT;
        proven.proof.composed.sub_proofs[non_lead_idx].sub_public_inputs[new_commit_off] +=
            BabyBear::new(1);

        let result =
            dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit);
        match result {
            Err(FullTurnVerifyError::SubProofInvalid { index, label, .. }) => {
                assert_eq!(
                    index, non_lead_idx,
                    "the NON-LEAD leg must be the rejected sub-proof — the verifier checks beyond the lead"
                );
                assert_ne!(
                    index, lead_idx,
                    "the rejection must NOT be the lead leg (that would prove only the lead is checked)"
                );
                assert_eq!(
                    label, "effect-vm-rotated",
                    "the rejected leg is the corrupted rotated chain leg"
                );
            }
            Err(FullTurnVerifyError::CommitmentMismatch { which, .. }) => {
                assert!(
                    which == "chain_adjacency" || which == "new_commitment",
                    "a tampered non-lead-leg NEW must fail adjacency or the endpoint, got which={which}"
                );
            }
            Ok(()) => panic!(
                "ARGUS rung 3 REGRESSION: a tampered NON-LEAD cohort leg was ACCEPTED — the node \
                 verifier checks only the lead leg and a forged tail cohort SLIPPED!"
            ),
            Err(other) => panic!(
                "expected SubProofInvalid (step-3 crypto, non-lead index) or CommitmentMismatch \
                 (step-4 chain), got {other:?}"
            ),
        }
    }

    // ──────────────────────────────────────────────────────────────────────
    // FRESHNESS / no-double-spend routing (the LIVE bindings this module wires)
    // ──────────────────────────────────────────────────────────────────────

    /// Build a turn-level `NoteSpend` effect with the given raw nullifier.
    fn note_spend_effect(nullifier: [u8; 32], value: u64) -> dregg_turn::Effect {
        dregg_turn::Effect::NoteSpend {
            nullifier: dregg_cell::note::Nullifier(nullifier),
            note_tree_root: [0u8; 32],
            value,
            asset_type: 0,
            spending_proof: Vec::new(),
            value_commitment: None,
        }
    }

    /// ROUTING: `spent_nullifiers` classifies a spend turn (so the commit path
    /// routes it to the freshness fn) and a non-spend turn (which stays on the
    /// self-sovereign path).
    #[test]
    fn routing_identifies_spend_vs_non_spend() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        let transfer = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 100,
        }];
        assert!(
            spent_nullifiers(&transfer).is_empty(),
            "a pure transfer is NOT a spend turn — stays on the self-sovereign path",
        );

        let nf = [0x5Eu8; 32];
        let spend = vec![note_spend_effect(nf, 500)];
        assert_eq!(
            spent_nullifiers(&spend),
            vec![nf],
            "a NoteSpend turn surfaces its nullifier so the commit path routes it to freshness",
        );

        // Nested inside ExerciseViaCapability is still detected.
        let nested = vec![dregg_turn::Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![note_spend_effect(nf, 500)],
        }];
        assert_eq!(
            spent_nullifiers(&nested),
            vec![nf],
            "a NoteSpend nested under ExerciseViaCapability is still routed to freshness",
        );
    }

    /// CONTROL (honest spend): a NoteSpend turn whose freshness is proven against
    /// the node's canonical spent-nullifier set VERIFIES through the bound
    /// verify→accept leg.
    #[test]
    fn honest_spend_freshness_verifies() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x11u8; 32];
        // Some previously-spent nullifiers (NOT including this turn's nf).
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i; 32]).collect();
        assert!(!previously.contains(&nf));

        let effects = vec![note_spend_effect(nf, 500)];
        let proven = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0xA0u8; 32],
            &nf,
            &previously,
        )
        .expect("honest spend (fresh against the canonical set) must prove + bound-verify");

        assert!(proven.proof.components.has_non_revocation);
        assert!(!proven.proof_bytes().is_empty());

        // Independent re-verification against the SAME canonical root the node
        // would derive (a light client's path).
        let canonical_root = canonical_revocation_root_for_set(&previously).unwrap();
        verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            Some(canonical_root),
            None,
        )
        .expect("light-client re-verify against the canonical root must accept");
    }

    /// ANTI-FORGERY binding (a) — RevocationRootMismatch: an honest spend proof
    /// is REJECTED when re-verified against a DIFFERENT (stale / wrong) revocation
    /// root than the one its freshness was proven against. This is exactly the
    /// counterfeiting hole the bound verify closes on the live path: a proof of
    /// freshness against one nullifier set must not be accepted as freshness
    /// against another.
    #[test]
    fn spend_against_wrong_revocation_root_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x22u8; 32];
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i; 32]).collect();

        let effects = vec![note_spend_effect(nf, 500)];
        let proven = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0xB0u8; 32],
            &nf,
            &previously,
        )
        .expect("honest spend proves");

        // A DIFFERENT canonical set (e.g. a staler view that already includes nf,
        // or simply a different set) yields a different canonical root.
        let other_set: Vec<[u8; 32]> = (1..=8u8).map(|i| [i; 32]).collect();
        let wrong_root = canonical_revocation_root_for_set(&other_set).unwrap();
        let honest_root = canonical_revocation_root_for_set(&previously).unwrap();
        assert_ne!(wrong_root, honest_root);

        let result = verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            Some(wrong_root),
            None,
        );
        match result {
            Err(FullTurnVerifyError::RevocationRootMismatch { expected, got }) => {
                assert_eq!(expected, wrong_root);
                assert_eq!(got, honest_root);
            }
            Ok(()) => panic!(
                "SOUNDNESS (no-double-spend binding a): a freshness proof against one nullifier \
                 set was ACCEPTED against a DIFFERENT root — the counterfeiting hole is OPEN!"
            ),
            Err(other) => panic!("expected RevocationRootMismatch, got {other:?}"),
        }
    }

    /// ANTI-FORGERY binding (b) — NullifierMismatch: a spend turn whose Effect-VM
    /// nullifier is N, but whose attached freshness proof attests a DIFFERENT item
    /// M, is REJECTED by the bound verify→accept leg. We drive this through the
    /// live freshness fn by passing a `spent_nullifier` (the freshness item) that
    /// differs from the turn's actual NoteSpend nullifier (the Effect-VM PI).
    #[test]
    fn spend_freshness_for_wrong_item_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        // The turn genuinely spends N.
        let n = [0x33u8; 32];
        // The prover attaches freshness for a DIFFERENT item M.
        let m = [0x44u8; 32];
        assert_ne!(n, m);
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i + 100; 32]).collect();

        let effects = vec![note_spend_effect(n, 500)];
        let result = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0xC0u8; 32],
            &m,
            &previously,
        );
        match result {
            Err(FullTurnProvingError::Verify(FullTurnVerifyError::NullifierMismatch {
                proven_item,
                effect_nullifier,
            })) => {
                assert_eq!(proven_item, nullifier_to_field(&m));
                assert_eq!(effect_nullifier, nullifier_to_field(&n));
            }
            Ok(_) => panic!(
                "SOUNDNESS (no-double-spend binding b): a spend of N whose freshness attests a \
                 DIFFERENT item M was ACCEPTED — the verify→accept gate did not fire!"
            ),
            Err(other) => panic!("expected Verify(NullifierMismatch), got {other:?}"),
        }
    }

    /// C4 CLOSE — a single-spend NoteSpend turn now proves ROTATED: the freshness path
    /// threads the cap-less rotation witness internally, so the composed proof carries the
    /// `"effect-vm-rotated"` leg (NOT the v1 `"effect-vm"`). The rotated note-spend descriptor
    /// (`noteSpendVmDescriptor2R24`) exposes the spent nullifier at PI[38], so `verify_full_turn`
    /// step 8 reads it from the rotated leg — the no-double-spend binding survives the rotation
    /// (the wrong-item / wrong-root teeth above run THROUGH this rotated path). This is the
    /// evidence that note-spend turns no longer fall back to v1 (unblocking C7).
    #[test]
    fn flow_b_note_spend_proves_rotated() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x77u8; 32];
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i; 32]).collect();
        assert!(!previously.contains(&nf));

        let effects = vec![note_spend_effect(nf, 500)];
        let proven = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0xA7u8; 32],
            &nf,
            &previously,
        )
        .expect("a single-spend note-spend turn must prove + bound-verify (now ROTATED)");

        let labels: Vec<&str> = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "the note-spend turn must prove through the ROTATED descriptor (C4 close); \
             sub-proofs = {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must NOT be present on the rotated note-spend turn; \
             sub-proofs = {labels:?}"
        );
        assert!(proven.proof.components.has_non_revocation);
    }

    /// C4 ANTI-GHOST (the rotated no-double-spend tooth, made EXPLICIT) — the freshness leg's
    /// nullifier binding survives the rotation, and a FORGED nullifier is REJECTED *through* the
    /// rotated path. Two halves on the SAME single-spend shape that rotates:
    ///
    ///  (1) HONEST: an honest single-spend freshness turn proves ROTATED, the rotated effect-vm
    ///      leg carries the 39-element PI vector (`ROT_NULLIFIER_PI_COUNT`), and its PI[38]
    ///      (`ROT_NULLIFIER_PI`) EQUALS the folded spent nullifier — i.e. the rotated leg actually
    ///      PINS this turn's nullifier (`EffectVmEmitRotationV3.noteSpendV3`), a real cryptographic
    ///      binding, not a free wire. (`honest_spend_freshness_verifies` proves the turn verifies;
    ///      this asserts the binding LIVES on the rotated leg specifically.)
    ///
    ///  (2) FORGED: a turn that genuinely spends N but whose attached freshness proof attests a
    ///      DIFFERENT item M is REJECTED by the bound verify→accept leg with `NullifierMismatch`,
    ///      and — because this single-spend turn rotates — `effect_nullifier` is read from the
    ///      ROTATED PI[38] (it equals `fold(N)`), proving the rejection fired on the rotated
    ///      step-8 tooth (not the v1 offset-198 one). This is the anti-ghost evidence that the C4
    ///      rotation did NOT weaken no-double-spend: a forged/substituted nullifier still UNSAT.
    #[test]
    fn flow_b_note_spend_rotated_nullifier_pin_is_antighost() {
        use dregg_circuit::effect_vm::trace_rotated::{ROT_NULLIFIER_PI, ROT_NULLIFIER_PI_COUNT};

        let alice = CellId::from_bytes([0xA1; 32]);
        let n = [0x9Au8; 32];
        let previously: Vec<[u8; 32]> = (10..=15u8).map(|i| [i; 32]).collect();
        assert!(!previously.contains(&n));

        // ── (1) HONEST: the rotated leg PINS this turn's nullifier at PI[38]. ──
        let effects = vec![note_spend_effect(n, 750)];
        let proven = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0x9Eu8; 32],
            &n,
            &previously,
        )
        .expect("honest single-spend freshness turn must prove + bound-verify (rotated)");

        // It rotated (the freshness path threads the cap-less rotation witness internally).
        let rotated_leg = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("the single-spend freshness turn must carry the rotated effect-vm leg (C4)");
        // The rotated note-spend leg carries the FIFTH appended pin (nullifier@ROT_NULLIFIER_PI) PLUS
        // the 16 WIDE commit PIs (the light-client flag-day): the wide note-spend vector is
        // ROT_NULLIFIER_PI_COUNT + 16. The nullifier still rides the prefix slot.
        assert_eq!(
            rotated_leg.sub_public_inputs.len(),
            ROT_NULLIFIER_PI_COUNT + 16,
            "a single-spend WIDE rotated leg publishes the note-spend prefix (nullifier@ROT_NULLIFIER_PI) \
             + the 16 wide 8-felt commit PIs"
        );
        // And PI[ROT_NULLIFIER_PI] IS this turn's folded nullifier — the binding is real, not a free wire.
        assert_eq!(
            rotated_leg.sub_public_inputs[ROT_NULLIFIER_PI],
            nullifier_to_field(&n),
            "rotated PI[ROT_NULLIFIER_PI] must pin the spend row's folded nullifier (EffectVmEmitRotationV3.noteSpendV3)"
        );

        // ── (2) FORGED: a freshness proof for a DIFFERENT item M is rejected THROUGH the rotated
        // leg (effect_nullifier read from rotated PI[38] == fold(N)). ──
        let m = [0x4Du8; 32];
        assert_ne!(n, m);
        let result = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects, // genuinely spends N
            [0x9Fu8; 32],
            &m, // but the prover attaches freshness for M
            &previously,
        );
        match result {
            Err(FullTurnProvingError::Verify(FullTurnVerifyError::NullifierMismatch {
                proven_item,
                effect_nullifier,
            })) => {
                assert_eq!(
                    proven_item,
                    nullifier_to_field(&m),
                    "the freshness leg proved item M fresh"
                );
                assert_eq!(
                    effect_nullifier,
                    nullifier_to_field(&n),
                    "the cross-checked nullifier is THIS turn's N, read from the ROTATED PI[38] — \
                     the rotated step-8 tooth fired (no-double-spend survived the C4 rotation)"
                );
            }
            Ok(_) => panic!(
                "ANTI-GHOST (rotated no-double-spend): a spend of N whose freshness attests a \
                 DIFFERENT item M was ACCEPTED on the rotated leg — the C4 weld weakened the tooth!"
            ),
            Err(other) => {
                panic!("expected Verify(NullifierMismatch) on the rotated leg, got {other:?}")
            }
        }
    }

    /// SOUNDNESS — the single-spend invariant survives the rotation. A turn with MORE THAN ONE
    /// NoteSpend must NOT commit to the rotated path: the rotated note-spend descriptor's
    /// first-row pin + the single freshness slot only faithfully cover ONE spend, so a second
    /// spend would be UNPINNED and ESCAPE the no-double-spend freshness check. The cap-less
    /// rotation-witness builder returns `None` for such a turn (the v1 leg runs instead, where the
    /// per-row D5 gate forces a single shared nullifier — a second DISTINCT nullifier is UNSAT). A
    /// single-spend turn, by contrast, DOES yield a rotation witness. This is the gate that keeps
    /// the rotation from silently weakening no-double-spend.
    #[test]
    fn cap_less_rotation_witness_refuses_multi_spend() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let n1 = [0x81u8; 32];
        let n2 = [0x82u8; 32];
        let receipts = [[0x88u8; 32]];

        // TWO NoteSpends ⇒ no rotation witness (keeps the v1 leg; the rotated leg can't cover it).
        let multi = vec![note_spend_effect(n1, 300), note_spend_effect(n2, 200)];
        assert!(
            rotation_witness_for_cap_less_turn(&alice, 1000, 0, &multi, &receipts).is_none(),
            "a multi-spend turn must NOT yield a rotation witness (the rotated note-spend leg \
             covers exactly one spend; a 2nd would escape the freshness check)"
        );

        // ONE NoteSpend ⇒ a rotation witness IS produced (the C4-closed single-spend shape).
        let single = vec![note_spend_effect(n1, 300)];
        assert!(
            rotation_witness_for_cap_less_turn(&alice, 1000, 0, &single, &receipts).is_some(),
            "a single-spend note-spend turn must yield a rotation witness (it rotates)"
        );
    }

    /// A spend whose nullifier is ALREADY in the canonical set (a double-spend)
    /// has no non-membership witness; the freshness fn refuses rather than fake a
    /// proof.
    #[test]
    fn double_spend_has_no_freshness_witness() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x55u8; 32];
        // nf is ALREADY spent.
        let previously: Vec<[u8; 32]> = vec![[1u8; 32], nf, [3u8; 32]];

        let effects = vec![note_spend_effect(nf, 500)];
        let result = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0xD0u8; 32],
            &nf,
            &previously,
        );
        assert!(
            matches!(result, Err(FullTurnProvingError::NullifierAlreadyRevoked)),
            "a double-spend must NOT be able to produce a freshness proof, got {result:?}",
        );
    }

    /// The canonical revocation tree honours the fixed-depth circuit capacity:
    /// a set within capacity builds; a set over capacity is refused (we never
    /// silently truncate, which could hide a double-spend).
    #[test]
    fn revocation_tree_respects_circuit_capacity() {
        let within: Vec<[u8; 32]> = (0..MAX_REVOCATION_TREE_ENTRIES as u8)
            .map(|i| [i; 32])
            .collect();
        assert!(
            canonical_revocation_tree_for_set(&within).is_ok(),
            "a set at the capacity bound must build",
        );

        let over: Vec<[u8; 32]> = (0..=MAX_REVOCATION_TREE_ENTRIES as u8)
            .map(|i| [i; 32])
            .collect();
        match canonical_revocation_tree_for_set(&over) {
            Err(FullTurnProvingError::RevocationCapacityExceeded { have, max }) => {
                assert_eq!(have, over.len());
                assert_eq!(max, MAX_REVOCATION_TREE_ENTRIES);
            }
            other => panic!("expected RevocationCapacityExceeded, got {other:?}"),
        }
    }

    // ──────────────────────────────────────────────────────────────────────
    // AUTHORITY / cap-membership routing (cap Phase D — the payoff gauntlet)
    // ──────────────────────────────────────────────────────────────────────

    use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
    use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, symbol};
    use dregg_turn::forest::{CallForest, CallTree};
    use dregg_turn::turn::{Turn, TurnResult};
    use dregg_turn::{ComputronCosts, TurnExecutor};

    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn set_field_action(target: CellId, auth: Authorization, value: [u8; 32]) -> Action {
        Action {
            target,
            method: symbol("set_field"),
            args: vec![],
            authorization: auth,
            preconditions: Default::default(),
            effects: vec![dregg_turn::Effect::SetField {
                cell: target,
                index: 0,
                value,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        }
    }

    /// A `send`-gated transfer FROM `from` TO `to` (the actor's own outgoing transfer — the actor's
    /// Effect-VM projection is `Transfer{direction:1}`, a ROTATABLE cohort effect whose R24
    /// descriptor models the nonce tick, unlike SetField).
    fn transfer_action(from: CellId, to: CellId, amount: u64, auth: Authorization) -> Action {
        Action {
            target: from,
            method: symbol("transfer"),
            args: vec![],
            authorization: auth,
            preconditions: Default::default(),
            effects: vec![dregg_turn::Effect::Transfer { from, to, amount }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        }
    }

    fn wrap_turn(agent: CellId, action: Action) -> Turn {
        Turn {
            agent,
            nonce: 0,
            call_forest: CallForest {
                roots: vec![CallTree {
                    action,
                    children: vec![],
                    hash: [0u8; 32],
                }],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Run a REAL breadstuff-gated turn through the executor (the cap Phase C
    /// capture path): the agent's c-list holds a breadstuff capability to the
    /// target, whose Signature-tier `set_state` the breadstuff satisfies.
    /// Returns the committed receipt (carrying the consumed-cap witness), the
    /// agent id, the agent's CANONICAL pre-state capability root (recomputed
    /// independently from the pre-execution c-list, exactly as the commit path
    /// captures it), and the turn's effects.
    fn run_breadstuff_gated_turn() -> (
        dregg_turn::TurnReceipt,
        CellId,
        BabyBear,
        Vec<dregg_turn::Effect>,
    ) {
        let token: [u8; 32] = [0xD5; 32];
        let mut agent = Cell::with_balance([0xA7u8; 32], [0u8; 32], 1_000);
        agent.permissions = open_permissions();

        let mut target = Cell::with_balance([0x3Bu8; 32], [0u8; 32], 500);
        let mut perms = open_permissions();
        perms.set_state = AuthRequired::Signature;
        target.permissions = perms;
        let target_id = target.id();

        // A decoy capability so the consumed cap is not the only leaf.
        agent
            .capabilities
            .grant(CellId::from_bytes([0x77u8; 32]), AuthRequired::None);
        let slot = agent
            .capabilities
            .grant_with_breadstuff(target_id, AuthRequired::None, Some(token))
            .expect("grant breadstuff cap");
        // Restrict the cap to EXACTLY SetField. `grant_with_breadstuff` leaves
        // `allowed_effects = None` (⇒ EFFECT_ALL ⇒ leaf mask limbs already
        // all-ones), which would make the inflated-mask forgery below a NO-OP.
        // A NARROW mask makes that forgery a REAL rights amplification.
        agent
            .capabilities
            .iter_mut()
            .find(|c| c.slot == slot)
            .expect("granted cap present")
            .allowed_effects = Some(dregg_cell::facet::EFFECT_SET_FIELD);

        let agent_id = agent.id();
        // The CANONICAL pre-state capability root, from the authoritative
        // pre-execution c-list (the same capture the commit path performs).
        let pre_cap_root = dregg_cell::compute_canonical_capability_root_felt(&agent.capabilities);

        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(target).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let turn = wrap_turn(
            agent_id,
            set_field_action(target_id, Authorization::Breadstuff(token), [42u8; 32]),
        );
        let effects: Vec<dregg_turn::Effect> = turn
            .call_forest
            .total_effects()
            .into_iter()
            .cloned()
            .collect();
        let receipt = match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { receipt, .. } => receipt,
            other => panic!("breadstuff turn must commit, got {other:?}"),
        };
        (receipt, agent_id, pre_cap_root, effects)
    }

    /// A capability-gated turn whose effect is the actor's OWN outgoing TRANSFER — the shape that
    /// ROTATES (the transfer R24 descriptor models the nonce tick; SetField's does NOT — see the
    /// seam note on the builder). The agent gates its OWN `send` at the Signature tier and holds a
    /// self-breadstuff-cap (restricted to EXACTLY Transfer) to satisfy it; the action transfers
    /// `amount` to a recipient. The agent's Effect-VM projection (`convert_effects_to_vm(agent, …)`)
    /// is then `[Transfer{direction:1}]` — a NON-EMPTY rotatable cohort transition.
    ///
    /// (The cross-cell fixture `run_breadstuff_gated_turn` — a SetField on a DIFFERENT cell — yields
    /// an EMPTY actor projection, a no-op actor transition the v1 leg proves but the rotated prover
    /// refuses; and a SELF-SetField would tick the nonce against the broken `setFieldVmDescriptor2-*R24`
    /// nonce-passthrough gate. So this self-Transfer shape is what faithfully exercises the rotated
    /// capability leg.)
    ///
    /// Returns the receipt, agent id, the agent's CANONICAL pre-state cap root, the turn's effects,
    /// and the agent's REAL before/after `Cell` (the `full_turn_pre_cell` analog + the post-exec
    /// ledger cell) so the rotated-cap tests build the witness from the REAL cell (faithful r23).
    fn run_self_cap_gated_turn_full() -> (
        dregg_turn::TurnReceipt,
        CellId,
        BabyBear,      // SCALAR lane-0 pre-state cap root (the EffectVm-seed)
        [BabyBear; 8], // FULL native 8-felt pre-state cap root (the membership root)
        Vec<dregg_turn::Effect>,
        Cell,
        Cell,
    ) {
        let token: [u8; 32] = [0xD5; 32];
        // The agent gates its OWN send at the Signature tier (so the consumed breadstuff is a
        // MEANINGFUL authorization), and holds a self-breadstuff-cap to satisfy it.
        let mut agent = Cell::with_balance([0xA7u8; 32], [0u8; 32], 1_000);
        let mut perms = open_permissions();
        perms.send = AuthRequired::Signature;
        agent.permissions = perms;
        let agent_id = agent.id();

        // The recipient (its `receive` is open).
        let recipient = Cell::with_balance([0x3Bu8; 32], [0u8; 32], 0);
        let recipient_id = recipient.id();

        // A decoy capability so the consumed cap is not the only leaf.
        agent
            .capabilities
            .grant(CellId::from_bytes([0x77u8; 32]), AuthRequired::None);
        // The SELF breadstuff cap (target == agent), restricted to EXACTLY Transfer (a narrow mask
        // so an inflated-mask forgery is a REAL amplification, not a no-op).
        let slot = agent
            .capabilities
            .grant_with_breadstuff(agent_id, AuthRequired::None, Some(token))
            .expect("grant self breadstuff cap");
        agent
            .capabilities
            .iter_mut()
            .find(|c| c.slot == slot)
            .expect("granted cap present")
            .allowed_effects = Some(dregg_cell::facet::EFFECT_TRANSFER);

        let pre_cap_root = dregg_cell::compute_canonical_capability_root_felt(&agent.capabilities);
        // The FULL native 8-felt openable membership root (the ~124-bit faithful
        // root the cap-membership leg / `CapMembershipExpectation.cap_root` binds).
        let pre_cap_root_8 =
            dregg_cell::compute_canonical_capability_root_8(&agent.capabilities).limbs();
        // The REAL before-state cell the commit path holds (real pk + c-list ⇒ faithful r23).
        let before_cell = agent.clone();

        let mut ledger = Ledger::new();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(recipient).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        // The action transfers 100 FROM the agent TO the recipient, authorized by the self-cap.
        let turn = wrap_turn(
            agent_id,
            transfer_action(
                agent_id,
                recipient_id,
                100,
                Authorization::Breadstuff(token),
            ),
        );
        let effects: Vec<dregg_turn::Effect> = turn
            .call_forest
            .total_effects()
            .into_iter()
            .cloned()
            .collect();
        let receipt = match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { receipt, .. } => receipt,
            other => panic!("self-cap breadstuff transfer must commit, got {other:?}"),
        };
        let after_cell = ledger
            .get(&agent_id)
            .expect("agent present after exec")
            .clone();
        (
            receipt,
            agent_id,
            pre_cap_root,
            pre_cap_root_8,
            effects,
            before_cell,
            after_cell,
        )
    }

    /// ROUTING: a capability-gated receipt is classified onto the cap path
    /// (the actor-held witness is found); a self-sovereign receipt is not.
    #[test]
    fn routing_identifies_capability_gated_vs_self_sovereign() {
        let (receipt, agent_id, _, _) = run_breadstuff_gated_turn();
        assert_eq!(receipt.consumed_capabilities.len(), 1);
        assert!(
            actor_consumed_cap(&receipt.consumed_capabilities, &agent_id).is_some(),
            "a breadstuff-gated turn routes to the cap-membership path"
        );
        assert!(
            actor_consumed_cap(&[], &agent_id).is_none(),
            "a self-sovereign turn (empty witnesses) stays on the existing paths"
        );
    }

    /// CONTROL: an honest capability-gated turn proves + verifies end-to-end
    /// WITH the cap-membership leg, bound to the canonical pre-state
    /// capability root and the receipt-disclosed consumed-cap leaf.
    #[test]
    fn honest_capability_gated_turn_proves_with_cap_leg() {
        // The SELF-Transfer cap fixture (the shape that ROTATES — the live cap-gated commit path
        // proves through the rotated descriptor under `recursion`, the v1 cap leg being retired).
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .expect("actor-held consumed-cap witness");
        let receipts = [receipt.receipt_hash()];

        let rotation = rotation_witness_for_capability(
            1_000,
            0,
            pre_cap_root,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "the honest cap-gated turn must yield a rotation witness (faithful real-cell r23)"
        );
        let proven = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xCAu8; 32],
            consumed,
            None,
            &[],
            rotation,
            Default::default(),
            None,
        )
        .expect("honest capability-gated turn must prove + cap-bound-verify");

        assert!(
            proven.proof.components.has_cap_membership,
            "cap leg attached"
        );
        assert!(!proven.proof_bytes().is_empty());

        // Independent re-verification (a light client's path): recompute the
        // expectation from the receipt witness + the canonical root.
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: pre_cap_root_8,
        };
        verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        )
        .expect("light-client re-verify with the cap expectation must accept");
    }

    /// ANTI-FORGERY 1 — a consumed-cap witness whose path does NOT reach the
    /// canonical pre-state cap_root is REJECTED: (a) the prover refuses a
    /// tampered-path witness outright; (b) an honest proof re-verified against
    /// a different expected root fails with `CapRootMismatch`.
    #[test]
    fn cap_witness_path_not_reaching_prestate_root_is_rejected() {
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .unwrap()
            .clone();
        let receipts = [receipt.receipt_hash()];
        let rotation = || {
            rotation_witness_for_capability(
                1_000,
                0,
                pre_cap_root,
                &before_cell,
                &after_cell,
                &receipts,
                &effects,
            )
        };

        // (a) Tamper a sibling: the path no longer recomputes the witness's
        // own root — the prover refuses (no sound leg exists), even WITH a rotation witness in hand.
        let mut tampered = consumed.clone();
        // Tamper the sibling digest (all 8 lanes) so the path no longer recomputes
        // the witness's own root.
        tampered.siblings[2] = tampered.siblings[2].map(|x| x ^ 1);
        let result = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xCBu8; 32],
            &tampered,
            None,
            &[],
            rotation(),
            Default::default(),
            None,
        );
        assert!(
            matches!(
                result,
                Err(FullTurnProvingError::ConsumedCapWitnessInvalid { .. })
            ),
            "a tampered membership path must be refused, got {result:?}"
        );

        // (b) Honest proof (ROTATED), verified against a DIFFERENT expected root: the
        // cap leg's in-circuit-bound root mismatches → CapRootMismatch.
        let proven = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xCCu8; 32],
            &consumed,
            None,
            &[],
            rotation(),
            Default::default(),
            None,
        )
        .expect("honest proof");
        // A genuinely distinct 8-felt root (every lane perturbed) — NOT a lane-0
        // squeeze — so the in-circuit-bound root mismatches on the full digest.
        let wrong_root = pre_cap_root_8.map(|f| f + BabyBear::new(1));
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: wrong_root,
        };
        match verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        ) {
            Err(FullTurnVerifyError::CapRootMismatch { expected, got }) => {
                assert_eq!(expected, wrong_root);
                assert_eq!(got, pre_cap_root_8);
            }
            Ok(()) => panic!(
                "SOUNDNESS (AUTHORITY): a cap-membership proof against one tree was \
                 ACCEPTED against a DIFFERENT root — the splicing hole is OPEN!"
            ),
            Err(other) => panic!("expected CapRootMismatch, got {other:?}"),
        }
    }

    /// ANTI-FORGERY 2 — a leaf-field tamper (INFLATED EffectMask) is REJECTED:
    /// the verifier recomputes the leaf digest from the disclosed witness
    /// fields and the leg's row-0-bound digest mismatches (`CapLeafMismatch`);
    /// and a receipt witness whose leaf was inflated no longer opens to the
    /// canonical root, so the prover refuses it outright.
    #[test]
    fn inflated_mask_leaf_tamper_is_rejected() {
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .unwrap()
            .clone();
        let receipts = [receipt.receipt_hash()];
        let rotation = || {
            rotation_witness_for_capability(
                1_000,
                0,
                pre_cap_root,
                &before_cell,
                &after_cell,
                &receipts,
                &effects,
            )
        };

        // The committed cap's rights are NARROW (exactly Transfer, EFFECT_TRANSFER = 1<<1 = 2) —
        // the inflation below is a REAL amplification, not a no-op.
        assert_eq!(
            consumed.leaf_mask_lo, 2,
            "fixture grants a Transfer-only mask"
        );
        assert_eq!(
            consumed.leaf_mask_hi, 0,
            "fixture grants a Transfer-only mask"
        );

        // (a) Prover side (rotated): an inflated-mask witness has no membership path to
        // the canonical root (the inflated leaf is NOT in the tree), so the cap path refuses even
        // with the rotation witness threaded.
        let mut inflated = consumed.clone();
        inflated.leaf_mask_lo = 0xFFFF;
        inflated.leaf_mask_hi = 0xFFFF;
        let result = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xCDu8; 32],
            &inflated,
            None,
            &[],
            rotation(),
            Default::default(),
            None,
        );
        assert!(
            matches!(
                result,
                Err(FullTurnProvingError::ConsumedCapWitnessInvalid { .. })
            ),
            "an inflated-mask leaf must be refused (not in the canonical tree), got {result:?}"
        );

        // (b) Verifier side: an honest ROTATED proof checked against an inflated-leaf
        // expectation mismatches the in-circuit-bound leaf digest.
        let proven = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xCEu8; 32],
            &consumed,
            None,
            &[],
            rotation(),
            Default::default(),
            None,
        )
        .expect("honest proof");
        let mut inflated_leaf = consumed.cap_leaf();
        let (lo, hi) = dregg_circuit::cap_root::split_effect_mask(0xFFFF_FFFF);
        inflated_leaf.mask_lo = lo;
        inflated_leaf.mask_hi = hi;
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: inflated_leaf,
            cap_root: pre_cap_root_8,
        };
        match verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        ) {
            Err(FullTurnVerifyError::CapLeafMismatch { expected, got }) => {
                assert_eq!(expected, inflated_leaf.digest());
                assert_eq!(got, consumed.cap_leaf().digest());
            }
            Ok(()) => panic!(
                "SOUNDNESS (AUTHORITY): an INFLATED-MASK leaf was ACCEPTED — rights \
                 amplification through the proof leg is OPEN!"
            ),
            Err(other) => panic!("expected CapLeafMismatch, got {other:?}"),
        }
    }

    /// ANTI-FORGERY 3 — splicing a DIFFERENT cell's cap_root is REJECTED: the
    /// witness opens to the agent's tree, so binding the leg to another cell's
    /// canonical root fails (prover refusal AND verifier `CapRootMismatch`).
    #[test]
    fn different_cells_cap_root_splice_is_rejected() {
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .unwrap()
            .clone();
        let receipts = [receipt.receipt_hash()];

        // A DIFFERENT cell with a different c-list ⇒ a different canonical root.
        let mut other = Cell::with_balance([0x99u8; 32], [0u8; 32], 10);
        other
            .capabilities
            .grant(CellId::from_bytes([0x55u8; 32]), AuthRequired::None);
        let other_root = dregg_cell::compute_canonical_capability_root_felt(&other.capabilities);
        // The other cell's FULL native 8-felt root — the holder root the splice
        // attempt binds against (distinct from the agent's, so the witness cannot
        // open to it).
        let other_root_8 =
            dregg_cell::compute_canonical_capability_root_8(&other.capabilities).limbs();
        assert_ne!(
            other_root, pre_cap_root,
            "distinct c-lists ⇒ distinct roots"
        );

        // (a) Prover refuses: the witness does not open to the other cell's root (the consumed
        // cap_root != the supplied root check fires before the rotated leg is built).
        let result = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            other_root,
            other_root_8,
            &effects,
            [0xCFu8; 32],
            &consumed,
            None,
            &[],
            None,
            Default::default(),
            None,
        );
        assert!(
            matches!(
                result,
                Err(FullTurnProvingError::ConsumedCapWitnessInvalid { .. })
            ),
            "a witness for the agent's tree must not prove under another cell's root"
        );

        // (b) Verifier rejects an honest ROTATED proof bound to the other cell's root.
        let rotation = rotation_witness_for_capability(
            1_000,
            0,
            pre_cap_root,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        let proven = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xD0u8; 32],
            &consumed,
            None,
            &[],
            rotation,
            Default::default(),
            None,
        )
        .expect("honest proof");
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: other_root_8,
        };
        let result = verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        );
        assert!(
            matches!(result, Err(FullTurnVerifyError::CapRootMismatch { .. })),
            "SOUNDNESS (AUTHORITY): another cell's cap_root must not bind, got {result:?}"
        );
    }

    /// CONTROL 2: self-sovereign turns are UNCHANGED — no cap leg is attached,
    /// and the plain verify path still accepts.
    #[test]
    fn self_sovereign_turn_unchanged_no_cap_leg() {
        let bob = CellId::from_bytes([0xB2; 32]);
        let pre_balance: u64 = 500;
        let pre_nonce: u64 = 1;
        let mut before_cell =
            dregg_cell::Cell::with_balance([0xA1; 32], [0u8; 32], pre_balance as i64);
        before_cell.state.set_nonce(pre_nonce);
        let alice = before_cell.id();
        let amount: u64 = 25;
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance((pre_balance - amount) as i64);
        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount,
        }];
        let receipt_hashes = [[0x11u8; 32]];
        let rotation = rotation_witness_for_self_sovereign(
            pre_balance,
            pre_nonce,
            &before_cell,
            &after_cell,
            &receipt_hashes,
            &effects,
        );
        let proven = prove_and_verify_finalized_turn(
            &alice,
            pre_balance,
            pre_nonce,
            &effects,
            [0xD1u8; 32],
            rotation,
        )
        .expect("self-sovereign turn proves as before");
        assert!(
            !proven.proof.components.has_cap_membership,
            "a self-sovereign turn carries NO cap-membership leg"
        );
        dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit)
            .expect("self-sovereign verification is unchanged");
    }

    /// A capability-gated turn whose proof LACKS the cap leg must be rejected
    /// when verified with the expectation (the leg cannot be stripped).
    #[test]
    fn missing_cap_leg_is_rejected_for_capability_gated_turn() {
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .unwrap()
            .clone();
        let receipts = [receipt.receipt_hash()];

        // Prove WITHOUT the cap leg (the legacy self-sovereign prover, ROTATED), then
        // try to pass it off as the capability-gated proof. The actor's own outgoing transfer is a
        // self-sovereign-shaped rotatable projection, so the cap-less rotation witness admits it.
        let rotation = rotation_witness_for_self_sovereign(
            1_000,
            0,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        let proven =
            prove_and_verify_finalized_turn(&agent_id, 1_000, 0, &effects, [0xD2u8; 32], rotation)
                .expect("legless proof proves");
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: pre_cap_root_8,
        };
        let result = verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        );
        assert!(
            matches!(result, Err(FullTurnVerifyError::MissingComponent(_))),
            "SOUNDNESS (AUTHORITY): a capability-gated turn without the cap leg must be \
             rejected, got {result:?}"
        );
    }

    // ──────────────────────────────────────────────────────────────────────
    // FLOW-B ROTATION of the CAPABILITY arm (C7 close — capability turns rotate)
    // ──────────────────────────────────────────────────────────────────────

    /// THE BUILDER GATE: the capability rotation witness is produced from the REAL before/after
    /// cells when their welded scalars match the v1 capability pre-state (real balance/nonce, zero
    /// fields, cap_root == the canonical pre-state root) — and is REFUSED (`None` ⇒ graceful v1
    /// fallback) when the supplied root does NOT match the cell's real c-list root (the faithful-or-
    /// fallback discipline; never a zero-pk stub).
    #[test]
    fn capability_rotation_witness_faithful_or_falls_back() {
        let (_receipt, _agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let receipts = [[0x11u8; 32]];

        // Real cell + the matching canonical root ⇒ a faithful rotation witness (its r23 folds the
        // REAL pk/permissions/c-list).
        let w = rotation_witness_for_capability(
            1_000,
            0,
            pre_cap_root,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(
            w.is_some(),
            "a cap-gated transfer turn over the REAL cell (cap_root == pre_cap_root) must yield a \
             faithful rotation witness"
        );

        // A WRONG pre-state root (the empty root — what a cap-less stub would carry) does NOT match
        // the cell's real c-list root, so the gate refuses rather than mint a leg that disagrees
        // with the v1 cap pre-state. This is the discipline that keeps a zero-pk/empty-authority
        // stub from ever being laundered onto the rotated path.
        let empty_root_8 = dregg_circuit::cap_root::empty_capability_root();
        assert_ne!(
            empty_root_8, pre_cap_root_8,
            "the fixture holds a non-empty c-list"
        );
        // The SCALAR lane-0 empty root the rotation-witness builder (a scalar-seed
        // API) consumes — disagreeing with the cell's real c-list root.
        let empty_root_felt =
            dregg_cell::compute_canonical_capability_root_felt(&dregg_cell::CapabilitySet::new());
        let w_bad = rotation_witness_for_capability(
            1_000,
            0,
            empty_root_felt,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(
            w_bad.is_none(),
            "a pre-state root that disagrees with the cell's real c-list root must fall back to v1"
        );
    }

    /// CONTROL (the C7-closing evidence): an honest capability-gated turn, proven with the rotation
    /// witness threaded, proves through the ROTATED descriptor (`"effect-vm-rotated"`, NOT the v1
    /// `"effect-vm"`) AND carries the cap-membership leg — both legs compose. This is the live
    /// commit-path call (`blocklace_sync` builds the witness from `full_turn_pre_cell` exactly so).
    #[test]
    fn flow_b_capability_gated_turn_proves_rotated() {
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .expect("actor-held consumed-cap witness");
        let receipts = [receipt.receipt_hash()];

        let rotation = rotation_witness_for_capability(
            1_000,
            0,
            pre_cap_root,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "the honest cap-gated turn must yield a rotation witness (faithful real-cell r23)"
        );

        let proven = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xCAu8; 32],
            consumed,
            None,
            &[],
            rotation,
            Default::default(),
            None,
        )
        .expect("the rotated capability-gated turn must prove + cap-bound-verify");

        // Both legs present: the ROTATED effect-vm leg AND the cap-membership leg.
        let labels: Vec<&str> = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "the live capability turn must prove through the rotated descriptor; sub-proofs = \
             {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must NOT be present on the rotated capability turn; sub-proofs = \
             {labels:?}"
        );
        assert!(
            proven.proof.components.has_cap_membership,
            "the cap-membership leg must still be attached on the rotated path"
        );

        // Independent re-verification with the cap expectation (a light client's path) accepts.
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: pre_cap_root_8,
        };
        verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        )
        .expect("light-client re-verify of the ROTATED cap turn with the expectation must accept");
    }

    /// THE CAP SOUNDNESS TOOTH SURVIVES ROTATION — a cap OVER-GRANT / amplification (granted ⊄ held)
    /// is still REFUSED on the ROTATED leg. We thread a genuine rotation witness (so the turn really
    /// IS on the rotated path), then present an INFLATED-mask consumed witness (rights amplified
    /// beyond the Transfer-only grant the c-list actually holds). The non-amp + authority-digest
    /// bind must bite regardless of the rotation:
    ///   (a) prover side — the inflated leaf is NOT a member of the canonical pre-state cap_root, so
    ///       the cap path REFUSES (`ConsumedCapWitnessInvalid`) BEFORE any proof is minted, even with
    ///       the rotation witness in hand;
    ///   (b) verifier side — an honest ROTATED proof re-checked against an inflated-leaf expectation
    ///       mismatches the in-circuit-bound leaf digest (`CapLeafMismatch`).
    /// This is the evidence the over-grant tooth fires on the rotated path, not only the happy path.
    #[test]
    fn cap_over_grant_refused_on_rotated_leg() {
        let (receipt, agent_id, pre_cap_root, pre_cap_root_8, effects, before_cell, after_cell) =
            run_self_cap_gated_turn_full();
        let consumed = actor_consumed_cap(&receipt.consumed_capabilities, &agent_id)
            .unwrap()
            .clone();
        let receipts = [receipt.receipt_hash()];

        // The genuine rotation witness for THIS turn (the turn is really on the rotated path).
        let rotation = rotation_witness_for_capability(
            1_000,
            0,
            pre_cap_root,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(rotation.is_some(), "the turn rotates");

        // The committed grant is NARROW (Transfer only, EFFECT_TRANSFER = 1<<1 = 2) — the inflation
        // below is a REAL amplification, not a no-op.
        assert_eq!(
            consumed.leaf_mask_lo, 2,
            "fixture grants a Transfer-only mask"
        );
        assert_eq!(
            consumed.leaf_mask_hi, 0,
            "fixture grants a Transfer-only mask"
        );

        // (a) PROVER SIDE on the rotated path: an OVER-GRANTED (inflated-mask) witness has no
        // membership path to the canonical cap_root → the cap path refuses even WITH the rotation
        // witness threaded. The amplification cannot ride the rotated leg.
        let mut over_granted = consumed.clone();
        over_granted.leaf_mask_lo = 0xFFFF;
        over_granted.leaf_mask_hi = 0xFFFF;
        let result = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xC1u8; 32],
            &over_granted,
            None,
            &[],
            rotation,
            Default::default(),
            None,
        );
        assert!(
            matches!(
                result,
                Err(FullTurnProvingError::ConsumedCapWitnessInvalid { .. })
            ),
            "SOUNDNESS (AUTHORITY, ROTATED): an OVER-GRANT (granted ⊄ held) must be REFUSED on the \
             rotated leg, got {result:?}"
        );

        // (b) VERIFIER SIDE on the rotated path: prove the honest turn ROTATED, then re-verify
        // against an inflated-leaf expectation — the rotated leg's row-0-bound leaf digest
        // mismatches (`CapLeafMismatch`), so the amplification is rejected at verify time too.
        let rotation2 = rotation_witness_for_capability(
            1_000,
            0,
            pre_cap_root,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        let proven = prove_and_verify_finalized_turn_capability(
            &agent_id,
            1_000,
            0,
            pre_cap_root,
            pre_cap_root_8,
            &effects,
            [0xC2u8; 32],
            &consumed,
            None,
            &[],
            rotation2,
            Default::default(),
            None,
        )
        .expect("honest ROTATED cap proof");
        // Confirm it really IS the rotated leg carrying the cap tooth.
        assert!(
            proven
                .proof
                .composed
                .sub_proofs
                .iter()
                .any(|sp| sp.label == "effect-vm-rotated"),
            "the soundness tooth must be exercised on the ROTATED leg"
        );
        let mut inflated_leaf = consumed.cap_leaf();
        let (lo, hi) = dregg_circuit::cap_root::split_effect_mask(0xFFFF_FFFF);
        inflated_leaf.mask_lo = lo;
        inflated_leaf.mask_hi = hi;
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: inflated_leaf,
            cap_root: pre_cap_root_8,
        };
        match verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        ) {
            Err(FullTurnVerifyError::CapLeafMismatch { expected, got }) => {
                assert_eq!(expected, inflated_leaf.digest());
                assert_eq!(got, consumed.cap_leaf().digest());
            }
            Ok(()) => panic!(
                "SOUNDNESS (AUTHORITY, ROTATED): an INFLATED-MASK leaf was ACCEPTED on the rotated \
                 leg — rights amplification through the proof is OPEN!"
            ),
            Err(other) => panic!("expected CapLeafMismatch on the rotated leg, got {other:?}"),
        }
    }

    // ──────────────────────────────────────────────────────────────────────
    // BEARER-DELEGATION AUTHORITY leg (the soundness fix —
    // `blocklace_sync.rs` routes a `holder != actor` witness through
    // `prove_and_verify_finalized_turn_capability_holder` bound to the
    // DELEGATOR's node-derived pre-state cap root). These teeth cover the
    // residual the prior code merely warned-and-fell-through on: a bearer
    // turn now PROVES the authority leg against the delegator's real c-list,
    // and a bearer turn whose delegator lacked the cap is REJECTED.
    // ──────────────────────────────────────────────────────────────────────

    /// Build the (delegator keypair, bearer pk) the bearer fixtures use. Fixed
    /// seeds ⇒ deterministic, reproducible cell ids. Real ed25519 keys: the
    /// executor verifies the delegation signature and resolves the delegator
    /// cell by `cell.public_key() == delegator_pk`, so the cell's public key
    /// MUST be a genuine verifying key.
    fn bearer_keys() -> (ed25519_dalek::SigningKey, [u8; 32], [u8; 32]) {
        use ed25519_dalek::SigningKey;
        let delegator_sk = SigningKey::from_bytes(&[7u8; 32]);
        let delegator_pk = delegator_sk.verifying_key().to_bytes();
        let bearer_pk = SigningKey::from_bytes(&[8u8; 32])
            .verifying_key()
            .to_bytes();
        (delegator_sk, delegator_pk, bearer_pk)
    }

    /// Construct the bearer turn's forest: the BEARER (actor) transfers FROM
    /// ITSELF to a recipient, authorized by a delegation of the delegator's
    /// capability over the BEARER cell (target == bearer). The actor's Effect-VM
    /// projection is therefore `[Transfer{direction:1}]` — a NON-EMPTY rotatable
    /// cohort transition (the same rotatable shape `run_self_cap_gated_turn_full`
    /// uses), so the live commit path proves it ROTATED under `recursion` (the
    /// v1 effect-vm fallback being retired).
    fn make_bearer_transfer_turn(
        delegator_sk: &ed25519_dalek::SigningKey,
        delegator_pk: [u8; 32],
        bearer_pk: [u8; 32],
        bearer_id: CellId,
        recipient_id: CellId,
    ) -> Turn {
        use ed25519_dalek::Signer;
        // The delegation is over the BEARER cell (so it satisfies the bearer's
        // own Signature-gated `send`).
        let message = dregg_turn::TurnExecutor::compute_bearer_delegation_message(
            &bearer_id,
            &AuthRequired::None,
            &bearer_pk,
            1_000,
            &[0u8; 32],
        );
        let signature = delegator_sk.sign(&message).to_bytes();
        let bearer_proof = dregg_turn::action::BearerCapProof {
            target: bearer_id,
            permissions: AuthRequired::None,
            delegation_proof: dregg_turn::DelegationProofData::SignedDelegation {
                delegator_pk,
                signature,
                bearer_pk,
            },
            expires_at: 1_000,
            revocation_channel: None,
            allowed_effects: None,
        };
        wrap_turn(
            bearer_id,
            transfer_action(
                bearer_id,
                recipient_id,
                100,
                Authorization::Bearer(bearer_proof),
            ),
        )
    }

    /// Run a REAL bearer-delegation turn through the executor (the cap Phase C
    /// bearer capture path, `authorize.rs`): a DELEGATOR cell holds a capability
    /// over the BEARER cell and signs a `SignedDelegation` the BEARER (actor)
    /// exercises via `Authorization::Bearer` to authorize its OWN outgoing
    /// transfer. The executor records the consumed-cap witness against the
    /// DELEGATOR's pre-state c-list, so the receipt carries a witness whose
    /// `holder` is the delegator (NOT the actor) — exactly the shape the commit
    /// path routes through the bearer authority leg.
    ///
    /// Returns the committed receipt (carrying the bearer consumed-cap witness),
    /// the actor (bearer) id, the DELEGATOR id, the delegator's CANONICAL
    /// pre-state capability root (recomputed independently, as the commit path's
    /// `delegator_pre_state_cap_roots` does), the actor's CANONICAL pre-state cap
    /// root (the EffectVm-seed root, distinct from the delegator's), the effects,
    /// and the actor's REAL before/after `Cell` (so the teeth build the actor's
    /// rotation witness from the real cell, exactly as the commit path does).
    #[allow(clippy::type_complexity)]
    fn run_bearer_delegated_turn() -> (
        dregg_turn::TurnReceipt,
        CellId,        // actor (bearer) id
        CellId,        // delegator id
        [BabyBear; 8], // delegator pre-state cap root (the authority-leg root, 8-felt)
        BabyBear,      // actor pre-state cap root (the EffectVm-seed root, SCALAR)
        [BabyBear; 8], // actor pre-state cap root (8-felt, for the distinctness assert)
        Vec<dregg_turn::Effect>,
        Cell, // bearer before-cell
        Cell, // bearer after-cell
    ) {
        let (delegator_sk, delegator_pk, bearer_pk) = bearer_keys();

        // DELEGATOR cell: holds a real capability over the BEARER (+ a decoy so
        // the consumed cap is not the only leaf), with open `delegate`/`access`.
        let mut delegator = Cell::with_balance(delegator_pk, [0u8; 32], 1_000);
        delegator.permissions = open_permissions();
        delegator
            .capabilities
            .grant(CellId::from_bytes([0x66u8; 32]), AuthRequired::None);

        // BEARER (actor) cell: gates its OWN `send` at the Signature tier (so the
        // delegated authority is MEANINGFUL), holds a decoy cap of its own.
        let bearer_token: [u8; 32] = [0u8; 32];
        let mut bearer = Cell::with_balance(bearer_pk, bearer_token, 1_000);
        let mut bearer_perms = open_permissions();
        bearer_perms.send = AuthRequired::Signature;
        bearer.permissions = bearer_perms;
        bearer
            .capabilities
            .grant(CellId::from_bytes([0x99u8; 32]), AuthRequired::None);
        let bearer_id = bearer.id();
        // The actor's EffectVm-seed root (SCALAR lane-0) AND its FULL native 8-felt
        // form (used only for the distinctness assert against the delegator root).
        let actor_cap_root =
            dregg_cell::compute_canonical_capability_root_felt(&bearer.capabilities);
        let actor_cap_root_8 =
            dregg_cell::compute_canonical_capability_root_8(&bearer.capabilities).limbs();

        // The delegator's capability is over the BEARER cell.
        delegator.capabilities.grant(bearer_id, AuthRequired::None);
        let delegator_id = delegator.id();
        // The authority-leg (holder) root is the FULL native 8-felt openable root.
        let delegator_cap_root =
            dregg_cell::compute_canonical_capability_root_8(&delegator.capabilities).limbs();
        assert_ne!(
            delegator_cap_root, actor_cap_root_8,
            "the bearer fixture must have distinct delegator/actor cap roots so the \
             authority-leg (holder) root genuinely differs from the EffectVm-seed (actor) root"
        );

        // The recipient (its `receive` is open).
        let recipient = Cell::with_balance([0x3Bu8; 32], [0u8; 32], 0);
        let recipient_id = recipient.id();

        let before_cell = bearer.clone();

        let mut ledger = Ledger::new();
        ledger.insert_cell(delegator).unwrap();
        ledger.insert_cell(bearer).unwrap();
        ledger.insert_cell(recipient).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let turn = make_bearer_transfer_turn(
            &delegator_sk,
            delegator_pk,
            bearer_pk,
            bearer_id,
            recipient_id,
        );
        let effects: Vec<dregg_turn::Effect> = turn
            .call_forest
            .total_effects()
            .into_iter()
            .cloned()
            .collect();
        let receipt = match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { receipt, .. } => receipt,
            other => panic!("bearer-delegated turn must commit, got {other:?}"),
        };
        let after_cell = ledger
            .get(&bearer_id)
            .expect("bearer present after exec")
            .clone();
        (
            receipt,
            bearer_id,
            delegator_id,
            delegator_cap_root,
            actor_cap_root,
            actor_cap_root_8,
            effects,
            before_cell,
            after_cell,
        )
    }

    /// ROUTING: a bearer-delegated receipt is classified onto the BEARER
    /// authority path — `bearer_consumed_cap` finds the `holder != actor`
    /// witness, `actor_consumed_cap` does NOT, and `delegator_pre_state_cap_roots`
    /// snapshots the delegator's real pre-state root keyed by its id. This is the
    /// routing the commit path depends on to reach the (None, Some(..)) arm.
    #[test]
    fn routing_identifies_bearer_delegated_turn() {
        let (
            receipt,
            bearer_id,
            delegator_id,
            delegator_cap_root,
            _actor_root,
            _actor_root_8,
            _eff,
            _b,
            _a,
        ) = run_bearer_delegated_turn();

        // The actor holds no consumed cap of its own; the bearer witness is the
        // delegator's.
        assert!(
            actor_consumed_cap(&receipt.consumed_capabilities, &bearer_id).is_none(),
            "the actor (bearer) holds no actor-cap witness — must not route the actor cap path"
        );
        let bearer = bearer_consumed_cap(&receipt.consumed_capabilities, &bearer_id)
            .expect("a bearer-delegated turn carries a holder != actor consumed-cap witness");
        assert_eq!(
            bearer.holder, delegator_id,
            "the bearer witness's holder is the DELEGATOR cell"
        );
        assert_eq!(
            bearer.auth_path,
            dregg_turn::ConsumedCapAuthPath::BearerSignedDelegation,
            "the witness records the bearer signed-delegation surface"
        );
        // The witness's recorded cap_root is the delegator's pre-state root: the
        // node re-derives the SAME value from its authoritative pre-execution
        // ledger (never trusting the receipt).
        // FULL native 8-felt equality: lift the witness's `[u32; 8]` cap root
        // per-lane into the field and compare it to the delegator's 8-felt root.
        assert_eq!(
            bearer.cap_root.map(BabyBear::new),
            delegator_cap_root,
            "the witness opens against the delegator's pre-state capability root"
        );

        // The node-side capture (`delegator_pre_state_cap_roots`) re-derives the
        // delegator root from the forest + pre-state ledger and keys it by the
        // delegator's id — the value the commit path feeds the authority leg.
        let (delegator_sk, delegator_pk, bearer_pk) = bearer_keys();
        let mut delegator = Cell::with_balance(delegator_pk, [0u8; 32], 1_000);
        delegator.permissions = open_permissions();
        delegator
            .capabilities
            .grant(CellId::from_bytes([0x66u8; 32]), AuthRequired::None);
        delegator.capabilities.grant(bearer_id, AuthRequired::None);
        let mut ledger = Ledger::new();
        ledger.insert_cell(delegator).unwrap();
        let turn = make_bearer_transfer_turn(
            &delegator_sk,
            delegator_pk,
            bearer_pk,
            bearer_id,
            CellId::from_bytes([0x3Bu8; 32]),
        );
        let roots = delegator_pre_state_cap_roots(&turn.call_forest, &ledger);
        assert_eq!(
            roots.get(&delegator_id),
            Some(&delegator_cap_root),
            "the node-derived delegator pre-state cap root must match (keyed by the delegator id)"
        );
    }

    /// CONTROL (honest bearer turn ACCEPTS with the authority leg): a real
    /// bearer-delegated turn proves + verifies end-to-end through
    /// `prove_and_verify_finalized_turn_capability_holder`, the cap-membership
    /// (authority) leg bound to the DELEGATOR's pre-state cap root — which is
    /// DISTINCT from the actor's EffectVm-seed root. A light client re-deriving
    /// the expectation from the receipt witness + the delegator's canonical root
    /// accepts. This is the honest case the soundness gap's verifier MUST admit.
    #[test]
    fn honest_bearer_delegated_turn_proves_with_authority_leg() {
        let (
            receipt,
            bearer_id,
            _delegator_id,
            delegator_cap_root,
            actor_cap_root,
            actor_cap_root_8,
            effects,
            before_cell,
            after_cell,
        ) = run_bearer_delegated_turn();
        let consumed = bearer_consumed_cap(&receipt.consumed_capabilities, &bearer_id)
            .expect("bearer consumed-cap witness")
            .clone();

        // The two roots genuinely differ: the actor's EffectVm-seed root vs the
        // delegator's authority-leg root (compared on the FULL 8-felt digest).
        assert_ne!(
            actor_cap_root_8, delegator_cap_root,
            "the authority leg binds a DIFFERENT root than the actor's EffectVm seed"
        );

        // The actor (bearer) transfers FROM itself ⇒ a rotatable `Transfer{dir:1}`
        // projection. Build the actor's rotation witness from the REAL before/after
        // cells EXACTLY as the commit path's bearer arm does (`blocklace_sync.rs`),
        // so the actor leg proves ROTATED while the delegator-bound cap leg runs
        // alongside it.
        let receipts = [receipt.receipt_hash()];
        let rotation = rotation_witness_for_self_sovereign(
            1_000,
            0,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "the bearer self-transfer must yield an actor rotation witness (faithful real cell)"
        );

        let proven = prove_and_verify_finalized_turn_capability_holder(
            &bearer_id,
            1_000,              // actor pre-balance
            0,                  // actor pre-nonce
            actor_cap_root,     // EffectVm-seed root (the ACTOR's)
            delegator_cap_root, // authority-leg root (the DELEGATOR's)
            &effects,
            [0xB0u8; 32],
            &consumed,
            None,
            &[],
            rotation,
            Default::default(),
            None,
        )
        .expect("honest bearer-delegated turn must prove + authority-bound-verify");

        assert!(
            proven.proof.components.has_cap_membership,
            "the AUTHORITY (cap-membership) leg is attached for a bearer turn"
        );
        assert!(!proven.proof_bytes().is_empty());

        // Light-client re-verify: recompute the expectation from the receipt
        // witness + the DELEGATOR's canonical pre-state root → accepts.
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: delegator_cap_root,
        };
        verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        )
        .expect("light-client re-verify against the delegator's root must accept");
    }

    /// SOUNDNESS TOOTH (the gap closed): a bearer turn whose DELEGATOR did NOT
    /// actually hold the cap is REJECTED. The node binds the authority leg to
    /// the delegator's REAL pre-state cap root; if a fabricated delegator (one
    /// whose c-list never contained the cap) is supplied, the proof is refused
    /// — both at the prover gate (the witness's recorded `cap_root` is not that
    /// cell's canonical root) AND at the verifier (an honest proof re-verified
    /// against the wrong holder root fails `CapRootMismatch`). This is the
    /// invalid case the soundness gap's verifier MUST reject; before the fix the
    /// authority leg was never bound, so such a turn slipped through with only
    /// the membership leg "proven."
    #[test]
    fn bearer_turn_whose_delegator_lacked_the_cap_is_rejected() {
        let (
            receipt,
            bearer_id,
            _delegator_id,
            delegator_cap_root,
            actor_cap_root,
            _actor_cap_root_8,
            effects,
            before_cell,
            after_cell,
        ) = run_bearer_delegated_turn();
        let consumed = bearer_consumed_cap(&receipt.consumed_capabilities, &bearer_id)
            .expect("bearer consumed-cap witness")
            .clone();
        let receipts = [receipt.receipt_hash()];
        let rotation = || {
            rotation_witness_for_self_sovereign(
                1_000,
                0,
                &before_cell,
                &after_cell,
                &receipts,
                &effects,
            )
        };

        // A would-be delegator that NEVER held the cap: a cell with a different
        // c-list ⇒ a different canonical root. (This is what the node would
        // derive for a forged `holder` that lacked the authority — or, in the
        // commit path, the empty root for an absent delegator.) The FULL native
        // 8-felt root the (impostor) holder leg would bind against.
        let mut impostor = Cell::with_balance([0x12u8; 32], [0u8; 32], 0);
        impostor
            .capabilities
            .grant(CellId::from_bytes([0x34u8; 32]), AuthRequired::None);
        let impostor_root =
            dregg_cell::compute_canonical_capability_root_8(&impostor.capabilities).limbs();
        assert_ne!(
            impostor_root, delegator_cap_root,
            "the impostor delegator's root must differ from the real delegator's"
        );

        // (a) PROVER refuses: the bearer witness's recorded cap_root is the REAL
        // delegator's root, which does not equal the impostor's node-derived
        // holder root → `ConsumedCapWitnessInvalid` (the cap was NOT a member of
        // this holder's authoritative pre-state c-list). The refusal fires before
        // the rotated leg is built, even WITH a rotation witness in hand.
        let result = prove_and_verify_finalized_turn_capability_holder(
            &bearer_id,
            1_000,
            0,
            actor_cap_root,
            impostor_root, // the holder root the cap did NOT belong to
            &effects,
            [0xB1u8; 32],
            &consumed,
            None,
            &[],
            rotation(),
            Default::default(),
            None,
        );
        assert!(
            matches!(
                result,
                Err(FullTurnProvingError::ConsumedCapWitnessInvalid { .. })
            ),
            "SOUNDNESS (BEARER AUTHORITY): a bearer turn bound to a holder root the cap was \
             never a member of must be REFUSED, got {result:?}"
        );

        // (b) VERIFIER rejects: prove the honest turn ROTATED (bound to the REAL
        // delegator root), then re-verify against the impostor's root — the
        // cap leg's in-circuit-bound root mismatches → `CapRootMismatch`. A
        // bearer proof for the delegator's tree cannot be replayed as authority
        // from a different (impostor) cell.
        let proven = prove_and_verify_finalized_turn_capability_holder(
            &bearer_id,
            1_000,
            0,
            actor_cap_root,
            delegator_cap_root,
            &effects,
            [0xB2u8; 32],
            &consumed,
            None,
            &[],
            rotation(),
            Default::default(),
            None,
        )
        .expect("honest bearer proof (bound to the real delegator root)");
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: impostor_root,
        };
        match verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        ) {
            Err(FullTurnVerifyError::CapRootMismatch { expected, got }) => {
                assert_eq!(expected, impostor_root);
                assert_eq!(got, delegator_cap_root);
            }
            Ok(()) => panic!(
                "SOUNDNESS (BEARER AUTHORITY): a bearer authority proof for the delegator's tree \
                 was ACCEPTED against a DIFFERENT (impostor) holder root — the delegated-authority \
                 splicing hole is OPEN!"
            ),
            Err(other) => panic!("expected CapRootMismatch, got {other:?}"),
        }
    }

    /// THE FEATURE (#225 cross-vat close): an HONEST CROSS-VAT cap-gated transfer —
    /// the actor `A` (cap holder) is DISTINCT from the cap's TARGET `src` cell `B`,
    /// and the published recipient `dst` is a third cell — proves + verifies
    /// end-to-end through the live node holder path, and the proof PUBLISHES the
    /// GENUINE `(actor, src, dst)` turn identity on PIs 38/39/40 with `actor != src`.
    ///
    /// Before the fix the node site forced `cap_turn_identity: None`, so the
    /// cap-open prover defaulted to the OWNER arm (`actor = dst = src = leaf.target`)
    /// — a genuine cross-vat transfer could NOT publish its real actor/dst. This
    /// test drives a `consumed` witness whose `leaf.target` is `B` (distinct from the
    /// actor `A`), confirms the node derives `actor = fold(A)`, `src = fold(B) =
    /// leaf.target`, `dst = fold(recipient)`, welds them into the TB cap-open PIs,
    /// and that the composed proof verifies. The convention: the single-felt cell
    /// projection is `cap_root::fold_bytes32(cell_id.as_bytes())` (the SAME fold the
    /// cap-leaf `target` uses — `cell/src/commitment.rs:506` — so `src` byte-matches
    /// what `verify_vm_descriptor2` anchors on the deployment side).
    #[test]
    fn honest_cross_vat_cap_gated_transfer_publishes_genuine_identity() {
        use dregg_circuit::cap_root::{CAP_TREE_DEPTH, CanonicalCapTree, fold_bytes32};
        use dregg_circuit::effect_vm::trace_rotated::{
            CAP_OPEN_TB_PI_ACTOR, CAP_OPEN_TB_PI_DST, CAP_OPEN_TB_PI_SRC,
        };

        // The actor (cap HOLDER) `A` and the cap's TARGET `src` cell `B` are DISTINCT
        // — this is the cross-vat shape (A spends a cap over B). We reuse the bearer
        // fixture's REAL actor before/after cells + rotation for the (independent)
        // state-transition leg; only the AUTHORITY (cap-membership) leg + the
        // published identity are cross-vat.
        let (
            receipt,
            actor_id, // `A` — the actor / cap holder (the bearer cell)
            _delegator_id,
            _delegator_cap_root,
            actor_cap_root, // EffectVm-seed root (the ACTOR's)
            _actor_cap_root_8,
            effects,
            before_cell,
            after_cell,
        ) = run_bearer_delegated_turn();

        // The recipient (`dst`) the turn's Transfer effect names.
        let dst_id = match effects.iter().find_map(|e| match e {
            dregg_turn::Effect::Transfer { to, .. } => Some(*to),
            _ => None,
        }) {
            Some(to) => to,
            None => panic!("bearer fixture must carry a Transfer effect"),
        };

        // `B` — the cap's TARGET cell, DISTINCT from the actor `A` and the recipient.
        let src_cell = CellId::from_bytes([0xB2u8; 32]);
        assert_ne!(
            src_cell, actor_id,
            "cross-vat: the cap target B != the actor A"
        );

        // The cap HOLDER cell's c-list: a cap whose TARGET is `B` (so `leaf.target =
        // fold(B)`), permitting Transfer, plus a decoy so the consumed cap is not the
        // sole leaf. We build the consumed witness directly against this holder tree
        // (the same shape `record_consumed_cap_witness` records), so the authority
        // leg opens to the holder's real root.
        let mut holder = Cell::with_balance([0xC4u8; 32], [0u8; 32], 1_000);
        holder.permissions = open_permissions();
        holder
            .capabilities
            .grant(CellId::from_bytes([0x12u8; 32]), AuthRequired::None); // decoy
        let slot = holder
            .capabilities
            .grant(src_cell, AuthRequired::None)
            .expect("grant cross-vat cap over B");
        // Transfer-permitting mask (so the cap-open submask check admits the Transfer
        // effect-kind bit; the cap genuinely confers the moved effect).
        holder
            .capabilities
            .iter_mut()
            .find(|c| c.slot == slot)
            .expect("granted cap present")
            .allowed_effects = Some(dregg_cell::facet::EFFECT_TRANSFER);
        let holder_cap_root =
            dregg_cell::compute_canonical_capability_root_8(&holder.capabilities).limbs();

        // Build the consumed-cap membership witness for the B-targeting leaf against
        // the holder's canonical tree (mirrors `record_consumed_cap_witness`).
        let consumed_leaf = dregg_cell::cap_ref_to_leaf(
            holder
                .capabilities
                .iter()
                .find(|c| c.slot == slot)
                .expect("granted cap present"),
        );
        assert_eq!(
            consumed_leaf.target,
            fold_bytes32(src_cell.as_bytes()),
            "the cap-leaf target IS fold_bytes32(B) — the convention the published `src` must match"
        );
        let leaves: Vec<_> = holder
            .capabilities
            .iter()
            .map(dregg_cell::cap_ref_to_leaf)
            .collect();
        let tree = CanonicalCapTree::new(leaves, CAP_TREE_DEPTH);
        let pos = tree
            .position_of(consumed_leaf.slot_hash)
            .expect("consumed leaf present in holder tree");
        let (siblings, directions) = tree.prove_membership(pos).expect("membership path");
        let consumed = dregg_turn::ConsumedCapWitness {
            holder: holder.id(),
            slot,
            action_path: vec![0],
            auth_path: dregg_turn::ConsumedCapAuthPath::BearerSignedDelegation,
            leaf_slot_hash: consumed_leaf.slot_hash.as_u32(),
            leaf_target: consumed_leaf.target.as_u32(),
            leaf_auth_tag: consumed_leaf.auth_tag.as_u32(),
            leaf_mask_lo: consumed_leaf.mask_lo.as_u32(),
            leaf_mask_hi: consumed_leaf.mask_hi.as_u32(),
            leaf_expiry: consumed_leaf.expiry.as_u32(),
            leaf_breadstuff: consumed_leaf.breadstuff.as_u32(),
            // FULL native 8-felt per-lane encoding (NOT a lane-0 squeeze): each
            // sibling digest and the tree root carry all 8 lanes into the witness.
            siblings: siblings
                .into_iter()
                .map(|s| s.map(|f| f.as_u32()))
                .collect(),
            directions,
            cap_root: tree.root().map(|f| f.as_u32()),
        };
        assert!(
            consumed.verify(),
            "the cross-vat consumed witness recomputes its own root"
        );

        // The actor's REAL rotation witness (the independent state-transition leg).
        let receipts = [receipt.receipt_hash()];
        let rotation = rotation_witness_for_self_sovereign(
            1_000,
            0,
            &before_cell,
            &after_cell,
            &receipts,
            &effects,
        );
        assert!(
            rotation.is_some(),
            "the actor self-transfer must yield a rotation witness (faithful real cell)"
        );

        // The expected GENUINE identity felts (what the node site now derives).
        let exp_actor = fold_bytes32(actor_id.as_bytes());
        let exp_src = BabyBear::new(consumed.leaf_target); // == fold_bytes32(B)
        let exp_dst = fold_bytes32(dst_id.as_bytes());
        assert_ne!(
            exp_actor, exp_src,
            "CROSS-VAT: the actor felt MUST differ from the src (cap-target) felt"
        );

        // PROVE + VERIFY through the live holder path (the actor's EffectVm-seed root
        // is the actor's; the authority leg opens against the holder's distinct root).
        let proven = prove_and_verify_finalized_turn_capability_holder(
            &actor_id,
            1_000,
            0,
            actor_cap_root,
            holder_cap_root,
            &effects,
            [0xC5u8; 32],
            &consumed,
            None,
            &[],
            rotation,
            Default::default(),
            None,
        )
        .expect("honest cross-vat cap-gated transfer must prove + authority-bound-verify");
        assert!(
            proven.proof.components.has_cap_membership,
            "the AUTHORITY (cap-membership) leg is attached for the cross-vat turn"
        );

        // The proof PUBLISHES the genuine cross-vat identity on the TB cap-open leg's
        // PIs 38/39/40 — `actor != src`, exactly the felts the node derived.
        let rotated_leg = proven
            .proof
            .composed
            .sub_proofs
            .iter()
            .find(|p| p.label == "effect-vm-rotated")
            .expect("the rotated effect-vm leg is present");
        assert!(
            rotated_leg.sub_public_inputs.len() > CAP_OPEN_TB_PI_DST,
            "the TB cap-open leg publishes the three turn-identity PIs (38/39/40)"
        );
        assert_eq!(
            rotated_leg.sub_public_inputs[CAP_OPEN_TB_PI_SRC], exp_src,
            "published src == leaf.target (fold_bytes32(B))"
        );
        assert_eq!(
            rotated_leg.sub_public_inputs[CAP_OPEN_TB_PI_ACTOR], exp_actor,
            "published actor == fold_bytes32(A) — the GENUINE cross-vat actor"
        );
        assert_eq!(
            rotated_leg.sub_public_inputs[CAP_OPEN_TB_PI_DST], exp_dst,
            "published dst == fold_bytes32(recipient)"
        );
        assert_ne!(
            rotated_leg.sub_public_inputs[CAP_OPEN_TB_PI_ACTOR],
            rotated_leg.sub_public_inputs[CAP_OPEN_TB_PI_SRC],
            "CROSS-VAT PUBLISHED: actor != src on the live proof (the feature — before the fix this \
             was forced equal by the owner-arm `None` default)"
        );

        // Light-client re-verify against the holder's root accepts.
        let expectation = dregg_sdk::CapMembershipExpectation {
            leaf: consumed.cap_leaf(),
            cap_root: holder_cap_root,
        };
        verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            None,
            Some(&expectation),
        )
        .expect("light-client re-verify of the cross-vat proof must accept");
    }

    /// DOMAIN-2 SOURCING: `caps_umem_weld_witness` builds a CAPS-domain weld witness from a c-list
    /// change (the shape the deployed cap path threads to the welded cap-open producer), and REFUSES
    /// (returns `None`) a non-caps (balance / heap) change or a no-op — so the deployed path only
    /// welds when the genuine actor projection diff is a caps reconciliation.
    #[test]
    fn caps_umem_weld_witness_sources_caps_diff_only() {
        let mut before = Cell::with_balance([0x5Au8; 32], [0u8; 32], 1_000);
        before.permissions = open_permissions();

        // (a) A CAPS change (grant a slot) ⇒ Some witness whose ops are all CAPS-domain.
        let mut after_caps = before.clone();
        after_caps
            .capabilities
            .grant(CellId::from_bytes([0x99u8; 32]), AuthRequired::None);
        let w = caps_umem_weld_witness(&before, &after_caps)
            .expect("a c-list change yields a CAPS-domain weld witness");
        assert!(
            !w.ops.is_empty()
                && w.ops
                    .iter()
                    .all(|op| op.key.domain() == dregg_turn::umem::UDomain::Caps),
            "the sourced witness reconciles the CAPS domain only"
        );

        // (b) A NO-OP (identical cells) ⇒ None (empty diff, nothing to weld).
        assert!(
            caps_umem_weld_witness(&before, &before).is_none(),
            "an empty actor projection diff yields no weld witness (stays bare)"
        );

        // (c) A BALANCE change (heap domain, NOT caps) ⇒ None — a value move is not a cap-open weld.
        let mut after_bal = before.clone();
        after_bal.state.set_balance(900);
        assert!(
            caps_umem_weld_witness(&before, &after_bal).is_none(),
            "a heap-domain (balance) change is refused — the cap-open weld reconciles CAPS only"
        );
    }
}
