//! End-to-end shielded transfer through the REAL executor (privacy M2-a).
//!
//! Moved here from `turn/src/executor/apply.rs` by PR2 of the turn-prover
//! extraction. Two things changed and both are improvements:
//!
//! 1. It now drives the executor's **public `execute()`** entry, not the
//!    `pub(crate)` `apply_effect` — because `LedgerJournal` deliberately stayed
//!    `pub(crate)`. So this is a whole authenticated turn, not an effect poke.
//! 2. The verifier is **injected** (`CircuitShieldedTransferVerifier`) rather than
//!    linked by `#[cfg(feature = "prover")]`. The uninjected case is its own
//!    canary in `shielded_fail_closed.rs`.
//!
//! The bar is unchanged: a `ShieldedTransfer` effect is ADMITTED when (and only
//! when) its hidden STARK side, its Pedersen conservation+range side, and the
//! nullifier gate all pass — and is REJECTED on a forged proof, a non-conserving
//! value set, or a re-presented (double-spent) nullifier. Not a stub: each
//! rejection is the genuine refusal from the real `dregg-circuit-prove` verifier /
//! `dregg-cell-crypto` conservation verifier / `NullifierSet::insert`.

use std::sync::Arc;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions, ShieldedNoteCommitment};
use dregg_cell_crypto::value_commitment::{
    BulletproofRangeProof, ValueCommitment, ValueCommitmentBytes, prove_conservation,
    scalar_from_blinding_bytes,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, ShieldedSpendWitness, ShieldedTransfer, ShieldedTransferWitness,
    ShieldedValueLeg, WideValueBindingProof, WideValueBindingWitness, prove_wide_value_binding,
    wide_transfer_message,
};
use dregg_turn::action::{ShieldedInputPayload, ShieldedLeg, ShieldedTransferPayload};
use dregg_turn::executor::shielded_nullifier_key;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnError,
    TurnExecutor,
    turn::{Turn, TurnResult},
};
use dregg_turn_prover::CircuitShieldedTransferVerifier;

const ASSET: u64 = 1;

// ── executor / turn plumbing (public API only) ───────────────────────────────

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

/// An executor with the REAL shielded verifier injected — the production wiring
/// a node performs at startup.
fn shielded_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
        .with_shielded_transfer_verifier(Arc::new(CircuitShieldedTransferVerifier::new()))
}

fn actor_cell() -> (CellId, Cell) {
    let mut pk = [0u8; 32];
    pk[0] = 0x5A;
    pk[31] = 0xA5;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    (cell.id(), cell)
}

fn shielded_turn(
    agent: CellId,
    previous_receipt_hash: Option<[u8; 32]>,
    payload: ShieldedTransferPayload,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::ShieldedTransfer { payload }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
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

/// Drive one shielded transfer through the whole public turn path.
/// `Ok(())` = committed; `Err(reason)` = the executor's genuine refusal text.
///
/// Each call gets a FRESH ledger (so nonce 0 is always correct), while the
/// EXECUTOR is reused across calls — that is the point: the nullifier set and the
/// shielded accumulator are executor state, so cross-turn double-spend is still
/// exercised without the ledger nonce getting in the way.
fn run(executor: &TurnExecutor, payload: ShieldedTransferPayload) -> Result<(), TurnError> {
    run_chained(executor, payload, None).map(|_| ())
}

/// As [`run`], but threads the executor's receipt chain so a SECOND turn on the
/// same executor is accepted by the chain gate. Returns the committed receipt
/// hash to chain onward.
fn run_chained(
    executor: &TurnExecutor,
    payload: ShieldedTransferPayload,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Result<[u8; 32], TurnError> {
    let (agent, cell) = actor_cell();
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell);
    match executor.execute(
        &shielded_turn(agent, previous_receipt_hash, payload),
        &mut ledger,
    ) {
        TurnResult::Committed { receipt, .. } => Ok(receipt.receipt_hash()),
        TurnResult::Rejected { reason, .. } => Err(reason),
        other => panic!("unexpected turn result: {other:?}"),
    }
}

fn refusal_reason(error: TurnError) -> String {
    match error {
        TurnError::InvalidEffect { reason } => reason,
        other => panic!("expected InvalidEffect, got {other:?}"),
    }
}

// ── shielded witness / payload construction (the real prover) ────────────────

fn range_proof_bytes(value: u64, blinding: &[u8; 32]) -> Vec<u8> {
    BulletproofRangeProof::prove_range(value, &scalar_from_blinding_bytes(blinding)).proof_bytes
}

fn wide_binding(input: &ShieldedTransferWitness, full_value: u64) -> WideValueBindingProof {
    let binding_blind: [BabyBear; BINDING_BLIND_LANES] =
        core::array::from_fn(|i| input.spend.randomness + BabyBear::new(0x100 + i as u32));
    prove_wide_value_binding(&WideValueBindingWitness {
        value: full_value,
        asset_type: input.leg.asset_type,
        legacy_randomness: input.spend.randomness,
        binding_blind,
    })
    .expect("prove mandatory native-wide input binding")
}

/// A shielded-spend witness with a genuine Poseidon2 Merkle path + its leg.
fn make_input(
    leaf_seed: u32,
    amount: u32,
    blinding: [u8; 32],
    key_seed: u32,
    depth: usize,
) -> ShieldedTransferWitness {
    let key = [
        BabyBear::new(key_seed),
        BabyBear::new(key_seed.wrapping_add(1)),
        BabyBear::new(key_seed.wrapping_add(2)),
        BabyBear::new(key_seed.wrapping_add(3)),
    ];
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        positions.push((i % 4) as u8);
        siblings.push([
            BabyBear::new((i as u32) * 7 + 1 + leaf_seed),
            BabyBear::new((i as u32) * 7 + 2 + leaf_seed),
            BabyBear::new((i as u32) * 7 + 3 + leaf_seed),
        ]);
    }
    let spend = ShieldedSpendWitness {
        value: BabyBear::new(amount),
        asset_type: BabyBear::new(ASSET as u32),
        owner: BabyBear::new(0x5EED ^ leaf_seed),
        randomness: BabyBear::new(0xC0FFEE ^ key_seed),
        key,
        siblings,
        positions,
    };
    let commitment = ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&blinding));
    ShieldedTransferWitness {
        spend,
        leg: ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: commitment.to_bytes().0,
        },
    }
}

/// Serialize a built circuit `ShieldedTransfer` + its conservation proof into
/// the executor wire payload — exactly what a client would post.
fn to_payload(
    transfer: &ShieldedTransfer,
    wide_bindings: &[WideValueBindingProof],
    conservation: dregg_cell_crypto::ConservationProof,
) -> ShieldedTransferPayload {
    assert_eq!(transfer.inputs.len(), wide_bindings.len());
    let leg = |l: &ShieldedValueLeg| ShieldedLeg {
        asset_type: l.asset_type,
        commitment_bytes: l.commitment_bytes,
    };
    ShieldedTransferPayload {
        merkle_root: transfer.merkle_root.as_u32(),
        inputs: transfer
            .inputs
            .iter()
            .zip(wide_bindings)
            .map(|(ip, wide)| ShieldedInputPayload {
                nullifier: ip.nullifier.as_u32(),
                legacy_value_binding: ip.value_binding.as_u32(),
                wide_value_binding: wide.claim.wide_binding.map(BabyBear::as_u32),
                spend_proof: ip.proof_bytes(),
                wide_value_proof: wide.proof_bytes(),
            })
            .collect(),
        input_legs: transfer.input_legs.iter().map(leg).collect(),
        output_legs: transfer.output_legs.iter().map(leg).collect(),
        output_range_proofs: transfer.output_range_proofs.clone(),
        conservation,
    }
}

/// A balanced one-in/one-out shielded transfer + the matching payload.
pub fn balanced_payload(leaf_seed: u32, key_seed: u32) -> ShieldedTransferPayload {
    let amount = 1_000_000u32;
    // Independent per-note blinding (derived from the seeds): the source of
    // value-commitment unlinkability — equal amounts still commit distinctly.
    let mut in_blinding = [3u8; 32];
    let mut out_blinding = [7u8; 32];
    in_blinding[..4].copy_from_slice(&leaf_seed.to_le_bytes());
    out_blinding[..4].copy_from_slice(&key_seed.to_le_bytes());
    let w = make_input(leaf_seed, amount, in_blinding, key_seed, 4);
    let wide = wide_binding(&w, amount as u64);
    let merkle_root = w.spend.merkle_root();
    let in_c = ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&in_blinding));
    let out_c = ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&out_blinding));
    let output_legs = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: out_c.to_bytes().0,
    }];
    let output_range_proofs = vec![range_proof_bytes(amount as u64, &out_blinding)];
    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        merkle_root,
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("prove balanced shielded transfer");
    let excess =
        scalar_from_blinding_bytes(&in_blinding) - scalar_from_blinding_bytes(&out_blinding);
    let msg = wide_transfer_message(&transfer, core::slice::from_ref(&wide))
        .expect("build native-wide conservation transcript");
    let conservation = prove_conservation(&[in_c], &[out_c], &excess, &msg);
    to_payload(&transfer, &[wide], conservation)
}

// ── ACCEPT: a balanced, in-range, well-formed shielded transfer is admitted,
//    and its nullifier is now spent in the production set. ──
#[test]
fn valid_shielded_transfer_is_admitted_and_spends_its_nullifier() {
    let executor = shielded_executor();
    let payload = balanced_payload(11, 0xABCD);
    let nf = shielded_nullifier_key(payload.inputs[0].nullifier);
    assert!(!executor.note_nullifiers.lock().unwrap().contains(&nf));
    run(&executor, payload).expect("a valid shielded transfer must be admitted");
    assert!(
        executor.note_nullifiers.lock().unwrap().contains(&nf),
        "the shielded input's nullifier is now spent in the production set"
    );
}

// ── ⚑ THE ON-RAMP FALSIFIER (docs/DESIGN-shielded-value-on-ramp.md §3.3) ──
//
// GATE 4 appends the output leg's bytes VERBATIM FROM THE WIRE, so the
// `note_shielded` accumulator — and therefore its `root8()` — is written by
// the PROVER, not derived from ledger state. What lands decodes as a
// Ristretto `ValueCommitment`: a Pedersen VALUE commitment, not the
// Poseidon2 NOTE commitment `hash_fact(value,[asset,owner,randomness])`
// that the shielded-spend membership gadget opens (and the transfer
// publishes no such note commitment anywhere — the wire has no field for it,
// `action.rs` `ShieldedLeg`).
//
// The consequence, and why this test is armed: `AccumulatorSound` for
// `note_shielded.root8()` — the `NoteAccumulatorCR` hypothesis of
// `ShieldedSpendPortDischarge.pin_accept_is_note_committed`
// (metatheory/Dregg2/Circuit/ShieldedSpendPortDischarge.lean:174,182) — is
// FALSE as this set is populated today. That is harmless ONLY because
// `root8()` is committed nowhere. Landing it as a carrier base limb (L1) or
// pinning membership to it (L4) before the value on-ramp corrects the
// appended leaf RELOCATES seam #15 one level up instead of closing it.
//
// PR2 NOTE: the verify-returns-value refactor did NOT change this. The prover
// still chooses the appended bytes; it now returns them instead of writing them.
// The core executor performs (and journals) the append. Who WRITES moved; what
// is written did not.
//
// When the on-ramp lands (L0.5: the wire carries a Poseidon2 note
// commitment and GATE 4 appends THAT), this test must be rewritten. The
// rewrite is the tripwire.
#[test]
fn shielded_append_is_prover_written_not_ledger_derived() {
    let executor = shielded_executor();
    let payload = balanced_payload(41, 0x4141);
    let leg_bytes = payload.output_legs[0].commitment_bytes;
    let leg_count = payload.output_legs.len();

    let empty_root = {
        let set = executor.note_shielded.lock().unwrap();
        assert!(set.is_empty(), "the shielded accumulator starts EMPTY");
        set.root8()
    };

    run(&executor, payload).expect("a valid shielded transfer must be admitted");

    let set = executor.note_shielded.lock().unwrap();
    assert!(
        set.contains(&ShieldedNoteCommitment(leg_bytes)),
        "GATE 4 appends the PROVER-SUPPLIED wire bytes verbatim — the \
         accumulator's contents are chosen by the prover, not derived from \
         ledger state"
    );
    assert_eq!(
        set.len(),
        leg_count,
        "nothing but the wire legs lands in the accumulator: there is no \
         ledger-derived note commitment to append"
    );
    assert_ne!(
        set.root8(),
        empty_root,
        "root8() therefore moves to a PROVER-DETERMINED value — this is \
         exactly why it must not become a committed carrier limb (L1) or a \
         membership pin (L4) before the on-ramp"
    );
    assert!(
        ValueCommitment::from_bytes(&ValueCommitmentBytes(leg_bytes)).is_some(),
        "what landed is a PEDERSEN VALUE commitment (a valid Ristretto \
         point), not the Poseidon2 NOTE commitment \
         hash_fact(value,[asset,owner,randomness]) the membership gadget \
         opens — the two encodings are disjoint, so no spend proof could \
         ever open against this accumulator"
    );
}

// ── WIDE CUTOVER TOOTH: x and x+p have the same legacy spend binding,
//    but distinct native carriers. The genuine x payload is admitted; an
//    x+p carrier spliced over its no-mint transcript is refused at the real
//    executor entry. This establishes that all sixteen lanes are live in
//    Turn acceptance. It does not claim the legacy note leaf precommits
//    which of two aliased openings was originally created.
#[test]
fn modulus_alias_splice_rejects_at_real_executor_no_mint_entry() {
    let leaf_seed = 31;
    let key_seed = 0x3131;
    let amount = 1_000_000u32;
    let honest_payload = balanced_payload(leaf_seed, key_seed);

    let honest_executor = shielded_executor();
    run(&honest_executor, honest_payload.clone())
        .expect("the full-width x carrier must be admitted");

    // Recreate the same spend witness and prove the distinct full-u64
    // opening x+p. Its compatibility felt is identical by construction.
    let mut in_blinding = [3u8; 32];
    in_blinding[..4].copy_from_slice(&leaf_seed.to_le_bytes());
    let input = make_input(leaf_seed, amount, in_blinding, key_seed, 4);
    let alias = wide_binding(&input, amount as u64 + BABYBEAR_P as u64);
    assert_eq!(
        alias.claim.legacy_binding.as_u32(),
        honest_payload.inputs[0].legacy_value_binding,
        "x and x+p must exercise the real old one-felt alias"
    );
    assert_ne!(
        alias.claim.wide_binding.map(BabyBear::as_u32),
        honest_payload.inputs[0].wide_value_binding,
        "the native carrier must distinguish x from x+p"
    );

    let mut alias_payload = honest_payload;
    alias_payload.inputs[0].wide_value_binding = alias.claim.wide_binding.map(BabyBear::as_u32);
    alias_payload.inputs[0].wide_value_proof = alias.proof_bytes();
    let alias_executor = shielded_executor();
    let reason = refusal_reason(
        run(&alias_executor, alias_payload)
            .expect_err("an x+p carrier spliced over x's no-mint transcript must reject"),
    );
    assert!(
        reason.contains("conservation") || reason.contains("range"),
        "wide splice must reach and fail the live no-mint verifier: {reason}"
    );
    assert!(alias_executor.note_nullifiers.lock().unwrap().is_empty());
}

#[test]
fn noncanonical_wide_public_lane_rejects_at_executor_entry() {
    let executor = shielded_executor();
    let mut payload = balanced_payload(32, 0x3232);
    payload.inputs[0].wide_value_binding[0] = BABYBEAR_P;
    let reason = refusal_reason(
        run(&executor, payload).expect_err("a noncanonical wide field encoding must reject"),
    );
    assert!(
        reason.contains("not canonical BabyBear"),
        "wide decoder refusal must be explicit: {reason}"
    );
}

// ── REJECT (forged membership): a tampered merkle_root breaks the hidden
//    STARK side — no fake membership. ──
#[test]
fn forged_membership_root_rejects() {
    let executor = shielded_executor();
    let mut payload = balanced_payload(12, 0xBEEF);
    payload.merkle_root = payload.merkle_root.wrapping_add(1);
    let reason = refusal_reason(run(&executor, payload).expect_err("forged root must reject"));
    assert!(reason.contains("STARK"), "got: {reason}");
}

// ── REJECT (no double-spend): the SAME shielded transfer presented twice is
//    refused by the nullifier gate — the genuine double-spend refusal. ──
#[test]
fn double_spent_shielded_nullifier_rejects() {
    let executor = shielded_executor();
    let payload = balanced_payload(13, 0xF00D);
    let first =
        run_chained(&executor, payload.clone(), None).expect("first shielded transfer admitted");
    let reason = refusal_reason(
        run_chained(&executor, payload, Some(first)).expect_err("second presentation must reject"),
    );
    assert!(
        reason.contains("double-spend"),
        "rejection must be the double-spend refusal, got: {reason}"
    );
}

// ── REJECT (non-conserving): an output committing to MORE than the input
//    (hidden inflation) fails the Pedersen conservation gate — even though the
//    STARK membership is genuine. Σδ ≠ 0 ⇒ refused. ──
#[test]
fn inflating_shielded_transfer_rejects_on_conservation() {
    let executor = shielded_executor();
    let amount = 1_000_000u32;
    let inflated = 2_000_000u64;
    let in_blinding = [3u8; 32];
    let out_blinding = [7u8; 32];
    let w = make_input(14, amount, in_blinding, 0x1234, 4);
    let wide = wide_binding(&w, amount as u64);
    let merkle_root = w.spend.merkle_root();
    let in_c = ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&in_blinding));
    // The output leg commits to the INFLATED value (a real, in-range value, so
    // its range proof is valid) — only conservation can catch this.
    let out_c = ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&out_blinding));
    let output_legs = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: out_c.to_bytes().0,
    }];
    let output_range_proofs = vec![range_proof_bytes(inflated, &out_blinding)];
    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        merkle_root,
        &[w],
        output_legs,
        output_range_proofs,
    )
    .expect("STARK builds even for an inflating transfer (caught at conservation)");
    // The prover still uses the blinding excess; the value imbalance makes the
    // excess carry a V-component, so the Schnorr-on-R proof cannot answer.
    let excess =
        scalar_from_blinding_bytes(&in_blinding) - scalar_from_blinding_bytes(&out_blinding);
    let msg = wide_transfer_message(&transfer, core::slice::from_ref(&wide))
        .expect("build native-wide conservation transcript");
    let conservation = prove_conservation(&[in_c], &[out_c], &excess, &msg);
    let payload = to_payload(&transfer, &[wide], conservation);
    let reason = refusal_reason(
        run(&executor, payload).expect_err("an inflating shielded transfer must reject"),
    );
    assert!(
        reason.contains("conservation") || reason.contains("range"),
        "rejection must be the value-conservation gate, got: {reason}"
    );
    // Nothing was spent — the transfer was refused before the nullifier gate
    // could record (the conservation gate precedes the spend).
    assert!(executor.note_nullifiers.lock().unwrap().is_empty());
}

// ── UNLINKABILITY: two independent shielded transfers of the SAME amount
//    produce DIFFERENT nullifiers / commitments / proofs — an observer cannot
//    link sender to receiver by the on-wire payload. ──
#[test]
fn distinct_transfers_are_unlinkable_on_the_wire() {
    let a = balanced_payload(21, 0x1111);
    let b = balanced_payload(22, 0x2222);
    assert_ne!(
        a.inputs[0].nullifier, b.inputs[0].nullifier,
        "distinct shielded inputs must reveal distinct nullifiers"
    );
    assert_ne!(
        a.output_legs[0].commitment_bytes, b.output_legs[0].commitment_bytes,
        "equal amounts must still commit to distinct (blinded) value commitments"
    );
    assert_ne!(
        a.inputs[0].spend_proof, b.inputs[0].spend_proof,
        "the hidden proofs reveal nothing linking the two transfers"
    );
    assert_ne!(
        a.inputs[0].wide_value_binding, b.inputs[0].wide_value_binding,
        "the native wide carriers retain fresh hidden blinding"
    );
}

// ── ⚑ FAIL-CLOSED CANARY (shielded transfer) ────────────────────────────────
//
// The ONE payload that the injected executor ADMITS is REFUSED by an executor
// with no verifier injected — and refused with a reason that names the missing
// verifier, so a verify-only deployment is never mistaken for a bad proof. This
// is the property the deleted `#[cfg(not(feature = "prover"))]` stub carried;
// it is now a runtime fact enforced by an `Option<Arc<dyn _>>` and a crate
// boundary, and the SAME executable checks both sides.
#[test]
fn uninjected_executor_refuses_the_very_transfer_the_injected_one_admits() {
    let payload = balanced_payload(51, 0x5151);

    // Same payload, verifier injected: ADMITTED.
    let injected = shielded_executor();
    run(&injected, payload.clone()).expect("the injected executor admits this transfer");
    assert_eq!(
        injected.note_shielded.lock().unwrap().len(),
        1,
        "the admitted transfer landed its output note"
    );

    // Same payload, NOTHING injected: REFUSED, and nothing landed.
    let bare = TurnExecutor::new(ComputronCosts::zero());
    let reason = refusal_reason(
        run(&bare, payload).expect_err("a verify-only executor must NOT admit a hidden transfer"),
    );
    assert!(
        reason.contains("injected shielded verifier"),
        "the refusal must name the MISSING VERIFIER, not masquerade as a proof failure: {reason}"
    );
    assert!(
        bare.note_nullifiers.lock().unwrap().is_empty(),
        "a fail-closed refusal spends nothing"
    );
    assert!(
        bare.note_shielded.lock().unwrap().is_empty(),
        "a fail-closed refusal appends nothing"
    );
}

// ── The seam's OTHER half: the trait never sees the journal. ────────────────
//
// `ShieldedTransferVerifier::verify` takes `&ShieldedTransferPayload` and returns
// `VerifiedShieldedTransfer` — no `&mut LedgerJournal`, no `&Ledger`, no
// `&TurnExecutor`. This test is the compile-time witness that the signature is
// verify-returns-VALUE, which is why `JournalEntry` could stay `pub(crate)`.
#[test]
fn the_verifier_trait_is_pure_verification_and_returns_the_state_to_land() {
    let payload = balanced_payload(61, 0x6161);
    let expected_commitment = ShieldedNoteCommitment(payload.output_legs[0].commitment_bytes);

    let verified = dregg_turn::ShieldedTransferVerifier::verify(
        &CircuitShieldedTransferVerifier::new(),
        &payload,
    )
    .expect("a balanced transfer verifies");

    assert_eq!(
        verified.nullifiers,
        vec![payload.inputs[0].nullifier],
        "the returned nullifiers are the ones the STARK proved"
    );
    assert_eq!(
        verified.output_commitments,
        vec![expected_commitment],
        "the returned commitments are what the core executor appends and journals"
    );
    // No ledger, no journal, no executor was involved above. The only way this
    // reaches state is through the core `apply` path.
}
