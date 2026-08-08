//! End-to-end shielded OFF-RAMP (`Effect::Deshield`) through the REAL executor, with the REAL
//! deshield verifier injected.
//!
//! **BOTH halves are genuine `dregg-circuit-prove` / Lean-emitted relations** — there is no stub
//! anywhere on this path. The spend is `dregg-shielded-spend-complete-fsi2::v1` under the
//! executor's live committed root; the value link is `dregg-shielded-deshield-value-link::v1`.
//!
//! ## What this file exists to pin
//!
//! Value could ENTER the shielded pool (`Effect::Shield`) and MOVE inside it
//! (`ShieldedTransfer`). It could never LEAVE. These are the two poles of the exit:
//!
//!   1. an honest Deshield SPENDS its shielded note (nullifier consumed, so it cannot leave
//!      twice), CREDITS the cleartext ledger exactly `v`, and commits;
//!   2. a Deshield that CREDITS MORE THAN IT SPENDS — a real, genuinely-proven value-link at
//!      `v' = 1_000_000` stapled to a genuine worth-`v` spend — is REFUSED, and credits NOTHING,
//!      spends NOTHING.

use std::sync::Arc;

use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, NoteCommitment, Nullifier, Permissions,
    ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32,
};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, ShieldedDeshield, ShieldedDeshieldLinkWitness, ShieldedDeshieldWitness,
    ShieldedSpendCompleteWitness, ShieldedSpendMembership, TREE_DEPTH, prove_shielded_deshield,
    prove_shielded_deshield_link, verify_shielded_deshield_link,
};
use dregg_turn::action::{Effect, ShieldedInputPayload};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, ProofVerifier, TurnError,
    TurnExecutor,
    turn::{Turn, TurnResult},
};
use dregg_turn_prover::CircuitDeshieldVerifier;

const ASSET: u64 = 1;
const VALUE: u64 = 500;
/// The decoy leaf, so the spent note is not the only member of the accumulator.
const DECOY: u32 = 0x0C0C_0001;

struct AcceptAllProofs;
impl ProofVerifier for AcceptAllProofs {
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        true
    }
}

fn blind() -> [BabyBear; BINDING_BLIND_LANES] {
    core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111))
}

/// A complete-spend witness over a committed `ShieldedNoteSet`, PLUS the leaves (in insertion
/// order) the executor's own accumulator must be primed with so its `root8()` is the root the
/// membership path folds to.
fn spend_and_leaves(
    value: u64,
    asset: u64,
    randomness: BabyBear,
) -> (ShieldedSpendCompleteWitness, Vec<ShieldedNoteCommitment>) {
    let probe = ShieldedSpendCompleteWitness {
        value,
        asset_type: asset,
        randomness,
        spending_key: [
            BabyBear::new(11),
            BabyBear::new(13),
            BabyBear::new(17),
            BabyBear::new(19),
        ],
        binding_blind: blind(),
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let decoy = ShieldedNoteCommitment(felt_to_bytes32(BabyBear::new(DECOY)));
    let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));
    let mut set = ShieldedNoteSet::new();
    set.insert(decoy).expect("decoy inserts");
    set.insert(commitment).expect("the spent note is committed");
    let path = set
        .membership_path(&commitment)
        .expect("the committed note has a membership path");
    (
        ShieldedSpendCompleteWitness {
            membership: ShieldedSpendMembership {
                positions: path.path.positions,
                siblings: path.path.siblings,
                next_addr: path.leaf.next_addr().wire(),
            },
            ..probe
        },
        vec![decoy, commitment],
    )
}

/// An executor with the REAL deshield verifier and its shielded accumulator primed with `leaves`,
/// in order — so `note_shielded.root8()` is the root the spend proof folds to.
fn offramp_executor(leaves: &[ShieldedNoteCommitment], inject: bool) -> TurnExecutor {
    let executor =
        TurnExecutor::with_proof_verifier(ComputronCosts::zero(), Box::new(AcceptAllProofs));
    let executor = if inject {
        executor.with_deshield_verifier(Arc::new(CircuitDeshieldVerifier::new()))
    } else {
        executor
    };
    {
        let mut set = executor.note_shielded.lock().unwrap();
        for leaf in leaves {
            set.insert(*leaf)
                .expect("priming the committed accumulator");
        }
    }
    executor
}

// ── executor / turn plumbing (public API only, mirrors shield_onramp.rs) ──

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

fn actor_cell() -> (CellId, Cell) {
    let mut pk = [0u8; 32];
    pk[0] = 0x5B;
    pk[31] = 0xB5;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    (cell.id(), cell)
}

fn deshield_turn(agent: CellId, effect: Effect) -> Turn {
    deshield_turn_chained(agent, effect, None)
}

/// A turn that continues the executor's receipt chain.
///
/// ⚑ This exists because the first draft did NOT have it, and the difference mattered. `run()`
/// builds a fresh `Ledger` each call, but the EXECUTOR's receipt chain persists across calls — so a
/// second turn with `previous_receipt_hash: None` is refused by `ReceiptChainMismatch` BEFORE any
/// effect is applied. The replay assertion below would then have been reading a refusal that had
/// nothing to do with the nullifier it claimed to be testing: a falsifier that had stopped
/// falsifying. It failed loudly instead of passing, which is the only reason this is a comment and
/// not a defect.
fn deshield_turn_chained(
    agent: CellId,
    effect: Effect,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        // Always 0: `run_chained` builds a FRESH `Ledger` per call, so the acting cell is new and
        // its nonce has not advanced. (The executor's receipt chain and nullifier set DO persist
        // across calls — which is the whole point of running the replay against the same
        // executor.) Passing 1 here reads as "the second turn" and is a `NonceReplay` refusal,
        // which would again be the wrong reason for the replay to fail.
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

/// Run one turn, returning the committed receipt hash (so a follow-up turn can continue the
/// executor's receipt chain and actually REACH the effect gates).
fn run_chained(
    executor: &TurnExecutor,
    effect: Effect,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Result<[u8; 32], TurnError> {
    let (agent, cell) = actor_cell();
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell);
    let turn = deshield_turn_chained(agent, effect, previous_receipt_hash);
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { receipt, .. } => Ok(receipt.receipt_hash()),
        TurnResult::Rejected { reason, .. } => Err(reason),
        other => panic!("unexpected turn result: {other:?}"),
    }
}

fn run(executor: &TurnExecutor, effect: Effect) -> Result<(), TurnError> {
    run_chained(executor, effect, None).map(|_| ())
}

fn refusal_reason(error: TurnError) -> String {
    match error {
        TurnError::InvalidEffect { reason } => reason,
        other => panic!("expected InvalidEffect, got {other:?}"),
    }
}

/// The wire input payload for a proven deshield's single spent note.
fn input_payload(deshield: &ShieldedDeshield) -> ShieldedInputPayload {
    let input = &deshield.inputs[0];
    ShieldedInputPayload {
        nullifier: input.nullifier.as_u32(),
        spend_wide_binding: input.spend_wide_binding.map(|f| f.as_u32()),
        spend_proof: input.proof_bytes(),
    }
}

fn deshield_effect(
    deshield: &ShieldedDeshield,
    declared_value: u64,
    declared_asset: u64,
    link_proof: Vec<u8>,
    cleartext_commitment: [u8; 32],
) -> Effect {
    Effect::Deshield {
        value: declared_value,
        asset_type: declared_asset,
        note_commitment: NoteCommitment(cleartext_commitment),
        encrypted_note: vec![],
        input: input_payload(deshield),
        link_proof,
    }
}

/// The 32-byte shielded-nullifier key the executor consumes, computed the way it computes it.
fn shielded_key(nullifier: u32) -> Nullifier {
    dregg_turn::executor::shielded_nullifier_key(nullifier)
}

// ══════════════════════════════════════════════════════════════════════════════
//  1. ⚑ POSITIVE POLE: spend the note, credit exactly `v`, nullify — and the
//     nullifier prevents a SECOND deshield of the same note.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn honest_deshield_credits_exactly_v_nullifies_and_cannot_be_repeated() {
    let (spend, leaves) = spend_and_leaves(VALUE, ASSET, BabyBear::new(0x777));
    let deshield = prove_shielded_deshield(&ShieldedDeshieldWitness { spend })
        .expect("the honest deshield proves");

    // The credit was READ OFF the relation's published limbs, not chosen.
    assert_eq!(
        (deshield.credit.value, deshield.credit.asset_type),
        (VALUE, ASSET),
        "the cleartext credit IS the spent note's value"
    );

    let cleartext = [0xD1u8; 32];
    let effect = deshield_effect(
        &deshield,
        deshield.credit.value,
        deshield.credit.asset_type,
        deshield.credit.link_proof.clone(),
        cleartext,
    );

    let executor = offramp_executor(&leaves, true);
    assert!(
        executor.note_nullifiers.lock().unwrap().is_empty(),
        "no nullifier is spent before the off-ramp runs"
    );
    assert_eq!(
        executor.note_shielded.lock().unwrap().len(),
        2,
        "the accumulator holds the decoy and the note about to leave"
    );

    let first_receipt =
        run_chained(&executor, effect, None).expect("an honest deshield must commit");

    // ── CONSERVATION, EXHIBITED. ──
    let nf = shielded_key(deshield.inputs[0].nullifier.as_u32());
    assert!(
        executor.note_nullifiers.lock().unwrap().contains(&nf),
        "the spent shielded note's nullifier is consumed (the note LEFT the pool)"
    );
    {
        let commitments = executor.note_commitments.lock().unwrap();
        assert!(
            commitments.contains(&NoteCommitment(cleartext)),
            "the cleartext note is created — V ENTERED cleartext"
        );
        assert_eq!(
            commitments.value_of(&NoteCommitment(cleartext)),
            Some(VALUE),
            "and it is recorded at EXACTLY the spent note's value: the value column sums to zero \
             across the boundary (V out of the pool, V into cleartext)"
        );
    }
    assert_eq!(
        executor.note_shielded.lock().unwrap().len(),
        2,
        "a deshield MINTS NOTHING shielded — the accumulator is unchanged (the Lean \
         narrow_site_census = [] as executor-visible behaviour)"
    );

    // ── THE NULLIFIER PREVENTS A SECOND DESHIELD OF THE SAME NOTE. ──
    // A DIFFERENT cleartext commitment, so the refusal can only be the nullifier and not a
    // duplicate-commitment rejection standing in for it.
    let replay = deshield_effect(
        &deshield,
        deshield.credit.value,
        deshield.credit.asset_type,
        deshield.credit.link_proof.clone(),
        [0xD2u8; 32],
    );
    // ⚑ CONTINUE THE RECEIPT CHAIN. Without `first_receipt` the executor refuses with
    // `ReceiptChainMismatch` before any effect runs, and this assertion would be reading a
    // refusal that has nothing to do with the nullifier.
    let reason = refusal_reason(
        run_chained(&executor, replay, Some(first_receipt))
            .expect_err("the same note must not be deshielded twice"),
    );
    assert!(
        reason.contains("double-spend"),
        "the refusal must be the DOUBLE-SPEND gate — not the receipt chain, not a duplicate \
         commitment (the replay carries a different cleartext commitment for exactly that \
         reason): {reason}"
    );
    assert!(
        !executor
            .note_commitments
            .lock()
            .unwrap()
            .contains(&NoteCommitment([0xD2u8; 32])),
        "a refused replay credits NOTHING — the second cleartext note never lands"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
//  2. ⚑ THE NEGATIVE POLE: credit 1_000_000 for a note worth 500 → REFUSED.
//
//     Constructed, not mutated: the forged link is a GENUINE proof of the
//     deshield relation at v' = 1_000_000, stapled onto the genuine worth-500
//     spend. The divergence is asserted PRESENT and the forged proof is shown to
//     verify against its OWN public inputs before any executor verdict is read,
//     so "refused" cannot be "malformed".
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn deshield_that_credits_more_than_it_spends_is_refused() {
    let inflated = 1_000_000u64;
    let randomness = BabyBear::new(0x777);
    let (spend, leaves) = spend_and_leaves(VALUE, ASSET, randomness);
    let blinds = spend.binding_blind;
    let honest = prove_shielded_deshield(&ShieldedDeshieldWitness { spend })
        .expect("the honest deshield proves");

    // A GENUINE value-link proof — of the SAME relation, at the WRONG value.
    let theft = prove_shielded_deshield_link(&ShieldedDeshieldLinkWitness {
        value: inflated,
        asset_type: ASSET,
        in_randomness: randomness,
        in_binding_blind: blinds,
    })
    .expect("the inflated link is a genuine proof of the relation, at the wrong value");

    // ── THE DIVERGENCE, ASSERTED PRESENT, BEFORE ANY VERDICT. ──
    assert_ne!(VALUE, inflated);
    assert_eq!(honest.credit.value, VALUE, "the note is worth 500");
    assert_eq!(
        theft.claim.credit().expect("limbs recompose"),
        (inflated, ASSET),
        "the forged link publishes a credit of 1_000_000 — the attack is genuinely constructed"
    );
    assert_ne!(
        theft.claim.in_wide_binding, honest.inputs[0].spend_wide_binding,
        "VACUITY GUARD: the forged link's carrier differs from the spent note's, or there is \
         nothing for the join to separate"
    );
    assert_ne!(
        theft.proof_bytes(),
        honest.credit.link_proof,
        "VACUITY GUARD: the stapled proof is a different object from the honest one"
    );
    // ── AND IT IS NOT MERELY MALFORMED: it verifies against its OWN public inputs. ──
    verify_shielded_deshield_link(
        &theft.proof_bytes(),
        &theft.claim.in_wide_binding,
        inflated,
        ASSET,
    )
    .expect(
        "the forged link is a VALID proof about its own statement — what it is not is a proof \
         about the note this effect spends",
    );

    // The effect: the honest spend of a worth-500 note, DECLARING a 1_000_000 credit, carrying the
    // genuine 1_000_000 link proof.
    let cleartext = [0xE1u8; 32];
    let effect = deshield_effect(&honest, inflated, ASSET, theft.proof_bytes(), cleartext);
    assert!(
        matches!(
            &effect,
            Effect::Deshield {
                value: 1_000_000,
                ..
            }
        ),
        "the effect credits 1_000_000 while spending a note worth 500"
    );

    let executor = offramp_executor(&leaves, true);
    let reason = refusal_reason(
        run(&executor, effect)
            .expect_err("a deshield crediting 1_000_000 for a worth-500 note MUST be refused"),
    );
    assert!(
        reason.contains("credit") || reason.contains("deshield"),
        "the refusal must name the off-ramp value link: {reason}"
    );

    // ── NOTHING MOVED. ──
    assert!(
        executor.note_commitments.lock().unwrap().is_empty(),
        "a refused deshield credits NOTHING — no cleartext note is created"
    );
    assert!(
        executor.note_nullifiers.lock().unwrap().is_empty(),
        "a refused deshield spends NOTHING (verify precedes the nullify, and the journal unwinds \
         any partial state regardless)"
    );
    assert_eq!(
        executor.note_shielded.lock().unwrap().len(),
        2,
        "and the shielded accumulator is untouched"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
//  3. FAIL-CLOSED CANARY: no deshield verifier injected ⇒ refused BY NAME.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn uninjected_executor_refuses_the_very_deshield_the_injected_one_admits() {
    let (spend, leaves) = spend_and_leaves(VALUE, ASSET, BabyBear::new(0x888));
    let deshield = prove_shielded_deshield(&ShieldedDeshieldWitness { spend })
        .expect("the honest deshield proves");
    let effect = |cm: [u8; 32]| {
        deshield_effect(
            &deshield,
            deshield.credit.value,
            deshield.credit.asset_type,
            deshield.credit.link_proof.clone(),
            cm,
        )
    };

    // Injected: admitted.
    let injected = offramp_executor(&leaves, true);
    run(&injected, effect([0xF1u8; 32])).expect("the injected executor admits the honest deshield");
    assert_eq!(injected.note_commitments.lock().unwrap().len(), 1);

    // No deshield verifier: REFUSED, and the refusal names the missing verifier.
    let bare = offramp_executor(&leaves, false);
    let reason = refusal_reason(
        run(&bare, effect([0xF1u8; 32]))
            .expect_err("a verify-only executor must NOT admit a deshield"),
    );
    assert!(
        reason.contains("deshield verifier"),
        "the refusal must name the MISSING VERIFIER, not masquerade as a proof failure: {reason}"
    );
    assert!(bare.note_commitments.lock().unwrap().is_empty());
    assert!(bare.note_nullifiers.lock().unwrap().is_empty());
}

// ══════════════════════════════════════════════════════════════════════════════
//  4. SEAM #15, inherited: a spend judged under a root the executor does not hold
//     refuses — here, an executor whose accumulator was never primed.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn a_deshield_of_a_note_the_executor_never_committed_refuses() {
    let (spend, leaves) = spend_and_leaves(VALUE, ASSET, BabyBear::new(0x999));
    let deshield = prove_shielded_deshield(&ShieldedDeshieldWitness { spend })
        .expect("the honest deshield proves");
    let effect = deshield_effect(
        &deshield,
        deshield.credit.value,
        deshield.credit.asset_type,
        deshield.credit.link_proof.clone(),
        [0xA1u8; 32],
    );

    // An executor holding the DECOY only — the spent note was never committed here.
    let foreign = offramp_executor(&leaves[..1], true);
    let reason = refusal_reason(run(&foreign, effect).expect_err(
        "a note that is not in THIS executor's committed accumulator cannot be deshielded",
    ));
    assert!(
        reason.contains("deshield"),
        "the refusal must come from the deshield gate: {reason}"
    );
    assert!(foreign.note_commitments.lock().unwrap().is_empty());
    assert!(foreign.note_nullifiers.lock().unwrap().is_empty());
}
