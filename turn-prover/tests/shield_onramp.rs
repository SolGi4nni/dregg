//! End-to-end shielded ON-RAMP (`Effect::Shield`, Fork B pass A2b) through the REAL
//! executor, with the REAL shield-opening verifier injected.
//!
//! The MINT half (the shield-opening STARK) is genuine `dregg-circuit-prove` /
//! Lean-emitted `dregg-shielded-shield::v1` — not a stub. The DEBIT half (the
//! cleartext note-spend) rides an `AcceptAllProofs` mock proof-verifier + a
//! well-formed FNSP-v2 carrier whose successor root matches the executor's planned
//! insert: the note-spend's OWN soundness is exercised by the `NoteSpend` suites, so
//! here it is a stand-in that lets the shielded on-ramp's MONEY-CONSERVATION be
//! shown — the two properties this file exists to pin:
//!
//!   1. an honest Shield DEBITS its cleartext note, APPENDS the exact Poseidon2 note
//!      commitment `hash_fact(V,[A,owner,rand])` to `note_shielded`, and commits;
//!   2. a Shield that MINTS MORE THAN IT DEBITS (a real worth-20 opening declared as
//!      a value-10 debit) is REFUSED — the ledger-conservation twin of A2a's
//!      value-decouple KAT — and appends NOTHING, spends NOTHING.

use std::sync::Arc;

use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, NoteCommitment, Nullifier, NullifierSet, Permissions,
    ShieldedNoteCommitment, felt_to_bytes32,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::shielded::shield_opening::{prove_shield_opening, shield_note_commitment};
use dregg_turn::action::Effect;
use dregg_turn::faithful_note_spend::FaithfulNoteSpendProofCarrier;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, ProofVerifier, TurnError,
    TurnExecutor,
    turn::{Turn, TurnResult},
};
use dregg_turn_prover::CircuitShieldOpeningVerifier;

const ASSET: u64 = 1;
const OWNER: u32 = 0x5EED;
const RAND: u32 = 0xC0FFEE;

// ── the debit half: a mock proof verifier that accepts the note-spend inner proof ──

/// Accepts every note-spend inner proof. The FNSP-v2 carrier's successor-root
/// binding (checked by the executor against its OWN planned insert) is the real
/// tooth that keeps this from admitting an arbitrary spend; the inner STARK's
/// soundness is the `NoteSpend` suites' job, not this on-ramp file's.
struct AcceptAllProofs;
impl ProofVerifier for AcceptAllProofs {
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        true
    }
}

/// An executor with BOTH seams a full shield needs: the REAL shield-opening verifier
/// (mint) and a mock note-spend proof verifier (debit).
fn onramp_executor() -> TurnExecutor {
    TurnExecutor::with_proof_verifier(ComputronCosts::zero(), Box::new(AcceptAllProofs))
        .with_shield_opening_verifier(Arc::new(CircuitShieldOpeningVerifier::new()))
}

// ── executor / turn plumbing (public API only, mirrors shielded_executor.rs) ──

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
    pk[0] = 0x5A;
    pk[31] = 0xA5;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    (cell.id(), cell)
}

fn shield_turn(agent: CellId, effect: Effect) -> Turn {
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
        nonce: 0,
        call_forest: forest,
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

fn run(executor: &TurnExecutor, effect: Effect) -> Result<(), TurnError> {
    let (agent, cell) = actor_cell();
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell);
    match executor.execute(&shield_turn(agent, effect), &mut ledger) {
        TurnResult::Committed { .. } => Ok(()),
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

// ── the mint half: a REAL shield-opening proof + its canonical commitment bytes ──

/// A genuine shield-opening proof for `(value, ASSET)`, plus the 32-byte encoding of
/// the note commitment it opens — `felt_to_bytes32(hash_fact(value,[ASSET,owner,rand]))`.
fn real_opening(value: u64) -> (Vec<u8>, [u8; 32]) {
    let v = BabyBear::new(value as u32);
    let a = BabyBear::new(ASSET as u32);
    let owner = BabyBear::new(OWNER);
    let rand = BabyBear::new(RAND);
    let proof = prove_shield_opening(v, a, owner, rand).expect("a genuine shield opening proves");
    let cm = shield_note_commitment(v, a, owner, rand);
    let shield_proof = postcard::to_allocvec(&proof.proof).expect("serialize Ir2BatchProof");
    (shield_proof, felt_to_bytes32(cm))
}

/// The commitment bytes a worth-`value` note WOULD open to (for the falsifier's
/// disequality assertion).
fn commitment_bytes_for(value: u64) -> [u8; 32] {
    felt_to_bytes32(shield_note_commitment(
        BabyBear::new(value as u32),
        BabyBear::new(ASSET as u32),
        BabyBear::new(OWNER),
        BabyBear::new(RAND),
    ))
}

// ── the debit half: a well-formed FNSP-v2 carrier the mock verifier accepts ──

fn faithful_root_bytes(seed: u32) -> [u8; 32] {
    let mut r = [0u8; 32];
    for lane in 0..8 {
        r[lane * 4..lane * 4 + 4].copy_from_slice(&(seed + lane as u32).to_le_bytes());
    }
    r
}

/// The successor nullifier root the executor will PLAN for `insert(nf, value)` into
/// its (fresh, empty) note-nullifier set — computed the exact same way the executor
/// does (`NullifierSet::root8().to_bytes32()`), so the FNSP-v2 successor binding holds.
fn planned_successor(nf: [u8; 32], value: u64) -> [u8; 32] {
    let mut set = NullifierSet::new();
    set.insert(Nullifier(nf), value)
        .expect("fresh nullifier insert");
    set.root8().to_bytes32()
}

fn debit_spending_proof(nf: [u8; 32], value: u64) -> Vec<u8> {
    FaithfulNoteSpendProofCarrier::new(0, planned_successor(nf, value), vec![0xAB, 0xCD])
        .expect("well-formed FNSP-v2 carrier")
        .encode()
}

fn shield_effect(
    value: u64,
    note_commitment: [u8; 32],
    shield_proof: Vec<u8>,
    nf: [u8; 32],
) -> Effect {
    Effect::Shield {
        value,
        asset_type: ASSET,
        note_commitment: NoteCommitment(note_commitment),
        encrypted_note: vec![],
        shield_proof,
        nullifier: Nullifier(nf),
        note_tree_root: faithful_root_bytes(100),
        spending_proof: debit_spending_proof(nf, value),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
//  1. HONEST: debit V, append hash_fact(V,[A,owner,rand]), commit.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn honest_shield_debits_and_appends_the_note_commitment() {
    let value = 10u64;
    let nf = [0x77u8; 32];
    let (shield_proof, cm_bytes) = real_opening(value);
    let effect = shield_effect(value, cm_bytes, shield_proof, nf);

    let executor = onramp_executor();
    assert!(
        executor.note_shielded.lock().unwrap().is_empty(),
        "the shielded accumulator starts EMPTY"
    );
    assert!(executor.note_nullifiers.lock().unwrap().is_empty());

    run(&executor, effect).expect("an honest shield must commit");

    assert!(
        executor
            .note_shielded
            .lock()
            .unwrap()
            .contains(&ShieldedNoteCommitment(cm_bytes)),
        "the note enters note_shielded as felt_to_bytes32(hash_fact(V,[A,owner,rand]))"
    );
    assert_eq!(
        executor.note_shielded.lock().unwrap().len(),
        1,
        "exactly one shielded note was minted"
    );
    assert!(
        executor
            .note_nullifiers
            .lock()
            .unwrap()
            .contains(&Nullifier(nf)),
        "the debited cleartext note's nullifier is now spent (V left cleartext)"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
//  2. ⚑ THE MINTING-REFUSAL: debit 10, mint a REAL worth-20 opening → REFUSED.
//     The ledger-conservation twin of the A2a value-decouple KAT.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn shield_that_mints_more_than_it_debits_is_refused() {
    let debited = 10u64;
    let minted = 20u64;
    // A GENUINE worth-20 opening (piVALUE=20, CM = hash_fact(20,...)).
    let (proof20, cm20_bytes) = real_opening(minted);

    // ── assert the mutation is PRESENT before reading the verdict ──
    // The effect will carry the worth-20 commitment while DECLARING a value-10 debit.
    assert_eq!(
        cm20_bytes,
        commitment_bytes_for(minted),
        "the carried commitment is the worth-20 opening"
    );
    assert_ne!(
        cm20_bytes,
        commitment_bytes_for(debited),
        "the worth-20 commitment is NOT the worth-10 one — the debit(10) < mint(20) attack \
         is genuinely constructed, not a no-op"
    );

    let nf = [0x88u8; 32];
    // Declares value=10 (the debit) but hands the worth-20 commitment + its proof.
    let effect = shield_effect(debited, cm20_bytes, proof20, nf);
    assert!(
        matches!(&effect, Effect::Shield { value: 10, .. }),
        "the effect debits 10 while minting 20"
    );

    let executor = onramp_executor();
    let reason = refusal_reason(
        run(&executor, effect).expect_err("a shield that debits 10 but mints 20 MUST be refused"),
    );
    assert!(
        reason.contains("shield-opening") || reason.contains("verification failed"),
        "the refusal must be the shield-opening decouple rejection (mint-worth-more is UNSAT), \
         got: {reason}"
    );
    assert!(
        executor.note_shielded.lock().unwrap().is_empty(),
        "a refused shield mints NOTHING — the outcome worse than the theft, kept closed"
    );
    assert!(
        executor.note_nullifiers.lock().unwrap().is_empty(),
        "a refused shield spends NOTHING (the mint verify precedes the debit, and the journal \
         unwinds any partial state regardless)"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
//  3. FAIL-CLOSED CANARY: no shield-opening verifier injected ⇒ refused by name.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn uninjected_executor_refuses_the_very_shield_the_injected_one_admits() {
    let value = 10u64;
    let nf = [0x99u8; 32];
    let (shield_proof, cm_bytes) = real_opening(value);

    // Injected: admitted.
    let injected = onramp_executor();
    run(
        &injected,
        shield_effect(value, cm_bytes, shield_proof.clone(), nf),
    )
    .expect("the injected executor admits the honest shield");
    assert_eq!(injected.note_shielded.lock().unwrap().len(), 1);

    // Only the note-spend verifier injected, NO shield-opening verifier: REFUSED.
    let bare = TurnExecutor::with_proof_verifier(ComputronCosts::zero(), Box::new(AcceptAllProofs));
    let reason = refusal_reason(
        run(&bare, shield_effect(value, cm_bytes, shield_proof, nf))
            .expect_err("a verify-only executor must NOT admit a shield"),
    );
    assert!(
        reason.contains("shield-opening verifier"),
        "the refusal must name the MISSING VERIFIER, not masquerade as a proof failure: {reason}"
    );
    assert!(bare.note_shielded.lock().unwrap().is_empty());
    assert!(bare.note_nullifiers.lock().unwrap().is_empty());
}

// ══════════════════════════════════════════════════════════════════════════════
//  4. The MINT seam directly: the verifier is pure, and a decoupled claim rejects.
// ══════════════════════════════════════════════════════════════════════════════
#[test]
fn the_shield_opening_verifier_accepts_honest_and_rejects_decoupled() {
    use dregg_turn::shielded_verifier::ShieldOpeningVerifier;

    let (honest_proof, cm10) = real_opening(10);
    let v = CircuitShieldOpeningVerifier::new();

    // Honest: returns the PROVEN public data.
    let verified = v
        .verify(10, ASSET, cm10, &honest_proof)
        .expect("an honest shield opening verifies");
    assert_eq!(verified.value, 10);
    assert_eq!(verified.asset_type, ASSET);
    assert_eq!(verified.note_commitment, cm10);

    // Decoupled: the SAME proof, claimed at value 20 (or the worth-20 commitment at
    // value 10) — both must REJECT (the piBinding forces the proven cell).
    let (proof20, cm20) = real_opening(20);
    assert!(
        v.verify(10, ASSET, cm20, &proof20).is_err(),
        "a worth-20 opening claimed as a value-10 mint must reject"
    );
    assert!(
        v.verify(20, ASSET, cm10, &honest_proof).is_err(),
        "a worth-10 opening claimed as a value-20 mint must reject"
    );
}
