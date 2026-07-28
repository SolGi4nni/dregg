//! Sovereign-witness tests — Phase 1 algebraic teeth + wire-malleability.
//!
//! Layer: AIR (Effect VM) + canonical signing message + verifier-side
//! replay. See `AUDIT-sovereign-witness-teeth.md`,
//! `SOVEREIGN-WITNESS-AIR-DESIGN.md`, and `EXECUTOR-HONESTY-AUDIT.md` T9.
//!
//! Three concerns:
//!
//!   1. Phase 1: legal witness accepted; tampered key / sequence-regression
//!      rejected.
//!   2. T9 (executor skips sovereign witness): AIR must algebraically
//!      constrain the witness; it can't just decorate the receipt.
//!   3. Wire-malleability: turn v3 signing message must cover sovereign
//!      witnesses so tamper-then-sign fails.
//!
//! AIR-transition tests remain `#[ignore]`d on the sovereign-witness teeth
//! lane. Executor and wire-hash checks below are live when the implementation
//! already exposes the defense.

use std::collections::HashMap;

use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, Ledger, Permissions, StateConstraint, field_from_u64,
};
use dregg_turn::action::{WitnessBlob, symbol};
use dregg_turn::{
    Action, ActionBuilder, Authorization, CallForest, ComputronCosts, DelegationMode, Effect,
    SovereignCellWitness, Turn, TurnBuilder, TurnError, TurnExecutor, TurnResult,
};
use dregg_types::{SigningKey, sign};

fn permissive_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(31);
    let mut cell = Cell::with_balance(
        pk,
        [0u8; 32],
        i64::try_from(balance).expect("balance fits i64"),
    );
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn signing_cell(seed: u8, balance: u64) -> (Cell, SigningKey) {
    let seed_bytes = [seed; 32];
    let signing_key = SigningKey::from_bytes(&seed_bytes);
    let mut cell = Cell::with_balance(
        *signing_key.public_key().as_bytes(),
        [0u8; 32],
        i64::try_from(balance).expect("balance fits i64"),
    );
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    (cell, signing_key)
}

fn turn_with_witnesses(agent: CellId, witnesses: HashMap<CellId, SovereignCellWitness>) -> Turn {
    Turn {
        agent,
        nonce: 0,
        call_forest: dregg_turn::CallForest::new(),
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: witnesses,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn set_field_turn(
    agent: CellId,
    target: CellId,
    witnesses: HashMap<CellId, SovereignCellWitness>,
) -> Turn {
    set_field_turn_with_action_witnesses(agent, target, witnesses, 0, [1u8; 32], vec![])
}

fn set_field_turn_with_action_witnesses(
    agent: CellId,
    target: CellId,
    witnesses: HashMap<CellId, SovereignCellWitness>,
    // `Effect::SetField.index` is the canonical committed-map key: a `u64`, not a
    // slot ordinal. (`Cell::state::set_field` still takes a `usize` slot index —
    // `post_set_field_commitment` below keeps that type.)
    index: u64,
    value: [u8; 32],
    witness_blobs: Vec<WitnessBlob>,
) -> Turn {
    let mut call_forest = CallForest::new();
    call_forest.add_root(Action {
        target,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs,
    });

    Turn {
        agent,
        nonce: 0,
        call_forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: witnesses,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn two_set_field_turn(
    agent: CellId,
    first: CellId,
    second: CellId,
    witnesses: HashMap<CellId, SovereignCellWitness>,
) -> Turn {
    let first_action = ActionBuilder::new_unchecked_for_tests(first, "set_field", agent)
        .effect_set_field(first, 0, [1u8; 32])
        .build();
    let second_action = ActionBuilder::new_unchecked_for_tests(second, "set_field", agent)
        .effect_set_field(second, 0, [2u8; 32])
        .build();
    let mut builder = TurnBuilder::new(agent, 0);
    builder.add_action(first_action);
    builder.add_action(second_action);
    let mut turn = builder.fee(0).build();
    turn.sovereign_witnesses = witnesses;
    turn
}

fn dummy_sovereign_witness(
    cell: Cell,
    effects_hash: [u8; 32],
    sequence: u64,
) -> SovereignCellWitness {
    let cell_id = cell.id();
    SovereignCellWitness {
        cell_id,
        old_commitment: [0xAA; 32],
        new_commitment: [0xBB; 32],
        effects_hash,
        timestamp: 0,
        sequence,
        signature: [0xAB; 64],
        cell_state: cell,
        transition_proof: None,
    }
}

fn signed_sovereign_witness(
    cell: &Cell,
    signing_key: &SigningKey,
    old_commitment: [u8; 32],
    effects_hash: [u8; 32],
    sequence: u64,
) -> SovereignCellWitness {
    signed_sovereign_witness_for_federation(
        &[0u8; 32],
        cell,
        signing_key,
        old_commitment,
        effects_hash,
        sequence,
    )
}

fn signed_sovereign_witness_for_federation(
    federation_id: &[u8; 32],
    cell: &Cell,
    signing_key: &SigningKey,
    old_commitment: [u8; 32],
    effects_hash: [u8; 32],
    sequence: u64,
) -> SovereignCellWitness {
    // Default: declare the UNCHANGED state as the post-state (suitable for
    // negative tests that reject before the post-execution commitment check).
    // Positive tests that mutate the cell must declare the real post-effect
    // commitment via `signed_sovereign_witness_with_new_commitment`.
    let new_commitment = cell.state_commitment();
    signed_sovereign_witness_with_new_commitment(
        federation_id,
        cell,
        signing_key,
        old_commitment,
        new_commitment,
        effects_hash,
        sequence,
    )
}

/// SECURITY (sovereign-witness hardening): a witness must name the REAL
/// post-state commitment and the REAL per-cell effects hash for the turn it
/// rides — the executor re-executes and checks the declared `new_commitment`
/// against the recomputed post-state (`SovereignCommitmentMismatch`), and
/// rule 7b compares the declared `effects_hash` against
/// `Turn::sovereign_effects_hash(cell)` (`EffectsHashMismatch`). Callers whose
/// turn mutates the cell pass the post-effect commitment here.
///
/// ⚠ `effects_hash` is passed through VERBATIM. This helper used to coerce an
/// all-zero argument into `blake3("dregg-sovereign-witness-empty-effects")`,
/// which was a defensible stand-in while the only rule about `effects_hash` was
/// "must not be the zero placeholder". Rule 7b replaced that rule with a
/// BINDING (`execute.rs`: "The zero placeholder is still refused; it is refused
/// by the rule that binds"), and against a binding the coercion is not a
/// stand-in — it is a value that can never match, so every positive sovereign
/// test in this file died the moment the binding landed. A fixture that
/// manufactures a hash the executor cannot accept is worse than one that
/// demands the caller compute the real one, so callers now do: see
/// [`set_field_effects_hash`].
fn signed_sovereign_witness_with_new_commitment(
    federation_id: &[u8; 32],
    cell: &Cell,
    signing_key: &SigningKey,
    old_commitment: [u8; 32],
    new_commitment: [u8; 32],
    effects_hash: [u8; 32],
    sequence: u64,
) -> SovereignCellWitness {
    let cell_id = cell.id();
    let timestamp = 0;
    let message = SovereignCellWitness::signing_message_for_federation(
        federation_id,
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: sign(signing_key, &message).0,
        cell_state: cell.clone(),
        transition_proof: None,
    }
}

/// The post-state commitment of `cell` after the executor applies
/// `SetField(index, value)` — i.e. the value the sovereign witness must declare
/// as `new_commitment` for a turn whose sole effect is that field write.
fn post_set_field_commitment(cell: &Cell, index: usize, value: [u8; 32]) -> [u8; 32] {
    let mut post = cell.clone();
    post.state.set_field(index, value);
    post.state_commitment()
}

/// The per-cell effects hash that executor rule 7b demands of a witness riding
/// the turn `set_field_turn_with_action_witnesses(agent, target, …, index,
/// value, …)` builds.
///
/// `Turn::sovereign_effects_hash` is a pure function of the call forest — it
/// never reads `sovereign_witnesses` — so the value is computable from an
/// otherwise-identical turn carrying an EMPTY witness map, before the witness
/// it must be signed into exists. That is what makes rule 7b testable from the
/// outside without duplicating the canonical hash's definition here: this
/// helper calls the same `Turn` method the executor calls, so a change to the
/// canonical encoding cannot silently pass by moving both sides together.
fn set_field_effects_hash(agent: CellId, target: CellId, index: u64, value: [u8; 32]) -> [u8; 32] {
    set_field_turn_with_action_witnesses(agent, target, HashMap::new(), index, value, vec![])
        .sovereign_effects_hash(&target)
}

fn sovereign_fixture(seed: u8) -> (Ledger, CellId, CellId, Cell, SigningKey, [u8; 32]) {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let (sovereign, signing_key) = signing_cell(seed, 500);
    let sovereign_id = sovereign.id();
    let old_commitment = sovereign.state_commitment();
    ledger
        .register_sovereign_cell(sovereign_id, old_commitment)
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    (
        ledger,
        agent_id,
        sovereign_id,
        sovereign,
        signing_key,
        old_commitment,
    )
}

// ===========================================================================
// Phase 1: legal witness path
// ===========================================================================

#[test]
fn sovereign_witness_with_legal_key_accepts() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(2);
    // The turn's sole effect is SetField(0, [1;32]); the witness must declare
    // the resulting post-state as `new_commitment` (executor re-executes and
    // checks it — see `SovereignCommitmentMismatch`).
    let new_commitment = post_set_field_commitment(&sovereign, 0, [1u8; 32]);
    let witness = signed_sovereign_witness_with_new_commitment(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        set_field_effects_hash(agent_id, sovereign_id, 0, [1u8; 32]),
        1,
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "legal sovereign witness must commit, got: {result:?}"
    );
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        1,
        "committed sovereign witness must advance the replay sequence"
    );
}

#[test]
fn sovereign_witness_with_tampered_key_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, _real_key, old_commitment) =
        sovereign_fixture(2);
    let wrong_key = SigningKey::from_bytes(&[99u8; 32]);
    let witness = signed_sovereign_witness(&sovereign, &wrong_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "sovereign witness signed by the wrong key must reject, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_sequence_regression_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(3);
    ledger.bump_sovereign_witness_sequence(&sovereign_id, 2);

    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("sequence")
        ),
        "regressed sovereign witness sequence must reject, got: {result:?}"
    );
}

// ===========================================================================
// T9: executor cannot skip sovereign witness verification
// ===========================================================================

#[test]
fn sovereign_cell_turn_without_witness_rejects() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let sovereign = permissive_cell(2, 500);
    let sovereign_id = sovereign.id();
    ledger
        .register_sovereign_cell(sovereign_id, sovereign.state_commitment())
        .unwrap();

    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    let action = ActionBuilder::new_unchecked_for_tests(sovereign_id, "set_field", agent_id)
        .effect_set_field(sovereign_id, 0, [1u8; 32])
        .build();
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.add_action(action);
    let turn = builder.fee(0).build();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::SovereignWitnessRequired { cell },
                ..
            } if *cell == sovereign_id
        ),
        "sovereign mutation without witness must reject, got: {result:?}"
    );
}

// ===========================================================================
// THE EFFECTS BINDING (executor rule 7b, `execute.rs`)
//
// `witness.effects_hash` rides in the canonical signing message and, until
// 2026-07-27, was compared against NOTHING. `TurnError::EffectsHashMismatch`
// was defined (`turn/src/error.rs:286`), formatted (`:890`) and matched in a
// handler (`starbridge-v2/src/debug.rs`) — and CONSTRUCTED ZERO TIMES, while
// `turn/src/turn.rs` stated the executor "recomputes both during forest
// execution". A sovereign owner signed `H(Transfer 10)`, the executor applied
// `Transfer 20`, and it committed.
//
// The placeholder that used to sit here (`air_proof_constrains_sovereign_
// witness_to_transition`, `#[ignore]`d "blocked on T9") described this exact
// attack in a comment and `panic!("blocked")`. It is now driven, twice.
// ===========================================================================

/// The post-state commitment of `cell` after it sends `amount` — the value a
/// sovereign witness must declare as `new_commitment` for a turn whose sole
/// effect is that outbound transfer.
fn post_transfer_commitment(cell: &Cell, amount: u64) -> [u8; 32] {
    let mut post = cell.clone();
    post.state
        .set_balance(post.state.balance() - i64::try_from(amount).expect("amount fits i64"));
    post.state_commitment()
}

/// A turn whose sole effect is `Transfer { from: sovereign, to, amount }`,
/// carried by an action TARGETING the sovereign cell (so the transfer needs no
/// cross-cell `Send` permission — the authority in question is the witness).
fn transfer_turn(
    agent: CellId,
    sovereign: CellId,
    to: CellId,
    amount: u64,
    witnesses: HashMap<CellId, SovereignCellWitness>,
) -> Turn {
    let mut call_forest = CallForest::new();
    call_forest.add_root(Action {
        target: sovereign,
        method: symbol("pay"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: sovereign,
            to,
            amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });

    Turn {
        agent,
        nonce: 0,
        call_forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: witnesses,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// The canonical `effects_hash` for `sovereign` on the turn `transfer_turn`
/// builds — computed by calling the SAME `Turn::sovereign_effects_hash` the
/// executor calls, on an otherwise-identical witness-free turn (the canonical
/// sequence never reads `sovereign_witnesses`).
fn transfer_effects_hash(agent: CellId, sovereign: CellId, to: CellId, amount: u64) -> [u8; 32] {
    transfer_turn(agent, sovereign, to, amount, HashMap::new()).sovereign_effects_hash(&sovereign)
}

/// THE ATTACK, as written in the retired placeholder's own comment: the witness
/// authorized `Transfer(10)`, the executor is handed `Transfer(20)`.
///
/// The witness is otherwise PERFECT — signed by the cell's own key over the
/// canonical federation message, correct `old_commitment`, correct sequence, no
/// `transition_proof`. The only thing wrong is that the effect set it signed is
/// not the effect set in the turn.
#[test]
fn sovereign_witness_authorizing_transfer_10_refuses_transfer_20() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(20);

    // What Alice signed: pay the agent 10, ending at balance 490.
    let authorized = transfer_effects_hash(agent_id, sovereign_id, agent_id, 10);
    let witness = signed_sovereign_witness_with_new_commitment(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        post_transfer_commitment(&sovereign, 10),
        authorized,
        1,
    );

    // What the submitter attaches it to: pay the agent 20.
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let forgery = transfer_turn(agent_id, sovereign_id, agent_id, 20, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&forgery, &mut ledger);
    match &result {
        TurnResult::Rejected {
            reason:
                TurnError::EffectsHashMismatch {
                    cell,
                    expected,
                    got,
                },
            ..
        } => {
            assert_eq!(
                *expected,
                transfer_effects_hash(agent_id, sovereign_id, agent_id, 20),
                "the executor must name the canonical hash of the turn it was handed"
            );
            assert_eq!(*got, authorized, "and the hash the owner actually signed");
            assert_ne!(
                expected, got,
                "an EffectsHashMismatch with equal legs is not a mismatch"
            );
            assert_eq!(
                *cell, sovereign_id,
                "the error must name the witness that was wrong"
            );
        }
        other => panic!(
            "a witness authorizing Transfer(10) must not authorize Transfer(20); got: {other:?}"
        ),
    }

    // Nothing moved, and the replay sequence did not advance.
    assert_eq!(
        ledger.get_sovereign_commitment(&sovereign_id),
        Some(&old_commitment),
        "a refused forgery must leave the sovereign commitment untouched"
    );
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        0,
        "a refused forgery must not burn the witness sequence"
    );
}

/// THE COMMITMENT-BLIND FORGERY — the one that proves this check is not
/// redundant.
///
/// Alice signs "pay Bob 10". The submitter rewrites the payee to Mallory and
/// leaves the amount alone. Alice's post-state is BYTE-IDENTICAL under both
/// effect sets (she is down 10 either way), so `SovereignCommitmentMismatch`
/// — the only other thing checking a sovereign witness's declarations — is
/// structurally blind to it. If rule 7b is removed, this turn COMMITS and
/// Mallory is paid with Alice's signature.
#[test]
fn sovereign_witness_authorizing_payment_to_bob_refuses_payment_to_mallory() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(21);

    let bob = permissive_cell(30, 0);
    let bob_id = bob.id();
    ledger.insert_cell(bob).unwrap();
    let mallory = permissive_cell(31, 0);
    let mallory_id = mallory.id();
    ledger.insert_cell(mallory).unwrap();

    // Alice signs "pay Bob 10". Her declared post-state is balance 490 — which
    // is ALSO her post-state under the forgery.
    let new_commitment = post_transfer_commitment(&sovereign, 10);
    let authorized = transfer_effects_hash(agent_id, sovereign_id, bob_id, 10);
    let witness = signed_sovereign_witness_with_new_commitment(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        authorized,
        1,
    );
    assert_eq!(
        new_commitment,
        post_transfer_commitment(&sovereign, 10),
        "the two effect sets must be commitment-INDISTINGUISHABLE for this test to bite"
    );

    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let forgery = transfer_turn(agent_id, sovereign_id, mallory_id, 10, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&forgery, &mut ledger);
    match &result {
        TurnResult::Rejected {
            reason:
                TurnError::EffectsHashMismatch {
                    cell,
                    expected,
                    got,
                },
            ..
        } => {
            assert_eq!(
                *expected,
                transfer_effects_hash(agent_id, sovereign_id, mallory_id, 10),
                "the executor must name the canonical hash of the turn it was handed"
            );
            assert_eq!(*got, authorized);
            assert_eq!(
                *cell, sovereign_id,
                "the error must name the witness that was wrong"
            );
        }
        other => {
            panic!("rewriting the payee under a sovereign signature must reject; got: {other:?}")
        }
    }

    assert_eq!(
        ledger
            .get(&mallory_id)
            .expect("mallory hosted")
            .state
            .balance(),
        0,
        "Mallory must not be paid by a signature that named Bob"
    );
    assert_eq!(
        ledger.get_sovereign_commitment(&sovereign_id),
        Some(&old_commitment),
        "a refused forgery must leave the sovereign commitment untouched"
    );
}

/// THE HONEST POLE. A check that refuses everything is exactly as useless as
/// one that refuses nothing, so: the SAME fixture, the SAME witness shape, with
/// the effect set the owner actually signed — and it COMMITS, moves the value,
/// advances the sovereign commitment and burns the sequence.
#[test]
fn sovereign_witness_matching_its_turn_commits() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(22);

    let bob = permissive_cell(30, 0);
    let bob_id = bob.id();
    ledger.insert_cell(bob).unwrap();

    let new_commitment = post_transfer_commitment(&sovereign, 10);
    let witness = signed_sovereign_witness_with_new_commitment(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        transfer_effects_hash(agent_id, sovereign_id, bob_id, 10),
        1,
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let honest = transfer_turn(agent_id, sovereign_id, bob_id, 10, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&honest, &mut ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "a witness carrying the canonical effects hash of its own turn must COMMIT, got: {result:?}"
    );
    assert_eq!(
        ledger.get(&bob_id).expect("bob hosted").state.balance(),
        10,
        "the honest pole must actually move the value"
    );
    assert_eq!(
        ledger.get_sovereign_commitment(&sovereign_id),
        Some(&new_commitment),
        "the honest pole must advance the sovereign commitment to the declared post-state"
    );
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        1,
        "the honest pole must burn the witness sequence"
    );
}

/// The canonical hash is CELL-BOUND: two sovereign cells in one turn get two
/// different digests, so a witness digest cannot be transplanted between them
/// even when their projections coincide.
#[test]
fn canonical_effects_hash_is_cell_bound() {
    let (_ledger, agent_id, alice_id, _alice, _key, _old) = sovereign_fixture(23);
    let (bob_cell, _bob_key) = signing_cell(24, 500);
    let bob_id = bob_cell.id();

    let turn = transfer_turn(agent_id, alice_id, bob_id, 10, HashMap::new());
    assert_ne!(
        turn.sovereign_effects_hash(&alice_id),
        turn.sovereign_effects_hash(&bob_id),
        "one turn must not yield one witness digest for two different cells"
    );

    // …and it is never the zero sentinel, even for a witness that authorizes
    // nothing — which is why the executor no longer needs a zero-placeholder
    // special case (`execute.rs` rule 7b).
    let empty = turn_with_witnesses(agent_id, HashMap::new());
    assert_ne!(
        empty.sovereign_effects_hash(&alice_id),
        [0u8; 32],
        "the empty projection must still have an honest, non-zero encoding"
    );
}

// ===========================================================================
// Wire-malleability (T9 tail)
// ===========================================================================

#[test]
fn signing_message_covers_sovereign_witness_payload() {
    let agent = CellId([1u8; 32]);
    let cell = permissive_cell(3, 0);
    let cell_id = cell.id();

    let mut witnesses_a = HashMap::new();
    witnesses_a.insert(
        cell_id,
        dummy_sovereign_witness(cell.clone(), [0x11; 32], 1),
    );
    let turn_a = turn_with_witnesses(agent, witnesses_a);

    let mut witnesses_b = HashMap::new();
    witnesses_b.insert(cell_id, dummy_sovereign_witness(cell, [0x22; 32], 1));
    let turn_b = turn_with_witnesses(agent, witnesses_b);

    assert_ne!(
        turn_a.hash(),
        turn_b.hash(),
        "Turn::hash must change when sovereign witness payload bytes change"
    );

    let msg_a = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0x11; 32],
        0,
        1,
    );
    let msg_b = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0x22; 32],
        0,
        1,
    );
    assert_ne!(
        msg_a, msg_b,
        "sovereign witness signing message must bind effects_hash payload"
    );
}

#[test]
fn tamper_then_sign_witness_workflow_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(7);
    let mut witness =
        signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);

    witness.effects_hash = [0x44; 32];
    let wrong_key = SigningKey::from_bytes(&[0x55; 32]);
    let message = SovereignCellWitness::signing_message(
        &witness.cell_id,
        &witness.old_commitment,
        &witness.new_commitment,
        &witness.effects_hash,
        witness.timestamp,
        witness.sequence,
    );
    witness.signature = sign(&wrong_key, &message).0;

    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "tamper-then-sign with a non-cell key must reject, got: {result:?}"
    );
}

// ===========================================================================
// Cross-cutting: sovereign + bilateral + slot caveats
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign witness AIR teeth + γ.2 + caveat-correctness: full composition"]
fn sovereign_witness_plus_bilateral_transfer_plus_slot_caveats() {
    // Composition mandate — see CAVEAT-LAYER-COVERAGE composition row.
    panic!("blocked");
}

// ===========================================================================
// Sanity: presence of sovereign_witnesses field on Turn does not by itself
// authorize a non-sovereign mutation.
// ===========================================================================

// ===========================================================================
// Extended adversarial scenarios (Phase 1 + AIR teeth)
// ===========================================================================

#[test]
fn sovereign_witness_cross_cell_reuse_rejects() {
    let (mut ledger, agent_id, alice_id, alice, alice_key, alice_old_commitment) =
        sovereign_fixture(4);
    let (bob, _bob_key) = signing_cell(5, 500);
    let bob_id = bob.id();
    ledger
        .register_sovereign_cell(bob_id, bob.state_commitment())
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(bob_id, AuthRequired::None);

    let alice_witness =
        signed_sovereign_witness(&alice, &alice_key, alice_old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(bob_id, alice_witness);
    let turn = set_field_turn(agent_id, bob_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("payload cell_id")
        ),
        "witness for {alice_id} reused under {bob_id} must reject, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_exact_replay_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(8);
    // First turn applies SetField(0, [1;32]); witness declares that post-state.
    let new_commitment = post_set_field_commitment(&sovereign, 0, [1u8; 32]);
    let witness = signed_sovereign_witness_with_new_commitment(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        set_field_effects_hash(agent_id, sovereign_id, 0, [1u8; 32]),
        1,
    );

    let mut first_witnesses = HashMap::new();
    first_witnesses.insert(sovereign_id, witness.clone());
    let first = set_field_turn(agent_id, sovereign_id, first_witnesses);
    let first_result = TurnExecutor::new(ComputronCosts::zero()).execute(&first, &mut ledger);
    assert!(
        matches!(&first_result, TurnResult::Committed { .. }),
        "initial witness use must commit before replay check, got: {first_result:?}"
    );

    let mut replay_witnesses = HashMap::new();
    replay_witnesses.insert(sovereign_id, witness);
    let mut replay = set_field_turn(agent_id, sovereign_id, replay_witnesses);
    replay.nonce = 1;

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&replay, &mut ledger);
    let rejected_as_replay = matches!(
        &result,
        TurnResult::Rejected {
            reason: TurnError::SovereignCommitmentMismatch { .. },
            ..
        }
    ) || matches!(
        &result,
        TurnResult::Rejected {
            reason: TurnError::InvalidEffect { reason },
            ..
        } if reason.contains("sequence")
    );
    assert!(
        rejected_as_replay,
        "exact sovereign witness replay must reject before commit, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_after_key_rotation_old_key_rejects() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let (old_cell, old_key) = signing_cell(9, 500);
    let old_id = old_cell.id();
    let new_key = SigningKey::from_bytes(&[0x99; 32]);
    let mut rotated =
        Cell::remote_stub_with_id_pk_balance(old_id, *new_key.public_key().as_bytes(), 500);
    rotated.permissions = old_cell.permissions.clone();
    let old_commitment = rotated.state_commitment();
    ledger
        .register_sovereign_cell(old_id, old_commitment)
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(old_id, AuthRequired::None);

    let witness = signed_sovereign_witness(&rotated, &old_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(old_id, witness);
    let turn = set_field_turn(agent_id, old_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "old key must not sign for rotated sovereign cell key, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_equal_sequence_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(3);
    ledger.bump_sovereign_witness_sequence(&sovereign_id, 1);

    let witness = signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("sequence")
        ),
        "sovereign witness with sequence equal to current must reject, got: {result:?}"
    );
}

#[test]
fn sovereign_witness_payload_tamper_with_intact_signature_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(6);
    let mut witness =
        signed_sovereign_witness(&sovereign, &signing_key, old_commitment, [0u8; 32], 1);
    witness.effects_hash = [0xEF; 32];
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "payload tamper after signing must reject, got: {result:?}"
    );
}

#[test]
fn turn_with_two_sovereign_cells_one_witness_invalid_rejects() {
    let (mut ledger, agent_id, alice_id, alice, alice_key, alice_old_commitment) =
        sovereign_fixture(10);
    let (bob, _bob_key) = signing_cell(11, 500);
    let bob_id = bob.id();
    let bob_old_commitment = bob.state_commitment();
    ledger
        .register_sovereign_cell(bob_id, bob_old_commitment)
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(bob_id, AuthRequired::None);

    // Alice's witness is VALID — including its effects hash, which must be the
    // canonical one for the two-action turn below. Witness verification walks a
    // `HashMap`, so Alice may be checked first; if her witness failed rule 7b
    // this test would go green on an `EffectsHashMismatch` it never meant to
    // assert and Bob's bad signature would never be reached.
    let two_cell_effects_hash = |cell: &CellId| {
        two_set_field_turn(agent_id, alice_id, bob_id, HashMap::new()).sovereign_effects_hash(cell)
    };
    let alice_witness = signed_sovereign_witness(
        &alice,
        &alice_key,
        alice_old_commitment,
        two_cell_effects_hash(&alice_id),
        1,
    );
    let wrong_key = SigningKey::from_bytes(&[0xAA; 32]);
    let bob_witness = signed_sovereign_witness(
        &bob,
        &wrong_key,
        bob_old_commitment,
        two_cell_effects_hash(&bob_id),
        1,
    );

    let mut witnesses = HashMap::new();
    witnesses.insert(alice_id, alice_witness);
    witnesses.insert(bob_id, bob_witness);
    let turn = two_set_field_turn(agent_id, alice_id, bob_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "one invalid sovereign witness must reject the whole turn, got: {result:?}"
    );
}

#[test]
fn extra_witness_for_non_sovereign_cell_does_not_grant_authorization() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(1, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let (hosted, hosted_key) = signing_cell(12, 500);
    let hosted_id = hosted.id();
    let hosted_commitment = hosted.state_commitment();
    ledger.insert_cell(hosted.clone()).unwrap();

    let witness = signed_sovereign_witness(&hosted, &hosted_key, hosted_commitment, [0u8; 32], 1);
    let mut witnesses = HashMap::new();
    witnesses.insert(hosted_id, witness);
    let turn = set_field_turn(agent_id, hosted_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("non-sovereign")
        ),
        "extra witness for hosted cell must not grant authorization, got: {result:?}"
    );
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: tx-time vs verify-time consistency — the witness's sequence number bound in the AIR PI must equal the sequence number in the witness payload AND in the on-chain cell state"]
fn sovereign_witness_sequence_pi_state_payload_must_agree() {
    panic!("blocked");
}

// ===========================================================================
// Composition: sovereign witness + slot caveats
// ===========================================================================

#[test]
fn sovereign_cell_slot_caveats_still_fire() {
    let (mut ledger, agent_id, sovereign_id, mut sovereign, signing_key, _) = sovereign_fixture(13);
    sovereign.program = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }]);
    sovereign.state.set_field(0, field_from_u64(10));
    let old_commitment = sovereign.state_commitment();
    ledger
        .update_sovereign_commitment(&sovereign_id, old_commitment)
        .unwrap();

    // The witness declares the REAL effects hash for this turn, so rule 7b
    // (`EffectsHashMismatch`) cannot be what rejects it — the Monotonic caveat
    // has to be. A fixture that fails the effects binding would "pass" a
    // rejection assertion while proving nothing about slot caveats at all.
    let witness = signed_sovereign_witness(
        &sovereign,
        &signing_key,
        old_commitment,
        set_field_effects_hash(agent_id, sovereign_id, 0, field_from_u64(9)),
        1,
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn_with_action_witnesses(
        agent_id,
        sovereign_id,
        witnesses,
        0,
        field_from_u64(9),
        vec![],
    );

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::ProgramViolation { .. },
                ..
            }
        ),
        "sovereign witness must not bypass Monotonic slot caveat, got: {result:?}"
    );
}

#[test]
fn sovereign_with_preimage_gate_requires_both_witnesses() {
    let (mut ledger, agent_id, sovereign_id, mut sovereign, signing_key, _) = sovereign_fixture(14);
    let preimage = [0x42; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    sovereign.program = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: dregg_cell::program::HashKind::Blake3,
    }]);
    let old_commitment = sovereign.state_commitment();
    ledger
        .update_sovereign_commitment(&sovereign_id, old_commitment)
        .unwrap();

    // Both turns apply SetField(0, commitment); the witness declares that
    // post-state (the commit path re-executes and verifies it).
    let new_commitment = post_set_field_commitment(&sovereign, 0, commitment);
    let witness = signed_sovereign_witness_with_new_commitment(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        set_field_effects_hash(agent_id, sovereign_id, 0, commitment),
        1,
    );
    let mut missing_preimage_witnesses = HashMap::new();
    missing_preimage_witnesses.insert(sovereign_id, witness.clone());
    let missing_preimage = set_field_turn_with_action_witnesses(
        agent_id,
        sovereign_id,
        missing_preimage_witnesses,
        0,
        commitment,
        vec![],
    );

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&missing_preimage, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::ProgramViolation { .. },
                ..
            }
        ),
        "sovereign witness alone must not satisfy PreimageGate, got: {result:?}"
    );

    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let mut with_preimage = set_field_turn_with_action_witnesses(
        agent_id,
        sovereign_id,
        witnesses,
        0,
        commitment,
        vec![WitnessBlob::preimage(preimage)],
    );
    with_preimage.nonce = 1;

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&with_preimage, &mut ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "sovereign witness plus PreimageGate witness should commit, got: {result:?}"
    );
}

// ===========================================================================
// Sovereign + cross-federation
// ===========================================================================

#[test]
fn sovereign_witness_cross_federation_replay_rejects() {
    let fed_a = [0xA1u8; 32];
    let fed_b = [0xB2u8; 32];
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(15);

    let msg_a = SovereignCellWitness::signing_message_for_federation(
        &fed_a,
        &sovereign_id,
        &old_commitment,
        &[0u8; 32],
        &[0u8; 32],
        0,
        1,
    );
    let msg_b = SovereignCellWitness::signing_message_for_federation(
        &fed_b,
        &sovereign_id,
        &old_commitment,
        &[0u8; 32],
        &[0u8; 32],
        0,
        1,
    );
    assert_ne!(
        msg_a, msg_b,
        "sovereign witness signing message must bind federation_id"
    );

    let witness = signed_sovereign_witness_for_federation(
        &fed_a,
        &sovereign,
        &signing_key,
        old_commitment,
        [0u8; 32],
        1,
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(fed_b);
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature invalid")
        ),
        "sovereign witness signed for fed A must reject at fed B, got: {result:?}"
    );
}

// ===========================================================================
// Sanity: Turn::hash covers the sovereign_witnesses field
// ===========================================================================

#[test]
fn sovereign_witnesses_field_is_covered_by_turn_hash() {
    let agent = CellId([1u8; 32]);

    let empty = turn_with_witnesses(agent, HashMap::new());

    // Construct a non-empty witness — bytes only need to differ from the
    // default for the hash check (we're NOT validating the witness's
    // signature here, only that Turn::hash sees the witness map).
    let cell_pk = [0xCA; 32];
    let cell = Cell::with_balance(cell_pk, [0u8; 32], 0);
    let cell_id = cell.id();
    let mut witnesses = HashMap::new();
    let w = SovereignCellWitness {
        cell_id,
        old_commitment: [0xAA; 32],
        new_commitment: [0xBB; 32],
        effects_hash: [0xCC; 32],
        timestamp: 0,
        sequence: 1,
        signature: [0xAB; 64],
        cell_state: cell,
        transition_proof: None,
    };
    witnesses.insert(cell_id, w);
    let with_witness = turn_with_witnesses(agent, witnesses);

    assert_ne!(
        empty.hash(),
        with_witness.hash(),
        "Turn::hash MUST cover sovereign_witnesses — see EXECUTOR-HONESTY-AUDIT.md T9 wire-malleability"
    );

    // SovereignCellWitness::signing_message must be a publicly callable
    // function so verifier-side replay can recompute the signing
    // message and reject witnesses whose payload was tampered.
    let msg = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0xCC; 32],
        0,
        1,
    );
    assert!(
        msg.starts_with(b"dregg-sovereign-witness-v1:"),
        "signing message must begin with the v1 domain separator"
    );
}

#[test]
fn turn_sovereign_witnesses_field_is_a_map_and_constructs_empty() {
    use dregg_turn::Turn;
    use std::collections::HashMap;
    let agent = CellId([1u8; 32]);
    let turn = Turn {
        agent,
        nonce: 0,
        call_forest: dregg_turn::CallForest::new(),
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    assert!(turn.sovereign_witnesses.is_empty());
}

// ===========================================================================
// Executor rules 7 & 8 — the fail-closed gates that had NO red-flag test
// (added 2026-07-16, lane 3).
//
// Every pre-existing witness in this file is built by
// `signed_sovereign_witness_with_new_commitment`, which (a) hard-codes
// `transition_proof: None` and (b) COERCES an all-zero `effects_hash` into a
// non-zero hash. So rules 7 and 8 in `turn/src/executor/execute.rs` — three
// unconditional `return TurnResult::Rejected` guards — were structurally
// UNTRIPPABLE through this suite: deleting any of them broke no test. These
// tests trip each one directly.
// ===========================================================================

/// A sovereign witness signed EXACTLY as the executor's rule-5 check demands,
/// with caller-chosen `new_commitment` / `effects_hash` passed through VERBATIM
/// (no zero-coercion) and an optional v1 `transition_proof` attached AFTER
/// signing.
///
/// Attaching post-signing is faithful to the threat: the canonical signing
/// message (`SovereignCellWitness::signing_message_for_federation`) does NOT
/// cover `transition_proof`, so a proof-bearing witness carries a fully VALID
/// signature. The proof field is wire-malleable; only rule 8 stops it.
fn raw_sovereign_witness(
    federation_id: &[u8; 32],
    cell: &Cell,
    signing_key: &SigningKey,
    old_commitment: [u8; 32],
    new_commitment: [u8; 32],
    effects_hash: [u8; 32],
    sequence: u64,
    transition_proof: Option<Vec<u8>>,
) -> SovereignCellWitness {
    let cell_id = cell.id();
    let timestamp = 0;
    let message = SovereignCellWitness::signing_message_for_federation(
        federation_id,
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: sign(signing_key, &message).0,
        cell_state: cell.clone(),
        transition_proof,
    }
}

/// SECURITY (executor rule 8, `execute.rs`): the v1 hand-AIR witness-STARK
/// verify is RETIRED, so a sovereign witness carrying a `transition_proof`
/// MUST fail closed on every build with `InvalidExecutionProof`.
///
/// This is the highest-blast-radius gate in the sovereign path: the witness is
/// otherwise PERFECT (correct old/new commitments, valid signature, correct
/// sequence) — the control leg below proves the identical witness COMMITS once
/// the proof is removed. So the ONLY thing standing between an unverified 4 KiB
/// proof blob and a committed sovereign transition is rule 8. If someone
/// "un-retires" the path by deleting the guard (or re-gates it behind a phantom
/// feature, as `cell-crypto::peer_exchange` had done), this test flags RED.
///
/// NB `dregg_turn::turn` still documents that a `Some` proof "is verified via
/// EffectVmAir" and lets the executor "verify in lieu of re-executing" — stale
/// prose describing a capability the code rejects outright. Named, not fixed.
#[test]
fn sovereign_witness_carrying_v1_transition_proof_fails_closed() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(3);
    let new_commitment = post_set_field_commitment(&sovereign, 0, [1u8; 32]);
    // The REAL effects hash: rule 7b runs BEFORE rule 8, so a witness that
    // failed the effects binding would be rejected as `EffectsHashMismatch` and
    // this test would "pass" a rejection assertion while never reaching the
    // guard it exists to hold.
    let effects_hash = set_field_effects_hash(agent_id, sovereign_id, 0, [1u8; 32]);

    let witness = raw_sovereign_witness(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        effects_hash,
        1,
        Some(vec![0u8; 4096]),
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    match &result {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(reason, TurnError::InvalidExecutionProof(_)),
            "a v1 transition_proof-bearing sovereign witness must be rejected with \
             InvalidExecutionProof, got: {reason:?}"
        ),
        other => panic!("expected Rejected (fail-closed), got: {other:?}"),
    }
    // The rejected turn must not have advanced the sovereign replay sequence.
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        0,
        "a fail-closed reject must not advance the sovereign replay sequence"
    );

    // CONTROL: the byte-identical witness WITHOUT the proof commits. This is what
    // makes the test BITE — it proves the rejection is caused by the proof field
    // alone, not by some unrelated defect in the fixture. Run against a FRESH
    // fixture: the rejected turn above still bumps the agent's nonce (reject-path
    // nonce charging), so replaying into the same ledger would trip NonceReplay
    // and mask what we are actually asserting.
    let (mut ledger2, agent2, sovereign2_id, sovereign2, key2, old2) = sovereign_fixture(3);
    let control = raw_sovereign_witness(
        &[0u8; 32],
        &sovereign2,
        &key2,
        old2,
        post_set_field_commitment(&sovereign2, 0, [1u8; 32]),
        effects_hash,
        1,
        None,
    );
    let mut control_witnesses = HashMap::new();
    control_witnesses.insert(sovereign2_id, control);
    let control_turn = set_field_turn(agent2, sovereign2_id, control_witnesses);
    let control_result =
        TurnExecutor::new(ComputronCosts::zero()).execute(&control_turn, &mut ledger2);
    assert!(
        matches!(&control_result, TurnResult::Committed { .. }),
        "control: the same witness without a v1 proof must commit, got: {control_result:?}"
    );
}

/// SECURITY (executor rule 7a, `execute.rs`): an all-zero `new_commitment` is a
/// legacy placeholder, NOT an explicit no-op commitment. A no-op sovereign
/// transition must still sign the real unchanged state commitment. Accepting the
/// zero sentinel would let a sovereign cell commit a transition to an
/// UNSPECIFIED post-state — the executor would have no declared post-state to
/// check its re-execution against.
#[test]
fn sovereign_witness_zero_new_commitment_placeholder_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(4);
    let effects_hash = *blake3::hash(b"dregg-sovereign-witness-empty-effects").as_bytes();

    // Signed correctly OVER the zero placeholder — so rules 2-6 all pass and
    // only rule 7 can reject this.
    let witness = raw_sovereign_witness(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        [0u8; 32],
        effects_hash,
        1,
        None,
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    match &result {
        TurnResult::Rejected { reason, .. } => {
            let msg = format!("{reason:?}");
            assert!(
                msg.contains("zero new_commitment"),
                "expected the rule-7 zero-new_commitment placeholder rejection, got: {msg}"
            );
        }
        other => panic!("a zero new_commitment placeholder must be rejected, got: {other:?}"),
    }
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        0,
        "a rejected placeholder witness must not advance the replay sequence"
    );
}

/// SECURITY (executor rule 7b, `execute.rs`): the all-zero `effects_hash` — the
/// legacy placeholder — must still be refused, and the interesting part is now
/// **what refuses it**.
///
/// This test used to assert a standalone `"zero effects_hash"` rejection string.
/// That string is GONE: rule 7b replaced the sentinel check with the BINDING
/// (`witness.effects_hash == turn.sovereign_effects_hash(cell)`), and
/// `execute.rs` states the reasoning — "Special-casing one wrong value implies
/// the others are fine, and that implication is exactly what this hole was made
/// of. The zero placeholder is still refused; it is refused by the rule that
/// binds." So the property is strictly stronger and the assertion follows it:
/// the placeholder is rejected AS an `EffectsHashMismatch`, and the reported
/// `got` is the placeholder itself.
///
/// Pinning `got` matters. Asserting only the variant would also pass if the
/// executor rejected some *other* witness field and happened to reuse the
/// variant; asserting `got == [0u8; 32]` says the rule looked at the value this
/// test supplied.
#[test]
fn sovereign_witness_zero_effects_hash_placeholder_rejects() {
    let (mut ledger, agent_id, sovereign_id, sovereign, signing_key, old_commitment) =
        sovereign_fixture(5);
    let new_commitment = post_set_field_commitment(&sovereign, 0, [1u8; 32]);

    let witness = raw_sovereign_witness(
        &[0u8; 32],
        &sovereign,
        &signing_key,
        old_commitment,
        new_commitment,
        [0u8; 32],
        1,
        None,
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(sovereign_id, witness);
    let turn = set_field_turn(agent_id, sovereign_id, witnesses);

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    match &result {
        TurnResult::Rejected {
            reason:
                TurnError::EffectsHashMismatch {
                    cell,
                    expected,
                    got,
                },
            ..
        } => {
            assert_eq!(
                *got, [0u8; 32],
                "the rejection must name the placeholder this test supplied"
            );
            assert_eq!(
                *expected,
                turn.sovereign_effects_hash(&sovereign_id),
                "the expected side must be the canonical per-cell hash of THIS turn"
            );
            assert_eq!(
                *cell, sovereign_id,
                "the error must name the witness that was wrong"
            );
        }
        other => panic!(
            "a zero effects_hash placeholder must be rejected by the rule-7b effects \
             binding, got: {other:?}"
        ),
    }
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&sovereign_id),
        0,
        "a rejected placeholder witness must not advance the replay sequence"
    );
}
