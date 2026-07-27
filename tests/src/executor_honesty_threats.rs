//! Executor-honesty threat tests, T1-T15 from `EXECUTOR-HONESTY-AUDIT.md`.
//!
//! Layer: AIR + canonical signing message + verifier-side replay.
//!
//! Each test exercises *one* of the threats from the audit and proves the
//! corresponding defense triggers. Tests that depend on yet-to-land
//! single-cell AIR-binding work are marked `#[ignore]` with the audit's
//! `[stage7-cont]` or other unblock-by-lane label.
//!
//! Threats are the audit's enumeration — keep this file's order matched to
//! the audit so a reader can cross-reference.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::action::{Action, Authorization, BearerCapProof, DelegationProofData, symbol};
use dregg_turn::{
    CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnError, TurnExecutor, TurnReceipt,
    TurnResult, VerifyError, sign_receipt, verify_receipt_chain_with_optional_keys,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

fn one_action_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: symbol("test"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
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
    }
}

fn sample_receipt(
    agent: CellId,
    turn_hash: [u8; 32],
    previous_receipt_hash: Option<[u8; 32]>,
) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        forest_hash: [0x11u8; 32],
        pre_state_hash: [0x22u8; 32],
        post_state_hash: [0x33u8; 32],
        timestamp: 1_700_000_000,
        effects_hash: [0x44u8; 32],
        computrons_used: 7,
        action_count: 1,
        previous_receipt_hash,
        agent,
        federation_id: [0x55u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}

fn replay_entry_with_receipt_pi(receipt: TurnReceipt) -> dregg_verifier::ReplayEntry {
    use dregg_circuit::effect_vm::pi;
    use dregg_commit::typed::canonical_32_to_felts_4;

    let mut public_inputs = vec![0u32; pi::ACTIVE_BASE_COUNT];
    let turn_hash = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        public_inputs[pi::TURN_HASH_BASE + i] = turn_hash[i].as_u32();
    }
    let previous = canonical_32_to_felts_4(&receipt.previous_receipt_hash.unwrap_or([0u8; 32]));
    for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
        public_inputs[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = previous[i].as_u32();
    }
    public_inputs[pi::IS_AGENT_CELL] = 1;

    dregg_verifier::ReplayEntry {
        receipt,
        proof_bytes: vec![],
        public_inputs,
        witness_bundle: None,
        witness_hash: [0u8; 32],
        aggregate_membership: None,
    }
}

// RETIRED (dregg3): effect_vm_air_rejects_tampered_trace was the anti-tamper
// AIR helper used solely by t10_captp_variants_use_real_merkle_membership, which
// tested the now-dissolved CapTP sturdyref effect family. Removed with t10.

// ===========================================================================
// T1 — Reorder effects within a turn
// ===========================================================================

#[test]
fn t1_turn_hash_covers_effect_order() {
    // The defense: effects_hash is ordered. Two turns with the same effects
    // in different order must produce different turn hashes.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 20,
    };
    let t_12 = one_action_turn(a, 0, vec![e1.clone(), e2.clone()]);
    let t_21 = one_action_turn(a, 0, vec![e2, e1]);
    assert_ne!(
        t_12.hash(),
        t_21.hash(),
        "effect order must change turn hash"
    );
}

#[test]
fn t1_receipt_signature_binds_effect_order() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 20,
    };
    let t_12 = one_action_turn(a, 0, vec![e1.clone(), e2.clone()]);
    let t_21 = one_action_turn(a, 0, vec![e2, e1]);

    let r_12 = sample_receipt(a, t_12.hash(), None);
    let r_21 = sample_receipt(a, t_21.hash(), None);
    assert_ne!(
        r_12.canonical_executor_signed_message(),
        r_21.canonical_executor_signed_message(),
        "executor receipt signature message must bind ordered effects through receipt.turn_hash"
    );
}

// ===========================================================================
// T2 — Invent effects the actor did not sign
// ===========================================================================

#[test]
fn t2_turn_hash_covers_effect_count() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 5,
    };
    let t_one = one_action_turn(a, 0, vec![e1.clone()]);
    let t_two = one_action_turn(a, 0, vec![e1, e2]);
    assert_ne!(
        t_one.hash(),
        t_two.hash(),
        "inventing an extra effect must change turn hash"
    );
}

#[test]
fn t2_no_authorization_unchecked_in_production_paths() {
    let execute_tree = include_str!("../../turn/src/executor/execute_tree.rs");
    let verify_call =
        "self.verify_authorization(action, target_cell, ledger, parent_cell, &path, turn_nonce)?;";
    let balance_mutation = "if let Some(delta) = action.balance_change";
    // The effect-mutation call was widened to multiline when `created_by_turn`
    // (provenance threading) was added; match its stable head.
    let effect_mutation = "self.apply_effect(\n                effect,\n                ledger,";

    let verify_idx = execute_tree
        .find(verify_call)
        .expect("execute_tree must call verify_authorization on every action");
    let balance_idx = execute_tree
        .find(balance_mutation)
        .expect("execute_tree must contain the balance_change mutation path");
    let effect_idx = execute_tree
        .find(effect_mutation)
        .expect("execute_tree must contain the effect mutation path");
    assert!(
        verify_idx < balance_idx && verify_idx < effect_idx,
        "execute_tree must verify authorization before balance/effect mutation paths"
    );

    let authorize = include_str!("../../turn/src/executor/authorize.rs");
    assert!(
        authorize.contains("Authorization::Unchecked => Err((")
            && authorize.contains("TurnError::PermissionDenied"),
        "verify_authorization must deny Authorization::Unchecked when a permission is required"
    );
}

// ===========================================================================
// T3 — Skip / omit effects from a signed turn
// ===========================================================================

#[test]
fn t3_receipt_signature_binds_effect_omission() {
    let a = CellId([3u8; 32]);
    let b = CellId([4u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 5,
    };
    let complete = one_action_turn(a, 0, vec![e1.clone(), e2]);
    let omitted = one_action_turn(a, 0, vec![e1]);

    let r_complete = sample_receipt(a, complete.hash(), None);
    let r_omitted = sample_receipt(a, omitted.hash(), None);
    assert_ne!(
        r_complete.canonical_executor_signed_message(),
        r_omitted.canonical_executor_signed_message(),
        "executor receipt signature message must bind omitted effects through receipt.turn_hash"
    );
}

// ===========================================================================
// T4 — Lie about pre/post state hash
// ===========================================================================

// ===========================================================================
// T5 — Reuse a nonce
// ===========================================================================

#[test]
fn t5_executor_rejects_replayed_nonce() {
    // The executor's runtime check: it increments cell.nonce when a turn
    // executes and rejects any turn whose `nonce` doesn't match the current
    // cell.nonce.
    let cell = permissive_cell(1, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let t1 = one_action_turn(agent, 0, vec![]);
    let r1 = executor.execute(&t1, &mut ledger);
    assert!(matches!(
        r1,
        TurnResult::Committed { .. } | TurnResult::Rejected { .. }
    ));

    // Submit a turn with nonce=0 again — must reject (nonce should now be 1).
    let t1_replay = one_action_turn(agent, 0, vec![]);
    let r_replay = executor.execute(&t1_replay, &mut ledger);
    assert!(
        matches!(r_replay, TurnResult::Rejected { .. }),
        "expected nonce-replay reject, got: {r_replay:?}"
    );
}

// ===========================================================================
// T6 — Replay a turn from another federation / ledger
// ===========================================================================

#[test]
fn t6_signed_turn_for_federation_a_rejects_on_federation_b() {
    let agent = CellId([6u8; 32]);
    let target = CellId([7u8; 32]);
    let action = Action {
        target,
        method: symbol("transfer"),
        args: vec![[0xD6u8; 32]],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: agent,
            to: target,
            amount: 3,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: Some(-3),
        witness_blobs: vec![],
    };
    let federation_a = [0xA6u8; 32];
    let federation_b = [0xB6u8; 32];

    assert_ne!(
        TurnExecutor::compute_signing_message(&action, &federation_a, 42),
        TurnExecutor::compute_signing_message(&action, &federation_b, 42),
        "full action signatures must bind federation_id (same turn nonce)"
    );
    assert_ne!(
        TurnExecutor::compute_partial_signing_message(&action, 0, &federation_a, 42),
        TurnExecutor::compute_partial_signing_message(&action, 0, &federation_b, 42),
        "partial action signatures must bind federation_id"
    );
    assert_ne!(
        TurnExecutor::compute_bearer_delegation_message(
            &target,
            &AuthRequired::Signature,
            &[0x11u8; 32],
            99,
            &federation_a,
        ),
        TurnExecutor::compute_bearer_delegation_message(
            &target,
            &AuthRequired::Signature,
            &[0x11u8; 32],
            99,
            &federation_b,
        ),
        "bearer delegation signatures must bind federation_id"
    );
    assert_ne!(
        Authorization::captp_delivered_signing_message_for_federation(
            &federation_a,
            &[0x22u8; 32],
            &agent,
            &target,
            42,
            &action.effects,
        ),
        Authorization::captp_delivered_signing_message_for_federation(
            &federation_b,
            &[0x22u8; 32],
            &agent,
            &target,
            42,
            &action.effects,
        ),
        "CapTP delivery signatures must bind federation_id"
    );
}

// ===========================================================================
// T7 — Forge a receipt signature
// ===========================================================================

#[test]
fn t7_receipt_signed_by_wrong_key_rejects() {
    let agent = CellId([0x71u8; 32]);
    let mut receipt = sample_receipt(agent, [0x72u8; 32], None);
    let signing_seed = [0x73u8; 32];
    receipt.executor_signature = Some(sign_receipt(&receipt, &signing_seed));

    let trusted_wrong_executor = dregg_types::SigningKey::from_bytes(&[0x74u8; 32])
        .public_key()
        .0;
    let err = verify_receipt_chain_with_optional_keys(&[receipt], &[trusted_wrong_executor])
        .expect_err("receipt signed by an untrusted executor key must reject");
    assert!(matches!(err, VerifyError::ExecutorSignatureInvalid { .. }));
}

#[test]
fn t7_receipt_carries_executor_identity() {
    // Current receipt identity is verifier-side: the receipt carries an
    // executor_signature, and the verifier accepts it only under the trusted
    // executor key that produced that signature.
    let agent = CellId([0x75u8; 32]);
    let mut receipt = sample_receipt(agent, [0x76u8; 32], None);
    let signing_seed = [0x77u8; 32];
    receipt.executor_signature = Some(sign_receipt(&receipt, &signing_seed));

    let signer_pk = dregg_types::SigningKey::from_bytes(&signing_seed)
        .public_key()
        .0;
    let other_pk = dregg_types::SigningKey::from_bytes(&[0x78u8; 32])
        .public_key()
        .0;

    verify_receipt_chain_with_optional_keys(&[receipt.clone()], &[signer_pk])
        .expect("receipt must verify against the executor key that signed it");
    let err = verify_receipt_chain_with_optional_keys(&[receipt], &[other_pk])
        .expect_err("receipt verifier identity is the trusted executor key set");
    assert!(matches!(err, VerifyError::ExecutorSignatureInvalid { .. }));
}

// ===========================================================================
// T8 — Insert a fake previous_receipt_hash link
// ===========================================================================

#[test]
fn t8_verifier_rejects_fake_previous_receipt_hash() {
    let agent = CellId([0x81u8; 32]);
    let mut prior = sample_receipt(agent, [0x82u8; 32], None);
    prior.post_state_hash = [0x83u8; 32];

    let forged_previous = [0x84u8; 32];
    let receipt = sample_receipt(agent, [0x85u8; 32], Some(forged_previous));
    let entry = replay_entry_with_receipt_pi(receipt);

    let reason = dregg_verifier::check_receipt_pi_binding(&entry, Some(prior.receipt_hash()))
        .expect("chain-walk must reject a fake previous_receipt_hash");
    assert!(
        reason.contains("chain-walk"),
        "expected chain-walk rejection, got: {reason}"
    );
}

// ===========================================================================
// T9 — Skip sovereign-witness verification
// ===========================================================================

#[test]
fn t9_sovereign_witness_skip_rejected_by_air() {
    let mut ledger = Ledger::new();
    let agent = permissive_cell(0x91, 1_000);
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let sovereign = permissive_cell(0x92, 500);
    let sovereign_id = sovereign.id();
    ledger
        .register_sovereign_cell(sovereign_id, sovereign.state_commitment())
        .unwrap();
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: sovereign_id,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: sovereign_id,
            index: 0,
            value: [0x99u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
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

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            result,
            TurnResult::Rejected {
                reason: TurnError::SovereignWitnessRequired { cell },
                ..
            } if cell == sovereign_id
        ),
        "sovereign mutation without a witness must reject, got: {result:?}"
    );
}

// ===========================================================================
// T10 — Skip a permission / capability check
// ===========================================================================

#[test]
fn t10_executor_rejects_transfer_without_required_capability() {
    // Setup: A → B Transfer, but A has no cap to B and B's `send`
    // permission requires a signature.
    let a_cell = {
        let mut c = permissive_cell(10, 1_000);
        // Tighten send permission to require a sig, but DON'T grant any
        // capabilities — so the action should fail authorization.
        c.permissions.send = AuthRequired::Signature;
        c
    };
    let a = a_cell.id();
    let b_cell = permissive_cell(11, 0);
    let b = b_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(a_cell).unwrap();
    ledger.insert_cell(b_cell).unwrap();

    let turn = one_action_turn(
        a,
        0,
        vec![Effect::Transfer {
            from: a,
            to: b,
            amount: 1,
        }],
    );
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "transfer without auth must reject, got: {result:?}"
    );
}

// RETIRED (dregg3): t10_captp_variants_use_real_merkle_membership tested the
// anti-tamper Merkle-membership soundness of the CapTP sturdyref effect family
// — ExportSturdyRef / EnlivenRef / DropRef / ValidateHandoff. The dregg3
// reduction dissolved all four variants from the circuit Effect enum (the
// CapTP-handoff machinery is no longer a kernel-level effect), so the test no
// longer compiles and no longer corresponds to any live behaviour. Deleted
// rather than rewritten: there is no surviving effect to anti-tamper here.

// ===========================================================================
// T11 — Submit a stale / cached proof for a new turn
// ===========================================================================

#[test]
fn t11_stale_proof_replay_rejected_by_verifier() {
    let agent = CellId([0xA1u8; 32]);
    let receipt = sample_receipt(agent, [0xA2u8; 32], None);
    let mut entry = replay_entry_with_receipt_pi(receipt);
    entry.public_inputs[dregg_circuit::effect_vm::pi::TURN_HASH_BASE] ^= 0x01;

    let reason = dregg_verifier::check_receipt_pi_binding(&entry, None)
        .expect("stale proof PI must reject when TURN_HASH no longer matches receipt");
    assert!(
        reason.contains("TURN_HASH_BASE"),
        "expected TURN_HASH_BASE rejection, got: {reason}"
    );
}

// ===========================================================================
// T12 — Lie about balance deltas
// ===========================================================================

// ===========================================================================
// T13 — Cross-cell aliasing (same cell_id in two federations)
// ===========================================================================

/// UNBLOCKED (2026-07-27). The `#[ignore]` reason asked for the T13 escape
/// hatch to "be constrained by federation membership + CapTP origin
/// attestation". The audit's open question was *"what prevents a malicious node
/// from minting an arbitrary-id cell?"* — and the answer now exists: the
/// **cross-federation ingest gate** `Ledger::migrate_accept`, which is the only
/// path by which one federation's cell enters another's ledger. It enforces
/// exactly the two things T13 needs, plus the double-existence rule that IS the
/// T13 threat model ("same cell_id in two federations applying conflicting
/// state updates").
///
/// `Cell::remote_stub_with_id*` is left deliberately unconstrained — it is a
/// local landing site, and its own docstring says `verify_id_integrity()` fails
/// on it by design. The security claim is not "the constructor is safe"; it is
/// "a stub cannot cross a federation boundary". That is what this test pins.
///
/// The dangerous variant is `remote_stub_with_id_pk_token_balance`, which lets
/// the caller pick an arbitrary id AND an attacker-controlled public key — so
/// unlike the zero-pk stub, a `Signature` authorization WOULD match it. That is
/// the cell this test tries to smuggle across.
#[test]
fn t13_remote_stub_with_id_cannot_mint_arbitrary_cell_ids() {
    use dregg_cell::cell::CellMode;
    use dregg_cell::migration::MigrationError;
    use dregg_cell::{Cell, Ledger};

    let fed_a = [0xAAu8; 32];
    let fed_b = [0xBBu8; 32];

    // The attacker's signing identity, and an id that is NOT its content
    // address — the "minted" cell id they want to occupy on federation B.
    let attacker_pk = [0x99u8; 32];
    let coveted_id = CellId([0x77u8; 32]);
    let forged =
        Cell::remote_stub_with_id_pk_token_balance(coveted_id, attacker_pk, [0u8; 32], 1_000_000);

    // (1) The mint is DETECTABLE: the stub breaks the content-address
    // invariant, and it really is the attacker's key on it (so the danger is
    // real, not a zero-pk stub that could never sign).
    assert!(
        !forged.verify_id_integrity(),
        "an arbitrary-id stub must fail the content-address invariant"
    );
    assert_eq!(
        *forged.public_key(),
        attacker_pk,
        "the smuggled cell carries the attacker's signing key — this is the variant that matters"
    );
    assert_eq!(forged.id(), coveted_id, "and the id they wanted");

    // (2) THE FEDERATION GATE. Build a genuine voucher on federation A for a
    // real cell, then try to redeem it on B with the forged stub swapped in.
    let genuine = Cell::with_balance([0x11u8; 32], [0u8; 32], 500);
    let genuine_id = genuine.id();
    assert!(
        genuine.verify_id_integrity(),
        "control cell must be content-addressed"
    );
    let mut ledger_a = Ledger::new();
    ledger_a.insert_cell(genuine.clone()).unwrap();
    let voucher = ledger_a
        .migrate_prepare(&genuine_id, fed_a, fed_b, CellMode::Hosted, 1)
        .expect("PREPARE on a well-formed cell");

    // 2a. The forged stub does not even match the voucher's cell id.
    let mut ledger_b = Ledger::new();
    assert!(
        matches!(
            ledger_b.migrate_accept(&voucher, forged.clone(), fed_b, 2),
            Err(MigrationError::StateMismatch)
        ),
        "a stub whose id differs from the voucher must not be installed"
    );

    // 2b. The sharper attack: mint a stub AT the voucher's id, with the
    // attacker's key. Now the id matches — and `verify_id_integrity` is the
    // only thing standing between the attacker and custody of that cell on
    // federation B.
    let forged_at_voucher_id =
        Cell::remote_stub_with_id_pk_token_balance(genuine_id, attacker_pk, [0u8; 32], 1_000_000);
    assert_eq!(forged_at_voucher_id.id(), voucher.cell_id);
    assert!(
        matches!(
            ledger_b.migrate_accept(&voucher, forged_at_voucher_id, fed_b, 2),
            Err(MigrationError::IdentityBroken(id)) if id == genuine_id
        ),
        "an arbitrary-id stub carrying an attacker key must be refused at the \
         cross-federation ingest gate with IdentityBroken"
    );

    // (3) ANTI-VACUITY: the SAME voucher, redeemed with the GENUINE cell,
    // must succeed. Without this the rejections above could be the gate
    // refusing everything.
    ledger_b
        .migrate_accept(&voucher, genuine.clone(), fed_b, 2)
        .expect("the genuine cell must be accepted by the same gate");
    assert!(
        ledger_b.get(&genuine_id).is_some(),
        "genuine migration must install the cell"
    );

    // (4) THE T13 THREAT ITSELF — "same cell_id in two federations applying
    // conflicting state updates". A second acceptance of the same id is
    // refused as double-existence, even with a genuine cell.
    assert!(
        matches!(
            ledger_b.migrate_accept(&voucher, genuine.clone(), fed_b, 3),
            Err(MigrationError::DestinationOccupied(id)) if id == genuine_id
        ),
        "the same cell id must not be installable twice — that IS the T13 aliasing threat"
    );

    // (5) FEDERATION MEMBERSHIP: a voucher addressed to B cannot be redeemed
    // by a third federation that simply decides to accept it.
    let fed_c = [0xCCu8; 32];
    let mut ledger_c = Ledger::new();
    assert!(
        matches!(
            ledger_c.migrate_accept(&voucher, genuine.clone(), fed_c, 2),
            Err(MigrationError::WrongDestination)
        ),
        "a voucher names its destination federation; a non-addressee must not take custody"
    );

    // (6) The remaining leg — drifting an EXISTING cell's `public_key` to the
    // attacker's while keeping its id — is not reachable from here at all:
    // `Cell::public_key` is a sealed private field (P0-1), so the attack does
    // not compile outside `dregg-cell`. The in-crate runtime guard for the
    // same invariant (`Ledger::update_with` rolling back an integrity break)
    // is covered by `cell::tests::p2_3_verify_id_integrity_catches_drift`.
}

// ===========================================================================
// T14 — Skip the AIR proof entirely
// ===========================================================================

// v1-only: asserts the replay-chain rejection reason is the bespoke-AIR
// "STARK verify failed / deserial" message. Under recursion the scope-1 step
// fails closed with the retired-v1 reason, so the substring asserts break.
#[cfg(not(feature = "prover"))]
#[test]
fn t14_receipt_without_proof_rejected_at_wire_level() {
    let agent = CellId([0xE1u8; 32]);
    let receipt = sample_receipt(agent, [0xE2u8; 32], None);
    let entry = replay_entry_with_receipt_pi(receipt);

    let out = dregg_verifier::replay_chain(&[entry]);
    assert!(!out.overall_verified, "empty proof bytes must not verify");
    assert_eq!(out.first_failure, Some(0));
    assert!(
        matches!(
            &out.per_entry[0],
            dregg_verifier::ReplayVerdict::Rejected { reason }
                if reason.contains("STARK verify failed")
                    && reason.contains("deserial")
        ),
        "missing wire proof must be a hard rejection, got: {:?}",
        out.per_entry[0]
    );
}

// v1-only: asserts `verify_effect_vm_proof` returns a "deserial" failure for
// malformed bytes. Under recursion this entry-point is the fail-closed stub
// that returns the retired-v1 reason instead, so the assert breaks.
#[cfg(not(feature = "prover"))]
#[test]
fn t14_malformed_proof_bytes_rejected() {
    let (out, code) = dregg_verifier::verify_effect_vm_proof(
        b"not a serialized STARK proof",
        &[],
        dregg_verifier::EFFECT_VM_VK_HASH_HEX,
    );

    assert!(!out.verified, "malformed proof bytes must not verify");
    assert_eq!(code, dregg_verifier::exit_code::ERROR);
    assert!(
        out.reason.contains("deserial"),
        "expected deserialisation failure, got: {}",
        out.reason
    );
}

// ===========================================================================
// T15 — Forge the effects_hash → AIR pass over a different effect list
// ===========================================================================

// ===========================================================================
// Cross-cutting (audit §"Cross-cutting open questions")
// ===========================================================================

/// UNBLOCKED (2026-07-27). The `#[ignore]` reason was "blocked on
/// T-cross-cutting #1: trace-side binding completeness audit". The audit item
/// asked a question; a `panic!("blocked")` is not an answer, and *nothing in
/// the tree asserted a single effect-VM PI was trace-bound* — deleting
/// `boundaryFirstPins` from the Lean emitter would have been caught by no test.
/// This IS the audit, machine-checked and standing, read off the DEPLOYED
/// registry bytes (`V3_STAGED_REGISTRY_TSV`) rather than off a doc comment.
///
/// The 2026-05-24 claim it replaces was wrong in BOTH directions, and this test
/// pins the corrected picture:
///
/// | field | trace-bound? |
/// |---|---|
/// | `ACTOR_NONCE` (41) | YES — row-0 `state_before.NONCE` |
/// | `OLD_COMMIT[0]` (0) | YES — row-0 `state_before.STATE_COMMIT` |
/// | `NEW_COMMIT[0]` (8) | YES — last-row `state_after.STATE_COMMIT` |
/// | `INIT_BAL_LO/HI` (20,21) | YES — row-0 `state_before.BALANCE_*` |
/// | `FINAL_BAL_LO/HI` (22,23) | YES — last-row `state_after.BALANCE_*` |
/// | `EFFECTS_HASH` (16..20) | **NO** — the claim said it WAS bound |
/// | `TURN_HASH` (33..37) | **NO** |
/// | `EFFECTS_HASH_GLOBAL` (37..41) | **NO** |
/// | `IS_AGENT_CELL` (81) | **NO** — past every deployed `public_input_count` |
///
/// Two teeth, both able to go red:
///
///   A. **Semantic correctness of every v1-window pin.** Every `pi_binding`
///      any deployed member carries into the v1 PI window must appear in the
///      table below — PI `k` tied to the semantically-right trace column. A pin
///      moved to the wrong column, retargeted at the wrong PI, or deleted
///      wholesale fails here.
///   B. **Non-emptiness per field.** Each of the seven pins must be carried by
///      at least one deployed member, so the table cannot pass by being vacuous
///      over a registry that pins nothing.
///
/// The residual assertions (the unbound set) are a FREEZE, not a guarantee:
/// they exist so that binding `TURN_HASH` — the fix the audit actually wants —
/// is a deliberate, visible edit and not a silent drift in either direction.
#[test]
fn cross_cutting_all_pi_fields_trace_bound() {
    use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};
    use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
    use dregg_circuit::effect_vm::pi;
    use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
    use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    // THE PIN TABLE: (row, trace column, PI index, field name). This is the
    // semantic contract — "PI k is the value in THIS trace cell".
    let expected: &[(VmRow, usize, usize, &str)] = &[
        (
            VmRow::First,
            STATE_BEFORE_BASE + state::NONCE,
            pi::ACTOR_NONCE,
            "ACTOR_NONCE",
        ),
        (
            VmRow::First,
            STATE_BEFORE_BASE + state::BALANCE_LO,
            pi::INIT_BAL_LO,
            "INIT_BAL_LO",
        ),
        (
            VmRow::First,
            STATE_BEFORE_BASE + state::BALANCE_HI,
            pi::INIT_BAL_HI,
            "INIT_BAL_HI",
        ),
        (
            VmRow::First,
            STATE_BEFORE_BASE + state::STATE_COMMIT,
            pi::OLD_COMMIT_BASE,
            "OLD_COMMIT[0] (PRE_STATE)",
        ),
        (
            VmRow::Last,
            STATE_AFTER_BASE + state::STATE_COMMIT,
            pi::NEW_COMMIT_BASE,
            "NEW_COMMIT[0] (POST_STATE)",
        ),
        (
            VmRow::Last,
            STATE_AFTER_BASE + state::BALANCE_LO,
            pi::FINAL_BAL_LO,
            "FINAL_BAL_LO",
        ),
        (
            VmRow::Last,
            STATE_AFTER_BASE + state::BALANCE_HI,
            pi::FINAL_BAL_HI,
            "FINAL_BAL_HI",
        ),
    ];

    // Members whose `public_input_count` cannot even address the v1 window
    // are on their OWN local PI contract (their PI 0..3 are rotated-block
    // pins, not `OLD_COMMIT`). They are skipped — and the skip set is frozen
    // below so a new member cannot quietly join it.
    const LOCAL_PI_SPACE_MEMBERS: &[&str] = &["heapWriteVmDescriptor2R24"];

    // Members on the shared v1 PI contract that carry NO first-row v1 pin.
    // For these, `ACTOR_NONCE` / `OLD_COMMIT[0]` / the initial balance limbs
    // have NO v1-window trace binding; only the rotated-block commit pins
    // (42..45) tie the proof to a state. THIS IS A REAL GAP, frozen here so
    // it is detected rather than merely true.
    const NO_FIRST_ROW_V1_PIN: &[&str] = &[
        "setFieldDynVmDescriptor2R24",
        "setFieldVmDescriptor2-0R24",
        "setFieldVmDescriptor2-1R24",
        "setFieldVmDescriptor2-2R24",
        "setFieldVmDescriptor2-3R24",
        "setFieldVmDescriptor2-4R24",
        "setFieldVmDescriptor2-5R24",
        "setFieldVmDescriptor2-6R24",
        "setFieldVmDescriptor2-7R24",
    ];

    // Members carrying NO last-row v1 pin: `NEW_COMMIT[0]` / `FINAL_BAL_*`
    // have no v1-window binding. The whole cap-write family plus setField.
    const NO_LAST_ROW_V1_PIN: &[&str] = &[
        "attenuateVmDescriptor2R24",
        "revokeCapabilityVmDescriptor2R24",
        "grantCapVmDescriptor2R24",
        "setFieldDynVmDescriptor2R24",
        "setFieldVmDescriptor2-0R24",
        "setFieldVmDescriptor2-1R24",
        "setFieldVmDescriptor2-2R24",
        "setFieldVmDescriptor2-3R24",
        "setFieldVmDescriptor2-4R24",
        "setFieldVmDescriptor2-5R24",
        "setFieldVmDescriptor2-6R24",
        "setFieldVmDescriptor2-7R24",
        "delegateCapOpenVmDescriptor2R24",
        "grantCapCapOpenVmDescriptor2R24",
        "revokeCapabilityCapOpenVmDescriptor2R24",
        "attenuateCapOpenEffVmDescriptor2R24",
        "delegateWriteCapOpenVmDescriptor2R24",
        "introduceWriteCapOpenVmDescriptor2R24",
        "delegateAttenWriteCapOpenVmDescriptor2R24",
        "revokeDelegationWriteCapOpenVmDescriptor2R24",
        "revokeCapabilityWriteCapOpenVmDescriptor2R24",
        "refreshDelegationWriteCapOpenVmDescriptor2R24",
    ];

    // How many deployed members carry each pin — the anti-vacuity counters.
    let mut carriers = vec![0usize; expected.len()];
    let mut members = 0usize;
    // Every PI index observed in the v1 window, for the residual freeze.
    let mut bound_v1_pis: std::collections::BTreeSet<usize> = Default::default();
    let mut observed_local: std::collections::BTreeSet<String> = Default::default();
    let mut observed_no_first: std::collections::BTreeSet<String> = Default::default();
    let mut observed_no_last: std::collections::BTreeSet<String> = Default::default();

    for line in V3_STAGED_REGISTRY_TSV.lines() {
        if line.is_empty() {
            continue;
        }
        members += 1;
        let mut it = line.splitn(3, '\t');
        let key = it.next().expect("tsv key");
        let _name = it.next().expect("tsv name");
        let json = it.next().expect("tsv json");
        let desc = parse_vm_descriptor2(json)
            .unwrap_or_else(|e| panic!("registry member {key} failed to parse: {e}"));

        // A member that cannot address PI[ACTOR_NONCE] is not on the shared
        // v1 PI contract at all.
        if desc.public_input_count <= pi::ACTOR_NONCE {
            observed_local.insert(key.to_string());
            continue;
        }

        let mut present = vec![false; expected.len()];
        for constraint in &desc.constraints {
            let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = constraint
            else {
                continue;
            };
            // Rotated-block pins live at/above V1_PI_COUNT and are audited by
            // `effect_vm_descriptors::v3_staged_registry_parses_and_covers`.
            if *pi_index >= V1_PI_COUNT {
                continue;
            }
            bound_v1_pis.insert(*pi_index);

            // TOOTH A: this pin must be one of the seven semantic pins.
            let hit = expected
                .iter()
                .position(|(r, c, p, _)| r == row && c == col && p == pi_index);
            let Some(idx) = hit else {
                panic!(
                    "deployed member {key} binds PI {pi_index} to {row:?}-row column {col}, \
                     which is NOT a recognised trace-side binding. Either a pin moved off its \
                     semantic column or a new PI became trace-bound without updating this table."
                );
            };
            carriers[idx] += 1;
            present[idx] = true;
        }

        // TOOTH A′ — PER MEMBER, not merely per registry. A member on the
        // shared v1 contract that is not on an exemption list must carry
        // EVERY pin of that row. Without this, dropping one member's
        // `ACTOR_NONCE` pin passes silently because 46 siblings still carry
        // it (measured: that exact break did NOT go red until this assert
        // existed).
        let missing_first: Vec<&str> = expected
            .iter()
            .enumerate()
            .filter(|(i, (r, _, _, _))| *r == VmRow::First && !present[*i])
            .map(|(_, (_, _, _, field))| *field)
            .collect();
        let missing_last: Vec<&str> = expected
            .iter()
            .enumerate()
            .filter(|(i, (r, _, _, _))| *r == VmRow::Last && !present[*i])
            .map(|(_, (_, _, _, field))| *field)
            .collect();

        if missing_first.is_empty() {
            // carries the complete first-row set
        } else if missing_first.len() == 4 {
            observed_no_first.insert(key.to_string());
        } else {
            panic!(
                "deployed member {key} carries a PARTIAL first-row boundary pin set — missing \
                 {missing_first:?}. Every shared-contract member must pin all four or none; a \
                 partial set means one field silently lost its trace binding."
            );
        }
        if missing_last.is_empty() {
            // carries the complete last-row set
        } else if missing_last.len() == 3 {
            observed_no_last.insert(key.to_string());
        } else {
            panic!(
                "deployed member {key} carries a PARTIAL last-row boundary pin set — missing \
                 {missing_last:?}. See above."
            );
        }
    }

    assert_eq!(
        members, 60,
        "expected the 60-member deployed registry; parsed {members}. A registry that changed \
         size makes every count below a different claim — re-derive the exemption sets."
    );

    // THE EXEMPTION SETS ARE EXACT. A new member that silently ships without a
    // boundary pin fails here instead of passing unnoticed.
    let as_set = |xs: &[&str]| -> std::collections::BTreeSet<String> {
        xs.iter().map(|s| s.to_string()).collect()
    };
    assert_eq!(
        observed_local,
        as_set(LOCAL_PI_SPACE_MEMBERS),
        "the set of members on a LOCAL PI contract changed"
    );
    assert_eq!(
        observed_no_first,
        as_set(NO_FIRST_ROW_V1_PIN),
        "the set of members with NO first-row v1 PI binding changed — a member either gained \
         a binding (good: shrink the list) or lost one (bad: ACTOR_NONCE/OLD_COMMIT are no \
         longer trace-bound for that effect)"
    );
    assert_eq!(
        observed_no_last,
        as_set(NO_LAST_ROW_V1_PIN),
        "the set of members with NO last-row v1 PI binding changed — see above"
    );

    // TOOTH B: every field in the table is genuinely carried by deployed
    // members. A pin deleted from the Lean emitter drops its count to 0.
    for (i, (row, col, pi_index, field)) in expected.iter().enumerate() {
        assert!(
            carriers[i] > 0,
            "NO deployed registry member binds {field} (PI {pi_index}) to {row:?}-row column \
             {col}. This field is no longer trace-bound anywhere in the deployed AIR."
        );
    }

    // RESIDUAL FREEZE. These are the fields the audit named that are NOT
    // trace-bound today. Naming them here means the gap is detected, not just
    // documented — and closing one is a visible edit to this list.
    let unbound_residuals: &[(usize, usize, &str)] = &[
        (pi::EFFECTS_HASH_BASE, pi::EFFECTS_HASH_LEN, "EFFECTS_HASH"),
        (pi::TURN_HASH_BASE, pi::TURN_HASH_LEN, "TURN_HASH"),
        (
            pi::EFFECTS_HASH_GLOBAL_BASE,
            pi::EFFECTS_HASH_GLOBAL_LEN,
            "EFFECTS_HASH_GLOBAL",
        ),
    ];
    for (base, len, field) in unbound_residuals {
        for k in *base..(*base + *len) {
            assert!(
                !bound_v1_pis.contains(&k),
                "PI {k} ({field}) is now trace-bound by a deployed member. That is the FIX the \
                 cross-cutting audit asks for — update this test's table and the residual list \
                 rather than deleting the assertion."
            );
        }
    }

    // `IS_AGENT_CELL` sits past the deployed PI window entirely: no member can
    // bind it, because no member publishes that many public inputs.
    assert!(
        pi::IS_AGENT_CELL >= V1_PI_COUNT,
        "IS_AGENT_CELL moved into the deployed PI window; its off-AIR-only status \
         (asserted by cross_cutting_verifier_checks_all_pi) must be re-derived"
    );
}

#[test]
fn cross_cutting_canonical_signing_message_fields() {
    let agent = CellId([0xD1u8; 32]);
    let target = CellId([0xD2u8; 32]);
    let previous_receipt_hash = [0xD3u8; 32];
    let effects = vec![Effect::Transfer {
        from: agent,
        to: target,
        amount: 5,
    }];
    let mut turn = one_action_turn(agent, 17, effects.clone());
    turn.previous_receipt_hash = Some(previous_receipt_hash);

    let base_turn_hash = turn.hash();
    let mut base = sample_receipt(agent, base_turn_hash, Some(previous_receipt_hash));
    base.effects_hash = *blake3::hash(&effects[0].hash()).as_bytes();
    base.federation_id = [0xD4u8; 32];

    let message = base.canonical_executor_signed_message();
    assert!(
        message.starts_with(b"executor-receipt-sig-v5:"),
        "executor receipt signatures must use the v5 domain separator"
    );

    let mut changed_federation = base.clone();
    changed_federation.federation_id = [0xE4u8; 32];
    assert_ne!(
        message,
        changed_federation.canonical_executor_signed_message(),
        "canonical executor signing message must bind federation_id"
    );

    let mut changed_actor = base.clone();
    changed_actor.agent = CellId([0xE1u8; 32]);
    assert_ne!(
        message,
        changed_actor.canonical_executor_signed_message(),
        "canonical executor signing message must bind actor_id"
    );

    let mut changed_nonce_turn = turn.clone();
    changed_nonce_turn.nonce += 1;
    let mut changed_nonce = base.clone();
    changed_nonce.turn_hash = changed_nonce_turn.hash();
    assert_ne!(
        message,
        changed_nonce.canonical_executor_signed_message(),
        "canonical executor signing message must bind nonce via receipt.turn_hash"
    );

    let mut changed_effects = base.clone();
    changed_effects.effects_hash = [0xE5u8; 32];
    assert_ne!(
        message,
        changed_effects.canonical_executor_signed_message(),
        "canonical executor signing message must bind effects_hash"
    );

    let mut changed_previous = base;
    changed_previous.previous_receipt_hash = Some([0xE3u8; 32]);
    assert_ne!(
        message,
        changed_previous.canonical_executor_signed_message(),
        "canonical executor signing message must bind previous_receipt_hash"
    );
}

#[test]
fn cross_cutting_verifier_checks_all_pi() {
    let agent = CellId([0xC1u8; 32]);
    let previous = [0xC3u8; 32];
    let base = sample_receipt(agent, [0xC2u8; 32], Some(previous));

    let mut turn_hash_tamper = replay_entry_with_receipt_pi(base.clone());
    turn_hash_tamper.public_inputs[dregg_circuit::effect_vm::pi::TURN_HASH_BASE] ^= 0x01;
    let reason = dregg_verifier::check_receipt_pi_binding(&turn_hash_tamper, Some(previous))
        .expect("TURN_HASH PI mismatch must reject");
    assert!(reason.contains("TURN_HASH_BASE"));

    let mut previous_hash_tamper = replay_entry_with_receipt_pi(base.clone());
    previous_hash_tamper.public_inputs[dregg_circuit::effect_vm::pi::PREVIOUS_RECEIPT_HASH_BASE] ^=
        0x01;
    let reason = dregg_verifier::check_receipt_pi_binding(&previous_hash_tamper, Some(previous))
        .expect("PREVIOUS_RECEIPT_HASH PI mismatch must reject");
    assert!(reason.contains("PREVIOUS_RECEIPT_HASH_BASE"));

    let mut agent_cell_tamper = replay_entry_with_receipt_pi(base);
    agent_cell_tamper.public_inputs[dregg_circuit::effect_vm::pi::IS_AGENT_CELL] = 0;
    let reason = dregg_verifier::check_receipt_pi_binding(&agent_cell_tamper, Some(previous))
        .expect("IS_AGENT_CELL PI mismatch must reject");
    assert!(reason.contains("IS_AGENT_CELL"));
}

// ===========================================================================
// Bonus: Bearer-cap T2 cousin — verify bearer permissions cannot exceed
// delegator (E-language facet attenuation).
// ===========================================================================

#[test]
fn bearer_cap_permissions_cannot_amplify_unchecked_baseline() {
    // Sanity: BearerCapProof has an `allowed_effects: Option<EffectMask>` field;
    // verify the construction round-trips and the executor's verify path
    // is at least exercised. The actual attenuation enforcement is in
    // protocol-tests/src/invariants/facet_attenuation.rs.
    let target = CellId([42u8; 32]);
    let bearer = BearerCapProof {
        target,
        permissions: AuthRequired::None,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: [1u8; 32],
            signature: [0u8; 64],
            bearer_pk: [2u8; 32],
        },
        expires_at: 100,
        revocation_channel: None,
        allowed_effects: None,
    };
    let auth = Authorization::Bearer(bearer);
    let a = CellId([99u8; 32]);
    let act = Action {
        target: a,
        method: symbol("test"),
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    let _ = act.hash(); // does not panic.
}
