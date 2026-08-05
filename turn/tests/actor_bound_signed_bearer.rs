//! Signed bearer delegation is authority for one concrete acting identity.
//! A valid delegation to Bob cannot be replayed in a turn whose actor is Mallory.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, DelegationProofData,
    symbol,
};
use dregg_turn::{CallForest, CallTree, ComputronCosts, Effect, Turn, TurnError, TurnExecutor};
use dregg_types::{SigningKey, sign};

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

fn actor(seed: u8) -> (SigningKey, Cell) {
    let key = SigningKey::from_bytes(&[seed; 32]);
    let mut cell = Cell::with_balance(key.public_key().0, [0u8; 32], 1_000);
    cell.permissions = open_permissions();
    (key, cell)
}

fn turn(actor: dregg_cell::CellId, target: dregg_cell::CellId, proof: BearerCapProof) -> Turn {
    let action = Action {
        target,
        method: symbol("actor-bound-bearer"),
        args: vec![],
        authorization: Authorization::Bearer(proof),
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: 0,
            value: [0x42; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    Turn {
        agent: actor,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree::new(action)],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

#[test]
fn signed_bearer_admits_its_named_actor_and_refuses_actor_substitution() {
    let (delegator_key, mut delegator) = actor(10);
    let (bob_key, bob) = actor(11);
    let (_mallory_key, mallory) = actor(12);
    let mut target = Cell::with_balance([13u8; 32], [0u8; 32], 500);
    target.permissions = open_permissions();
    let target_id = target.id();
    delegator
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("delegator holds the target capability");
    let bob_id = bob.id();
    let mallory_id = mallory.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(delegator).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(mallory).unwrap();
    ledger.insert_cell(target).unwrap();

    let expires_at = 1_000;
    let message = TurnExecutor::compute_bearer_delegation_message(
        &target_id,
        &AuthRequired::None,
        &bob_key.public_key().0,
        expires_at,
        &[0u8; 32],
    );
    let signature = sign(&delegator_key, &message).0;
    let proof = BearerCapProof {
        target: target_id,
        permissions: AuthRequired::None,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: delegator_key.public_key().0,
            signature,
            bearer_pk: bob_key.public_key().0,
        },
        expires_at,
        revocation_channel: None,
        allowed_effects: None,
    };

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let honest = executor.execute(&turn(bob_id, target_id, proof.clone()), &mut ledger.clone());
    assert!(
        honest.is_committed(),
        "delegation exercised by its named bearer must commit: {honest:?}"
    );

    let substituted = executor.execute(&turn(mallory_id, target_id, proof), &mut ledger);
    match substituted {
        dregg_turn::TurnResult::Rejected {
            reason: TurnError::BearerCapInvalidProof { reason, .. },
            ..
        } => assert!(
            reason.contains("bearer_pk does not match the acting cell public key"),
            "wrong refusal: {reason}"
        ),
        other => {
            panic!("a delegation issued to Bob must not authorize Mallory's actor cell: {other:?}")
        }
    }
}
