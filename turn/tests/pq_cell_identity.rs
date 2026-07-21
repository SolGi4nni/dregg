//! End-to-end canonical PQ cell enrollment and monotone rotation.
//!
//! These are hosted-executor tests: the live Cell commitment is the trust
//! anchor, while public keys and signatures remain untrusted turn bytes.

use std::collections::HashMap;

use dregg_cell::{Cell, CellId, Ledger, Preconditions, VerificationKey};
use dregg_turn::pq::{MlDsaTurnKey, cell_pq_creation_message, cell_pq_rotation_message};
use dregg_turn::{
    Action, Authorization, CallForest, CommitmentMode, ComputronCosts, DelegationMode, Effect,
    Turn, TurnExecutor, TurnResult,
};
use ed25519_dalek::{Signer, SigningKey};

const FEDERATION: [u8; 32] = [0x5a; 32];

fn hybrid_cell(seed: [u8; 32], token: [u8; 32], balance: i64) -> (Cell, SigningKey, MlDsaTurnKey) {
    let ed = SigningKey::from_bytes(&seed);
    let pq = MlDsaTurnKey::from_ed25519_seed(&seed);
    let cell = Cell::with_hybrid_balance(
        ed.verifying_key().to_bytes(),
        &pq.public_bytes(),
        token,
        balance,
    )
    .expect("valid ML-DSA key");
    (cell, ed, pq)
}

fn unsigned_action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: Vec::new(),
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: Vec::new(),
    }
}

fn hybrid_authorize(mut action: Action, ed: &SigningKey, pq: &MlDsaTurnKey, nonce: u64) -> Action {
    let message = TurnExecutor::compute_signing_message(&action, &FEDERATION, nonce);
    action.authorization = Authorization::HybridSignature {
        ed25519: ed.sign(&message).to_bytes(),
        ml_dsa: pq.sign(&message).expect("ML-DSA sign"),
        ml_dsa_pk: pq.public_bytes(),
    };
    action
}

fn turn(agent: CellId, nonce: u64, action: Action) -> Turn {
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);
    Turn {
        agent,
        nonce,
        fee: 0,
        memo: Some("canonical-pq-cell-identity".into()),
        valid_until: Some(i64::MAX / 2),
        call_forest,
        depends_on: Vec::new(),
        previous_receipt_hash: None,
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

#[test]
fn create_rotate_and_hostile_rollback_use_only_the_live_cell_anchor() {
    let (sponsor, sponsor_ed, sponsor_pq) = hybrid_cell([1u8; 32], [2u8; 32], 1_000_000);
    let sponsor_id = sponsor.id();
    let child_seed = [3u8; 32];
    let child_ed = SigningKey::from_bytes(&child_seed);
    let child_pq = MlDsaTurnKey::from_ed25519_seed(&child_seed);
    let child_token = [4u8; 32];
    let child_id = CellId::derive_raw(&child_ed.verifying_key().to_bytes(), &child_token);
    let creation_message = cell_pq_creation_message(
        child_id,
        &child_ed.verifying_key().to_bytes(),
        &child_token,
        &child_pq.public_bytes(),
    )
    .expect("creation transcript");
    let create = Effect::CreateHybridCell {
        public_key: child_ed.verifying_key().to_bytes(),
        token_id: child_token,
        balance: 0,
        ml_dsa_public_key: child_pq.public_bytes(),
        pq_possession_signature: child_pq.sign(&creation_message).expect("possession proof"),
    };

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(FEDERATION);
    executor.set_require_pq(true);
    assert!(executor.enrolled_pq_identity(&sponsor_id).is_none());
    let mut ledger = Ledger::new();
    ledger.insert_cell(sponsor).expect("sponsor insert");

    let create_action = hybrid_authorize(
        unsigned_action(sponsor_id, vec![create]),
        &sponsor_ed,
        &sponsor_pq,
        0,
    );
    assert!(matches!(
        executor.execute(&turn(sponsor_id, 0, create_action), &mut ledger),
        TurnResult::Committed { .. }
    ));
    let created = ledger.get(&child_id).expect("hybrid child created");
    assert_eq!(created.pq_identity().expect("identity anchor").key_epoch, 0);
    assert!(executor.enrolled_pq_identity(&child_id).is_none());

    let next_pq = MlDsaTurnKey::from_ed25519_seed(&[5u8; 32]);
    let rotation_message = cell_pq_rotation_message(
        child_id,
        child_ed.verifying_key().as_bytes(),
        0,
        &next_pq.public_bytes(),
    )
    .expect("rotation transcript");
    let rotate = Effect::RotatePqIdentity {
        cell: child_id,
        expected_epoch: 0,
        new_ml_dsa_public_key: next_pq.public_bytes(),
        new_key_possession_signature: next_pq
            .sign(&rotation_message)
            .expect("new-key possession proof"),
    };
    let rotate_action = hybrid_authorize(
        unsigned_action(child_id, vec![rotate]),
        &child_ed,
        &child_pq,
        0,
    );
    assert!(matches!(
        executor.execute(&turn(child_id, 0, rotate_action), &mut ledger),
        TurnResult::Committed { .. }
    ));
    let after_rotation = ledger.get(&child_id).expect("child survives rotation");
    assert_eq!(after_rotation.pq_identity().unwrap().key_epoch, 1);
    let epoch1_identity = after_rotation.pq_identity().cloned().unwrap();
    let epoch1_nonce = after_rotation.state.nonce();

    // Rotate first, then fail the following authority effect. The turn-level
    // undo journal must restore both the key anchor and the agent nonce.
    let third_pq = MlDsaTurnKey::from_ed25519_seed(&[6u8; 32]);
    let third_message = cell_pq_rotation_message(
        child_id,
        child_ed.verifying_key().as_bytes(),
        1,
        &third_pq.public_bytes(),
    )
    .expect("third-key transcript");
    let rotate_again = Effect::RotatePqIdentity {
        cell: child_id,
        expected_epoch: 1,
        new_ml_dsa_public_key: third_pq.public_bytes(),
        new_key_possession_signature: third_pq.sign(&third_message).expect("third-key possession"),
    };
    #[allow(deprecated)]
    let invalid_vk = VerificationKey::from_parts([0x11; 32], vec![0x22]);
    let fail_after_rotation = Effect::SetVerificationKey {
        cell: child_id,
        new_vk: Some(invalid_vk),
    };
    let hostile_action = hybrid_authorize(
        unsigned_action(child_id, vec![rotate_again, fail_after_rotation]),
        &child_ed,
        &next_pq,
        epoch1_nonce,
    );
    assert!(matches!(
        executor.execute(&turn(child_id, epoch1_nonce, hostile_action), &mut ledger),
        TurnResult::Rejected { .. }
    ));
    let rolled_back = ledger.get(&child_id).expect("child remains");
    assert_eq!(rolled_back.pq_identity(), Some(&epoch1_identity));
    assert_eq!(rolled_back.state.nonce(), epoch1_nonce);

    // A stale epoch cannot roll the anchor backward, even when both the current
    // action authorization and the proposed key's possession proof are valid.
    let stale_message = cell_pq_rotation_message(
        child_id,
        child_ed.verifying_key().as_bytes(),
        0,
        &third_pq.public_bytes(),
    )
    .expect("stale transcript is structurally valid");
    let stale = Effect::RotatePqIdentity {
        cell: child_id,
        expected_epoch: 0,
        new_ml_dsa_public_key: third_pq.public_bytes(),
        new_key_possession_signature: third_pq.sign(&stale_message).expect("stale possession"),
    };
    let stale_action = hybrid_authorize(
        unsigned_action(child_id, vec![stale]),
        &child_ed,
        &next_pq,
        epoch1_nonce,
    );
    assert!(matches!(
        executor.execute(&turn(child_id, epoch1_nonce, stale_action), &mut ledger),
        TurnResult::Rejected { .. }
    ));
    let after_stale = ledger.get(&child_id).expect("child remains");
    assert_eq!(after_stale.pq_identity(), Some(&epoch1_identity));
    assert_eq!(after_stale.state.nonce(), epoch1_nonce);
}
