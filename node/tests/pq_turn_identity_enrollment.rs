//! Native-PQ Turn identity enrollment at the node boundary.
//!
//! A required-PQ executor must derive its ML-DSA trust anchor from the canonical
//! live Cell, never from the authorization it is about to verify. Pre-v10 cells
//! may use an independently configured host enrollment as a migration bridge;
//! it is not TOFU and never overrides a Cell-committed identity. These tests pin
//! durable restart, that migration bridge, and hostile carried-key substitution.

use std::collections::HashMap;

use dregg_cell::{Cell, Ledger, Preconditions};
use dregg_node::executor_setup::new_submit_executor;
use dregg_node::state::NodeState;
use dregg_node::{
    install_mldsa_verified_keygen_core_real, install_mldsa_verified_sign_core_real,
    install_mldsa_verified_verify_core,
};
use dregg_turn::pq::MlDsaTurnKey;
use dregg_turn::{
    Action, Authorization, CallForest, CommitmentMode, ComputronCosts, DelegationMode, Effect,
    Turn, TurnError, TurnExecutor, TurnResult,
};
use ed25519_dalek::{Signer, SigningKey};

fn install_mldsa_runtime() {
    let _ = install_mldsa_verified_keygen_core_real();
    let _ = install_mldsa_verified_sign_core_real();
    let _ = install_mldsa_verified_verify_core();

    let verified_cores_installed = dregg_pq::lean_keygen_core_real_installed()
        && dregg_pq::lean_sign_core_real_installed()
        && dregg_pq::lean_verify_core_real_installed();
    if std::env::var("DREGG_REQUIRE_PQ_CORES").as_deref() == Ok("1") {
        assert!(
            verified_cores_installed,
            "DREGG_REQUIRE_PQ_CORES=1 requires all verified ML-DSA cores"
        );
    } else if !verified_cores_installed {
        assert!(
            matches!(
                std::env::var("DREGG_ALLOW_UNAUDITED_PQ").as_deref(),
                Ok("1")
            ),
            "an explicit test-only fallback opt-in is required when the verified cores are absent"
        );
    }
}

#[tokio::test]
async fn committed_cell_pq_identity_survives_checkpoint_restart() {
    install_mldsa_runtime();
    let dir = tempfile::tempdir().expect("tempdir");
    let seed = [0x2d; 32];
    let ed = SigningKey::from_bytes(&seed).verifying_key().to_bytes();
    let pq = MlDsaTurnKey::from_ed25519_seed(&seed);
    let mut cell = Cell::with_hybrid_balance(ed, &pq.public_bytes(), [0x91; 32], 123)
        .expect("valid canonical identity");
    let rotated = MlDsaTurnKey::from_ed25519_seed(&[0x3e; 32]);
    cell.rotate_pq_identity(0, &rotated.public_bytes())
        .expect("rotate before checkpoint");
    let cell_id = cell.id();
    let expected_identity = cell.pq_identity().cloned().unwrap();
    let expected_commitment = cell.state_commitment();

    {
        let state = NodeState::new(dir.path(), Vec::new()).expect("node state");
        let mut inner = state.write().await;
        inner.ledger.insert_cell(cell).expect("insert bound cell");
        inner
            .store
            .checkpoint_ledger(&inner.ledger, 17)
            .expect("durable checkpoint");
    }

    let restarted = NodeState::new(dir.path(), Vec::new()).expect("restart node state");
    let inner = restarted.read().await;
    let recovered = inner.ledger.get(&cell_id).expect("cell recovered");
    assert_eq!(recovered.pq_identity(), Some(&expected_identity));
    assert_eq!(recovered.state_commitment(), expected_commitment);
}

#[tokio::test]
async fn submit_executor_enrolls_host_known_targets_but_not_unknown_wire_identity() {
    // Production sets DREGG_REQUIRE_PQ_CORES=1 and this helper pins that exact
    // verified-runtime posture. A marshal-only build may run the same wiring
    // test only with the repository's explicit unaudited test opt-in.
    install_mldsa_runtime();

    let dir = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(dir.path(), Vec::new()).expect("node state");

    let (
        local_cell_id,
        local_ed25519,
        local_epoch,
        expected_local_ml_dsa,
        member_cell_id,
        member_ed25519,
        expected_member_ml_dsa,
        foreign_cell_id,
    ) = {
        let mut s = state.write().await;
        let local_seed = s.cclerk.gossip_signing_key().to_bytes();
        let local_ed25519 = s.cclerk.public_key().0;
        let mut local = Cell::new(local_ed25519, [0x51; 32]);
        local.state.set_delegation_epoch(7);
        let local_cell_id = local.id();
        s.ledger.insert_cell(local).expect("insert local target");

        let member_seed = [0x74; 32];
        let member_ed25519 = SigningKey::from_bytes(&member_seed)
            .verifying_key()
            .to_bytes();
        let expected_member_ml_dsa = MlDsaTurnKey::from_ed25519_seed(&member_seed).public_bytes();
        let member_ml_dsa = dregg_federation::frost::MlDsaPublicKey(
            expected_member_ml_dsa
                .clone()
                .try_into()
                .expect("fixed-size ML-DSA public key"),
        );
        s.set_federation_keys_hybrid(
            vec![dregg_types::PublicKey(member_ed25519)],
            vec![member_ml_dsa],
        );
        let mut member = Cell::new(member_ed25519, [0x53; 32]);
        member.state.set_delegation_epoch(9);
        let member_cell_id = member.id();
        s.ledger
            .insert_cell(member)
            .expect("insert configured member target");

        let foreign_ed25519 = SigningKey::from_bytes(&[0x92; 32])
            .verifying_key()
            .to_bytes();
        let foreign = Cell::new(foreign_ed25519, [0x52; 32]);
        let foreign_cell_id = foreign.id();
        s.ledger
            .insert_cell(foreign)
            .expect("insert foreign target");

        (
            local_cell_id,
            local_ed25519,
            7,
            MlDsaTurnKey::from_ed25519_seed(&local_seed).public_bytes(),
            member_cell_id,
            member_ed25519,
            expected_member_ml_dsa,
            foreign_cell_id,
        )
    };

    let executor = {
        let s = state.read().await;
        new_submit_executor(&s)
    };
    assert!(
        executor.require_pq(),
        "node admission defaults to native/required PQ"
    );

    let enrolled = executor
        .enrolled_pq_identity(&local_cell_id)
        .expect("locally owned target must be independently enrolled");
    assert_eq!(enrolled.target_ed25519, local_ed25519);
    assert_eq!(enrolled.epoch, local_epoch);
    assert_eq!(enrolled.public_key, expected_local_ml_dsa);

    let member_enrolled = executor
        .enrolled_pq_identity(&member_cell_id)
        .expect("configured federation-member target must be independently enrolled");
    assert_eq!(member_enrolled.target_ed25519, member_ed25519);
    assert_eq!(member_enrolled.epoch, 9);
    assert_eq!(member_enrolled.public_key, expected_member_ml_dsa);

    assert!(
        executor.enrolled_pq_identity(&foreign_cell_id).is_none(),
        "an unknown external cell must not be enrolled from self-carried/wire key material"
    );
}

/// The concrete Shor-projection attack: the attacker can produce a victim-valid
/// Ed25519 half, and produces a genuinely valid ML-DSA signature under its own
/// key.  The old self-carried-key rule accepted this pair.  Native Turn
/// authorization must reject it before any effect commits.
#[test]
fn required_pq_rejects_forged_ed25519_plus_attacker_owned_valid_ml_dsa() {
    install_mldsa_runtime();

    let victim_seed = [0x31; 32];
    let attacker_seed = [0xa4; 32];
    let victim_ed = SigningKey::from_bytes(&victim_seed);
    let victim_pq = MlDsaTurnKey::from_ed25519_seed(&victim_seed);
    let target = Cell::with_hybrid_balance(
        victim_ed.verifying_key().to_bytes(),
        &victim_pq.public_bytes(),
        [0x61; 32],
        100,
    )
    .expect("valid canonical ML-DSA key");
    let target_id = target.id();
    let fed = [0x71; 32];

    let unsigned = Action {
        target: target_id,
        method: [0; 32],
        args: Vec::new(),
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0xcc; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: Vec::new(),
    };
    let message = TurnExecutor::compute_signing_message(&unsigned, &fed, 0);
    // This is the classical ability a quantum attacker gains.
    let forged_ed25519 = victim_ed.sign(&message).to_bytes();
    // This half is not malformed or byte-flipped: it is a valid signature under
    // the attacker's own ML-DSA key, exactly the former substitution attack.
    let attacker_pq = MlDsaTurnKey::from_ed25519_seed(&attacker_seed);
    let attacker_ml_dsa = attacker_pq.sign(&message).expect("verified ML-DSA sign");
    let action = Action {
        authorization: Authorization::HybridSignature {
            ed25519: forged_ed25519,
            ml_dsa: attacker_ml_dsa,
            ml_dsa_pk: attacker_pq.public_bytes(),
        },
        ..unsigned
    };

    let mut forest = CallForest::new();
    forest.add_root(action);
    let turn = Turn {
        agent: target_id,
        nonce: 0,
        fee: 0,
        memo: Some("hostile-pq-key-substitution".to_string()),
        valid_until: Some(i64::MAX / 2),
        call_forest: forest,
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
    };

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(fed);
    executor.set_require_pq(true);
    assert!(executor.enrolled_pq_identity(&target_id).is_none());

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).expect("target insert");
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidAuthorization { reason },
                ..
            } if reason.contains("does not match the target cell's committed identity")
        ),
        "attacker-owned valid ML-DSA key must not authenticate the victim target: {result:?}"
    );
    assert_eq!(
        ledger.get(&target_id).expect("target remains").state.fields[0],
        [0u8; 32],
        "the hostile action must commit no state"
    );
}
