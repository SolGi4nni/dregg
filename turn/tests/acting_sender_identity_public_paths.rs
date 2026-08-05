//! Public-entry-point regression tests for `InputRef::Sender` identity.
//!
//! A signature is evidence *from* a sender, not the sender's identity.  In
//! particular, neither the first half of `Authorization::Signature` nor the
//! first 32 bytes of `HybridSignature::ed25519` is a public key.  These tests
//! install a real app-defined witnessed-predicate verifier and drive both live
//! executor surfaces to pin the value resolved for `InputRef::Sender`:
//!
//! - an ordinary root action sees the turn agent cell's public key;
//! - a mixed-atomic hosted action sees `MixedAtomicTurn::agent`'s cell key;
//! - a nested action sees its immediate parent cell's key; and
//! - an absent acting cell fails closed before predicate dispatch.
//!
//! Each positive pole carries deliberately permissive target permissions so
//! adversarial signature-shaped bytes can pass the unrelated authorization
//! lattice.  Its paired hostile pole configures the verifier to accept exactly
//! those decoy bytes.  A correct executor rejects that pole because it still
//! dispatches the acting cell's key.

use std::sync::{Arc, Mutex};

use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, Ledger, Permissions, Preconditions, StateConstraint,
};
use dregg_turn::action::{Action, Authorization, DelegationMode, Effect, WitnessBlob};
use dregg_turn::{CallForest, ComputronCosts, MixedAtomicTurn, Turn, TurnExecutor};

const VK_HASH: [u8; 32] = [0x91; 32];
const COMMITMENT: [u8; 32] = [0xC7; 32];
const PROOF: &[u8] = b"poa:sender-identity-proof-v1";

const ACTOR_KEY: [u8; 32] = [0xA1; 32];
const TARGET_KEY: [u8; 32] = [0xB2; 32];
const SIGNATURE_PREFIX: [u8; 32] = [0x51; 32];
const HYBRID_PREFIX: [u8; 32] = [0x61; 32];

#[derive(Clone)]
struct ExactSenderVerifier {
    expected: [u8; 32],
    seen: Arc<Mutex<Vec<[u8; 32]>>>,
}

impl WitnessedPredicateVerifier for ExactSenderVerifier {
    fn name(&self) -> &'static str {
        "public-path-exact-sender"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom { vk_hash: VK_HASH }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &COMMITMENT {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "commitment mismatch".into(),
            });
        }
        if proof_bytes != PROOF {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "proof mismatch".into(),
            });
        }

        let PredicateInput::Sender(sender) = input else {
            return Err(WitnessedPredicateError::InputShapeMismatch {
                kind_name: self.name(),
                expected: "Sender",
                actual: "non-Sender",
            });
        };
        self.seen.lock().unwrap().push(**sender);

        if **sender == self.expected {
            Ok(())
        } else {
            Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "resolved sender was not the expected acting cell".into(),
            })
        }
    }
}

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

fn open_cell(public_key: [u8; 32], balance: i64) -> Cell {
    let mut cell = Cell::with_balance(public_key, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn ledger_with_actor_and_target() -> (Ledger, CellId, CellId) {
    let target = open_cell(TARGET_KEY, 0);
    let target_id = target.id();
    let mut actor = open_cell(ACTOR_KEY, 1_000);
    actor
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("fixture actor can receive target capability");
    let actor_id = actor.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();
    (ledger, actor_id, target_id)
}

fn executor_expecting(expected: [u8; 32]) -> (TurnExecutor, Arc<Mutex<Vec<[u8; 32]>>>) {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        VK_HASH,
        Arc::new(ExactSenderVerifier {
            expected,
            seen: seen.clone(),
        }),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_witnessed_registry(registry);
    (executor, seen)
}

fn sender_precondition() -> Preconditions {
    Preconditions {
        witnessed: vec![WitnessedPredicate::custom(
            VK_HASH,
            COMMITMENT,
            InputRef::Sender,
            0,
        )],
        ..Default::default()
    }
}

fn action(target: CellId, authorization: Authorization, field: u64) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization,
        preconditions: sender_precondition(),
        effects: vec![Effect::SetField {
            cell: target,
            index: field,
            value: [0xD4; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![WitnessBlob::proof(PROOF.to_vec())],
    }
}

fn plain_set_field_action(target: CellId, field: u64, value: [u8; 32]) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: field,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn ledger_with_programmed_target(program: CellProgram) -> (Ledger, CellId, CellId) {
    let mut target = open_cell(TARGET_KEY, 0);
    target.program = program;
    let target_id = target.id();

    let mut actor = open_cell(ACTOR_KEY, 1_000);
    actor
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("fixture actor can receive target capability");
    let actor_id = actor.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();
    (ledger, actor_id, target_id)
}

fn turn(agent: CellId, roots: impl IntoIterator<Item = Action>) -> Turn {
    let mut forest = CallForest::new();
    for root in roots {
        forest.add_root(root);
    }
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
fn ordinary_root_sender_is_agent_cell_key_and_never_signature_prefix() {
    let signature = Authorization::Signature(SIGNATURE_PREFIX, [0x52; 32]);

    let (mut ledger, actor_id, target_id) = ledger_with_actor_and_target();
    let (executor, seen) = executor_expecting(ACTOR_KEY);
    let result = executor.execute(
        &turn(actor_id, [action(target_id, signature.clone(), 0)]),
        &mut ledger,
    );
    assert!(
        result.is_committed(),
        "actor-bound pole must commit: {result:?}"
    );
    assert_eq!(*seen.lock().unwrap(), vec![ACTOR_KEY]);
    assert_ne!(ACTOR_KEY, SIGNATURE_PREFIX);

    let (mut ledger, actor_id, target_id) = ledger_with_actor_and_target();
    let (executor, seen) = executor_expecting(SIGNATURE_PREFIX);
    let result = executor.execute(
        &turn(actor_id, [action(target_id, signature, 0)]),
        &mut ledger,
    );
    assert!(
        result.is_rejected(),
        "signature bytes must not satisfy an InputRef::Sender predicate: {result:?}"
    );
    assert_eq!(*seen.lock().unwrap(), vec![ACTOR_KEY]);
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0u8; 32]);
}

#[test]
fn mixed_atomic_sender_is_agent_cell_key_and_never_hybrid_signature_prefix() {
    let mut ed25519 = [0x62; 64];
    ed25519[..32].copy_from_slice(&HYBRID_PREFIX);
    let hybrid = Authorization::HybridSignature {
        ed25519,
        ml_dsa: vec![],
        ml_dsa_pk: vec![],
    };

    let (mut ledger, actor_id, target_id) = ledger_with_actor_and_target();
    let (executor, seen) = executor_expecting(ACTOR_KEY);
    let mixed = MixedAtomicTurn {
        agent: actor_id,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![action(target_id, hybrid.clone(), 0)],
    };
    let result = executor.execute_mixed_atomic(&mixed, &mut ledger);
    assert!(
        result.is_ok(),
        "actor-bound mixed pole must commit: {result:?}"
    );
    assert_eq!(*seen.lock().unwrap(), vec![ACTOR_KEY]);
    assert_ne!(ACTOR_KEY, HYBRID_PREFIX);

    let (mut ledger, actor_id, target_id) = ledger_with_actor_and_target();
    let (executor, seen) = executor_expecting(HYBRID_PREFIX);
    let mixed = MixedAtomicTurn {
        agent: actor_id,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![action(target_id, hybrid, 0)],
    };
    let result = executor.execute_mixed_atomic(&mixed, &mut ledger);
    assert!(
        result.is_err(),
        "hybrid signature bytes must not satisfy InputRef::Sender: {result:?}"
    );
    assert_eq!(*seen.lock().unwrap(), vec![ACTOR_KEY]);
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0u8; 32]);
}

#[test]
fn nested_sender_is_immediate_parent_cell_key_not_child_signature_prefix() {
    fn nested_turn(agent: CellId, target: CellId, child_auth: Authorization) -> Turn {
        let root = Action {
            target,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let child = action(target, child_auth, 1);
        let mut forest = CallForest::new();
        forest.add_root(root).add_child(child);
        let mut built = turn(agent, []);
        built.call_forest = forest;
        built
    }

    let child_auth = Authorization::Signature(SIGNATURE_PREFIX, [0x53; 32]);

    let (mut ledger, actor_id, target_id) = ledger_with_actor_and_target();
    let (executor, seen) = executor_expecting(TARGET_KEY);
    let result = executor.execute(
        &nested_turn(actor_id, target_id, child_auth.clone()),
        &mut ledger,
    );
    assert!(
        result.is_committed(),
        "child must receive its immediate parent cell identity: {result:?}"
    );
    assert_eq!(*seen.lock().unwrap(), vec![TARGET_KEY]);

    let (mut ledger, actor_id, target_id) = ledger_with_actor_and_target();
    let (executor, seen) = executor_expecting(SIGNATURE_PREFIX);
    let result = executor.execute(&nested_turn(actor_id, target_id, child_auth), &mut ledger);
    assert!(
        result.is_rejected(),
        "child signature bytes must not replace the parent cell identity: {result:?}"
    );
    assert_eq!(*seen.lock().unwrap(), vec![TARGET_KEY]);
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[1], [0u8; 32]);
}

#[test]
fn missing_acting_cell_fails_closed_before_sender_predicate_dispatch() {
    let target = open_cell(TARGET_KEY, 0);
    let target_id = target.id();
    let missing_actor = CellId::from_bytes([0xEE; 32]);

    let mut ordinary_ledger = Ledger::new();
    ordinary_ledger.insert_cell(target.clone()).unwrap();
    let (ordinary_executor, ordinary_seen) = executor_expecting(ACTOR_KEY);
    let result = ordinary_executor.execute(
        &turn(
            missing_actor,
            [action(target_id, Authorization::Unchecked, 0)],
        ),
        &mut ordinary_ledger,
    );
    assert!(result.is_rejected(), "missing ordinary actor must reject");
    assert!(ordinary_seen.lock().unwrap().is_empty());

    let mut mixed_ledger = Ledger::new();
    mixed_ledger.insert_cell(target).unwrap();
    let (mixed_executor, mixed_seen) = executor_expecting(ACTOR_KEY);
    let mixed = MixedAtomicTurn {
        agent: missing_actor,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![action(target_id, Authorization::Unchecked, 0)],
    };
    let result = mixed_executor.execute_mixed_atomic(&mixed, &mut mixed_ledger);
    assert!(result.is_err(), "missing mixed-atomic actor must reject");
    assert!(mixed_seen.lock().unwrap().is_empty());
    assert_eq!(
        mixed_ledger.get(&target_id).unwrap().state.fields[0],
        [0u8; 32]
    );
}

#[test]
fn mixed_atomic_cannot_bypass_a_touched_cells_immutable_program() {
    let (mut ledger, actor_id, target_id) =
        ledger_with_programmed_target(CellProgram::Predicate(vec![StateConstraint::Immutable {
            index: 0,
        }]));
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mixed = MixedAtomicTurn {
        agent: actor_id,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![plain_set_field_action(target_id, 0, [0xD5; 32])],
    };

    let result = executor.execute_mixed_atomic(&mixed, &mut ledger);
    assert!(
        result.is_err(),
        "mixed-atomic hosted effects must not bypass perpetual CellPrograms: {result:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0u8; 32]);
    assert_eq!(ledger.get(&actor_id).unwrap().state.nonce(), 0);
}

#[test]
fn mixed_atomic_rate_debits_are_staged_and_rollback_with_the_ledger() {
    let (mut ledger, actor_id, target_id) =
        ledger_with_programmed_target(CellProgram::Predicate(vec![StateConstraint::RateLimit {
            max_per_epoch: 1,
            epoch_duration: 100,
        }]));
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let over_limit = MixedAtomicTurn {
        agent: actor_id,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![
            plain_set_field_action(target_id, 0, [0xD6; 32]),
            plain_set_field_action(target_id, 1, [0xD7; 32]),
        ],
    };

    let result = executor.execute_mixed_atomic(&over_limit, &mut ledger);
    assert!(
        result.is_err(),
        "a second same-epoch action must exceed max_per_epoch=1: {result:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0u8; 32]);
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[1], [0u8; 32]);
    assert_eq!(ledger.get(&actor_id).unwrap().state.nonce(), 0);

    // The refused turn must not leave a phantom debit in executor state.  The
    // same first action, with the still-current nonce, remains admissible.
    let retry = MixedAtomicTurn {
        agent: actor_id,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![plain_set_field_action(target_id, 0, [0xD6; 32])],
    };
    let result = executor.execute_mixed_atomic(&retry, &mut ledger);
    assert!(
        result.is_ok(),
        "rollback must discard the refused turn's staged rate debit: {result:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0xD6; 32]);
    assert_eq!(ledger.get(&actor_id).unwrap().state.nonce(), 1);
}
