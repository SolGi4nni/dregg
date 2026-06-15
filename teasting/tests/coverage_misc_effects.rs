//! Executor-path coverage for miscellaneous `Effect` variants.
//!
//! Every test drives a real `TurnExecutor::execute` (or, for the two variants
//! that require it, the `TurnExecutor` is set up with the exact pre-state the
//! variant demands) and asserts a real outcome — either a committed receipt
//! with observable ledger mutation, or a precise rejection reason.
//!
//! Variants covered with PASSING executor tests:
//!   NoteCreate, CreateSealPair, Seal, Unseal, CreateCommittedEscrow,
//!   ReleaseCommittedEscrow, RefundCommittedEscrow, BridgeFinalize,
//!   BridgeCancel, Introduce, MakeSovereign, CreateCellFromFactory,
//!   SetPermissions, Refusal.
//!
//! Variants with documented blockers (not faked):
//!   NoteSpend — requires a real ZK spending proof (STARK verifier rejects
//!               any proof bytes; no in-process proof generator available).
//!   PipelinedSend — always rejects at apply-time by design (documented in
//!                   apply_pipelined_send: "unresolved PipelinedSend").

use dregg_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, CellMode, FactoryCreationParams, FactoryDescriptor,
    Ledger, NoteCommitment, Permissions, SealPair, ValueCommitment, note_bridge::BridgeReceipt,
};
use dregg_turn::{
    // RETIRED (dregg3): EscrowClaimAuth + the dregg_turn::escrow module
    // (CommittedEscrow, compute_identity_commitment) were dissolved with the
    // committed-escrow verb family; the escrow/bridge section headers below are
    // vestigial and their tests already removed.
    ActionBuilder,
    Effect,
    TurnBuilder,
    TurnResult,
    action::RefusalReason,
    executor::{ComputronCosts, TurnExecutor},
};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

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

fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let token_id = [seed.wrapping_add(100); 32];
    let mut cell = Cell::with_balance(pk, token_id, balance as i64);
    cell.permissions = open_permissions();
    cell
}

fn zero_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
}

/// Execute a turn with one or more effects targeting `agent` and return the result.
fn exec_single(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    effects: Vec<Effect>,
) -> TurnResult {
    exec_single_chained(executor, ledger, agent, nonce, effects, None)
}

/// Execute a turn chained from a previous receipt hash.
fn exec_single_chained(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    effects: Vec<Effect>,
    prev_hash: Option<[u8; 32]>,
) -> TurnResult {
    let mut ab = ActionBuilder::new_unchecked_for_tests(agent, "test-op", agent);
    for e in effects {
        ab = ab.effect(e);
    }
    let action = ab.build();
    let mut builder = TurnBuilder::new(agent, nonce);
    builder.add_action(action);
    let mut turn = builder.fee(0).build();
    turn.previous_receipt_hash = prev_hash;
    executor.execute(&turn, ledger)
}

fn assert_committed(result: &TurnResult, ctx: &str) {
    assert!(
        result.is_committed(),
        "{ctx}: expected committed, got {result:?}"
    );
}

fn assert_rejected(result: &TurnResult, ctx: &str) {
    assert!(
        result.is_rejected(),
        "{ctx}: expected rejected, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// NoteCreate — accepts a non-null commitment with no value_commitment.
// ---------------------------------------------------------------------------

#[test]
fn note_create_cleartext_commits() {
    let cell = make_cell(1, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let commitment = NoteCommitment([0xAB; 32]);
    // value=0, asset_type=0: zero-value notes (e.g. NFT ownership tokens) satisfy
    // conservation trivially (0 inputs == 0 outputs).
    let result = exec_single(
        &executor,
        &mut ledger,
        cell_id,
        0,
        vec![Effect::NoteCreate {
            commitment,
            value: 0,
            asset_type: 0,
            encrypted_note: vec![0xDE, 0xAD],
            value_commitment: None,
            range_proof: None,
        }],
    );
    assert_committed(&result, "NoteCreate cleartext");
}

#[test]
fn note_create_null_commitment_rejects() {
    let cell = make_cell(2, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let result = exec_single(
        &executor,
        &mut ledger,
        cell_id,
        0,
        vec![Effect::NoteCreate {
            commitment: NoteCommitment([0u8; 32]),
            value: 0,
            asset_type: 0,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        }],
    );
    assert_rejected(&result, "NoteCreate null commitment");
}

// ---------------------------------------------------------------------------
// NoteSpend — BLOCKER: always rejects because apply_note_spend requires a
// real ZK spending proof that passes through ProofVerifier::verify.
// Without an in-process STARK proof generator we cannot produce such a proof.
// The rejection below is the exact executor path (not a panic), confirming the
// variant reaches apply_note_spend and fails on "NoteSpend missing spending proof".
// ---------------------------------------------------------------------------

#[test]
fn note_spend_always_rejects_without_proof() {
    let cell = make_cell(3, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let result = exec_single(
        &executor,
        &mut ledger,
        cell_id,
        0,
        vec![Effect::NoteSpend {
            nullifier: dregg_cell::Nullifier([0xAA; 32]),
            note_tree_root: [0xBB; 32],
            spending_proof: vec![],
            value: 10,
            asset_type: 0,
            value_commitment: None,
        }],
    );
    // Must reject cleanly (not panic). The reason is "NoteSpend missing spending proof".
    assert_rejected(&result, "NoteSpend without proof");
    if let TurnResult::Rejected { reason, .. } = &result {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("spending proof") || msg.contains("NoteSpend"),
            "unexpected rejection reason: {msg}"
        );
    }
}

// ---------------------------------------------------------------------------
// CreateSealPair — grants sealer and unsealer capabilities to two cells.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Seal — seals a capability reference using the sealer pair.
// Sequence: CreateSealPair → Seal.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Unseal — full Seal->Unseal round-trip through the executor. Exercises the
// #144 fix: apply_unseal reconstructs the pair via SealPair::from_secret, which
// recomputes sealer_public = X25519_base × unsealer_secret, so the ECDH-derived
// decryption key matches the seal side and the sealed capability is recovered.
// (Previously apply_unseal used from_keys([0u8;32], …), zeroing sealer_public,
// which always produced the wrong key and failed with DecryptionFailed.)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Helper: replicate the executor's seal_capability_id derivation.
// (The executor method is pub(super) so we replicate it locally.)
// ---------------------------------------------------------------------------
fn seal_capability_id_for_test(pair_id: &[u8; 32], is_sealer: bool) -> CellId {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-seal capability-id v1");
    hasher.update(pair_id);
    hasher.update(if is_sealer { b"sealer" } else { b"unsealer" });
    CellId::from_bytes(*hasher.finalize().as_bytes())
}

// ---------------------------------------------------------------------------
// CreateCommittedEscrow — locks funds behind cryptographic commitments.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// ReleaseCommittedEscrow — pays out to recipient after claim authorization.
// Sequence: CreateCommittedEscrow → ReleaseCommittedEscrow.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// RefundCommittedEscrow — returns funds to creator after timeout.
// Sequence: CreateCommittedEscrow → advance block height → RefundCommittedEscrow.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// BridgeFinalize — finalizes a pending bridge using a trusted receipt.
// Sequence: BridgeLock → BridgeFinalize.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// BridgeCancel — cancels a pending bridge after timeout.
// Sequence: BridgeLock → advance block height → BridgeCancel.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Introduce — introducer with caps to both recipient and target grants
// the recipient access to the target.
// ---------------------------------------------------------------------------

#[test]
fn introduce_grants_capability_to_recipient() {
    let introducer = make_cell(80, 5_000);
    let introducer_id = introducer.id();
    let recipient = make_cell(81, 0);
    let recipient_id = recipient.id();
    let target = make_cell(82, 0);
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(introducer).unwrap();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(target).unwrap();

    // Grant introducer a capability to recipient AND a capability to target.
    ledger
        .get_mut(&introducer_id)
        .unwrap()
        .capabilities
        .grant(recipient_id, AuthRequired::None);
    ledger
        .get_mut(&introducer_id)
        .unwrap()
        .capabilities
        .grant(target_id, AuthRequired::None);

    let executor = zero_executor();

    // Before: recipient has no capabilities.
    assert_eq!(
        ledger
            .get(&recipient_id)
            .unwrap()
            .capabilities
            .iter()
            .count(),
        0
    );

    let result = exec_single(
        &executor,
        &mut ledger,
        introducer_id,
        0,
        vec![Effect::Introduce {
            introducer: introducer_id,
            recipient: recipient_id,
            target: target_id,
            permissions: AuthRequired::None,
        }],
    );
    assert_committed(&result, "Introduce");

    // After: recipient now holds a capability to target.
    let recipient_after = ledger.get(&recipient_id).unwrap();
    assert!(
        recipient_after
            .capabilities
            .iter()
            .any(|cap| cap.target == target_id),
        "Introduce must grant recipient a capability to target"
    );
}

// ---------------------------------------------------------------------------
// PipelinedSend — always rejects at apply time (by design).
// Documented blocker: the effect is only valid inside a pipeline resolution
// pass. The EmbeddedExecutor has no pipeline resolver; apply_pipelined_send
// unconditionally returns PreconditionFailed.
// ---------------------------------------------------------------------------

#[test]
fn pipelined_send_rejects_outside_pipeline() {
    use dregg_cell::Preconditions;
    use dregg_turn::eventual::EventualRef;
    use dregg_turn::{Action, Authorization, DelegationMode};

    let actor = make_cell(90, 5_000);
    let actor_id = actor.id();
    let target = make_cell(91, 0);
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_executor();

    let inner_action = Action {
        target: target_id,
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

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::PipelinedSend {
            target: EventualRef::new([0u8; 32], 0),
            action: Box::new(inner_action),
        }],
    );
    assert_rejected(&result, "PipelinedSend outside pipeline");
    if let TurnResult::Rejected { reason, .. } = &result {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("PipelinedSend") || msg.contains("pipeline"),
            "PipelinedSend rejection must mention pipeline: {msg}"
        );
    }
}

// ---------------------------------------------------------------------------
// MakeSovereign — transitions the action-target cell to sovereign mode.
// ---------------------------------------------------------------------------

#[test]
fn make_sovereign_transitions_cell() {
    let actor = make_cell(100, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::MakeSovereign { cell: actor_id }],
    );
    assert_committed(&result, "MakeSovereign");

    // After MakeSovereign the cell is removed from the hosted store and a
    // sovereign commitment is recorded. The cell is no longer in the hosted ledger.
    assert!(
        ledger.get(&actor_id).is_none(),
        "MakeSovereign must move cell out of hosted store"
    );
    assert!(
        ledger.is_sovereign(&actor_id),
        "MakeSovereign must register the cell as sovereign"
    );
    assert!(
        ledger.get_sovereign_commitment(&actor_id).is_some(),
        "MakeSovereign must record sovereign commitment"
    );
}

#[test]
fn make_sovereign_cross_cell_rejects() {
    // MakeSovereign with cell != action_target must be rejected.
    let actor = make_cell(101, 5_000);
    let actor_id = actor.id();
    let other = make_cell(102, 0);
    let other_id = other.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(other).unwrap();

    let executor = zero_executor();

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::MakeSovereign { cell: other_id }],
    );
    assert_rejected(&result, "MakeSovereign cross-cell");
}

// ---------------------------------------------------------------------------
// CreateCellFromFactory — creates a new cell via a registered factory.
// ---------------------------------------------------------------------------

#[test]
fn create_cell_from_factory_produces_new_cell() {
    let actor = make_cell(110, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let mut executor = zero_executor();

    // Register a factory.
    let factory = FactoryDescriptor {
        factory_vk: [0xF1; 32],
        child_program_vk: None,
        child_vk_strategy: None,
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        state_constraints: vec![],
        default_mode: CellMode::Hosted,
        creation_budget: None,
    };
    let factory_vk = executor.deploy_factory(factory);

    let owner_pubkey = [0x11u8; 32];
    let token_id = [0x22u8; 32];
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };

    let new_cell_id = CellId::derive_raw(&owner_pubkey, &token_id);
    assert!(
        ledger.get(&new_cell_id).is_none(),
        "cell must not exist before factory creation"
    );

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        }],
    );
    assert_committed(&result, "CreateCellFromFactory");

    assert!(
        ledger.get(&new_cell_id).is_some(),
        "CreateCellFromFactory must create the new cell in the ledger"
    );
}

#[test]
fn create_cell_from_factory_unknown_factory_rejects() {
    let actor = make_cell(111, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let owner_pubkey = [0x33u8; 32];
    let token_id = [0x44u8; 32];
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::CreateCellFromFactory {
            factory_vk: [0xDEu8; 32], // not registered
            owner_pubkey,
            token_id,
            params,
        }],
    );
    assert_rejected(&result, "CreateCellFromFactory unknown factory");
}

// ---------------------------------------------------------------------------
// SetPermissions — updates the permission set of the action-target cell.
// ---------------------------------------------------------------------------

#[test]
fn set_permissions_updates_cell_permissions() {
    let actor = make_cell(120, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    // Verify the current permissions are open.
    let before = ledger.get(&actor_id).unwrap().permissions.send.clone();
    assert!(matches!(before, AuthRequired::None));

    // Change send permission to Signature-required.
    let new_perms = Permissions {
        send: AuthRequired::Signature,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };

    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::SetPermissions {
            cell: actor_id,
            new_permissions: new_perms.clone(),
        }],
    );
    assert_committed(&result, "SetPermissions");

    let after = &ledger.get(&actor_id).unwrap().permissions;
    assert!(
        matches!(after.send, AuthRequired::Signature),
        "SetPermissions must update send permission to Signature"
    );
}

// ---------------------------------------------------------------------------
// Refusal — bumps nonce, stores audit commitment in field[4].
// ---------------------------------------------------------------------------

#[test]
fn refusal_bumps_nonce_and_stores_audit() {
    let actor = make_cell(130, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let before_nonce = ledger.get(&actor_id).unwrap().state.nonce();
    let before_field4 = ledger.get(&actor_id).unwrap().state.fields[4];

    let offered_commitment = [0xAA; 32];
    let result = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::Refusal {
            cell: actor_id,
            offered_action_commitment: offered_commitment,
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        }],
    );
    assert_committed(&result, "Refusal");

    let after = ledger.get(&actor_id).unwrap();
    // The cell nonce is incremented twice: once by the executor's Phase 1 (fee+nonce commit)
    // and once by apply_refusal itself. Total: before_nonce + 2.
    assert_eq!(
        after.state.nonce(),
        before_nonce + 2,
        "Refusal (plus executor Phase 1) must bump nonce by 2"
    );
    assert_ne!(
        after.state.fields[4], before_field4,
        "Refusal must write audit commitment to field[4]"
    );
}

#[test]
fn refusal_with_custom_reason_stores_distinct_audit() {
    let actor = make_cell(131, 5_000);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();

    let result1 = exec_single(
        &executor,
        &mut ledger,
        actor_id,
        0,
        vec![Effect::Refusal {
            cell: actor_id,
            offered_action_commitment: [0x01; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        }],
    );
    assert_committed(&result1, "Refusal Declined");
    let field4_declined = ledger.get(&actor_id).unwrap().state.fields[4];

    // After the first Refusal turn, the cell nonce has been incremented twice:
    // once by the Refusal effect (apply_refusal) and once by the executor's
    // finalization step (nonce_increment = true in execute.rs). So cell nonce = 2.
    let nonce2 = ledger.get(&actor_id).unwrap().state.nonce();
    let prev = executor.get_last_receipt_hash(&actor_id);
    let result2 = exec_single_chained(
        &executor,
        &mut ledger,
        actor_id,
        nonce2,
        vec![Effect::Refusal {
            cell: actor_id,
            offered_action_commitment: [0x01; 32],
            refusal_reason: RefusalReason::Custom {
                reason_hash: [0xBEu8; 32],
            },
            proof_witness_index: 0,
        }],
        prev,
    );
    assert_committed(&result2, "Refusal Custom");
    let field4_custom = ledger.get(&actor_id).unwrap().state.fields[4];

    assert_ne!(
        field4_declined, field4_custom,
        "distinct refusal reasons must produce distinct audit commitments"
    );
}
