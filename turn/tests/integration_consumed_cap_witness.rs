//! cap Phase C integration: the executor threads the CONSUMED-capability
//! witness into `TurnReceipt.consumed_capabilities`.
//!
//! Three teeth (all NON-vacuous):
//!   (a) a capability-gated turn's receipt carries the consumed-cap witness
//!       and the sorted-Merkle membership path VERIFIES against the REAL
//!       pre-state `capability_root` (recomputed independently via
//!       `dregg_cell::compute_canonical_capability_root*` — the same scheme
//!       the circuit's `cap_root` column seeds from);
//!   (b) a self-sovereign turn (owner-signature authority, no capability
//!       consumed) carries NONE;
//!   (c) `receipt_hash` (v3) is deterministic AND binds the witness — any
//!       tampered field changes the hash, so an executor cannot strip or
//!       forge the authority disclosure.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, DelegationProofData,
    symbol,
};
use dregg_turn::forest::{CallForest, CallTree};
use dregg_turn::turn::{ConsumedCapAuthPath, Turn, TurnResult};
use dregg_turn::{ComputronCosts, Effect, TurnExecutor};
use dregg_types::CellId;
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

struct TestKeypair {
    signing_key: SigningKey,
    public_key: [u8; 32],
}

impl TestKeypair {
    fn from_seed(seed: u8) -> Self {
        let mut seed_bytes = [0u8; 32];
        seed_bytes[0] = seed;
        let signing_key = SigningKey::from_bytes(&seed_bytes);
        let verifying_key: VerifyingKey = (&signing_key).into();
        let public_key = verifying_key.to_bytes();
        TestKeypair {
            signing_key,
            public_key,
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

fn set_field_action(target: CellId, auth: Authorization, value: [u8; 32]) -> Action {
    Action {
        target,
        method: symbol("set_field"),
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: 0,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn wrap_turn(agent: CellId, action: Action) -> Turn {
    Turn {
        agent,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree {
                action,
                children: vec![],
                hash: [0u8; 32],
            }],
            forest_hash: [0u8; 32],
        },
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

fn unwrap_receipt(result: TurnResult) -> dregg_turn::TurnReceipt {
    match result {
        TurnResult::Committed { receipt, .. } => receipt,
        other => panic!("expected Committed, got {:?}", other),
    }
}

/// Build the breadstuff-gated fixture: ACTOR (agent) holds a breadstuff-token
/// capability to TARGET; TARGET requires Signature-tier auth for SetField, so
/// `Authorization::Breadstuff(token)` is the consumed authority. Returns the
/// committed receipt plus the agent's PRE-state c-list snapshot.
fn run_breadstuff_gated_turn() -> (
    dregg_turn::TurnReceipt,
    CellId,
    u32,
    dregg_cell::CapabilitySet,
) {
    let token: [u8; 32] = [0xB5; 32];
    let agent_kp = TestKeypair::from_seed(41);
    let mut agent = Cell::with_balance(agent_kp.public_key, [0u8; 32], 1_000);
    agent.permissions = open_permissions();

    let mut target = Cell::with_balance([3u8; 32], [0u8; 32], 500);
    // Signature-tier set_state: Breadstuff satisfies the Signature arm.
    let mut perms = open_permissions();
    perms.set_state = AuthRequired::Signature;
    target.permissions = perms;
    let target_id = target.id();

    // A decoy capability before the consumed one, so the consumed cap is NOT
    // trivially at slot 0 / the only leaf in the tree.
    agent
        .capabilities
        .grant(CellId::from_bytes([0x77u8; 32]), AuthRequired::None);
    let slot = agent
        .capabilities
        .grant_with_breadstuff(target_id, AuthRequired::None, Some(token))
        .expect("grant breadstuff cap");

    let agent_id = agent.id();
    let pre_caps = agent.capabilities.clone();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = wrap_turn(
        agent_id,
        set_field_action(target_id, Authorization::Breadstuff(token), [42u8; 32]),
    );
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));
    (receipt, agent_id, slot, pre_caps)
}

// ---------------------------------------------------------------------------
// (a) Capability-gated turn: witness present + path verifies against the
//     REAL pre-state capability root.
// ---------------------------------------------------------------------------

#[test]
fn breadstuff_gated_turn_carries_verifying_consumed_cap_witness() {
    let (receipt, agent_id, slot, pre_caps) = run_breadstuff_gated_turn();

    assert_eq!(
        receipt.consumed_capabilities.len(),
        1,
        "exactly one capability was consumed to authorize the turn"
    );
    let w = &receipt.consumed_capabilities[0];
    assert_eq!(w.holder, agent_id, "the ACTOR's c-list held the capability");
    assert_eq!(w.slot, slot, "the consumed slot is recorded");
    assert_eq!(w.auth_path, ConsumedCapAuthPath::Breadstuff);
    assert_eq!(w.action_path, vec![0], "root action consumed it");

    // The witness's own membership path verifies (leaf preimage → root).
    assert!(
        w.verify(),
        "the recorded sorted-Merkle membership path must verify"
    );

    // NON-vacuous: the root it opens against IS the real pre-state
    // capability root, recomputed independently from the pre-state c-list
    // via the canonical cell-side scheme (the same value the circuit's
    // cap_root column seeds from).
    let expected_root_felt = dregg_cell::compute_canonical_capability_root_felt(&pre_caps);
    assert_eq!(
        w.cap_root,
        expected_root_felt.as_u32(),
        "witness root must equal the REAL pre-state capability root"
    );
    assert_eq!(
        w.cap_root_bytes32(),
        dregg_cell::compute_canonical_capability_root(&pre_caps),
        "32-byte encoding agrees with compute_canonical_capability_root"
    );

    // The leaf preimage is the canonical 7-field leaf of the consumed cap.
    let consumed_ref = pre_caps
        .iter()
        .find(|c| c.slot == slot)
        .expect("consumed cap in pre-state c-list");
    let expected_leaf = dregg_cell::cap_ref_to_leaf(consumed_ref);
    assert_eq!(w.cap_leaf(), expected_leaf, "full leaf preimage recorded");
}

#[test]
fn bearer_gated_turn_records_delegator_consumed_cap_witness() {
    // Bearer path: the DELEGATOR's c-list capability is the consumed
    // authority. Mirrors `test_bearer_cap_signed_delegation_accepted`.
    let delegator_kp = TestKeypair::from_seed(10);
    let bearer_kp = TestKeypair::from_seed(11);

    let mut delegator_cell = Cell::with_balance(delegator_kp.public_key, [0u8; 32], 1_000);
    delegator_cell.permissions = open_permissions();
    let mut target_cell = Cell::with_balance([3u8; 32], [0u8; 32], 500);
    target_cell.permissions = open_permissions();
    let target_id = target_cell.id();
    let slot = delegator_cell
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("grant delegator cap");
    let delegator_id = delegator_cell.id();
    let pre_delegator_caps = delegator_cell.capabilities.clone();

    let mut bearer_cell = Cell::with_balance(bearer_kp.public_key, [0u8; 32], 1_000);
    bearer_cell.permissions = open_permissions();
    let bearer_id = bearer_cell.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(delegator_cell).unwrap();
    ledger.insert_cell(target_cell).unwrap();
    ledger.insert_cell(bearer_cell).unwrap();

    let expires_at = 1_000u64;
    let permissions = AuthRequired::None;
    let message = TurnExecutor::compute_bearer_delegation_message(
        &target_id,
        &permissions,
        &bearer_kp.public_key,
        expires_at,
        &[0u8; 32],
    );
    let sig = delegator_kp.signing_key.sign(&message);
    let proof = BearerCapProof {
        target: target_id,
        permissions,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: delegator_kp.public_key,
            signature: sig.to_bytes(),
            bearer_pk: bearer_kp.public_key,
        },
        expires_at,
        revocation_channel: None,
        allowed_effects: None,
    };

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = wrap_turn(
        bearer_id,
        set_field_action(target_id, Authorization::Bearer(proof), [99u8; 32]),
    );
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));

    assert_eq!(receipt.consumed_capabilities.len(), 1);
    let w = &receipt.consumed_capabilities[0];
    assert_eq!(
        w.holder, delegator_id,
        "the DELEGATOR's c-list held the consumed authority"
    );
    assert_eq!(w.slot, slot);
    assert_eq!(w.auth_path, ConsumedCapAuthPath::BearerSignedDelegation);
    assert!(w.verify(), "membership path must verify");
    assert_eq!(
        w.cap_root,
        dregg_cell::compute_canonical_capability_root_felt(&pre_delegator_caps).as_u32(),
        "witness root must equal the delegator's REAL pre-state capability root"
    );
}

// ---------------------------------------------------------------------------
// (b) Self-sovereign turn: no capability consumed → empty vec.
// ---------------------------------------------------------------------------

#[test]
fn self_sovereign_turn_carries_no_consumed_cap_witness() {
    // Owner-signature authority: the agent acts on its OWN signature-gated
    // cell with a real Ed25519 signature — no capability is consumed.
    let agent_kp = TestKeypair::from_seed(7);
    let agent = Cell::with_balance(agent_kp.public_key, [0u8; 32], 1_000);
    // Default Cell permissions require Signature — keep them.
    let agent_id = agent.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let mut action = set_field_action(agent_id, Authorization::Unchecked, [5u8; 32]);
    let message = TurnExecutor::compute_signing_message(&action, &[0u8; 32]);
    let sig = agent_kp.signing_key.sign(&message).to_bytes();
    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&sig[..32]);
    s.copy_from_slice(&sig[32..]);
    action.authorization = Authorization::Signature(r, s);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = wrap_turn(agent_id, action);
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));

    assert!(
        receipt.consumed_capabilities.is_empty(),
        "self-sovereign turn consumes no capability — empty vec, zero overhead"
    );
}

// ---------------------------------------------------------------------------
// (c) receipt_hash v3: deterministic; binds the consumed witness.
// ---------------------------------------------------------------------------

#[test]
fn receipt_hash_v3_is_deterministic_and_binds_consumed_witness() {
    let (receipt, _, _, _) = run_breadstuff_gated_turn();

    // Determinism.
    let h1 = receipt.receipt_hash();
    let h2 = receipt.receipt_hash();
    assert_eq!(h1, h2, "receipt_hash must be deterministic");

    // Tamper every load-bearing witness field: the v3 hash must move.
    let base = receipt.clone();

    let mut t = base.clone();
    t.consumed_capabilities[0].leaf_mask_lo ^= 1;
    assert_ne!(
        t.receipt_hash(),
        h1,
        "tampered leaf_mask_lo must change receipt_hash"
    );

    let mut t = base.clone();
    t.consumed_capabilities[0].slot ^= 1;
    assert_ne!(
        t.receipt_hash(),
        h1,
        "tampered slot must change receipt_hash"
    );

    let mut t = base.clone();
    t.consumed_capabilities[0].cap_root ^= 1;
    assert_ne!(
        t.receipt_hash(),
        h1,
        "tampered cap_root must change receipt_hash"
    );

    let mut t = base.clone();
    t.consumed_capabilities[0].siblings[0] ^= 1;
    assert_ne!(
        t.receipt_hash(),
        h1,
        "tampered sibling must change receipt_hash"
    );

    let mut t = base.clone();
    t.consumed_capabilities[0].directions[0] ^= 1;
    assert_ne!(
        t.receipt_hash(),
        h1,
        "tampered direction bit must change receipt_hash"
    );

    let mut t = base.clone();
    t.consumed_capabilities[0].holder = CellId::from_bytes([0xEE; 32]);
    assert_ne!(
        t.receipt_hash(),
        h1,
        "tampered holder must change receipt_hash"
    );

    // STRIPPING the witness entirely must also change the hash (the
    // disclosure cannot be silently removed).
    let mut t = base.clone();
    t.consumed_capabilities.clear();
    assert_ne!(
        t.receipt_hash(),
        h1,
        "stripped witness must change receipt_hash"
    );

    // And a tampered witness no longer verifies (the path is real).
    let mut t = base;
    t.consumed_capabilities[0].leaf_mask_lo ^= 1;
    assert!(
        !t.consumed_capabilities[0].verify(),
        "a tampered leaf must fail the membership-path verification"
    );
}
