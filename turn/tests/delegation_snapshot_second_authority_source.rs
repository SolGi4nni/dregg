//! The delegation snapshot is a SECOND authority source, and every check shaped
//! around the c-list was blind to it. Two exhibits, both driven end-to-end
//! through `TurnExecutor::execute`.
//!
//! A cell confers cross-cell authority from two stores — its own c-list
//! (`Cell::capabilities`) and a `DelegatedRef` snapshot (`Cell::delegation`),
//! installed in production by `Effect::SpawnWithDelegation`,
//! `Effect::RefreshDelegation`, and the executor's `DelegationMode::SnapshotRefresh`
//! chain walk. The snapshot is a VERBATIM copy of the ancestor's `CapabilityRef`s:
//! `expires_at`, `permissions` and `allowed_effects` all ride along.
//!
//! **Exhibit A — expiry was not applied to snapshot-borne authority.**
//! `has_access_including_delegation_at` documented itself as filtering lapsed
//! capabilities, and its direct branch did (`CapabilitySet::has_access_at`). Its
//! delegation branch called `DelegatedRef::has_capability`, which was
//! `snapshot.iter().any(|cap| &cap.target == target)` — target equality alone. So
//! a capability that the PARENT could no longer exercise still let the CHILD
//! reach the target, through the predicate that the cross-cell gate, the
//! delegation chain walk, the CapTP held-grounding and the bearer delegator check
//! all consult.
//!
//! **Exhibit B — `granted ≤ held` was skipped on snapshot-borne authority.**
//! `verify_bearer_cap` gated presence on the delegation-aware predicate and then
//! resolved the bounding capability from the delegator's c-list ALONE. For a
//! delegator whose authority was snapshot-borne, that lookup returned `None` and
//! the entire amplification block was skipped — no rights check, no facet
//! attenuation — after which `verify_authorization` returns `Ok(())` for Bearer
//! without ever reaching the target cell's permission lattice.
//!
//! Both are closed at the root by `Cell::resolve_authority_at`: one resolution,
//! both stores, `CapabilityRef::is_live_at` applied to each, and a `HeldAuthority`
//! whose `SelfOwned` (genuinely unbounded) and `NoneHeld` variants cannot be
//! confused the way a bare `Option::None` was.

use dregg_cell::{
    AuthRequired, Cell, CellId, EFFECT_TRANSFER, Ledger, Permissions,
    permissions::Action as PAction,
};
use dregg_turn::action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, DelegationProofData,
    symbol,
};
use dregg_turn::{CallForest, CallTree, ComputronCosts, Effect, Turn, TurnError, TurnExecutor};
use dregg_types::{SigningKey, sign};

const EXPIRES_AT: u64 = 100;
const BEFORE_EXPIRY: u64 = 50;
const AFTER_EXPIRY: u64 = 200;

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

fn keyed_cell(seed: u8, balance: i64) -> (SigningKey, Cell) {
    let key = SigningKey::from_bytes(&[seed; 32]);
    let mut cell = Cell::with_balance(key.public_key().0, [0u8; 32], balance);
    cell.permissions = open_permissions();
    (key, cell)
}

fn wrap(agent: CellId, action: Action) -> Turn {
    Turn {
        agent,
        nonce: 0,
        fee: 0,
        call_forest: CallForest {
            roots: vec![CallTree::new(action)],
            forest_hash: [0u8; 32],
        },
        valid_until: None,
        memo: None,
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

fn spawn_delegated(parent: CellId, child_pk: [u8; 32]) -> Turn {
    wrap(
        parent,
        Action {
            target: parent,
            method: symbol("spawn_delegated"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::SpawnWithDelegation {
                child_public_key: child_pk,
                child_token_id: [0u8; 32],
                max_staleness: 1_000_000,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        },
    )
}

fn set_field_on(actor: CellId, target: CellId, auth: Authorization, value: [u8; 32]) -> Turn {
    wrap(
        actor,
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
        },
    )
}

/// Build: parent holding ONE capability to `target`, a child spawned off it (so
/// the child's authority over `target` is purely snapshot-borne, its own c-list
/// empty), and the target. `grant` shapes the parent's capability.
///
/// Returns `(ledger, parent_id, child_id, target_id)`. The spawn is driven
/// through `execute`, so the snapshot is the one production actually installs.
fn snapshot_world(
    child_pk: [u8; 32],
    spawn_height: u64,
    grant: impl FnOnce(&mut Cell, CellId),
) -> (Ledger, CellId, CellId, CellId) {
    let (_pkey, mut parent) = keyed_cell(1, 1_000_000);
    let parent_id = parent.id();
    let mut target = Cell::with_balance([13u8; 32], [0u8; 32], 500);
    target.permissions = open_permissions();
    let target_id = target.id();
    grant(&mut parent, target_id);

    let mut ledger = Ledger::new();
    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(1000);
    executor.set_block_height(spawn_height);
    let spawned = executor.execute(&spawn_delegated(parent_id, child_pk), &mut ledger);
    assert!(spawned.is_committed(), "spawn must commit: {spawned:?}");

    let child_id = CellId::derive_raw(&child_pk, &[0u8; 32]);
    ledger
        .get_mut(&child_id)
        .unwrap()
        .state
        .set_balance(100_000);
    (ledger, parent_id, child_id, target_id)
}

// ───────────────────────── Exhibit A: snapshot expiry ─────────────────────────

/// The child's snapshot carries the parent's capability VERBATIM, expiry
/// included — so the executor has the lapse date in hand and needs no freshness
/// argument to honour it.
#[test]
fn a_expired_snapshot_capability_is_refused_after_its_expiry() {
    let (mut ledger, parent_id, child_id, target_id) =
        snapshot_world([42u8; 32], BEFORE_EXPIRY, |parent, target_id| {
            parent
                .capabilities
                .grant_with_expiry(target_id, AuthRequired::None, EXPIRES_AT)
                .expect("parent holds an EXPIRING capability to the target");
        });

    // The snapshot really did carry the expiring capability (not an empty one).
    let child = ledger.get(&child_id).expect("child exists");
    let snap = child.delegation.as_ref().expect("child holds a snapshot");
    assert_eq!(snap.source, parent_id);
    assert!(
        snap.names_target(&target_id),
        "the snapshot must NAME the target — otherwise this exhibit tests nothing"
    );
    assert_eq!(
        snap.snapshot
            .iter()
            .find(|c| c.target == target_id)
            .and_then(|c| c.expires_at),
        Some(EXPIRES_AT),
        "the snapshot copies `expires_at` verbatim — that is what makes the lapse readable"
    );

    // The PARENT's own path already refused past the expiry. Whatever the child
    // is allowed to do, it cannot exceed this.
    let parent = ledger.get(&parent_id).unwrap();
    assert!(
        parent.capabilities.has_access_at(&target_id, BEFORE_EXPIRY),
        "parent's direct authority is live before the expiry"
    );
    assert!(
        !parent.capabilities.has_access_at(&target_id, AFTER_EXPIRY),
        "parent's direct authority is dead after the expiry"
    );

    // NEW-REJECTS: past the expiry, the child's snapshot-borne authority is dead
    // too. Driven end-to-end — this is `execute`, not a predicate read.
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(AFTER_EXPIRY);
    let lapsed = executor.execute(
        &set_field_on(child_id, target_id, Authorization::Unchecked, [0x99; 32]),
        &mut ledger,
    );
    match lapsed {
        dregg_turn::TurnResult::Rejected {
            reason: TurnError::CapabilityNotHeld { actor, target },
            ..
        } => {
            assert_eq!(actor, child_id);
            assert_eq!(target, target_id);
        }
        other => panic!(
            "an EXPIRED capability sitting in a delegation snapshot must not confer \
             cross-cell authority: {other:?}"
        ),
    }
    assert_ne!(
        ledger.get(&target_id).unwrap().state.fields[0],
        [0x99; 32],
        "the refused turn must not have written the target"
    );
}

/// COMPLETENESS: the same child, the same snapshot, BEFORE the expiry — honest
/// delegated authority is untouched.
#[test]
fn a_live_snapshot_capability_still_confers_authority_before_expiry() {
    let (mut ledger, _parent_id, child_id, target_id) =
        snapshot_world([43u8; 32], BEFORE_EXPIRY, |parent, target_id| {
            parent
                .capabilities
                .grant_with_expiry(target_id, AuthRequired::None, EXPIRES_AT)
                .expect("parent holds an expiring capability");
        });

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(1500);
    executor.set_block_height(BEFORE_EXPIRY + 1);
    let live = executor.execute(
        &set_field_on(child_id, target_id, Authorization::Unchecked, [0x77; 32]),
        &mut ledger,
    );
    assert!(
        live.is_committed(),
        "honest delegated authority inside its lifetime must still work: {live:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0x77; 32]);
}

/// COMPLETENESS: a snapshot capability with NO expiry is unaffected by the
/// liveness filter at any height — the fix does not quietly time-bound
/// unbounded grants.
#[test]
fn a_unbounded_snapshot_capability_is_unaffected_by_height() {
    let (mut ledger, _parent_id, child_id, target_id) =
        snapshot_world([44u8; 32], BEFORE_EXPIRY, |parent, target_id| {
            parent
                .capabilities
                .grant(target_id, AuthRequired::None)
                .expect("parent holds an UNBOUNDED capability");
        });

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(9999);
    executor.set_block_height(AFTER_EXPIRY * 100);
    let far_future = executor.execute(
        &set_field_on(child_id, target_id, Authorization::Unchecked, [0x55; 32]),
        &mut ledger,
    );
    assert!(
        far_future.is_committed(),
        "an unexpiring snapshot capability must keep conferring authority: {far_future:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0x55; 32]);
}

/// A snapshot capability frozen to `Impossible` confers nothing either — the
/// same liveness predicate, the other leg. The c-list sibling
/// (`CapabilitySet::holds_unfrozen_ref_to`) has always refused `Impossible`; the snapshot
/// branch never looked.
#[test]
fn a_impossible_snapshot_capability_confers_nothing() {
    let (mut ledger, _parent_id, child_id, target_id) =
        snapshot_world([45u8; 32], BEFORE_EXPIRY, |parent, target_id| {
            parent
                .capabilities
                .grant(target_id, AuthRequired::Impossible)
                .expect("parent holds a FROZEN capability");
        });

    let child = ledger.get(&child_id).unwrap();
    assert!(
        child.delegation.as_ref().unwrap().names_target(&target_id),
        "the frozen capability IS in the snapshot — that is the point"
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let frozen = executor.execute(
        &set_field_on(child_id, target_id, Authorization::Unchecked, [0x11; 32]),
        &mut ledger,
    );
    assert!(
        matches!(
            frozen,
            dregg_turn::TurnResult::Rejected {
                reason: TurnError::CapabilityNotHeld { .. },
                ..
            }
        ),
        "an `Impossible` capability in a snapshot must confer nothing: {frozen:?}"
    );
}

// ─────────────── Exhibit B: bearer amplification off a snapshot ───────────────

/// Build a delegator whose ONLY authority over the target is snapshot-borne
/// (its own c-list is empty), shaped by `grant`, plus a bearer cell.
///
/// Returns `(ledger, delegator_key, delegator_id, bearer_key, bearer_id, target_id)`.
fn bearer_world(
    grant: impl FnOnce(&mut Cell, CellId),
) -> (Ledger, SigningKey, CellId, SigningKey, CellId, CellId) {
    let delegator_key = SigningKey::from_bytes(&[70u8; 32]);
    let delegator_pk = delegator_key.public_key().0;
    let (mut ledger, _parent_id, delegator_id, target_id) =
        snapshot_world(delegator_pk, BEFORE_EXPIRY, grant);

    let (bearer_key, bearer) = keyed_cell(71, 100_000);
    let bearer_id = bearer.id();
    ledger.insert_cell(bearer).unwrap();

    // The delegator's OWN c-list must be empty for this exhibit to be about the
    // snapshot at all.
    let delegator = ledger.get(&delegator_id).unwrap();
    assert!(
        delegator.capabilities.is_empty(),
        "the delegator's authority must be purely snapshot-borne"
    );
    assert!(
        delegator
            .delegation
            .as_ref()
            .expect("delegator holds a snapshot")
            .names_target(&target_id),
        "the snapshot must carry the target capability"
    );
    (
        ledger,
        delegator_key,
        delegator_id,
        bearer_key,
        bearer_id,
        target_id,
    )
}

fn signed_bearer_proof(
    delegator_key: &SigningKey,
    bearer_key: &SigningKey,
    target: CellId,
    permissions: AuthRequired,
    allowed_effects: Option<u32>,
) -> BearerCapProof {
    let expires_at = 1_000_000;
    let message = TurnExecutor::compute_bearer_delegation_message(
        &target,
        &permissions,
        &bearer_key.public_key().0,
        expires_at,
        &[0u8; 32],
    );
    BearerCapProof {
        target,
        permissions,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: delegator_key.public_key().0,
            signature: sign(delegator_key, &message).0,
            bearer_pk: bearer_key.public_key().0,
        },
        expires_at,
        revocation_channel: None,
        allowed_effects,
    }
}

/// NEW-REJECTS (rights lattice): a delegator whose snapshot-borne capability is
/// `Signature`-gated signs a bearer grant of `None` — the broadest tier there is
/// — and the amplification refusal now fires. It could not fire before: the
/// bounding capability was resolved from an EMPTY c-list, so `granted ≤ held`
/// had nothing to compare and skipped itself.
#[test]
fn b_bearer_grant_cannot_amplify_a_snapshot_borne_capability() {
    let (mut ledger, delegator_key, _delegator_id, bearer_key, bearer_id, target_id) =
        bearer_world(|parent, target_id| {
            parent
                .capabilities
                .grant(target_id, AuthRequired::Signature)
                .expect("parent holds a SIGNATURE-gated capability");
        });

    let proof = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None, // ← broader than the held `Signature`
        None,
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let amplified = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(proof),
            [0xAA; 32],
        ),
        &mut ledger,
    );
    match amplified {
        dregg_turn::TurnResult::Rejected {
            reason:
                TurnError::BearerCapAmplification {
                    target,
                    delegator_permissions,
                    bearer_permissions,
                },
            ..
        } => {
            assert_eq!(target, target_id);
            assert_eq!(delegator_permissions, AuthRequired::Signature);
            assert_eq!(bearer_permissions, AuthRequired::None);
        }
        other => panic!(
            "a bearer grant BROADER than the delegator's snapshot-borne capability \
             must be refused: {other:?}"
        ),
    }
    assert_ne!(
        ledger.get(&target_id).unwrap().state.fields[0],
        [0xAA; 32],
        "the refused turn must not have written the target"
    );
}

/// NEW-REJECTS (facet): the delegator's snapshot-borne capability is faceted to
/// TRANSFER only. The bearer proof names no facet, so it INHERITS the
/// delegator's — but the inherited facet was `None` before, because it was read
/// off a c-list lookup that found nothing. A `SetField` under a transfer-only
/// facet is now refused.
#[test]
fn b_bearer_inherits_the_snapshot_borne_facet_and_setfield_is_refused() {
    let (mut ledger, delegator_key, _delegator_id, bearer_key, bearer_id, target_id) =
        bearer_world(|parent, target_id| {
            parent
                .capabilities
                .grant_faceted(target_id, AuthRequired::None, EFFECT_TRANSFER)
                .expect("parent holds a TRANSFER-ONLY faceted capability");
        });

    // Rights are equal (`None` ≤ `None`), so this exhibit isolates the FACET leg.
    let proof = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None,
        None, // no bearer facet ⇒ inherits the delegator's
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let faceted = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(proof),
            [0xBB; 32],
        ),
        &mut ledger,
    );
    match faceted {
        dregg_turn::TurnResult::Rejected {
            reason:
                TurnError::BearerCapFacetViolation {
                    target,
                    allowed_mask,
                    ..
                },
            ..
        } => {
            assert_eq!(target, target_id);
            assert_eq!(
                allowed_mask, EFFECT_TRANSFER,
                "the inherited facet must be the delegator's snapshot-borne mask"
            );
        }
        other => panic!(
            "a SetField under a TRANSFER-only snapshot-borne facet must be refused: {other:?}"
        ),
    }
    assert_ne!(ledger.get(&target_id).unwrap().state.fields[0], [0xBB; 32]);
}

/// NEW-REJECTS (facet, explicit): the bearer proof NAMES a wider facet than the
/// delegator's snapshot-borne one. This is the `is_facet_attenuation` leg, which
/// also lived inside the skipped block.
#[test]
fn b_bearer_cannot_name_a_facet_wider_than_the_snapshot_borne_one() {
    let (mut ledger, delegator_key, _delegator_id, bearer_key, bearer_id, target_id) =
        bearer_world(|parent, target_id| {
            parent
                .capabilities
                .grant_faceted(target_id, AuthRequired::None, EFFECT_TRANSFER)
                .expect("parent holds a TRANSFER-ONLY faceted capability");
        });

    let proof = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None,
        Some(EFFECT_TRANSFER | dregg_cell::EFFECT_SET_FIELD), // ← widens
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let widened = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(proof),
            [0xCC; 32],
        ),
        &mut ledger,
    );
    match widened {
        dregg_turn::TurnResult::Rejected {
            reason:
                TurnError::BearerCapFacetAmplification {
                    target,
                    delegator_mask,
                    bearer_mask,
                },
            ..
        } => {
            assert_eq!(target, target_id);
            assert_eq!(delegator_mask, EFFECT_TRANSFER);
            assert_eq!(bearer_mask, EFFECT_TRANSFER | dregg_cell::EFFECT_SET_FIELD);
        }
        other => panic!("a bearer facet WIDER than the delegator's must be refused: {other:?}"),
    }
}

/// NEW-REJECTS (expiry, through the bearer path): Exhibit A's wound reached this
/// site too. Past the snapshot capability's expiry the delegator holds nothing,
/// so the bearer proof it signed rests on nothing.
#[test]
fn b_bearer_proof_dies_with_the_snapshot_capability_it_rests_on() {
    let (mut ledger, delegator_key, _delegator_id, bearer_key, bearer_id, target_id) =
        bearer_world(|parent, target_id| {
            parent
                .capabilities
                .grant_with_expiry(target_id, AuthRequired::None, EXPIRES_AT)
                .expect("parent holds an expiring capability");
        });

    let proof = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None,
        None,
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(AFTER_EXPIRY);
    let lapsed = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(proof),
            [0xDD; 32],
        ),
        &mut ledger,
    );
    assert!(
        matches!(
            lapsed,
            dregg_turn::TurnResult::Rejected {
                reason: TurnError::BearerCapDelegatorLacksCapability { .. },
                ..
            }
        ),
        "a bearer proof resting on a LAPSED snapshot capability must be refused: {lapsed:?}"
    );
}

/// COMPLETENESS: an honest, non-amplifying bearer grant off a snapshot-borne
/// capability still works, and still writes. Without this the refusals above
/// would be indistinguishable from breaking the whole path.
#[test]
fn b_honest_bearer_attenuation_off_a_snapshot_still_commits() {
    let (mut ledger, delegator_key, _delegator_id, bearer_key, bearer_id, target_id) =
        bearer_world(|parent, target_id| {
            parent
                .capabilities
                .grant(target_id, AuthRequired::None)
                .expect("parent holds a full capability");
        });

    let proof = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None, // equal to held — attenuation is reflexive
        None,
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let honest = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(proof),
            [0xEE; 32],
        ),
        &mut ledger,
    );
    assert!(
        honest.is_committed(),
        "an honest bearer grant off a snapshot-borne capability must still commit: {honest:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0xEE; 32]);
}

/// COMPLETENESS: a genuinely ATTENUATING bearer grant off a snapshot-borne
/// capability commits — the refusals are about amplification, not about the
/// snapshot being a second-class source.
#[test]
fn b_strictly_narrowing_bearer_grant_off_a_snapshot_still_commits() {
    let (mut ledger, delegator_key, _delegator_id, bearer_key, bearer_id, target_id) =
        bearer_world(|parent, target_id| {
            parent
                .capabilities
                .grant_faceted(
                    target_id,
                    AuthRequired::None,
                    EFFECT_TRANSFER | dregg_cell::EFFECT_SET_FIELD,
                )
                .expect("parent holds a TRANSFER|SET_FIELD faceted capability");
        });

    let proof = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None,
        Some(dregg_cell::EFFECT_SET_FIELD), // strictly narrower than the held mask
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let narrowed = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(proof),
            [0xFF; 32],
        ),
        &mut ledger,
    );
    assert!(
        narrowed.is_committed(),
        "a strictly narrowing bearer grant must still commit: {narrowed:?}"
    );
    assert_eq!(ledger.get(&target_id).unwrap().state.fields[0], [0xFF; 32]);
}

/// COMPLETENESS: the c-list-borne bearer path is byte-for-byte the path it was.
/// `resolve_authority_at` orders c-list entries BEFORE snapshot-borne ones, so a
/// delegator holding the capability directly is bounded by exactly the entry
/// that bounded it before.
#[test]
fn b_clist_borne_bearer_delegation_is_unchanged() {
    let (delegator_key, mut delegator) = keyed_cell(80, 100_000);
    let (bearer_key, bearer) = keyed_cell(81, 100_000);
    let bearer_id = bearer.id();
    let mut target = Cell::with_balance([82u8; 32], [0u8; 32], 500);
    target.permissions = open_permissions();
    let target_id = target.id();
    delegator
        .capabilities
        .grant(target_id, AuthRequired::None)
        .expect("delegator holds the capability DIRECTLY");

    let mut ledger = Ledger::new();
    ledger.insert_cell(delegator).unwrap();
    ledger.insert_cell(bearer).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);

    let honest = signed_bearer_proof(
        &delegator_key,
        &bearer_key,
        target_id,
        AuthRequired::None,
        None,
    );
    let ok = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(honest),
            [0x01; 32],
        ),
        &mut ledger.clone(),
    );
    assert!(ok.is_committed(), "c-list-borne bearer must commit: {ok:?}");

    // And a c-list-borne amplification is still refused, as it always was.
    // A FRESH executor: the per-agent receipt chain is executor state, and the
    // commit above already advanced the bearer's chain.
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(2000);
    executor.set_block_height(BEFORE_EXPIRY);
    let (delegator2_key, mut delegator2) = keyed_cell(83, 100_000);
    delegator2
        .capabilities
        .grant(target_id, AuthRequired::Signature)
        .expect("narrow direct capability");
    ledger.insert_cell(delegator2).unwrap();
    let amplifying = signed_bearer_proof(
        &delegator2_key,
        &bearer_key,
        target_id,
        AuthRequired::None,
        None,
    );
    let bad = executor.execute(
        &set_field_on(
            bearer_id,
            target_id,
            Authorization::Bearer(amplifying),
            [0x02; 32],
        ),
        &mut ledger,
    );
    assert!(
        matches!(
            bad,
            dregg_turn::TurnResult::Rejected {
                reason: TurnError::BearerCapAmplification { .. },
                ..
            }
        ),
        "c-list-borne amplification must still be refused: {bad:?}"
    );
}

// ───────────── The root, asserted where both sources meet ─────────────

/// `Cell::resolve_authority_at` is the single point, and it answers for BOTH
/// stores at once. The three outcomes are distinct variants — which is the
/// structural repair: the old c-list-only lookup returned `Option::None` for
/// "actor owns the target" (unbounded, correct) AND for "authority came from a
/// store I did not read" (unbounded, a hole), and the amplification check keyed
/// on that `None`.
#[test]
fn resolver_answers_for_both_stores_and_separates_self_from_absent() {
    use dregg_cell::{AuthoritySource, HeldAuthority};

    let (mut ledger, parent_id, child_id, target_id) =
        snapshot_world([90u8; 32], BEFORE_EXPIRY, |parent, target_id| {
            parent
                .capabilities
                .grant_with_expiry(target_id, AuthRequired::None, EXPIRES_AT)
                .expect("expiring capability");
        });
    let unrelated = Cell::with_balance([91u8; 32], [0u8; 32], 0);
    let unrelated_id = unrelated.id();
    ledger.insert_cell(unrelated).unwrap();

    let child = ledger.get(&child_id).unwrap();

    // Snapshot-borne, live: resolved, and TAGGED as snapshot-borne so the
    // consumed-cap witness recorder does not ask the child's own cap tree for a
    // membership path that cannot exist.
    match child.resolve_authority_at(&target_id, BEFORE_EXPIRY) {
        HeldAuthority::Caps(caps) => {
            assert_eq!(caps.len(), 1);
            assert_eq!(caps[0].source, AuthoritySource::DelegationSnapshot);
        }
        other => panic!("live snapshot authority must resolve to Caps: {other:?}"),
    }

    // Snapshot-borne, lapsed: gone.
    assert!(matches!(
        child.resolve_authority_at(&target_id, AFTER_EXPIRY),
        HeldAuthority::NoneHeld
    ));

    // Self and absent are DIFFERENT answers.
    assert!(matches!(
        child.resolve_authority_at(&child_id, AFTER_EXPIRY),
        HeldAuthority::SelfOwned
    ));
    assert!(matches!(
        child.resolve_authority_at(&unrelated_id, BEFORE_EXPIRY),
        HeldAuthority::NoneHeld
    ));

    // The parent's c-list-borne authority is tagged as such.
    match ledger
        .get(&parent_id)
        .unwrap()
        .resolve_authority_at(&target_id, BEFORE_EXPIRY)
    {
        HeldAuthority::Caps(caps) => {
            assert_eq!(caps[0].source, AuthoritySource::Clist);
        }
        other => panic!("parent's direct authority must resolve to Caps: {other:?}"),
    }

    // A permission-lattice sanity pin: the target's own `AuthRequired` is what
    // the DIRECT cross-cell path consults and the Bearer path short-circuits.
    assert_eq!(
        *ledger
            .get(&target_id)
            .unwrap()
            .permissions
            .for_action(PAction::SetState),
        AuthRequired::None
    );
}
