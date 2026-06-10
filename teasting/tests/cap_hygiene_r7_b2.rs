//! EXECUTOR CAP-HYGIENE close: R7 epoch-at-retrieval + B2 runtime-laxity.
//!
//! # R7 (DREGG3 §6) — epoch-at-retrieval
//!
//! THE LAUNDERING ATTACK (live before this close): a capability sealed into a
//! box BEFORE a revocation could be unsealed + exercised AFTER it — storage
//! laundered freshness. The R7 rule: stored caps carry the grantor's
//! `delegation_epoch` captured at store time (`SealedBox::seal_epoch`,
//! `CapabilityRef::stored_epoch`), and retrieval/exercise re-checks the stamp
//! against the grantor's CURRENT epoch, rejecting with
//! `TurnError::CapabilityStale`.
//!
//! Migration window (loud): unstamped boxes (`sealer: None`) and direct-grant
//! caps (`stored_epoch: None`) are EXEMPT — pre-R7 persisted state keeps the
//! legacy semantics until refreshed.
//!
//! # B2 — the executor must install genuinely-attenuated grants
//!
//! `apply_grant_capability` used to gate ONLY the AuthRequired axis and then
//! install `expires_at: None, allowed_effects: None` — amplifying on the mask
//! + expiry axes. The circuit (Phase B2) already enforces submask +
//! AuthRequired-lattice + expiry-monotone; these tests pin the executor to the
//! same semantics, including the FAITHFUL install of the granted fields.

use dregg_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, EFFECT_ALL, EFFECT_SET_FIELD, EFFECT_TRANSFER,
    Ledger, Permissions, SealPair,
};
use dregg_turn::{
    ActionBuilder, Effect, TurnBuilder, TurnError, TurnResult,
    executor::{ComputronCosts, TurnExecutor},
};

// ---------------------------------------------------------------------------
// Shared helpers (same shape as teasting/tests/coverage_misc_effects.rs)
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
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn zero_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
}

fn exec_single(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    effects: Vec<Effect>,
) -> TurnResult {
    let mut ab = ActionBuilder::new_unchecked_for_tests(agent, "test-op", agent);
    for e in effects {
        ab = ab.effect(e);
    }
    let action = ab.build();
    let mut builder = TurnBuilder::new(agent, nonce);
    builder.add_action(action);
    let turn = builder.fee(0).build();
    executor.execute(&turn, ledger)
}

fn assert_committed(result: &TurnResult, ctx: &str) {
    assert!(
        result.is_committed(),
        "{ctx}: expected committed, got {result:?}"
    );
}

fn assert_capability_stale(result: &TurnResult, ctx: &str) {
    match result {
        TurnResult::Rejected {
            reason: TurnError::CapabilityStale { .. },
            ..
        } => {}
        other => panic!("{ctx}: expected Rejected(CapabilityStale), got {other:?}"),
    }
}

/// Replicate the executor's seal_capability_id derivation (pub(super)).
fn seal_capability_id_for_test(pair_id: &[u8; 32], is_sealer: bool) -> CellId {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-seal capability-id v1");
    hasher.update(pair_id);
    hasher.update(if is_sealer { b"sealer" } else { b"unsealer" });
    CellId::from_bytes(*hasher.finalize().as_bytes())
}

fn plain_cap(target: CellId) -> CapabilityRef {
    CapabilityRef {
        target,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
    }
}

/// Set up [sealer P (with a delegated child C), unsealer-holder A,
/// recipient R, cap-target T] + a box sealed by P STAMPED at P's current
/// delegation epoch. Returns (ledger, p_id, c_id, a_id, r_id, sealed_box).
fn seal_attack_setup() -> (
    Ledger,
    CellId,
    CellId,
    CellId,
    CellId,
    dregg_cell::SealedBox,
) {
    let parent = make_cell(1, 1_000);
    let p_id = parent.id();
    let mut child = make_cell(2, 0);
    // The child is delegated from P (the link RevokeDelegation requires).
    child.delegate = Some(p_id);
    let c_id = child.id();
    let actor = make_cell(3, 1_000);
    let a_id = actor.id();
    let recipient = make_cell(4, 0);
    let r_id = recipient.id();
    let target = make_cell(5, 0);
    let t_id = target.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(child).unwrap();
    ledger.insert_cell(actor).unwrap();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(target).unwrap();

    // Seal a cap over T, stamped with P's identity + CURRENT epoch — the
    // same stamp `apply_seal` produces (the box itself travels client-side,
    // so the regression builds it via the shared `seal_stamped` primitive).
    let pair = SealPair::generate();
    let seal_epoch = ledger.get(&p_id).unwrap().state.delegation_epoch();
    let sealed = pair.seal_stamped(&plain_cap(t_id), p_id, seal_epoch);

    // Give A the unsealer capability (key material in breadstuff).
    let unsealer_cap_id = seal_capability_id_for_test(&pair.id, false);
    ledger
        .get_mut(&a_id)
        .unwrap()
        .capabilities
        .grant_with_breadstuff(
            unsealer_cap_id,
            AuthRequired::None,
            Some(pair.unsealer_secret),
        );

    (ledger, p_id, c_id, a_id, r_id, sealed)
}

// ===========================================================================
// R7 — seal / unseal
// ===========================================================================

/// THE LAUNDERING ATTACK as a regression: seal cap → revoke (P's epoch bump
/// via a real `RevokeDelegation` turn) → unseal must be REJECTED with
/// `CapabilityStale`, and the recipient must receive NOTHING.
#[test]
fn r7_unseal_rejects_cap_sealed_before_revocation() {
    let (mut ledger, p_id, c_id, a_id, r_id, sealed) = seal_attack_setup();
    let executor = zero_executor();

    // P revokes the child's delegation — bumps P's delegation_epoch past the
    // box's stamp.
    let revoke = exec_single(
        &executor,
        &mut ledger,
        p_id,
        0,
        vec![Effect::RevokeDelegation { child: c_id }],
    );
    assert_committed(&revoke, "RevokeDelegation (epoch bump)");
    assert_eq!(
        ledger.get(&p_id).unwrap().state.delegation_epoch(),
        1,
        "revocation must bump the parent's delegation epoch"
    );

    // The laundering attempt: unseal the pre-revocation box.
    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::Unseal {
            sealed_box: sealed,
            recipient: r_id,
        }],
    );
    assert_capability_stale(&result, "Unseal after sealer's revocation");
    assert_eq!(
        ledger.get(&r_id).unwrap().capabilities.len(),
        0,
        "stale unseal must install NOTHING on the recipient"
    );
}

/// Control: the identical seal → unseal flow WITHOUT the revocation commits
/// and installs the capability.
#[test]
fn r7_unseal_fresh_stamped_box_commits() {
    let (mut ledger, _p_id, _c_id, a_id, r_id, sealed) = seal_attack_setup();
    let executor = zero_executor();

    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::Unseal {
            sealed_box: sealed,
            recipient: r_id,
        }],
    );
    assert_committed(&result, "Unseal (no revocation)");
    assert_eq!(
        ledger.get(&r_id).unwrap().capabilities.len(),
        1,
        "fresh unseal must install the capability"
    );
}

/// Migration window (documented semantics): an UNSTAMPED box (`sealer: None`,
/// e.g. sealed pre-R7) is exempt from the staleness check and still unseals
/// after a revocation. This pins the legacy-exemption behavior so a future
/// tightening is a deliberate decision, not drift.
#[test]
fn r7_unseal_legacy_unstamped_box_exempt_from_epoch_check() {
    let (mut ledger, p_id, c_id, a_id, r_id, _stamped) = seal_attack_setup();
    let executor = zero_executor();

    // Rebuild an UNSTAMPED box for the same cap with the same pair the
    // unsealer cap was injected for — recover the pair from the injected
    // breadstuff so the test stays one setup.
    let unsealer_cap = ledger
        .get(&a_id)
        .unwrap()
        .capabilities
        .iter()
        .next()
        .unwrap()
        .clone();
    let pair = SealPair::from_secret(unsealer_cap.breadstuff.unwrap());
    let t_id = make_cell(5, 0).id();
    let legacy_box = pair.seal(&plain_cap(t_id));
    assert_eq!(legacy_box.sealer, None);

    let revoke = exec_single(
        &executor,
        &mut ledger,
        p_id,
        0,
        vec![Effect::RevokeDelegation { child: c_id }],
    );
    assert_committed(&revoke, "RevokeDelegation");

    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::Unseal {
            sealed_box: legacy_box,
            recipient: r_id,
        }],
    );
    assert_committed(&result, "Unseal of legacy unstamped box (migration window)");
}

// ===========================================================================
// R7 — exercise-via-capability with a delegated snapshot
// ===========================================================================

/// Set up [target/grantor T (with delegated child C), actor A holding a
/// SNAPSHOT-stamped cap over T]. Returns (ledger, t_id, c_id, a_id, slot).
fn exercise_snapshot_setup() -> (Ledger, CellId, CellId, CellId, u32) {
    let target = make_cell(10, 1_000);
    let t_id = target.id();
    let mut child = make_cell(11, 0);
    child.delegate = Some(t_id);
    let c_id = child.id();
    let actor = make_cell(12, 1_000);
    let a_id = actor.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(child).unwrap();
    ledger.insert_cell(actor).unwrap();

    // A holds a cap over T stamped with T's delegation epoch at store time
    // (the delegation-snapshot shape).
    let stored_epoch = ledger.get(&t_id).unwrap().state.delegation_epoch();
    let slot = ledger
        .get_mut(&a_id)
        .unwrap()
        .capabilities
        .grant_snapshot(t_id, AuthRequired::None, None, stored_epoch)
        .unwrap();

    (ledger, t_id, c_id, a_id, slot)
}

fn set_field_inner(t_id: CellId) -> Effect {
    Effect::SetField {
        cell: t_id,
        index: 0,
        value: [9u8; 32],
    }
}

/// Snapshot-stamped cap → grantor revokes (epoch bump) → exercise REJECTED.
#[test]
fn r7_exercise_rejects_stale_snapshot_cap() {
    let (mut ledger, t_id, c_id, a_id, slot) = exercise_snapshot_setup();
    let executor = zero_executor();

    let revoke = exec_single(
        &executor,
        &mut ledger,
        t_id,
        0,
        vec![Effect::RevokeDelegation { child: c_id }],
    );
    assert_committed(&revoke, "RevokeDelegation (grantor epoch bump)");

    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::ExerciseViaCapability {
            cap_slot: slot,
            inner_effects: vec![set_field_inner(t_id)],
        }],
    );
    assert_capability_stale(&result, "ExerciseViaCapability after grantor revocation");
    assert_eq!(
        ledger.get(&t_id).unwrap().state.fields[0],
        [0u8; 32],
        "stale exercise must not mutate the target"
    );
}

/// Control: the same exercise WITHOUT the revocation commits.
#[test]
fn r7_exercise_fresh_snapshot_cap_commits() {
    let (mut ledger, t_id, _c_id, a_id, slot) = exercise_snapshot_setup();
    let executor = zero_executor();

    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::ExerciseViaCapability {
            cap_slot: slot,
            inner_effects: vec![set_field_inner(t_id)],
        }],
    );
    assert_committed(&result, "ExerciseViaCapability (no revocation)");
    assert_eq!(ledger.get(&t_id).unwrap().state.fields[0], [9u8; 32]);
}

/// Migration window: a DIRECT grant (`stored_epoch: None`) is exempt — it
/// still exercises after the grantor's epoch bump. (Direct grants are
/// revoked by `RevokeCapability` on the holder's c-list, not by epoch.)
#[test]
fn r7_exercise_direct_grant_exempt_from_epoch_check() {
    let (mut ledger, t_id, c_id, a_id, _snapshot_slot) = exercise_snapshot_setup();
    let executor = zero_executor();

    // A second, DIRECT (unstamped) cap over T.
    let direct_slot = ledger
        .get_mut(&a_id)
        .unwrap()
        .capabilities
        .grant(t_id, AuthRequired::None)
        .unwrap();

    let revoke = exec_single(
        &executor,
        &mut ledger,
        t_id,
        0,
        vec![Effect::RevokeDelegation { child: c_id }],
    );
    assert_committed(&revoke, "RevokeDelegation");

    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::ExerciseViaCapability {
            cap_slot: direct_slot,
            inner_effects: vec![set_field_inner(t_id)],
        }],
    );
    assert_committed(&result, "direct-grant exercise (migration-window exempt)");
}

// ===========================================================================
// B2 — grant must be attenuated on EVERY axis and installed faithfully
// ===========================================================================

/// Set up [granter G holding a faceted+expiring cap over T, beneficiary B].
/// G holds: permissions=None(⊤-most-permissive is fine for the lattice axis),
/// allowed_effects=Some(EFFECT_TRANSFER), expires_at=Some(100).
fn grant_setup() -> (Ledger, CellId, CellId, CellId) {
    let granter = make_cell(20, 1_000);
    let g_id = granter.id();
    let beneficiary = make_cell(21, 0);
    let b_id = beneficiary.id();
    let target = make_cell(22, 0);
    let t_id = target.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(granter).unwrap();
    ledger.insert_cell(beneficiary).unwrap();
    ledger.insert_cell(target).unwrap();

    // G's held cap: TRANSFER-only facet, expiring at height 100.
    let g = ledger.get_mut(&g_id).unwrap();
    let slot = g
        .capabilities
        .grant_faceted(t_id, AuthRequired::None, EFFECT_TRANSFER)
        .unwrap();
    g.capabilities
        .attenuate_in_place(slot, AuthRequired::None, None, Some(100))
        .unwrap();

    (ledger, g_id, b_id, t_id)
}

fn grant_effect(from: CellId, to: CellId, cap: CapabilityRef) -> Effect {
    Effect::GrantCapability { from, to, cap }
}

/// Mask axis: granting a WIDER effect mask than held must be rejected —
/// both the `None` (= EFFECT_ALL) widening and an explicit superset mask.
#[test]
fn b2_grant_rejects_mask_amplification() {
    for widened_mask in [None, Some(EFFECT_TRANSFER | EFFECT_SET_FIELD), Some(EFFECT_ALL)] {
        let (mut ledger, g_id, b_id, t_id) = grant_setup();
        let executor = zero_executor();
        let mut cap = plain_cap(t_id);
        cap.allowed_effects = widened_mask;
        cap.expires_at = Some(50); // expiry axis kept legal — isolate the mask axis
        let result = exec_single(
            &executor,
            &mut ledger,
            g_id,
            0,
            vec![grant_effect(g_id, b_id, cap)],
        );
        assert!(
            matches!(
                result,
                TurnResult::Rejected {
                    reason: TurnError::DelegationDenied { .. },
                    ..
                }
            ),
            "grant with widened mask {widened_mask:?} must be DelegationDenied, got {result:?}"
        );
        assert_eq!(
            ledger.get(&b_id).unwrap().capabilities.len(),
            0,
            "rejected grant must install nothing"
        );
    }
}

/// Expiry axis: granting unbounded (`None`) or later-expiring from a
/// height-bounded hold must be rejected (expiry-monotone, None = ⊤).
#[test]
fn b2_grant_rejects_expiry_amplification() {
    for widened_expiry in [None, Some(200u64)] {
        let (mut ledger, g_id, b_id, t_id) = grant_setup();
        let executor = zero_executor();
        let mut cap = plain_cap(t_id);
        cap.allowed_effects = Some(EFFECT_TRANSFER); // mask axis kept legal
        cap.expires_at = widened_expiry;
        let result = exec_single(
            &executor,
            &mut ledger,
            g_id,
            0,
            vec![grant_effect(g_id, b_id, cap)],
        );
        assert!(
            matches!(
                result,
                TurnResult::Rejected {
                    reason: TurnError::DelegationDenied { .. },
                    ..
                }
            ),
            "grant with widened expiry {widened_expiry:?} must be DelegationDenied, got {result:?}"
        );
    }
}

/// The faithful-install payoff: a properly attenuated grant commits AND the
/// installed entry carries the granted `allowed_effects` + `expires_at`
/// (+ stored_epoch) — not the old silently-widened `None`/`None`.
#[test]
fn b2_grant_installs_genuinely_attenuated_entry() {
    let (mut ledger, g_id, b_id, t_id) = grant_setup();
    let executor = zero_executor();
    let mut cap = plain_cap(t_id);
    cap.allowed_effects = Some(EFFECT_TRANSFER);
    cap.expires_at = Some(50);
    cap.stored_epoch = Some(0);

    let result = exec_single(
        &executor,
        &mut ledger,
        g_id,
        0,
        vec![grant_effect(g_id, b_id, cap)],
    );
    assert_committed(&result, "attenuated grant");

    let installed = ledger
        .get(&b_id)
        .unwrap()
        .capabilities
        .lookup_by_target(&t_id)
        .expect("grant must install an entry on the beneficiary")
        .clone();
    assert_eq!(
        installed.allowed_effects,
        Some(EFFECT_TRANSFER),
        "installed entry must carry the granted mask (B2 faithful install)"
    );
    assert_eq!(
        installed.expires_at,
        Some(50),
        "installed entry must carry the granted expiry (B2 faithful install)"
    );
    assert_eq!(
        installed.stored_epoch,
        Some(0),
        "installed entry must carry the R7 snapshot stamp"
    );
}

/// Self-grant: the implicit self-cap is ⊤ on every axis, so any requested
/// mask/expiry is admissible — and must be installed faithfully, not widened.
#[test]
fn b2_self_grant_carries_requested_attenuation() {
    let granter = make_cell(30, 1_000);
    let g_id = granter.id();
    let beneficiary = make_cell(31, 0);
    let b_id = beneficiary.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(granter).unwrap();
    ledger.insert_cell(beneficiary).unwrap();
    let executor = zero_executor();

    let mut cap = plain_cap(g_id); // target == from: self-grant
    cap.allowed_effects = Some(EFFECT_TRANSFER);
    cap.expires_at = Some(10);

    let result = exec_single(
        &executor,
        &mut ledger,
        g_id,
        0,
        vec![grant_effect(g_id, b_id, cap)],
    );
    assert_committed(&result, "attenuated self-grant");

    let installed = ledger
        .get(&b_id)
        .unwrap()
        .capabilities
        .lookup_by_target(&g_id)
        .unwrap()
        .clone();
    assert_eq!(installed.allowed_effects, Some(EFFECT_TRANSFER));
    assert_eq!(installed.expires_at, Some(10));
}

/// Unseal faithful install: a faceted + expiring sealed cap must come out of
/// the box with its facet/expiry INTACT on the recipient's c-list (the old
/// install path widened both to None).
#[test]
fn b2_unseal_installs_faithful_fields() {
    let (mut ledger, p_id, _c_id, a_id, r_id, _plain) = seal_attack_setup();
    let executor = zero_executor();

    // Re-derive the pair from the injected unsealer cap and seal a FACETED
    // cap (stamped fresh, so the R7 gate passes).
    let unsealer_cap = ledger
        .get(&a_id)
        .unwrap()
        .capabilities
        .iter()
        .next()
        .unwrap()
        .clone();
    let pair = SealPair::from_secret(unsealer_cap.breadstuff.unwrap());
    let t_id = make_cell(5, 0).id();
    let mut faceted = plain_cap(t_id);
    faceted.allowed_effects = Some(EFFECT_TRANSFER);
    faceted.expires_at = Some(77);
    let seal_epoch = ledger.get(&p_id).unwrap().state.delegation_epoch();
    let sealed = pair.seal_stamped(&faceted, p_id, seal_epoch);

    let result = exec_single(
        &executor,
        &mut ledger,
        a_id,
        0,
        vec![Effect::Unseal {
            sealed_box: sealed,
            recipient: r_id,
        }],
    );
    assert_committed(&result, "Unseal of faceted cap");
    let installed = ledger
        .get(&r_id)
        .unwrap()
        .capabilities
        .lookup_by_target(&t_id)
        .expect("unseal must install on recipient")
        .clone();
    assert_eq!(
        installed.allowed_effects,
        Some(EFFECT_TRANSFER),
        "unseal must preserve the facet mask"
    );
    assert_eq!(
        installed.expires_at,
        Some(77),
        "unseal must preserve the expiry"
    );
}
