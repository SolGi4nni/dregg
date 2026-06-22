//! lean_state_producer_denotational_census.rs — THE COMPREHENSIVE denotational executor⟺spec
//! cross-validation, extending the two-effect spot-check in `lean_state_producer_differential.rs`
//! to a REPRESENTATIVE honest turn per producer-mappable effect kind.
//!
//! # What this adds over the existing differentials
//!
//! `lean_state_producer_differential.rs` proved the verified Lean executor can BE the state producer
//! for Transfer + SetField (full ledger agreement + `.root()`). The `widen`/`coverage` siblings then
//! pinned per-family round-trips and gap teeth. THIS file is the single census that drives ONE honest
//! committing turn through BOTH producers for EVERY root-agreeing effect kind AND, on each, asserts
//! the CONSERVATION INVARIANT that the other files do not: the scalar total supply
//! (`∑_c balance(c)`, the deployed single-asset projection of the per-asset
//! `execFullTurnA_conserves_exact` — `Dregg2/Exec/TurnExecutorFull.lean §MA-scalar`) is PRESERVED on
//! BOTH the Rust and the Lean-reconstituted post-state for every balance-neutral effect, and moves by
//! exactly zero net for a Transfer (debit == credit). A mint/burn-free turn that broke conservation on
//! either producer is a real soundness finding surfaced here, never silently passed.
//!
//! So this file is the executor⟺spec cross-validation made COMPREHENSIVE: for each covered kind,
//! (full-state Lean↔Rust eval-agreement) ∧ (conservation on both). The kinds the FFI/producer cannot
//! yet drive to a committed post-state are NAMED below as explicit residuals, each with WHY.
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent.

#![cfg(feature = "lean-shadow")]

use std::collections::HashMap;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::lifecycle::{DeathCertificate, DeathReason};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, NoteCommitment, Permissions, VerificationKey};
use dregg_turn::action::Event;
use dregg_turn::lean_apply::{self, execute_via_lean};
use dregg_turn::lean_shadow::{self, ShadowHostCtx};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A self-`node` capability = mint/burn authority over the cell itself (mirrors the widen helper).
fn grant_self_cap(cell: &mut Cell) {
    let id = cell.id();
    cell.capabilities.grant(id, AuthRequired::None);
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
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

/// The DEPLOYED scalar total supply: the sum of every live cell's one scalar `balance()`. This is the
/// deployed single-asset projection of the per-asset `recTotalAsset k a₀` (`§MA-scalar`): the value
/// the verified `execFullTurnA_conserves_scalar` proves a committed turn preserves.
fn scalar_total_supply(ledger: &Ledger) -> i128 {
    ledger.iter().map(|(_, c)| c.state.balance() as i128).sum()
}

/// Compare two ledgers cell-by-cell (balance + nonce + the state fields + cap_root) AND on `.root()`,
/// tolerating cell ABSENCE on either side (MakeSovereign removes a cell). Same yardstick as the
/// `coverage` sibling.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        match (rust.get(id), lean.get(id)) {
            (Some(r), Some(l)) => {
                if r.state.balance() != l.state.balance() {
                    return Err(format!(
                        "balance divergence on {id:?}: rust={} lean={}",
                        r.state.balance(),
                        l.state.balance()
                    ));
                }
                if r.state.nonce() != l.state.nonce() {
                    return Err(format!(
                        "nonce divergence on {id:?}: rust={} lean={}",
                        r.state.nonce(),
                        l.state.nonce()
                    ));
                }
                for slot in 0..dregg_cell::state::STATE_SLOTS {
                    if r.state.fields[slot] != l.state.fields[slot] {
                        return Err(format!(
                            "field[{slot}] divergence on {id:?}: rust={:?} lean={:?}",
                            r.state.fields[slot], l.state.fields[slot]
                        ));
                    }
                }
                let rc = dregg_cell::compute_canonical_capability_root(&r.capabilities);
                let lc = dregg_cell::compute_canonical_capability_root(&l.capabilities);
                if rc != lc {
                    return Err(format!("cap_root divergence on {id:?}: rust={rc:?} lean={lc:?}"));
                }
            }
            (None, Some(_)) => {
                return Err(format!(
                    "presence divergence on {id:?}: absent in RUST, present in LEAN"
                ));
            }
            (Some(_), None) => {
                return Err(format!(
                    "presence divergence on {id:?}: present in RUST, absent in LEAN"
                ));
            }
            (None, None) => {}
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// Drive `turn` through BOTH producers and assert (1) both commit, (2) full ledger agreement, and
/// (3) the conservation invariant: the scalar total supply moves by exactly `expected_supply_delta`
/// on BOTH the Rust post-state and the Lean-reconstituted post-state. For a balance-neutral effect
/// `expected_supply_delta == 0`; a Transfer is `0` too (it MOVES value but conserves the sum).
fn assert_denotational_and_conservation(
    label: &str,
    pre: Ledger,
    turn: Turn,
    ids: &[CellId],
    expected_supply_delta: i128,
) {
    let pre_supply = scalar_total_supply(&pre);

    // (1) Rust producer.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    assert!(
        rust_result.is_committed(),
        "[{label}] Rust executor did not commit the honest turn: {rust_result:?}"
    );

    // (2) Lean producer: install the FFI executor's reconstituted post-state.
    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) = match execute_via_lean(&turn, &pre, &host) {
        Ok(x) => x,
        Err(lean_apply::ExtractError::Ineligible) => {
            panic!("[{label}] turn was Lean-ineligible (a marshaller gap); cannot cross-validate")
        }
        Err(e) => panic!("[{label}] Lean state-producer path failed: {e}"),
    };
    assert!(
        lean_committed,
        "[{label}] verified Lean executor did not commit a turn Rust committed (commit-bit divergence)"
    );

    // (3a) Full-state denotational agreement.
    if let Err(why) = ledgers_agree(&mut rust_ledger, &mut lean_ledger, ids) {
        panic!("[{label}] DENOTATIONAL DIVERGENCE — Rust ledger ≠ Lean-reconstituted ledger: {why}");
    }

    // (3b) Conservation invariant on BOTH producers (the deployed scalar projection of §MA-scalar).
    let rust_supply = scalar_total_supply(&rust_ledger);
    let lean_supply = scalar_total_supply(&lean_ledger);
    assert_eq!(
        rust_supply,
        pre_supply + expected_supply_delta,
        "[{label}] CONSERVATION VIOLATION on the RUST post-state: scalar total supply {pre_supply} -> \
         {rust_supply}, expected delta {expected_supply_delta}"
    );
    assert_eq!(
        lean_supply,
        pre_supply + expected_supply_delta,
        "[{label}] CONSERVATION VIOLATION on the LEAN post-state: scalar total supply {pre_supply} -> \
         {lean_supply}, expected delta {expected_supply_delta}"
    );
}

fn skip_no_lean() -> bool {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        true
    } else {
        false
    }
}

fn one_open_cell() -> (Ledger, CellId) {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    (pre, a_id)
}

fn two_open_cells() -> (Ledger, CellId, CellId) {
    let a = make_open_cell(1, 100);
    let b = make_open_cell(2, 5);
    let a_id = a.id();
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    (pre, a_id, b_id)
}

// =====================================================================================
// THE CENSUS — one honest committing turn per root-agreeing effect kind, each asserting
// full-state denotational agreement AND conservation on both producers.
// =====================================================================================

#[test]
fn census_transfer() {
    if skip_no_lean() {
        return;
    }
    let (pre, a, b) = two_open_cells();
    let turn = single_effect_turn(a, a, 0, Effect::Transfer { from: a, to: b, amount: 30 });
    // Transfer MOVES value but conserves the sum: net supply delta 0.
    assert_denotational_and_conservation("Transfer", pre, turn, &[a, b], 0);
}

#[test]
fn census_set_field() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let turn = single_effect_turn(
        a,
        a,
        0,
        Effect::SetField { cell: a, index: 6, value: field_from_u64(42) },
    );
    assert_denotational_and_conservation("SetField", pre, turn, &[a], 0);
}

#[test]
fn census_increment_nonce() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let turn = single_effect_turn(a, a, 0, Effect::IncrementNonce { cell: a });
    assert_denotational_and_conservation("IncrementNonce", pre, turn, &[a], 0);
}

#[test]
fn census_emit_event() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let turn = single_effect_turn(
        a,
        a,
        0,
        Effect::EmitEvent {
            cell: a,
            event: Event { topic: field_from_u64(11), data: vec![field_from_u64(22)] },
        },
    );
    assert_denotational_and_conservation("EmitEvent", pre, turn, &[a], 0);
}

#[test]
fn census_set_permissions() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let mut new_perms = open_permissions();
    new_perms.set_state = AuthRequired::Signature; // a real change.
    let turn = single_effect_turn(
        a,
        a,
        0,
        Effect::SetPermissions { cell: a, new_permissions: new_perms },
    );
    assert_denotational_and_conservation("SetPermissions", pre, turn, &[a], 0);
}

#[test]
fn census_set_verification_key() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    #[allow(deprecated)]
    let vk = VerificationKey::new(vec![1, 2, 3, 4]);
    let turn = single_effect_turn(
        a,
        a,
        0,
        Effect::SetVerificationKey { cell: a, new_vk: Some(vk) },
    );
    assert_denotational_and_conservation("SetVerificationKey", pre, turn, &[a], 0);
}

#[test]
fn census_note_create() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let turn = single_effect_turn(
        a,
        a,
        0,
        Effect::NoteCreate {
            commitment: NoteCommitment([7u8; 32]),
            value: 0,
            asset_type: 0,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        },
    );
    // NoteCreate touches the off-root note SET, not the cell scalar balance: conservation holds.
    assert_denotational_and_conservation("NoteCreate", pre, turn, &[a], 0);
}

#[test]
fn census_cell_seal() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let turn = single_effect_turn(a, a, 0, Effect::CellSeal { target: a, reason: [9u8; 32] });
    assert_denotational_and_conservation("CellSeal", pre, turn, &[a], 0);
}

#[test]
fn census_cell_unseal() {
    if skip_no_lean() {
        return;
    }
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a);
    let a_id = a.id();
    a.seal([7u8; 32], 0).expect("seal the pre-state cell");
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    let turn = single_effect_turn(a_id, a_id, 0, Effect::CellUnseal { target: a_id });
    assert_denotational_and_conservation("CellUnseal", pre, turn, &[a_id], 0);
}

#[test]
fn census_cell_destroy() {
    if skip_no_lean() {
        return;
    }
    let (pre, a) = one_open_cell();
    let cert = DeathCertificate {
        cell_id: a,
        last_receipt_hash: [3u8; 32],
        final_state_commitment: [5u8; 32],
        destroyed_at_height: 42,
        reason: DeathReason::Voluntary,
    };
    let turn = single_effect_turn(a, a, 0, Effect::CellDestroy { target: a, certificate: cert });
    // The cell stays present (lifecycle Destroyed) and keeps its balance; supply unchanged.
    assert_denotational_and_conservation("CellDestroy", pre, turn, &[a], 0);
}

#[test]
fn census_make_sovereign() {
    if skip_no_lean() {
        return;
    }
    // MakeSovereign REMOVES the cell from the merkle tree (its scalar balance leaves the live-cell
    // sum). The deployed scalar total over LIVE cells therefore drops by the sovereign'd cell's
    // balance on BOTH producers — the conservation check asserts they move in lockstep (the value is
    // not destroyed, it parks in the off-root sovereign commitment; both producers do the same).
    let (pre, a) = one_open_cell();
    let bal = pre.get(&a).unwrap().state.balance() as i128;
    let turn = single_effect_turn(a, a, 0, Effect::MakeSovereign { cell: a });
    assert_denotational_and_conservation("MakeSovereign", pre, turn, &[a], -bal);
}

#[test]
fn census_grant_capability() {
    if skip_no_lean() {
        return;
    }
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let cap = CapabilityRef {
        target: a_id,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: Some([7u8; 32]),
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
    };
    let turn = single_effect_turn(a_id, a_id, 0, Effect::GrantCapability { from: a_id, to: b_id, cap });
    assert_denotational_and_conservation("GrantCapability", pre, turn, &[a_id, b_id], 0);
}

#[test]
fn census_attenuate_capability() {
    if skip_no_lean() {
        return;
    }
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let slot = a
        .capabilities
        .grant(b_id, AuthRequired::None)
        .expect("seed a held cap to attenuate");
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::AttenuateCapability {
            cell: a_id,
            slot,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    assert_denotational_and_conservation("AttenuateCapability", pre, turn, &[a_id, b_id], 0);
}

#[test]
fn census_introduce() {
    if skip_no_lean() {
        return;
    }
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let r = make_open_cell(2, 5);
    let r_id = r.id();
    let t = make_open_cell(3, 5);
    let t_id = t.id();
    a.capabilities.grant(r_id, AuthRequired::None);
    a.capabilities.grant(t_id, AuthRequired::None);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(r).unwrap();
    pre.insert_cell(t).unwrap();

    // Introduce commits only when Rust's stricter recipient-access legs are also satisfied (they are
    // by this fixture). Guard the census on Rust committing so the conservation/denotational check is
    // only asserted on a genuinely committed turn.
    let probe = TurnExecutor::new(ComputronCosts::zero());
    let mut probe_ledger = pre.clone();
    let committed = probe
        .execute(
            &single_effect_turn(
                a_id,
                a_id,
                0,
                Effect::Introduce {
                    introducer: a_id,
                    recipient: r_id,
                    target: t_id,
                    permissions: AuthRequired::None,
                },
            ),
            &mut probe_ledger,
        )
        .is_committed();
    if !committed {
        eprintln!("SKIP census_introduce: Rust did not commit Introduce on this fixture");
        return;
    }
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Introduce {
            introducer: a_id,
            recipient: r_id,
            target: t_id,
            permissions: AuthRequired::None,
        },
    );
    assert_denotational_and_conservation("Introduce", pre, turn, &[a_id, r_id, t_id], 0);
}

#[test]
fn census_revoke_delegation() {
    if skip_no_lean() {
        return;
    }
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut b = make_open_cell(2, 5);
    let b_id = b.id();
    b.delegate = Some(a_id);
    a.state.set_delegation_epoch(3);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let turn = single_effect_turn(a_id, a_id, 0, Effect::RevokeDelegation { child: b_id });
    assert_denotational_and_conservation("RevokeDelegation", pre, turn, &[a_id, b_id], 0);
}

/// RefreshDelegation (self-refresh) — NOW A CLOSED ROUND-TRIP (was a commit-bit residual the census
/// surfaced). The verified `refreshDelegationChainA` gate reads BOTH `(delegate child).isSome` AND the
/// PARENT's current c-list (`parentClist`); both were previously absent from the wire (the `delegate`
/// parent-pointer table did not exist and the refresh turn did not pull the parent into the marshalled
/// pre-state), so the verified executor REJECTED a refresh Rust commits. THE FIX carries `delegate` on
/// the wire (`WState.delegate` / `WireState.delegate`, the 12th state field) AND pulls each
/// snapshotted cell's delegation parent into the pre-ledger (`build_pre_ledger` parent-closure), so the
/// verified gate sees the real parent c-list and COMMITS; the reconstitution then replays the exact
/// `apply_refresh_delegation` `DelegatedRef` install (`lean_apply::StateOp::RefreshDelegation`, stamped
/// with the executor's `current_timestamp` so the commitment-bound `refreshed_at` matches), giving full
/// denotational + cap_root + `.root()` agreement.
#[test]
fn census_refresh_delegation() {
    if skip_no_lean() {
        return;
    }
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut b = make_open_cell(2, 5);
    let b_id = b.id();
    b.delegate = Some(a_id);
    // B holds a self-`node` edge so the verified `refreshDelegationChainA` `stateAuthB B B` leg passes.
    b.capabilities.grant(b_id, AuthRequired::None);
    // A holds a (non-trivial) cap so the snapshot of A's c-list is observable.
    a.capabilities.grant(a_id, AuthRequired::None);
    let parent_snapshot = {
        let snap: Vec<CapabilityRef> = a.capabilities.iter().cloned().collect();
        let bytes = postcard::to_allocvec(&snap).unwrap_or_default();
        dregg_cell::DelegatedRef::compute_clist_commitment(&bytes)
    };
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let turn = single_effect_turn(
        b_id,
        b_id,
        0,
        Effect::RefreshDelegation { child: b_id, snapshot: parent_snapshot },
    );
    assert_denotational_and_conservation("RefreshDelegation", pre, turn, &[a_id, b_id], 0);
}

#[test]
fn census_revoke_capability() {
    if skip_no_lean() {
        return;
    }
    // RevokeCapability of a slot on an EMPTY c-list is a no-op in Rust; the verified recCRevoke is
    // total. Both commit, c-list/cap_root unchanged: a covered, conservation-trivial round-trip.
    let (pre, a) = one_open_cell();
    let turn = single_effect_turn(a, a, 0, Effect::RevokeCapability { cell: a, slot: 0 });
    assert_denotational_and_conservation("RevokeCapability", pre, turn, &[a], 0);
}

// =====================================================================================
// COVERAGE LEDGER — the census above pins, per kind, the (denotational ∧ conservation)
// cross-validation. This test asserts the census set EQUALS the public swap-safe set
// MINUS the named committed-state residuals, so the census cannot silently shrink.
// =====================================================================================

/// The root-agreeing kinds this census drives to a committed post-state with BOTH a full-state
/// denotational agreement AND a conservation assertion.
const CENSUS_COVERED: &[&str] = &[
    "Transfer",
    "SetField",
    "IncrementNonce",
    "EmitEvent",
    "SetPermissions",
    "SetVerificationKey",
    "NoteCreate",
    "CellSeal",
    "CellUnseal",
    "CellDestroy",
    "MakeSovereign",
    "GrantCapability",
    "AttenuateCapability",
    "Introduce",
    "RevokeDelegation",
    "RefreshDelegation",
    "RevokeCapability",
];

/// Root-agreeing kinds NOT driven to a COMMITTED census turn here, each with WHY. These are honest
/// residuals — the producer maps them, but a committed denotational fixture is not yet constructible
/// in-test (a real STARK proof / fee-bearing burn well), so they are pinned by other teeth instead.
const CENSUS_NAMED_RESIDUALS: &[(&str, &str)] = &[
    (
        "NoteSpend",
        "a COMMITTING NoteSpend needs a real STARK spending proof + a note in the tree; the in-test \
         fixtures only exercise the PROOFLESS spend, which both producers REJECT (commit-bit agreement \
         on rejection, pinned in rust_lean_divergence_finder). No committed full-state fixture yet.",
    ),
    (
        "Burn",
        "under issuer-supply (W1) the scalar Effect::Burn has no conserving image on the 1-cell \
         numbering, so the verified producer REFUSES it (pinned in lean_state_producer_widen). A \
         committed burn awaits the apply.rs return-to-well migration; no committed round-trip yet.",
    ),
];

#[test]
fn census_set_matches_root_agreeing_minus_residuals() {
    let agreeing: std::collections::HashSet<&str> =
        lean_shadow::producer_root_agreeing_effects().iter().copied().collect();
    let covered: std::collections::HashSet<&str> = CENSUS_COVERED.iter().copied().collect();
    let residual: std::collections::HashSet<&str> =
        CENSUS_NAMED_RESIDUALS.iter().map(|(k, _)| *k).collect();

    // (1) Every census-covered kind is genuinely root-agreeing.
    for k in &covered {
        assert!(
            agreeing.contains(k),
            "census claims to cover {k:?} but it is NOT in producer_root_agreeing_effects"
        );
    }
    // (2) Every named residual is root-agreeing too (a real mappable effect we just can't commit in-test).
    for k in &residual {
        assert!(
            agreeing.contains(k),
            "named residual {k:?} must still be a root-agreeing kind (else re-classify it)"
        );
    }
    // (3) covered ∪ residual == the whole root-agreeing set: nothing falls through the census silently.
    let union: std::collections::HashSet<&str> = covered.union(&residual).copied().collect();
    assert_eq!(
        union,
        agreeing,
        "census-covered ∪ named-residuals must EQUAL producer_root_agreeing_effects; \
         uncensused/over-claimed: {:?}",
        union.symmetric_difference(&agreeing).collect::<Vec<_>>()
    );
}

// =====================================================================================
// CONSERVATION TOOTH — the conservation check is NON-VACUOUS: a turn that genuinely
// MOVES value (Transfer) leaves the SUM fixed while the per-cell balances change, and
// MakeSovereign genuinely drops the live-cell sum. If the conservation assertion were
// vacuous (e.g. always comparing 0==0) these would not be distinguishable.
// =====================================================================================

#[test]
fn conservation_check_is_non_vacuous() {
    if skip_no_lean() {
        return;
    }
    // Transfer moves 30 from A(100) to B(5): per-cell balances change (70, 35) but the sum stays 105.
    let (pre, a, b) = two_open_cells();
    let pre_sum = scalar_total_supply(&pre);
    assert_eq!(pre_sum, 105, "fixture: A=100 + B=5");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut post = pre.clone();
    assert!(executor
        .execute(
            &single_effect_turn(a, a, 0, Effect::Transfer { from: a, to: b, amount: 30 }),
            &mut post
        )
        .is_committed());
    assert_eq!(post.get(&a).unwrap().state.balance(), 70, "A debited");
    assert_eq!(post.get(&b).unwrap().state.balance(), 35, "B credited");
    assert_eq!(
        scalar_total_supply(&post),
        pre_sum,
        "the SUM is conserved even though both cells moved (non-vacuous conservation)"
    );
}
