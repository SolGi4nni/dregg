//! lean_state_producer_coverage.rs — EMPIRICAL producer-coverage classification.
//!
//! `lean_shadow::producer_mappable_effects()` enumerates the effect kinds whose forest crosses the
//! wire so the VERIFIED Lean executor RUNS as the state producer (`produce_via_lean`). But "the
//! producer runs" is NOT the same as "the Lean-produced `.root()` EQUALS the Rust `.root()`": a
//! mappable effect may touch a commitment field the wire model drops. For the SURVIVOR effects
//! whose dropped value is TURN or HOST data (the lifecycle payloads, the full `Permissions`/`VK`
//! structs, the cap leaves, the sovereign removal, the revoke epoch bump) the commit-gated replay
//! (`lean_apply::{CapOp,StateOp}`) CLOSES the gap — pinned here by *_closed round-trips plus a
//! rejection tooth each. What remains (audit-field/archive commitments; the escrow settle
//! commit-bit legs) are real SWAP-GAPS, asserted to diverge, never silent passes.
//!
//! This file is the EMPIRICAL yardstick that keeps the two coverage lists HONEST:
//!   * [`producer_root_agreeing_effects`] — the producer runs AND the reconstituted ledger agrees
//!     with Rust on full cell state + `cap_root` + `.root()`. THE swap-safe set.
//!   * [`producer_root_gap_effects`] — the producer runs but the root DIVERGES (a characterized
//!     wire-model gap). Each is asserted to diverge (a negative tooth), so the gap is pinned and a
//!     future wire-model widening that closes it will FAIL this test (forcing a re-classification).
//!
//! Every entry in BOTH lists is exercised here by a representative single-effect turn run through
//! both producers — so neither list can drift into a vacuous claim. Mirrors the discipline of
//! `lean_state_producer_widen.rs` (round-trip families + swap-gap negative teeth), extended to the
//! WHOLE mappable surface and cross-checked against the public coverage enumerations.
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent.

#![cfg(feature = "lean-shadow")]

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, NoteCommitment, Permissions, VerificationKey};
use dregg_turn::lean_apply::{self, execute_via_lean};
use dregg_turn::lean_shadow::{
    self, ShadowHostCtx, producer_mappable_effects, producer_root_agreeing_effects,
    producer_root_gap_effects,
};
use dregg_turn::action::{Event, RefusalReason};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, ProofCondition,
    TurnExecutor, turn::Turn,
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

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
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

/// Compare two ledgers on balance + nonce + the 8 state fields + cap_root + `.root()`.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        // A cell may be ABSENT on one side (e.g. MakeSovereign removes it from `self.cells` in Rust
        // but the wire reconstitution keeps it). A presence mismatch is itself a divergence.
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
                return Err(format!("presence divergence on {id:?}: absent in RUST, present in LEAN"))
            }
            (Some(_), None) => {
                return Err(format!("presence divergence on {id:?}: present in RUST, absent in LEAN"))
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

/// Run both producers; `Ok(())` on full agreement, `Err(why)` on the first divergence (incl. a
/// commit-bit divergence). Both must commit; an ineligible turn is reported as a GAP.
fn diff(pre: Ledger, turn: Turn, ids: &[CellId]) -> Result<(), String> {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!("legacy Rust executor did not commit: {rust_result:?}"));
    }

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) = match execute_via_lean(&turn, &pre, &host) {
        Ok(x) => x,
        Err(lean_apply::ExtractError::Ineligible) => {
            return Err("turn was Lean-ineligible (a marshaller GAP — no wire arm)".to_string());
        }
        Err(e) => return Err(format!("Lean state-producer path errored: {e}")),
    };
    if !lean_committed {
        return Err("commit-bit divergence: Rust committed, Lean did not".to_string());
    }
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, ids)
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

// =====================================================================================
// LIST CONSISTENCY — the public enumerations must PARTITION the mappable set with no
// overlap, so neither list can hide a gap or over-claim coverage.
// =====================================================================================

#[test]
fn coverage_lists_partition_the_mappable_set() {
    let mappable: std::collections::HashSet<&str> =
        producer_mappable_effects().iter().copied().collect();
    let agreeing: std::collections::HashSet<&str> =
        producer_root_agreeing_effects().iter().copied().collect();
    let gaps: std::collections::HashSet<&str> =
        producer_root_gap_effects().iter().copied().collect();

    // (1) agreeing ∪ gaps == mappable
    let union: std::collections::HashSet<&str> = agreeing.union(&gaps).copied().collect();
    assert_eq!(
        union, mappable,
        "root-agreeing ∪ root-gap must equal the mappable set; missing/extra: {:?}",
        union.symmetric_difference(&mappable).collect::<Vec<_>>()
    );
    // (2) agreeing ∩ gaps == ∅
    let overlap: Vec<&&str> = agreeing.intersection(&gaps).collect();
    assert!(
        overlap.is_empty(),
        "an effect cannot be BOTH root-agreeing and a root-gap: {overlap:?}"
    );
}

// =====================================================================================
// ROOT-AGREEING FAMILIES (newly pinned by this file) — the reconstituted ledger AGREES.
// (Transfer/SetField/Burn/IncrementNonce/Revoke-empty/forests are pinned in the widen file.)
// =====================================================================================

#[test]
fn emit_event_root_agrees() {
    if skip_no_lean() {
        return;
    }
    // EmitEvent journals an event but mutates NO cell commitment field (apply.rs:703 records the
    // event in the receipt journal only). The wire `emit` arm likewise leaves cell state untouched.
    // So both producers commit and the reconstituted ledger agrees on state + cap_root + root.
    let (pre, a_id) = one_open_cell();
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::EmitEvent {
            cell: a_id,
            event: Event { topic: field_from_u64(11), data: vec![field_from_u64(22)] },
        },
    );
    diff(pre, turn, &[a_id]).expect("EmitEvent must round-trip (no cell-commitment mutation)");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"EmitEvent"));
}

#[test]
fn revoke_delegation_round_trips_epoch_closed() {
    if skip_no_lean() {
        return;
    }
    // DELEGATION-EPOCH ROOT-GAP CLOSE. A COMMITTING RevokeDelegation bumps the PARENT cell's
    // `delegation_epoch` and clears the CHILD's `delegation` snapshot (apply.rs
    // `apply_revoke_delegation`), both folded into `compute_canonical_state_commitment`. Neither
    // crosses the wire — but the mutation is fully DETERMINISTIC from the turn (parent = the
    // action target, child = the effect operand), so the commit-gated replay
    // (`lean_apply::apply_state_ops`) performs the same `bump_delegation_epoch()` +
    // `delegation = None`, gated on the same pre-state `child.delegate == Some(parent)` edge.
    // The non-zero starting epoch (3 → 4) makes the round-trip non-vacuous: a
    // template-carried-forward reconstitution (the old gap) would bind epoch 3 → root divergence.
    //
    // Set up a real parent(A)→child(B) delegation so the revoke COMMITS in Rust (a self-revoke
    // with no delegation present is `DelegationDenied` — exercised by the rejection tooth below).
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut b = make_open_cell(2, 5);
    let b_id = b.id();
    // B is delegated to A: set B.delegate = A so `apply_revoke_delegation` finds the edge to remove.
    b.delegate = Some(a_id);
    // Give A a non-zero starting epoch so the bump is observable in the commitment.
    a.state.set_delegation_epoch(3);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Confirm Rust really commits AND bumps A's delegation_epoch (so the close is genuinely about
    // the epoch commitment field).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let res = executor.execute(
        &single_effect_turn(a_id, a_id, 0, Effect::RevokeDelegation { child: b_id }),
        &mut rust_ledger,
    );
    assert!(res.is_committed(), "Rust RevokeDelegation must commit on a real parent→child edge: {res:?}");
    assert_eq!(
        rust_ledger.get(&a_id).unwrap().state.delegation_epoch(),
        4,
        "Rust must have bumped the parent's delegation_epoch (3 -> 4)"
    );

    // The reconstituted ledger must carry the replayed bump + cleared snapshot, not the template's.
    let turn = single_effect_turn(a_id, a_id, 0, Effect::RevokeDelegation { child: b_id });
    let host = ShadowHostCtx::diag();
    let (lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(lean_committed, "the verified revoke commits on a real parent→child edge");
    assert_eq!(
        lean_ledger.get(&a_id).unwrap().state.delegation_epoch(),
        4,
        "the replay must bump the parent's delegation_epoch exactly as apply_revoke_delegation"
    );
    assert!(
        lean_ledger.get(&b_id).unwrap().delegation.is_none(),
        "the replay must clear the child's delegation snapshot"
    );

    diff(pre, turn, &[a_id, b_id]).expect(
        "RevokeDelegation must round-trip (delegation-epoch root-gap closed via the turn replay)",
    );
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"RevokeDelegation"));
}

#[test]
fn revoke_of_non_delegated_child_rejected_by_rust_surfaced_not_replayed() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH for the revoke close, pinning the CHARACTERIZED RESIDUAL named in
    // `producer_root_agreeing_effects`: Rust REJECTS a revoke of a non-delegated child
    // (`DelegationDenied` — the pre-state `child.delegate == Some(parent)` gate fails), while the
    // verified revoke guard is `True` (revocation is unconditional in the kernel). The replay's
    // OWN edge gate (`lean_apply::apply_state_ops`) mirrors the Rust pre-state check, so NO field
    // moves on the reconstituted side either — no fabricated epoch bump, no cleared snapshot; the
    // reconstituted ledger equals the Rust rollback (roots agree). If the commit bits diverge
    // (Lean committed, Rust rolled back), the producer path surfaces it as a CoveredDivergence
    // and KEEPS the Rust state — surfaced loudly, never silently committed.
    use dregg_turn::lean_apply::{ProducerOutcome, produce_via_lean};

    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    // NO delegation edge: B.delegate stays None.
    a.state.set_delegation_epoch(3);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let turn = single_effect_turn(a_id, a_id, 0, Effect::RevokeDelegation { child: b_id });

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        !executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust must REJECT a revoke of a non-delegated child (DelegationDenied)"
    );

    // The reconstituted side never fabricates the mutation, whatever the verified commit bit says.
    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, _lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert_eq!(
        lean_ledger.get(&a_id).unwrap().state.delegation_epoch(),
        3,
        "the replay's edge gate must refuse to bump the epoch without a pre-state edge"
    );
    assert!(
        lean_ledger.get(&b_id).unwrap().delegation.is_none()
            && lean_ledger.get(&b_id).unwrap().delegate.is_none(),
        "the child must be untouched"
    );
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id])
        .expect("a rejected revoke leaves both ledgers at the (rolled-back) pre-state");

    // Producer mode: whatever the verified commit bit, the COMMITTED ledger must be the Rust
    // (rolled-back) state, and a commit-bit divergence must surface as CoveredDivergence.
    let executor2 = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (result, outcome) = produce_via_lean(&executor2, &turn, &mut ledger);
    assert!(!result.is_committed(), "producer-mode result must match the Rust rejection");
    assert_eq!(
        ledger.root(),
        rust_ledger.root(),
        "the committed ledger must be the Rust rollback, never a fabricated revoke"
    );
    match outcome {
        // The verified gate also rejected → full agreement on the rollback.
        ProducerOutcome::LeanProduced { committed: false, agree: true, .. } => {}
        // The characterized residual: the kernel's unconditional revoke committed where Rust
        // rejected — surfaced as a divergence, Rust state kept.
        ProducerOutcome::CoveredDivergence { lean_committed: true, rust_committed: false, .. } => {}
        other => panic!(
            "a rejected revoke must either agree on the rollback or surface the commit-bit \
             residual as CoveredDivergence, got {other:?}"
        ),
    }
}

#[test]
fn note_create_root_agrees() {
    if skip_no_lean() {
        return;
    }
    // NoteCreate inserts a commitment into the note SET (a side-table OUTSIDE the cell merkle root)
    // and mutates no cell commitment field. Both producers commit; the cell-ledger root agrees (the
    // note set does not feed `cell::Ledger::root()`).
    let (pre, a_id) = one_open_cell();
    let turn = single_effect_turn(
        a_id,
        a_id,
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
    diff(pre, turn, &[a_id]).expect("NoteCreate must round-trip (note set is off the cell root)");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"NoteCreate"));
}

// =====================================================================================
// ROOT-GAP FAMILIES — the producer RUNS but the reconstituted `.root()` DIVERGES. Each
// asserts the SPECIFIC divergence (a negative tooth) so the gap is characterized, not a
// silent pass. (CellSeal/CellDestroy are pinned in the widen file too; the cap-fidelity
// effects GrantCapability/AttenuateCapability/Introduce are now root-AGREEING, see the
// `*_round_trips_cap_fidelity_closed` tests.)
// =====================================================================================

#[test]
fn set_permissions_round_trips_perm_struct_closed() {
    if skip_no_lean() {
        return;
    }
    // PERM-STRUCT ROOT-GAP CLOSE. SetPermissions rewrites the cell's full 8-field `Permissions`
    // struct (a commitment field) and the wire `setperms` arm carries only a collapsed scalar —
    // but the struct is entirely TURN-supplied, so the commit-gated replay
    // (`lean_apply::apply_state_ops`) installs the exact struct `apply_set_permissions` writes.
    // We change ONE field (set_state: None → Signature), so a template-carried-forward
    // reconstitution (the old gap) would bind a different permissions fold → the round-trip is
    // non-vacuous.
    let (pre, a_id) = one_open_cell();
    let mut new_perms = open_permissions();
    new_perms.set_state = AuthRequired::Signature; // a real permission change.
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetPermissions { cell: a_id, new_permissions: new_perms.clone() },
    );

    // The reconstituted ledger must carry the turn's full struct, not the template's.
    let host = ShadowHostCtx::diag();
    let (lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(lean_committed, "the verified setPermissionsA gate commits the self-targeted change");
    assert_eq!(
        lean_ledger.get(&a_id).unwrap().permissions,
        new_perms,
        "the replay must install the exact turn-supplied Permissions struct"
    );

    diff(pre, turn, &[a_id])
        .expect("SetPermissions must round-trip (perm-struct root-gap closed via the turn replay)");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"SetPermissions"));
}

#[test]
fn unauthorized_cross_cell_set_permissions_rejected_by_both() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH for the perm-struct close: a CROSS-CELL SetPermissions by an actor holding
    // NO capability over the target is rejected by Rust (`check_cross_cell_permission` →
    // CapabilityNotHeld) AND by the verified gate (`stateAuthB actor cell` has no edge). The
    // commit-gated replay does not fire, so neither side's permissions move — a forged permission
    // rewrite cannot fabricate a commitment.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let b_perms = b.permissions.clone();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let mut new_perms = open_permissions();
    new_perms.set_state = AuthRequired::Impossible; // the would-be hostile rewrite.
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetPermissions { cell: b_id, new_permissions: new_perms },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        !executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust must REJECT a cross-cell SetPermissions without a held capability"
    );

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(!lean_committed, "the verified gate must also REJECT the unauthorized rewrite");
    assert_eq!(
        lean_ledger.get(&b_id).unwrap().permissions,
        b_perms,
        "the rejected rewrite must leave B's permissions at the pre-state"
    );
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id])
        .expect("a rejected SetPermissions leaves both ledgers at the (rolled-back) pre-state");
}

#[test]
fn set_verification_key_round_trips_vk_struct_closed() {
    if skip_no_lean() {
        return;
    }
    // VK-STRUCT ROOT-GAP CLOSE. SetVerificationKey installs a full `VerificationKey { hash, data }`
    // (the commitment binds `vk.hash`); the wire `setvk` arm carries only the low-64-bit collapse.
    // The struct is TURN-supplied, so the commit-gated replay installs the exact VK
    // `apply_set_verification_key` writes (the apply path — both producers' — enforces
    // `vk.hash == blake3(vk.data)`, so only an integrity-bound VK can ever land).
    let (pre, a_id) = one_open_cell();
    #[allow(deprecated)]
    let vk = VerificationKey::new(vec![1, 2, 3, 4]);
    let expected_hash = vk.hash;
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetVerificationKey { cell: a_id, new_vk: Some(vk) },
    );

    let host = ShadowHostCtx::diag();
    let (lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(lean_committed, "the verified setVKA gate commits the self-targeted change");
    assert_eq!(
        lean_ledger.get(&a_id).unwrap().verification_key.as_ref().map(|v| v.hash),
        Some(expected_hash),
        "the replay must install the exact turn-supplied VerificationKey"
    );

    diff(pre, turn, &[a_id])
        .expect("SetVerificationKey must round-trip (vk-struct root-gap closed via the turn replay)");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"SetVerificationKey"));
}

#[test]
fn unauthorized_cross_cell_set_verification_key_rejected_by_both() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH for the vk-struct close: a CROSS-CELL SetVerificationKey by an actor with
    // no held capability is rejected by Rust (CapabilityNotHeld) and by the verified `stateAuthB`
    // gate. The VK does not move on either side — a forged program-identity rewrite cannot
    // fabricate a commitment.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    #[allow(deprecated)]
    let vk = VerificationKey::new(vec![9, 9, 9]);
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetVerificationKey { cell: b_id, new_vk: Some(vk) },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        !executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust must REJECT a cross-cell SetVerificationKey without a held capability"
    );

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(!lean_committed, "the verified gate must also REJECT the unauthorized vk rewrite");
    assert!(
        lean_ledger.get(&b_id).unwrap().verification_key.is_none(),
        "the rejected rewrite must leave B's verification key unset"
    );
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id])
        .expect("a rejected SetVerificationKey leaves both ledgers at the (rolled-back) pre-state");
}

#[test]
fn make_sovereign_round_trips_structural_closed() {
    if skip_no_lean() {
        return;
    }
    // STRUCTURAL ROOT-GAP CLOSE. MakeSovereign REMOVES the cell from `Ledger::cells` (its merkle
    // leaf disappears; the state commitment parks in the off-root `sovereign_commitments`). The
    // verified `sovereignRebind` performs the same regime move (the readable record is dropped
    // behind a commitment-only re-emit), and the commit-gated replay calls
    // `Ledger::make_sovereign` at ledger-build time — the SAME structural move
    // `apply_make_sovereign` performs — so the reconstituted leaf SET, and therefore `.root()`,
    // equals Rust's. The extractor SKIPS the rebound commitment-only wire record rather than
    // fail-closing on its missing scalars.
    let (pre, a_id) = one_open_cell();
    let turn = single_effect_turn(a_id, a_id, 0, Effect::MakeSovereign { cell: a_id });

    // Confirm Rust really removed the cell (so the close is structural, not a no-commit).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(executor.execute(&turn, &mut rust_ledger).is_committed(), "Rust MakeSovereign commits");
    assert!(rust_ledger.get(&a_id).is_none(), "Rust must have removed the now-sovereign cell");

    // The reconstituted ledger must have removed the cell too (presence agreement — the leaf SET).
    let host = ShadowHostCtx::diag();
    let (lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(lean_committed, "the verified makeSovereign gate commits the self-targeted rebind");
    assert!(
        lean_ledger.get(&a_id).is_none(),
        "the replay must remove the now-sovereign cell from the reconstituted ledger"
    );

    diff(pre, turn, &[a_id]).expect(
        "MakeSovereign must round-trip (structural root-gap closed via the make_sovereign replay)",
    );
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"MakeSovereign"));
}

#[test]
fn cross_cell_make_sovereign_rejected_by_both() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH for the sovereign close: a CROSS-CELL MakeSovereign (effect cell ≠ action
    // target — "only the cell itself can make itself sovereign") is rejected by Rust
    // (`apply_make_sovereign`'s structural guard) and the collector mirrors that guard
    // (`collect_state_ops` only gathers a self-targeted rebind), so NO removal is replayed: the
    // foreign cell stays present on both sides and the reconstitution equals the Rust rollback —
    // a hostile turn cannot evict someone else's cell from the ledger.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Action targets A; the rebind aims at B.
    let turn = single_effect_turn(a_id, a_id, 0, Effect::MakeSovereign { cell: b_id });

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        !executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust must REJECT a cross-cell MakeSovereign"
    );
    assert!(rust_ledger.get(&b_id).is_some(), "the rejected rebind must not remove B");

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(!lean_committed, "the verified gate must also REJECT the cross-cell rebind");
    assert!(
        lean_ledger.get(&b_id).is_some(),
        "the reconstituted ledger must keep the foreign cell — no fabricated removal"
    );
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id])
        .expect("a rejected MakeSovereign leaves both ledgers at the (rolled-back) pre-state");
}

#[test]
fn refusal_is_an_audit_field_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // Refusal bumps the target nonce AND writes a Poseidon2-ish commitment of
    // `(offered_action_commitment, reason_discriminant)` into field[4] (the audit slot; apply.rs
    // §3). The wire `refusal` arm routes to a stateStep that does not reproduce that exact field-4
    // commitment, so the audit field (a cell commitment field) diverges → root diverges. Pinned as
    // a gap (the audit-field commitment scheme is not carried on the wire).
    let (pre, a_id) = one_open_cell();
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Refusal {
            cell: a_id,
            offered_action_commitment: [3u8; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        },
    );
    match diff(pre, turn, &[a_id]) {
        Ok(()) => {
            // If Rust and Lean happen to agree on field[4] this is genuinely a round-trip; promote
            // it. Until then it is pinned as a gap.
            panic!(
                "Refusal unexpectedly round-tripped — re-classify it into producer_root_agreeing_effects \
                 (the audit-field commitment now matches across producers)"
            )
        }
        Err(why) => assert!(
            why.contains("field[")
                || why.contains("ROOT divergence")
                || why.contains("commit-bit")
                || why.contains("nonce divergence"),
            "Refusal swap-gap should be a field[4]/nonce/root/commit-bit divergence (Rust writes the \
             audit-field commitment AND bumps the target nonce, which the wire `refusal` arm does \
             not reproduce identically), got: {why}"
        ),
    }
    assert!(lean_shadow::producer_root_gap_effects().contains(&"Refusal"));
}

#[test]
fn attenuate_capability_round_trips_cap_fidelity_closed() {
    if skip_no_lean() {
        return;
    }
    // CAP-FIDELITY ROOT-GAP CLOSE. AttenuateCapability narrows a HELD c-list slot in place: dregg1's
    // `apply.rs` rewrites the held `CapabilityRef`'s `permissions` (`AuthRequired`) to a strictly
    // narrower value, changing that cell's `cap_root` → `.root()`. The verified kernel decides the
    // commit; the commit-gated turn-driven replay (`lean_apply::apply_cap_ops`) mirrors
    // `attenuate_in_place` byte-for-byte, so the narrowed leaf's `cap_root` AGREES with Rust. We
    // narrow None → Signature (a leaf that genuinely moves), so the round-trip is non-vacuous.
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    // Seed a HELD cap on A over a target cell B with the WIDEST permission (`None`), so an in-place
    // narrowing to a STRICTLY narrower `AuthRequired` is what apply.rs accepts as monotone
    // (`narrower.is_narrower_or_equal(old)`: `Signature.is_narrower_or_equal(None)` is true; the
    // reverse `None.is_narrower_or_equal(Signature)` is FALSE — None is the least restrictive).
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let slot = a
        .capabilities
        .grant(b_id, AuthRequired::None)
        .expect("seed a held cap to attenuate");
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Narrow the held cap from None → Signature (a monotone narrowing apply.rs accepts), which
    // rewrites that cell's `cap_root`. The wire `caps` model carries only a bare `Cap::Node` edge,
    // so the Lean reconstitution keeps `AuthRequired::None` → cap_root diverges.
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

    // Confirm Rust really narrowed the held cap (so the gap is genuinely about cap fidelity).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust AttenuateCapability (None -> Signature) must commit as a monotone narrowing"
    );
    {
        let a_caps = &rust_ledger.get(&a_id).unwrap().capabilities;
        assert!(
            a_caps.iter().any(|c| c.target == b_id && c.permissions == AuthRequired::Signature),
            "Rust must have narrowed A's held cap over B to Signature"
        );
    }

    diff(pre, turn, &[a_id, b_id])
        .expect("AttenuateCapability must round-trip (cap-fidelity root-gap closed)");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"AttenuateCapability"));
}

// =====================================================================================
// THE FLIPPED DEFAULT — `produce_via_lean` as the DEFAULT-ON commit-path producer.
// These pin the SAFETY of the flip: on the covered (root-agreeing) set the verified
// executor's state is ACTUALLY INSTALLED (Lean produces) AND agrees with Rust; on a
// root-gap effect the producer falls back to Rust and does NOT commit a divergent root
// (no silent divergence); the covered-set gate is decided by `forest_is_root_agreeing`.
// =====================================================================================

/// The covered-set predicate is purely a Rust decision (no Lean link needed): a Transfer turn is
/// covered (root-agreeing), a SetPermissions turn is NOT (a characterized root-gap).
#[test]
fn forest_is_root_agreeing_covers_transfer_not_refusal() {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 0);
    let b_id = b.id();

    let transfer = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Transfer { from: a_id, to: b_id, amount: 10 },
    );
    assert!(
        lean_shadow::forest_is_root_agreeing(&transfer),
        "a Transfer turn must be in the swap-safe covered set"
    );
    assert!(lean_shadow::first_root_gap_kind(&transfer).is_none());

    // Refusal is one of the REMAINING characterized root-gaps (the audit-field commitment is not
    // wire-carried and not turn-replayable — apply.rs derives field[4] from a hash scheme the
    // reconstitution does not reproduce); SetPermissions/MakeSovereign/the lifecycle pair are now
    // CLOSED (see their *_closed tests above), so the gap exemplar here must be a real one.
    let refusal = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Refusal {
            cell: a_id,
            offered_action_commitment: [3u8; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        },
    );
    assert!(
        !lean_shadow::forest_is_root_agreeing(&refusal),
        "a Refusal turn touches a root-gap effect — must NOT be covered"
    );
    assert_eq!(
        lean_shadow::first_root_gap_kind(&refusal),
        Some("Refusal"),
        "the fallback reason must name the offending root-gap kind"
    );
}

/// On a COVERED (root-agreeing) Transfer turn, `produce_via_lean` actually makes the verified Lean
/// executor the PRODUCER: the post-state ledger it leaves behind is the Lean-reconstituted one, the
/// outcome is `LeanProduced { agree: true }`, and the committed root equals BOTH producers' root.
#[test]
fn produce_via_lean_installs_verified_state_on_covered_transfer() {
    if skip_no_lean() {
        return;
    }
    use dregg_turn::lean_apply::{produce_via_lean, ProducerOutcome};

    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 0);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Independent Rust-only run to know the expected committed post-state.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Transfer { from: a_id, to: b_id, amount: 10 },
    );
    let mut rust_only = pre.clone();
    assert!(executor.execute(&turn, &mut rust_only).is_committed(), "Rust Transfer commits");
    let expected_root = rust_only.root();

    // Producer mode: this is the live commit-path call.
    let executor2 = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (result, outcome) = produce_via_lean(&executor2, &turn, &mut ledger);
    assert!(result.is_committed(), "producer-mode Transfer commits");

    match outcome {
        ProducerOutcome::LeanProduced { agree, lean_root, rust_root, .. } => {
            assert!(agree, "covered Transfer must agree (Lean root == Rust root)");
            assert_eq!(lean_root, rust_root, "the two producers' roots must be equal");
        }
        other => panic!("covered Transfer must produce LeanProduced, got {other:?}"),
    }

    // The COMMITTED ledger is the Lean-produced one — and it equals the Rust post-state (the swap).
    assert_eq!(ledger.root(), expected_root, "the committed root must be the verified-producer root");
    assert_eq!(ledger.get(&a_id).unwrap().state.balance(), 90);
    assert_eq!(ledger.get(&b_id).unwrap().state.balance(), 10);
}

/// On a ROOT-GAP turn (Refusal — a REMAINING gap; the former exemplar SetPermissions is now
/// CLOSED), `produce_via_lean` falls back to the Rust producer for that turn: the outcome is
/// `Fallback { RootGap }`, the committed ledger is the RUST post-state, and NO divergent Lean root
/// is committed. This is the "no silent divergence" guarantee that makes the default-on flip safe.
#[test]
fn produce_via_lean_falls_back_on_root_gap_refusal() {
    if skip_no_lean() {
        return;
    }
    use dregg_turn::lean_apply::{produce_via_lean, ExtractError, ProducerOutcome};

    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Refusal {
            cell: a_id,
            offered_action_commitment: [3u8; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        },
    );

    // Expected Rust post-state.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_only = pre.clone();
    let rust_committed = executor.execute(&turn, &mut rust_only).is_committed();
    let expected_root = rust_only.root();

    let executor2 = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (result, outcome) = produce_via_lean(&executor2, &turn, &mut ledger);
    assert_eq!(result.is_committed(), rust_committed, "producer-mode result matches Rust");

    match outcome {
        ProducerOutcome::Fallback { reason: ExtractError::RootGap { kind } } => {
            assert_eq!(kind, "Refusal", "fallback must name the root-gap kind");
        }
        other => panic!("a root-gap turn must fall back with RootGap, got {other:?}"),
    }

    // The committed ledger is the RUST post-state (no divergent Lean root committed).
    assert_eq!(ledger.root(), expected_root, "root-gap turn must commit the Rust post-state");
}

// =====================================================================================
// §SIDE-TABLE holding-store families (escrow / obligation) — the off-cell-merkle-root
// CREATE effects ROUND-TRIP (only a `bal` debit changes + an off-root record is parked);
// the SETTLE effects (release/refund) are characterized commit-bit gaps (Rust gates on a
// condition proof / past timeout the verified settle gate does not model).
// =====================================================================================

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

