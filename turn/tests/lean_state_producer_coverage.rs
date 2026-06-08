//! lean_state_producer_coverage.rs — EMPIRICAL producer-coverage classification.
//!
//! `lean_shadow::producer_mappable_effects()` enumerates the effect kinds whose forest crosses the
//! wire so the VERIFIED Lean executor RUNS as the state producer (`produce_via_lean`). But "the
//! producer runs" is NOT the same as "the Lean-produced `.root()` EQUALS the Rust `.root()`": some
//! mappable effects touch a commitment field the wire model drops (lifecycle; the full
//! `Permissions`/`VK` struct; the per-cap slot/perm detail behind `cap_root`) or are structurally
//! re-shaped by Rust (MakeSovereign REMOVES the cell from the ledger), so their reconstituted root
//! DIVERGES. Those are real SWAP-GAPS, not silent passes.
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

use dregg_cell::lifecycle::CellLifecycle;
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
fn revoke_delegation_root_agrees() {
    if skip_no_lean() {
        return;
    }
    // RevokeDelegation on a child with no delegation snapshot is a no-op on the commitment fields
    // the wire carries; `.revokeDelegationA` routes to a total registry edit. Both commit; the
    // reconstituted ledger agrees.
    let (pre, a_id) = one_open_cell();
    let turn = single_effect_turn(a_id, a_id, 0, Effect::RevokeDelegation { child: a_id });
    diff(pre, turn, &[a_id]).expect("RevokeDelegation must round-trip");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"RevokeDelegation"));
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
        },
    );
    diff(pre, turn, &[a_id]).expect("NoteCreate must round-trip (note set is off the cell root)");
    assert!(lean_shadow::producer_root_agreeing_effects().contains(&"NoteCreate"));
}

// =====================================================================================
// ROOT-GAP FAMILIES — the producer RUNS but the reconstituted `.root()` DIVERGES. Each
// asserts the SPECIFIC divergence (a negative tooth) so the gap is characterized, not a
// silent pass. (CellSeal/CellDestroy/GrantCapability are pinned in the widen file too.)
// =====================================================================================

#[test]
fn set_permissions_is_a_perm_struct_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // SetPermissions rewrites the cell's full `Permissions` struct (a commitment field). The wire
    // `setperms` arm carries a COLLAPSED scalar, and the reconstitution does not reinstall the full
    // struct — so the Rust post-state (new permissions) and the Lean reconstitution (template
    // permissions carried forward) bind DIFFERENT commitments → root diverges.
    let (pre, a_id) = one_open_cell();
    let mut new_perms = open_permissions();
    new_perms.set_state = AuthRequired::Signature; // a real permission change.
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetPermissions { cell: a_id, new_permissions: new_perms },
    );
    match diff(pre, turn, &[a_id]) {
        Ok(()) => panic!(
            "SetPermissions unexpectedly round-tripped — the permissions-struct swap-gap may have \
             closed; re-classify (the wire would now carry the full Permissions struct)"
        ),
        Err(why) => assert!(
            why.contains("ROOT divergence") || why.contains("commit-bit divergence"),
            "SetPermissions swap-gap should be a ROOT/commit-bit divergence, got: {why}"
        ),
    }
    assert!(lean_shadow::producer_root_gap_effects().contains(&"SetPermissions"));
}

#[test]
fn set_verification_key_is_a_vk_struct_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // SetVerificationKey installs a full `VerificationKey { hash, data }` (a commitment field). The
    // wire `setvk` arm carries only the low-64-bit collapse of the vk hash; the reconstitution does
    // not reinstall the struct → root diverges.
    let (pre, a_id) = one_open_cell();
    #[allow(deprecated)]
    let vk = VerificationKey::new(vec![1, 2, 3, 4]);
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetVerificationKey { cell: a_id, new_vk: Some(vk) },
    );
    match diff(pre, turn, &[a_id]) {
        Ok(()) => panic!(
            "SetVerificationKey unexpectedly round-tripped — the vk-struct swap-gap may have closed"
        ),
        Err(why) => assert!(
            why.contains("ROOT divergence") || why.contains("commit-bit divergence"),
            "SetVerificationKey swap-gap should be a ROOT/commit-bit divergence, got: {why}"
        ),
    }
    assert!(lean_shadow::producer_root_gap_effects().contains(&"SetVerificationKey"));
}

#[test]
fn make_sovereign_is_a_structural_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // MakeSovereign REMOVES the cell from `Ledger::cells` (it moves to `sovereign_commitments`,
    // which does NOT feed `Ledger::root()`), so the Rust post-root drops that leaf. The verified
    // `WireState` echoes the cell still present, so the reconstitution KEEPS it → a presence/root
    // divergence. A structural swap-gap (the wire state model has no "cell removed to sovereign"
    // transition), characterized here, never silently passed.
    let (pre, a_id) = one_open_cell();
    let turn = single_effect_turn(a_id, a_id, 0, Effect::MakeSovereign { cell: a_id });

    // Confirm Rust really removed the cell (so the gap is structural, not a no-commit).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(executor.execute(&turn, &mut rust_ledger).is_committed(), "Rust MakeSovereign commits");
    assert!(rust_ledger.get(&a_id).is_none(), "Rust must have removed the now-sovereign cell");

    match diff(pre, turn, &[a_id]) {
        Ok(()) => panic!(
            "MakeSovereign unexpectedly round-tripped — the structural swap-gap may have closed \
             (the wire state would now model the sovereign-removal transition)"
        ),
        Err(why) => assert!(
            why.contains("presence divergence") || why.contains("ROOT divergence"),
            "MakeSovereign swap-gap should be a presence/root divergence, got: {why}"
        ),
    }
    assert!(lean_shadow::producer_root_gap_effects().contains(&"MakeSovereign"));
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
            why.contains("field[") || why.contains("ROOT divergence") || why.contains("commit-bit"),
            "Refusal swap-gap should be a field[4]/root/commit-bit divergence, got: {why}"
        ),
    }
    assert!(lean_shadow::producer_root_gap_effects().contains(&"Refusal"));
}

#[test]
fn attenuate_capability_is_a_cap_fidelity_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // AttenuateCapability narrows a HELD c-list slot in place: dregg1's `apply.rs` rewrites the
    // held `CapabilityRef`'s `permissions` (`AuthRequired`) to a strictly narrower value (and may
    // bind a finite expiry), changing that cell's `cap_root` → `.root()`. The wire `caps` model
    // carries only bare `Cap::Node(target)` edges (no per-cap `AuthRequired`/expiry), and the
    // verified `attenuate` is a NO-OP on a `node` cap (it only filters `.endpoint` rights). So the
    // Lean-reconstituted c-list keeps the unchanged `node` edge (`AuthRequired::None`), hashing to a
    // DIFFERENT `cap_root` than Rust's narrowed cap. Same cap-fidelity gap class as GrantCapability;
    // asserted as a SPECIFIC divergence (a negative tooth), characterized, never a silent pass.
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    // Seed a HELD cap on A over a target cell B with a NON-None permission, so the in-place narrowing
    // genuinely rewrites the cap_root (and the wire's bare-`node` reconstruction cannot coincide).
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let slot = a
        .capabilities
        .grant(b_id, AuthRequired::Signature)
        .expect("seed a held cap to attenuate");
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Narrow the held cap from Signature → None (a monotone narrowing apply.rs accepts).
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::AttenuateCapability {
            cell: a_id,
            slot,
            narrower_permissions: AuthRequired::None,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );

    // Confirm Rust really narrowed the held cap (so the gap is genuinely about cap fidelity).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    if executor.execute(&turn, &mut rust_ledger).is_committed() {
        let a_caps = &rust_ledger.get(&a_id).unwrap().capabilities;
        assert!(
            a_caps.iter().any(|c| c.target == b_id && c.permissions == AuthRequired::None),
            "Rust must have narrowed A's held cap over B to None"
        );
    }

    match diff(pre, turn, &[a_id, b_id]) {
        Ok(()) => panic!(
            "AttenuateCapability unexpectedly round-tripped — the cap-fidelity swap-gap may have \
             closed (the wire caps model would now carry per-cap AuthRequired/expiry)"
        ),
        Err(why) => assert!(
            why.contains("cap_root divergence")
                || why.contains("ROOT divergence")
                || why.contains("commit-bit divergence"),
            "AttenuateCapability swap-gap should be a cap_root/root/commit-bit divergence, got: {why}"
        ),
    }
    assert!(lean_shadow::producer_root_gap_effects().contains(&"AttenuateCapability"));
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
fn forest_is_root_agreeing_covers_transfer_not_setpermissions() {
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

    let mut new_perms = open_permissions();
    new_perms.set_state = AuthRequired::Signature;
    let setperms = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetPermissions { cell: a_id, new_permissions: new_perms },
    );
    assert!(
        !lean_shadow::forest_is_root_agreeing(&setperms),
        "a SetPermissions turn touches a root-gap effect — must NOT be covered"
    );
    assert_eq!(
        lean_shadow::first_root_gap_kind(&setperms),
        Some("SetPermissions"),
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

/// On a ROOT-GAP turn (SetPermissions), `produce_via_lean` falls back to the Rust producer for that
/// turn: the outcome is `Fallback { RootGap }`, the committed ledger is the RUST post-state (the new
/// permissions are applied), and NO divergent Lean root is committed. This is the "no silent
/// divergence" guarantee that makes the default-on flip safe.
#[test]
fn produce_via_lean_falls_back_on_root_gap_setpermissions() {
    if skip_no_lean() {
        return;
    }
    use dregg_turn::lean_apply::{produce_via_lean, ExtractError, ProducerOutcome};

    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let mut new_perms = open_permissions();
    new_perms.set_state = AuthRequired::Signature;
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetPermissions { cell: a_id, new_permissions: new_perms },
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
            assert_eq!(kind, "SetPermissions", "fallback must name the root-gap kind");
        }
        other => panic!("a root-gap turn must fall back with RootGap, got {other:?}"),
    }

    // The committed ledger is the RUST post-state (no divergent Lean root committed).
    assert_eq!(ledger.root(), expected_root, "root-gap turn must commit the Rust post-state");
    if rust_committed {
        assert_eq!(
            ledger.get(&a_id).unwrap().permissions.set_state,
            AuthRequired::Signature,
            "the Rust producer's new permissions must be the committed state"
        );
    }
}
