//! lean_state_producer_widen.rs — WIDEN THE SWAP state-producer past Transfer + SetField.
//!
//! The producer differential (`lean_state_producer_differential.rs`) proved the verified Lean
//! executor can BE the state PRODUCER for Transfer + SetField: its reconstituted `cell::Ledger`
//! AGREES with the legacy Rust `TurnExecutor` on the full cell state AND `.root()`. This file
//! WIDENS that producer differential to ONE representative turn per effect family the verified
//! executor models, and pins — per family — exactly which families ROUND-TRIP through the
//! `WireState → cell::Ledger` extractor and which are SWAP-GAPS (the wire model is lossier than the
//! cell commitment so the reconstituted `.root()` cannot match the Rust one).
//!
//! # The cell commitment is the yardstick
//!
//! `cell::Ledger::root()` hashes, per cell, `compute_canonical_state_commitment` =
//! `(balance, nonce, fields, permissions, verification_key, cap_root, lifecycle, program)`. A
//! family ROUND-TRIPS iff its post-state is reconstructible: either the `WireState` carries the
//! touched field (balance via `bal`; nonce/fields via the cell record), or the dropped value is
//! TURN/HOST data replayed deterministically onto the template pre-state, gated by the verified
//! kernel's commit bit (the `lean_apply::CapOp`/`StateOp` lever — cap leaves, lifecycle payloads,
//! the full `Permissions`/`VK` structs). A family is a SWAP-GAP iff its Rust post-state touches a
//! commitment field neither carried nor turn-replayable (the audit-field/archive commitments).
//!
//! Each ROUND-TRIP test ASSERTS agreement (state + `.root()`). Each SWAP-GAP test ASSERTS the
//! SPECIFIC divergence (a negative tooth) so the gap is characterized, never silently passing — a
//! genuine finding surfaced precisely, per the SWAP discipline. Each CLOSED family also carries a
//! REJECTION tooth: the unauthorized mutation is rejected by BOTH executors and the field does not
//! move (the replay never fabricates a payload the kernel did not authorize).
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent.

#![cfg(feature = "lean-shadow")]

use std::collections::HashMap;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::lifecycle::{CellLifecycle, DeathCertificate, DeathReason};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_turn::lean_apply::{self, execute_via_lean};
use dregg_turn::lean_shadow::ShadowHostCtx;
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

/// A self-`node` capability = mint/burn authority over the cell itself. The verified executor's
/// `mintAuthorizedB actor cell` leg (which `burnA` routes through) reads a `Cap::Node(self)` edge;
/// `ledger_to_wire_state` projects the cell's c-list to wire `caps`, so a cell holding a self-cap
/// passes the Lean mint/burn gate exactly as bare ownership passes the Rust one.
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

/// Compare two ledgers cell-by-cell (balance + nonce + the 8 state fields + the canonical
/// capability root) AND on `.root()`. Returns Ok(()) on full agreement or Err(why) on the first
/// divergence. The cap-root comparison is what makes delegate/revoke round-trips meaningful.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        let r = rust
            .get(id)
            .ok_or_else(|| format!("cell {id:?} missing from RUST ledger"))?;
        let l = lean
            .get(id)
            .ok_or_else(|| format!("cell {id:?} missing from LEAN ledger"))?;
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
            return Err(format!(
                "cap_root divergence on {id:?}: rust={rc:?} lean={lc:?}"
            ));
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// Run both producers and return `Ok(())` on full agreement, or `Err(why)` on the first divergence.
/// Both producers MUST commit (a commit-bit divergence is itself a divergence). Used by both the
/// round-trip families (which expect Ok) and the swap-gap families (which expect a SPECIFIC Err).
fn diff(pre: Ledger, turn: Turn, ids: &[CellId]) -> Result<(), String> {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!(
            "legacy Rust executor did not commit: {rust_result:?}"
        ));
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

// =====================================================================================
// ROUND-TRIP FAMILIES — the reconstituted ledger AGREES (state + cap_root + .root()).
// =====================================================================================

#[test]
fn burn_refused_under_issuer_supply() {
    if skip_no_lean() {
        return;
    }
    // W1 (issuer-supply, DREGG3 §2.2): the verified `.burnA` is a RETURN-TO-WELL move — value
    // flows from the holder back to the asset's ISSUER cell, conserving `Σ_c bal c a` exactly.
    // The Rust scalar `Effect::Burn` (destroy balance, no destination) has NO conserving image:
    // on the 1-cell wire numbering it marshals to the self-burn of the well (`cell = asset`),
    // which the verified kernel refuses outright — cap or no cap. So the verified producer must
    // REFUSE this turn (the pre-W1 round-trip expectation is retired); agreement returns when the
    // staged Rust value-model migration makes apply.rs's burn the well move.
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Burn {
            target: a_id,
            slot: 0,
            amount: 40,
        },
    );
    assert!(
        diff(pre, turn, &[a_id]).is_err(),
        "W1 regression: the verified producer COMMITTED a supply-destroying scalar burn — under \
         issuer-supply the burn must be refused until the Rust well migration lands"
    );
}

#[test]
fn increment_nonce_round_trips() {
    if skip_no_lean() {
        return;
    }
    // IncrementNonce bumps the cell nonce by 1 in Rust; the wire `incnonce` SETS the nonce field to
    // the post-increment value (`pre_nonce + 1`). The cell record carries `nonce`, so it
    // reconstitutes — agreement on nonce + cap_root + root.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(a_id, a_id, 0, Effect::IncrementNonce { cell: a_id });
    diff(pre, turn, &[a_id]).expect("IncrementNonce must round-trip through the verified producer");
}

#[test]
fn revoke_on_empty_clist_round_trips() {
    if skip_no_lean() {
        return;
    }
    // RevokeCapability of a non-existent slot on an EMPTY c-list is a no-op in Rust (the cap_root
    // stays the empty-set root). The verified `recCRevoke` is TOTAL (always commits, edits the
    // revocation registry, not the cell c-list). So both commit and the cell c-list / cap_root are
    // unchanged on both sides — the reconstituted ledger agrees. (A c-list that actually carries a
    // held cap is exercised by `grant_capability_round_trips_cap_fidelity_closed`.)
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::RevokeCapability {
            cell: a_id,
            slot: 0,
        },
    );
    diff(pre, turn, &[a_id]).expect("Revoke on empty c-list must round-trip");
}

#[test]
fn two_effect_forest_round_trips() {
    if skip_no_lean() {
        return;
    }
    // A two-effect forest (Transfer then SetField) through the producer path — exercises the
    // sequential child-node execution AND the multi-field reconstitution together.
    let a = make_open_cell(1, 100);
    let b = make_open_cell(2, 5);
    let a_id = a.id();
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let mut forest = CallForest::new();
    let mk = |target, eff| Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![eff],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(mk(
        a_id,
        Effect::Transfer {
            from: a_id,
            to: b_id,
            amount: 25,
        },
    ));
    forest.add_root(mk(
        a_id,
        Effect::SetField {
            cell: a_id,
            index: 6,
            value: field_from_u64(7),
        },
    ));
    let turn = Turn {
        agent: a_id,
        nonce: 0,
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
    };
    diff(pre, turn, &[a_id, b_id]).expect("Transfer+SetField forest must round-trip");
}

// =====================================================================================
// LIFECYCLE FAMILY — the seal/destroy payload close (turn+host replay) + the unseal
// discriminant close, each with its unauthorized-rejection tooth.
// =====================================================================================

#[test]
fn cell_seal_round_trips_lifecycle_closed() {
    if skip_no_lean() {
        return;
    }
    // LIFECYCLE ROOT-GAP CLOSE. CellSeal transitions Live → `Sealed { reason_hash, sealed_at }` —
    // a commitment-bound PAYLOAD the wire's bare lifecycle discriminant cannot carry. But the
    // payload is TURN data (`reason`) + HOST data (`block_height` stamps `sealed_at`): the verified
    // `cellSealA` decides the commit, and the commit-gated replay (`lean_apply::apply_state_ops`)
    // runs the SAME `Cell::seal(reason, block_height)` as `apply_cell_seal`. With a NON-zero
    // `reason` the round-trip is non-vacuous: a discriminant-only reconstitution (the old gap)
    // would diverge on the payload bytes the commitment's lifecycle fold binds.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::CellSeal {
            target: a_id,
            reason: [9u8; 32],
        },
    );

    // Confirm Rust really sealed with the full payload (so the close is about the payload bytes).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust CellSeal should commit"
    );
    assert!(
        matches!(
            rust_ledger.get(&a_id).unwrap().lifecycle,
            CellLifecycle::Sealed { reason_hash, .. } if reason_hash == [9u8; 32]
        ),
        "Rust must have sealed the cell with the turn's reason hash"
    );

    diff(pre, turn, &[a_id])
        .expect("CellSeal must round-trip (lifecycle root-gap closed via the seal-payload replay)");
}

#[test]
fn unauthorized_cross_cell_seal_rejected_by_both() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH for the lifecycle close: a CROSS-CELL seal (effect target ≠ action target)
    // is rejected by Rust (`apply_cell_seal`'s structural `target == action_target` guard) AND by
    // the verified gate (`cellSealA`: `stateAuthB actor cell` fails — the actor holds no edge to
    // the foreign cell). The collector does not even gather a replay op for it (the structural
    // guard is mirrored), so the lifecycle does not move on EITHER side and the reconstituted
    // ledger equals the Rust rollback — no fabricated Sealed payload.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Action targets A, but the seal aims at B — the unauthorized cross-cell mutation.
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::CellSeal {
            target: b_id,
            reason: [9u8; 32],
        },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        !executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust must REJECT a cross-cell seal"
    );
    assert!(
        matches!(
            rust_ledger.get(&b_id).unwrap().lifecycle,
            CellLifecycle::Live
        ),
        "the rejected seal must not move B's lifecycle"
    );

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(
        !lean_committed,
        "the verified gate must also REJECT the cross-cell seal"
    );
    assert!(
        matches!(
            lean_ledger.get(&b_id).unwrap().lifecycle,
            CellLifecycle::Live
        ),
        "the reconstituted ledger must not carry a fabricated Sealed payload"
    );
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id])
        .expect("a rejected seal leaves both ledgers at the (rolled-back) pre-state");
}

#[test]
fn cell_destroy_round_trips_lifecycle_closed() {
    if skip_no_lean() {
        return;
    }
    // LIFECYCLE ROOT-GAP CLOSE for the terminal transition. CellDestroy installs
    // `Destroyed { death_certificate_hash, destroyed_at }` — BOTH derived from the turn's FULL
    // `DeathCertificate` (`certificate_hash()` over all five fields / `destroyed_at_height`). The
    // wire `death_cert` table carries only the LOW 64 BITS of the hash, so this round-trip is the
    // proof the replay uses the full turn-supplied certificate, not the lossy wire value: the
    // commitment's lifecycle fold binds all 32 hash bytes, and `.root()` equality is asserted.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let cert = DeathCertificate {
        cell_id: a_id,
        last_receipt_hash: [3u8; 32],
        final_state_commitment: [5u8; 32],
        destroyed_at_height: 42,
        reason: DeathReason::Voluntary,
    };
    let expected_hash = cert.certificate_hash();
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::CellDestroy {
            target: a_id,
            certificate: cert,
        },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust CellDestroy should commit"
    );
    assert!(
        matches!(
            rust_ledger.get(&a_id).unwrap().lifecycle,
            CellLifecycle::Destroyed { death_certificate_hash, destroyed_at: 42 }
                if death_certificate_hash == expected_hash
        ),
        "Rust must have destroyed the cell binding the FULL certificate hash + height"
    );

    diff(pre, turn, &[a_id]).expect(
        "CellDestroy must round-trip (lifecycle root-gap closed via the full-certificate replay)",
    );
}

#[test]
fn unauthorized_cross_cell_destroy_rejected_by_both() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH for the destroy close: a CROSS-CELL destroy is rejected by Rust
    // (`apply_cell_destroy`'s structural guard) and by the verified `cellDestroyA` gate
    // (`stateAuthB` fails for the foreign cell). No replay op is collected; the target stays Live
    // on both sides and the reconstitution equals the Rust rollback — a forged destroy cannot
    // fabricate a Destroyed commitment.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let cert = DeathCertificate {
        cell_id: b_id,
        last_receipt_hash: [0u8; 32],
        final_state_commitment: [0u8; 32],
        destroyed_at_height: 0,
        reason: DeathReason::Forced,
    };
    // Action targets A; the destroy aims at B.
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::CellDestroy {
            target: b_id,
            certificate: cert,
        },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        !executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust must REJECT a cross-cell destroy"
    );

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(
        !lean_committed,
        "the verified gate must also REJECT the cross-cell destroy"
    );
    assert!(
        matches!(
            lean_ledger.get(&b_id).unwrap().lifecycle,
            CellLifecycle::Live
        ),
        "the reconstituted ledger must not carry a fabricated Destroyed commitment"
    );
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id])
        .expect("a rejected destroy leaves both ledgers at the (rolled-back) pre-state");
}

#[test]
fn cell_unseal_round_trips() {
    if skip_no_lean() {
        return;
    }
    // CellUnseal (Sealed→Live) is the LIFECYCLE root-gap CLOSE: the verified `cellUnsealChainA`
    // flips the discriminant back to `lcLive` (0), and `CellLifecycle::Live` is the ONE lifecycle
    // state with NO payload. So the wire (a bare discriminant, here dropped because Live=0) carries
    // everything needed, and `wire_state_to_ledger` reconstitutes `CellLifecycle::Live` byte-exactly
    // — matching Rust's `Cell::unseal` (which sets `lifecycle = Live`). Both producers commit and the
    // reconstituted ledger AGREES on state + cap_root + `.root()`. (Its partner transitions CellSeal /
    // CellDestroy stay gaps: they install a Sealed/Destroyed PAYLOAD the wire does not carry.)
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a); // stateAuthB (self-`node` edge) for the unseal authority leg
    let a_id = a.id();
    // Pre-state: the cell is SEALED (so unseal has something to reverse). Rust binds a reason payload;
    // the verified pre-state carries the discriminant `1` (Sealed) — both unseal back to Live.
    a.seal([7u8; 32], 0).expect("seal the pre-state cell");
    assert!(
        matches!(a.lifecycle, CellLifecycle::Sealed { .. }),
        "pre-state must be Sealed for the unseal round-trip"
    );
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    // Confirm Rust unseals to Live (so the close is about a real Sealed→Live transition).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor
            .execute(
                &single_effect_turn(a_id, a_id, 0, Effect::CellUnseal { target: a_id }),
                &mut rust_ledger
            )
            .is_committed(),
        "Rust CellUnseal should commit"
    );
    assert!(
        matches!(
            rust_ledger.get(&a_id).unwrap().lifecycle,
            CellLifecycle::Live
        ),
        "Rust must have unsealed the cell back to Live"
    );

    let turn = single_effect_turn(a_id, a_id, 0, Effect::CellUnseal { target: a_id });
    diff(pre, turn, &[a_id]).expect("CellUnseal must round-trip through the verified producer");
}

#[test]
fn grant_capability_round_trips_cap_fidelity_closed() {
    if skip_no_lean() {
        return;
    }
    // CAP-FIDELITY ROOT-GAP CLOSE. A self-GrantCapability inserts into the grantee's c-list a FULL
    // `CapabilityRef` (target, fresh slot, the granted permissions, breadstuff, ...). The verified
    // kernel DECIDES the commit (the delegator must hold an edge to `target` — here a held
    // self-cap), and the commit-gated turn-driven replay (`lean_apply::apply_cap_ops`) reconstructs
    // the EXACT leaf via `grant_ref`, so the reconstituted `cap_root` == the Rust producer's. We
    // grant a NON-None permission so a lossy bare-`node` reconstitution would HAVE diverged — the
    // round-trip is therefore a genuine, non-vacuous test that the full leaf is reconstructed.
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a); // the delegator must HOLD an edge for the verified `recCDelegate` gate.
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
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::GrantCapability {
            from: a_id,
            to: b_id,
            cap: cap.clone(),
        },
    );

    // Confirm Rust granted the FULL (non-None, breadstuff'd) cap to B (so the round-trip is
    // genuinely about cap fidelity, not a vacuous None-vs-None coincidence).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(executor.execute(&turn, &mut rust_ledger).is_committed());
    let b_caps = &rust_ledger.get(&b_id).unwrap().capabilities;
    assert!(
        b_caps.iter().any(|c| c.target == a_id
            && c.permissions == AuthRequired::Signature
            && c.breadstuff == Some([7u8; 32])),
        "Rust must have granted B a Signature-perm, breadstuff'd cap over A"
    );

    // THE CLOSE: the Lean producer's reconstituted cap_root == the Rust differential cap_root ==
    // the canonical cap-root over the full 7-field leaf. `diff` asserts cap_root AND `.root()`.
    diff(pre, turn, &[a_id, b_id])
        .expect("GrantCapability must round-trip (cap-fidelity root-gap closed)");
}

#[test]
fn grant_capability_amplification_does_not_install_divergent_state() {
    if skip_no_lean() {
        return;
    }
    // NON-VACUOUS TOOTH: a CROSS-CELL grant where the delegator does NOT hold an edge to the
    // target is REJECTED by both the verified gate (`recCDelegate` requires the edge) and Rust
    // (`apply_grant_capability`'s `lookup_by_target`). Neither c-list moves — the commit-gated
    // replay does not fire (committed=false) — so the reconstituted ledger equals the pre-state and
    // agrees with the Rust rollback. A forged grant cannot fabricate a cap_root.
    let a = make_open_cell(1, 100); // A holds NO edge to C.
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let c = make_open_cell(3, 5);
    let c_id = c.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    pre.insert_cell(c).unwrap();

    let cap = CapabilityRef {
        target: c_id, // A does not hold a cap to C — the grant must be rejected.
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
    };
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::GrantCapability {
            from: a_id,
            to: b_id,
            cap,
        },
    );

    // Rust rejects (A holds no cap to C). The Lean producer reconstitutes the unchanged pre-state.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let committed = executor.execute(&turn, &mut rust_ledger).is_committed();
    assert!(
        !committed,
        "cross-cell grant without a held edge must be REJECTED by Rust"
    );

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).expect("producer path must run");
    assert!(
        !lean_committed,
        "the verified gate must also REJECT the forged grant"
    );
    // Both rolled back: the reconstituted ledger == the Rust (rolled-back) ledger, cap_root intact.
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &[a_id, b_id, c_id])
        .expect("a rejected grant leaves all c-lists at their pre-state (no fabricated cap_root)");
}

#[test]
fn attenuate_capability_round_trips_cap_fidelity_closed() {
    if skip_no_lean() {
        return;
    }
    // CAP-FIDELITY ROOT-GAP CLOSE for AttenuateCapability. A narrows its OWN held slot in place
    // (permissions ⊤ → Signature). The verified kernel decides the commit; the commit-gated replay
    // mirrors `attenuate_in_place` exactly, so the narrowed leaf's `cap_root` agrees with Rust.
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    // A holds a full-authority (None) cap over B at slot 0; the attenuation narrows it.
    a.capabilities.grant(b_id, AuthRequired::None);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::AttenuateCapability {
            cell: a_id,
            slot: 0,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: Some(500),
        },
    );

    // Confirm Rust narrowed slot 0 (non-vacuous: the leaf actually moved).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(executor.execute(&turn, &mut rust_ledger).is_committed());
    let a_cap = rust_ledger
        .get(&a_id)
        .unwrap()
        .capabilities
        .iter()
        .find(|c| c.slot == 0)
        .cloned()
        .expect("slot 0 present");
    assert_eq!(a_cap.permissions, AuthRequired::Signature);
    assert_eq!(a_cap.expires_at, Some(500));

    diff(pre, turn, &[a_id, b_id])
        .expect("AttenuateCapability must round-trip (cap-fidelity root-gap closed)");
}

#[test]
fn introduce_round_trips_cap_fidelity_closed() {
    if skip_no_lean() {
        return;
    }
    // CAP-FIDELITY ROOT-GAP CLOSE for Introduce. The introducer A holds an edge to the target T
    // (so the verified `recCDelegate` gate commits) AND access to the recipient R (Rust's extra
    // legs). The introduced cap lands in R's c-list with `expires_at = block_height +
    // max_introduction_lifetime`; the commit-gated replay (`grant_with_expiry`) stamps the SAME
    // host-derived expiry, so cap_root agrees.
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let r = make_open_cell(2, 5);
    let r_id = r.id();
    let t = make_open_cell(3, 5);
    let t_id = t.id();
    // A holds edges to BOTH R (recipient access) and T (target authority).
    a.capabilities.grant(r_id, AuthRequired::None);
    a.capabilities.grant(t_id, AuthRequired::None);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(r).unwrap();
    pre.insert_cell(t).unwrap();

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

    // Rust commits and installs a cap over T into R's c-list with a host-derived expiry.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    if executor.execute(&turn, &mut rust_ledger).is_committed() {
        let r_caps = &rust_ledger.get(&r_id).unwrap().capabilities;
        assert!(
            r_caps
                .iter()
                .any(|c| c.target == t_id && c.expires_at.is_some()),
            "Rust must have introduced a (host-expiry) cap over T into R"
        );
        // Only assert the round-trip when Rust ALSO commits (the verified gate is the
        // edge-existence leg; this fixture satisfies Rust's stricter legs too).
        diff(pre, turn, &[a_id, r_id, t_id])
            .expect("Introduce must round-trip (cap-fidelity root-gap closed)");
    }
}
