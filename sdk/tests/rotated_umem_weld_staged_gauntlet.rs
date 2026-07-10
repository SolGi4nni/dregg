//! # THE ROTATED+UMEM WELD GAUNTLET (STAGED, VK-RISK-FREE) — the last precursor before the VK epoch.
//!
//! Where [`umem_cohort_staged_gauntlet`] proves the umem cohort leg STANDALONE (width-7, 0-PI) and
//! [`sovereign_rotated_c1`] proves the rotated R=24 leg standalone (the 46-PI effect proof), THIS
//! gauntlet bites the WELDED form: a REAL turn proved through ONE descriptor that carries BOTH the
//! whole rotated cohort proof AND the universal-memory reconciliation leg, via the staged SDK entry
//! [`dregg_sdk::full_turn_proof::prove_rotated_umem_welded_staged`] — the same code path the gated VK
//! flip will repoint the deployed prover onto.
//!
//! ## What this proves (the weld)
//!
//! For a real `before → after` cell transition (a transfer-out), the rotated descriptor's full
//! constraint set proves the effect semantics + the 46-PI rotated commit vector, AND the appended
//! `umem_op` leg reconciles the SAME transition's universal-memory touch (the Balance write) against
//! a REAL [`dregg_circuit::descriptor_ir2::UMemBoundaryWitness`]. One descriptor, one proof. The
//! rotated PIs stay intact — which is exactly what lets the IVC fold (the sibling test
//! [`circuit-prove/tests/ivc_turn_chain_rotated_umem_welded`]) read `old_root`/`new_root` off the
//! welded leg (the 0-PI cohort form could not supply them).
//!
//! ## The anti-forge tooth
//!
//! A FORGED umem op (its claimed committed `prev_val` disagrees with the genuine pre-state
//! projection) makes the offline universal-memory multiset inconsistent at the boundary, so the
//! deployed-form prover REFUSES — the weld does not weaken the umem leg's boundary tooth.
//!
//! ## VK-RISK-FREE
//!
//! Pure ADDITIVE: it exercises only the STAGED welded descriptor
//! ([`dregg_circuit::effect_vm_descriptors::weld_umem_into_rotated_descriptor`]) + the opt-in welded
//! prover; it touches no deployed descriptor JSON / VK / default prover, and never arms
//! `umem_witness_enabled`. The deployed default stays rotated+per-map until the gated VK epoch.
//!
//! Requires `prover`. Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest;
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_sdk::full_turn_proof::prove_rotated_umem_welded_staged;
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{
    UKey, UVal, UmemKind, UmemOp, project_record_kernel_state, record_kernel_boundary_agrees,
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

/// The validated rotated transfer producer cell (mirrors `rotation_batchstark_leaf_smoke`).
fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// The pre→post projection DIFF as a Blum WRITE op trace (the effect's universal-memory touch
/// exactly as the staged cohort gauntlet folds it).
fn ops_from_diff(
    pre: &dregg_turn::umem::UProjection,
    post: &dregg_turn::umem::UProjection,
) -> Vec<UmemOp> {
    let mut keys: Vec<&UKey> = pre.keys().chain(post.keys()).collect();
    keys.sort();
    keys.dedup();
    let mut ops = Vec::new();
    for k in keys {
        let a = pre.get(k);
        let b = post.get(k);
        if a != b {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: b.cloned(),
                prev_val: a.cloned(),
                prev_serial: 0,
            });
        }
    }
    ops
}

#[test]
fn rotated_umem_welded_transfer_proves_and_bites() {
    // -- a real transfer-out (the validated v1 reference witness). --
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![VmEffect::Transfer {
        amount,
        direction: 1,
    }];

    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    // The SAME transition's universal-memory touch: the Balance write (heap domain 1).
    record_kernel_boundary_agrees(&before_cell)
        .unwrap_or_else(|e| panic!("PRE projection must agree with per-map roots: {e}"));
    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert!(
        !ops.is_empty(),
        "the transfer must touch the universal memory"
    );
    assert!(
        ops.iter()
            .all(|o| o.key.domain().code() == UKey::Balance(before_cell.id()).domain().code()),
        "the transfer's umem touch is the single Balance domain"
    );

    let caveat = transfer_caveat_manifest();

    // CONTROL: the WELDED rotated+umem descriptor PROVES the real turn (rotated semantics + the
    // universal-memory reconciliation, one proof).
    prove_rotated_umem_welded_staged(&st, &effects, &before_w, &after_w, &caveat, &proj_pre, &ops)
        .expect("the welded rotated+umem descriptor proves the genuine transfer turn");

    // TOOTH: forge the first umem op's claimed committed pre-value — the boundary init then
    // disagrees with the genuine pre projection, the offline multiset is inconsistent, and the
    // deployed-form prover REFUSES on the welded path.
    let mut forged = ops.clone();
    forged[0].prev_val = match &forged[0].prev_val {
        Some(UVal::Int(v)) => Some(UVal::Int(v + 1)),
        Some(_) => Some(UVal::Int(123_456)),
        None => Some(UVal::Int(1)),
    };
    let r = prove_rotated_umem_welded_staged(
        &st, &effects, &before_w, &after_w, &caveat, &proj_pre, &forged,
    );
    assert!(
        r.is_err(),
        "a forged committed pre-state must refuse on the welded rotated+umem path"
    );
}

/// FAIL-CLOSED: a non-rotated-cohort effect has no welded descriptor and refuses.
#[test]
fn rotated_umem_welded_non_cohort_refuses() {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let before_cell = producer_cell(before_balance);
    let mut ledger = Ledger::new();
    ledger.insert_cell(before_cell.clone()).unwrap();
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[],
        &Default::default(),
    );
    let proj = project_record_kernel_state(&before_cell);
    let op = UmemOp {
        kind: UmemKind::Write,
        key: UKey::Balance(before_cell.id()),
        val: Some(UVal::Int(1)),
        prev_val: Some(UVal::Int(0)),
        prev_serial: 0,
    };
    // `IncrementNonce` is NOT a rotated cohort member with a umem cohort descriptor on this path.
    let r = prove_rotated_umem_welded_staged(
        &st,
        &[VmEffect::IncrementNonce],
        &before_w,
        &before_w,
        &transfer_caveat_manifest(),
        &proj,
        &[op],
    );
    assert!(
        r.is_err(),
        "a non-cohort effect must fail closed on the welded rotated+umem path"
    );
}
