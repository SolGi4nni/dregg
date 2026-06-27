//! # THE STAGED UMEM-COHORT DEPLOYED-PATH GAUNTLET (VK-RISK-FREE).
//!
//! The rotation-flip's deployed-routing precursor, proven end-to-end against the REAL
//! deployed-form prover — NOT a test lowering. Where the RANK-3 isolation test
//! (`circuit/tests/effect_vm_umem_cohort.rs`) BUILDS its descriptor at run time
//! (`build_umem_form`, the variable-width `6 + #domains` shape), THIS gauntlet bites the FIXED
//! per-effect cohort descriptor PARSED from the byte-pinned staged registry
//! (`UMEM_COHORT_V1_STAGED_REGISTRY_TSV`, the verified Lean
//! `EffectVmEmitUMemCohort.umemCohortRegistry`) through the staged SDK entry
//! [`prove_umem_cohort_staged`] — the same code path the gated VK flip will repoint onto.
//!
//! ## What this proves
//!
//! For each cohort effect (transfer · set-field · grant · attenuate), a real cell BEFORE → AFTER
//! the effect is projected into the ONE universal map (`project_record_kernel_state`); the
//! pre→post diff is the effect's umem op trace (single-domain by the cohort's design); and the
//! staged SDK prover resolves the FIXED cohort descriptor, builds the single-domain width-7 rows
//! plus the REAL `UMemBoundaryWitness`, and proves through the deployed-form `prove_vm_descriptor2_umem`
//! with that real boundary. The per-map agreement anchor (`record_kernel_boundary_agrees`) holds
//! at both endpoints, grounding the umem-form touch in the deployed per-map roots.
//!
//! ## Non-vacuity (the anti-forge tooth)
//!
//! `boundary_init_root_bound`: each op claims its prev cell against serial 0 (the committed
//! pre-state). A FORGED op whose `prev_val` disagrees with the genuine pre-state projection makes
//! the offline-memory multiset inconsistent at the boundary, so the deployed-form prover REFUSES.
//! This bites the real prover, not the harness.
//!
//! ## VK-RISK-FREE
//!
//! Pure ADDITIVE: it exercises only the STAGED registry + the opt-in `prove_umem_cohort_staged`
//! entry; it touches no deployed descriptor JSON / VK / default prover, and never arms
//! `umem_witness_enabled`. The deployed default stays per-map until the gated VK epoch.
//!
//! Requires `prover`. Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Permissions};
use dregg_circuit::effect_vm::Effect as VmEffect;
use dregg_circuit::field::BabyBear;
use dregg_sdk::full_turn_proof::prove_umem_cohort_staged;
use dregg_turn::umem::{
    UKey, UProjection, UVal, UmemKind, UmemOp, project_record_kernel_state,
    record_kernel_boundary_agrees,
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

fn make_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// The pre→post projection DIFF as a Blum WRITE op trace: every changed address becomes a write
/// of its post value over its genuine pre value, opened once against the boundary (serial 0).
/// This is the effect's universal-memory touch exactly as the executor's journal-derived trace
/// folds it (a same-value write is the disciplined shadow of a read).
fn ops_from_diff(pre: &UProjection, post: &UProjection) -> Vec<UmemOp> {
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

/// One cohort case: project BEFORE/AFTER, anchor per-map agreement at both endpoints, prove the
/// staged FIXED-cohort descriptor through the deployed-form prover, then exercise the forged-pre
/// tooth on the real path.
fn cohort_case(effect: &VmEffect, pre: &Cell, post: &Cell, expect_domain: u32) {
    record_kernel_boundary_agrees(pre)
        .unwrap_or_else(|e| panic!("PRE projection must agree with per-map roots: {e}"));
    record_kernel_boundary_agrees(post)
        .unwrap_or_else(|e| panic!("POST projection must agree with per-map roots: {e}"));

    let proj_pre = project_record_kernel_state(pre);
    let proj_post = project_record_kernel_state(post);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert!(!ops.is_empty(), "effect must touch the universal memory");
    assert!(
        ops.iter().all(|o| o.key.domain().code() == expect_domain),
        "this cohort leg must be single-domain (domain {expect_domain})"
    );

    // CONTROL: the staged FIXED cohort descriptor PROVES against the real boundary.
    prove_umem_cohort_staged(effect, &proj_pre, &ops).unwrap_or_else(|e| {
        panic!("staged umem cohort prove must accept the genuine {effect:?} leg: {e}")
    });

    // TOOTH (boundary_init_root_bound): forge the FIRST op's claimed pre cell — the row's prev
    // then disagrees with the boundary init (derived from the genuine pre projection), so the
    // offline-memory multiset is inconsistent and the deployed-form prover refuses.
    let mut forged = ops.clone();
    forged[0].prev_val = match &forged[0].prev_val {
        // an UPDATE touch: claim a different committed pre-value
        Some(UVal::Int(v)) => Some(UVal::Int(v + 1)),
        Some(_) => Some(UVal::Int(123_456)),
        // an INSERT touch (prev absent): claim a phantom pre-existing cell
        None => Some(UVal::Int(1)),
    };
    let r = prove_umem_cohort_staged(effect, &proj_pre, &forged);
    assert!(
        r.is_err(),
        "a forged committed pre-state ({effect:?}) must refuse on the staged deployed path"
    );
}

#[test]
fn staged_transfer_balance_cohort_proves_and_bites() {
    // TRANSFER's economic touch is the scalar Balance register (heap domain 1).
    let pre = make_cell(17, 1000);
    let mut post = pre.clone();
    post.state.set_balance(993);
    cohort_case(
        &VmEffect::Transfer {
            amount: 7,
            direction: 1,
        },
        &pre,
        &post,
        UKey::Balance(pre.id()).domain().code(),
    );
}

#[test]
fn staged_set_field_cohort_proves_and_bites() {
    // SET-FIELD on the committed user-field map → a heap-domain (1) write.
    let pre = make_cell(11, 1000);
    let mut post = pre.clone();
    let mut v = [0u8; 32];
    v[..4].copy_from_slice(&424242u32.to_le_bytes());
    assert!(post.state.set_field_ext(20, v), "field-map write");
    cohort_case(
        &VmEffect::SetField {
            field_idx: 20,
            value: BabyBear::new(424242),
        },
        &pre,
        &post,
        1,
    );
}

#[test]
fn staged_grant_cohort_proves_and_bites() {
    // GRANT a capability → a caps-domain (2) write (a fresh-slot insert).
    let pre = make_cell(13, 1000);
    let target = make_cell(14, 10).id();
    let mut post = pre.clone();
    post.capabilities
        .grant(target, AuthRequired::Either)
        .expect("grant");
    cohort_case(
        &VmEffect::GrantCapability {
            cap_entry: [BabyBear::ZERO; 8],
            phase_b: None,
        },
        &pre,
        &post,
        2,
    );
}

#[test]
fn staged_attenuate_cohort_proves_and_bites() {
    // ATTENUATE an existing capability in place → a caps-domain (2) write (in-place narrow).
    let mut pre = make_cell(15, 1000);
    let target = make_cell(16, 10).id();
    let slot = pre
        .capabilities
        .grant(target, AuthRequired::Either)
        .expect("grant");
    let mut post = pre.clone();
    post.capabilities
        .attenuate_in_place(slot, AuthRequired::Signature, None, None)
        .expect("attenuate narrows");
    cohort_case(
        &VmEffect::AttenuateCapability {
            cap_slot_hash: [BabyBear::ZERO; 8],
            narrower_commitment: [BabyBear::ZERO; 8],
            phase_b: None,
        },
        &pre,
        &post,
        2,
    );
}

/// THE NON-MEMBER FAIL-CLOSED: an effect with NO umem-cohort descriptor (state passthrough)
/// refuses on the staged path (it is not silently routed onto a wrong descriptor).
#[test]
fn staged_non_member_effect_refuses() {
    let pre = make_cell(21, 1000);
    let proj = project_record_kernel_state(&pre);
    let op = UmemOp {
        kind: UmemKind::Write,
        key: UKey::Balance(pre.id()),
        val: Some(UVal::Int(1)),
        prev_val: Some(UVal::Int(0)),
        prev_serial: 0,
    };
    let r = prove_umem_cohort_staged(&VmEffect::IncrementNonce, &proj, &[op]);
    assert!(
        r.is_err(),
        "a non-cohort effect must fail closed on the staged umem path"
    );
}
