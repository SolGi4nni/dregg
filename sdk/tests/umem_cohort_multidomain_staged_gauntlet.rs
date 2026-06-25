//! # THE STAGED MULTI-DOMAIN UMEM-COHORT DEPLOYED-PATH GAUNTLET (VK-RISK-FREE).
//!
//! The completion of the staged umem cohort to the FULL effect set: the effects whose state touch
//! spans MORE THAN ONE domain in a single effect — the NOTE/BRIDGE economic verbs that combine a
//! `nullifiers`-domain freshness insert (the spend/mint double-spend gate) with a `heap`-domain
//! balance write (the credit). The SINGLE-domain cohort path ([`prove_umem_cohort_staged`]) FAILS
//! CLOSED on such a leg (the width-7 fixed descriptor cannot witness two domains); this gauntlet
//! bites the FIXED MULTI-DOMAIN cohort descriptor PARSED from the byte-pinned staged registry
//! (`UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV`, the verified Lean
//! `EffectVmEmitUMemCohortMulti.umemCohortMultiRegistry`) through the staged SDK entry
//! [`prove_umem_cohort_multidomain_staged`] — the same code path the gated VK flip will repoint
//! onto for the multi-domain verbs.
//!
//! ## What this proves
//!
//! For `NoteSpend` and `BridgeMint`, a two-domain leg (a `heap` balance write + a `nullifiers`
//! freshness insert) builds the width-8 multi-domain rows + the REAL `UMemBoundaryWitness`, and the
//! staged SDK prover resolves the FIXED multi-domain descriptor (checking its baked-in `{heap,
//! nullifiers}` domain set against the leg's actual domains) and proves through the deployed-form
//! `prove_vm_descriptor2_umem` with that real boundary. So a multi-domain effect proves via the
//! (extended) umem cohort — STAGED — instead of failing closed.
//!
//! ## Teeth (the gauntlet bites)
//!
//! * **forged-pre** (`boundary_init_root_bound`): forging the heap op's claimed pre-balance makes
//!   the offline-memory multiset inconsistent at the boundary, so the deployed-form prover REFUSES.
//! * **single-domain leg fails closed**: a `NoteSpend` leg touching only `heap` is refused (it
//!   belongs on the width-7 single-domain cohort, not the multi-domain one).
//! * **domain-set mismatch fails closed**: a leg touching `{heap, caps}` against the `{heap,
//!   nullifiers}` descriptor is refused (the descriptor's committed VK backs a FIXED plane-set).
//! * **non-member fails closed**: a single-domain effect (`Transfer`) has no multi-domain
//!   descriptor and is refused.
//!
//! ## VK-RISK-FREE
//!
//! Pure ADDITIVE: it exercises only the STAGED multi-domain registry + the opt-in
//! `prove_umem_cohort_multidomain_staged` entry; it touches no deployed descriptor JSON / VK /
//! default prover, and never arms `umem_witness_enabled`.
//!
//! Requires `prover`. Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::Cell;
use dregg_circuit::effect_vm::Effect as VmEffect;
use dregg_circuit::field::BabyBear;
use dregg_sdk::full_turn_proof::prove_umem_cohort_multidomain_staged;
use dregg_turn::umem::{UKey, UProjection, UVal, UmemKind, UmemOp};

fn make_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    Cell::with_balance(pk, [0u8; 32], balance)
}

fn nullifier(seed: u8) -> [u8; 32] {
    let mut nf = [0u8; 32];
    nf[0] = seed;
    nf[31] = seed.wrapping_mul(53).wrapping_add(1);
    nf
}

/// A genuine two-domain NOTE/BRIDGE leg: PRE carries the cell's balance; the op trace credits the
/// balance (`heap`) AND inserts a fresh nullifier (`nullifiers`).
fn note_leg(seed: u8) -> (UProjection, Vec<UmemOp>) {
    let cell = make_cell(seed, 1000).id();
    let mut pre = UProjection::new();
    pre.insert(UKey::Balance(cell), UVal::Int(1000));
    let ops = vec![
        // heap: credit the balance 1000 -> 1007
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::Balance(cell),
            val: Some(UVal::Int(1007)),
            prev_val: Some(UVal::Int(1000)),
            prev_serial: 0,
        },
        // nullifiers: insert a fresh nullifier (prev absent — the freshness gate)
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::NoteNullifier(nullifier(seed)),
            val: Some(UVal::Present),
            prev_val: None,
            prev_serial: 0,
        },
    ];
    (pre, ops)
}

#[test]
fn multidomain_note_spend_proves_and_bites() {
    let effect = VmEffect::NoteSpend {
        nullifier: BabyBear::new(7),
        value: 7,
    };
    let (pre, ops) = note_leg(31);

    // CONTROL: the staged FIXED multi-domain cohort descriptor PROVES the genuine two-domain leg.
    prove_umem_cohort_multidomain_staged(&effect, &pre, &ops)
        .expect("staged multi-domain cohort must accept the genuine NoteSpend two-domain leg");

    // TOOTH (forged-pre): forge the heap op's claimed pre-balance; the boundary init (derived from
    // the genuine PRE) disagrees, so the offline-memory multiset is inconsistent and the prover
    // refuses on the real path.
    let mut forged = ops.clone();
    forged[0].prev_val = Some(UVal::Int(999));
    assert!(
        prove_umem_cohort_multidomain_staged(&effect, &pre, &forged).is_err(),
        "a forged committed pre-state must refuse on the staged multi-domain path"
    );
}

#[test]
fn multidomain_bridge_mint_proves() {
    let effect = VmEffect::BridgeMint {
        value_lo: BabyBear::new(7),
        mint_hash: BabyBear::new(11),
        value_full: 7,
    };
    let (pre, ops) = note_leg(44);
    prove_umem_cohort_multidomain_staged(&effect, &pre, &ops)
        .expect("staged multi-domain cohort must accept the genuine BridgeMint two-domain leg");
}

/// A NoteSpend leg touching ONLY `heap` (no nullifier) belongs on the width-7 single-domain cohort,
/// not the multi-domain one — the multi-domain generator fails closed (< 2 domains).
#[test]
fn multidomain_single_domain_leg_fails_closed() {
    let effect = VmEffect::NoteSpend {
        nullifier: BabyBear::new(7),
        value: 7,
    };
    let cell = make_cell(50, 1000).id();
    let mut pre = UProjection::new();
    pre.insert(UKey::Balance(cell), UVal::Int(1000));
    let ops = vec![UmemOp {
        kind: UmemKind::Write,
        key: UKey::Balance(cell),
        val: Some(UVal::Int(1007)),
        prev_val: Some(UVal::Int(1000)),
        prev_serial: 0,
    }];
    assert!(
        prove_umem_cohort_multidomain_staged(&effect, &pre, &ops).is_err(),
        "a single-domain leg must fail closed on the multi-domain path"
    );
}

/// A leg touching `{heap, caps}` against the `{heap, nullifiers}` descriptor is refused — the fixed
/// descriptor's committed VK backs a FIXED plane-set; it must not prove a different one.
#[test]
fn multidomain_domain_set_mismatch_fails_closed() {
    let effect = VmEffect::NoteSpend {
        nullifier: BabyBear::new(7),
        value: 7,
    };
    let cell = make_cell(60, 1000).id();
    let mut pre = UProjection::new();
    pre.insert(UKey::Balance(cell), UVal::Int(1000));
    let ops = vec![
        // heap
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::Balance(cell),
            val: Some(UVal::Int(1007)),
            prev_val: Some(UVal::Int(1000)),
            prev_serial: 0,
        },
        // caps (NOT nullifiers) — wrong second plane for this descriptor
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::CapSlot { cell, slot: 0 },
            val: Some(UVal::Present),
            prev_val: None,
            prev_serial: 0,
        },
    ];
    assert!(
        prove_umem_cohort_multidomain_staged(&effect, &pre, &ops).is_err(),
        "a {{heap, caps}} leg must fail closed against the {{heap, nullifiers}} descriptor"
    );
}

/// A single-domain effect (`Transfer`) has no multi-domain cohort descriptor — refused.
#[test]
fn multidomain_non_member_refuses() {
    let effect = VmEffect::Transfer {
        amount: 7,
        direction: 1,
    };
    let (pre, ops) = note_leg(70);
    assert!(
        prove_umem_cohort_multidomain_staged(&effect, &pre, &ops).is_err(),
        "a non-multi-domain-member effect must fail closed"
    );
}
