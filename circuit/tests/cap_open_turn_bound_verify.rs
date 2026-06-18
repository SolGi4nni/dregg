//! # THE TURN-IDENTITY WELD (#225) — the LEDGERLESS LIGHT CLIENT'S forcing tooth.
//!
//! The Lean keystone `Dregg2.Circuit.Emit.CapOpenTurnPins.effCapOpenV3TB` (descriptor
//! `transferCapOpenTBVmDescriptor2R24`, trace_width 409, public_input_count 41) is the LIVE transfer
//! cap-open PLUS two turn-identity columns (`actor`/`dst`) and three appended `.piBinding .last` gates
//! welding the cap-open `src`/`actor`/`dst` columns to NEW public-input slots (`src → PI[38]`, `actor →
//! PI[39]`, `dst → PI[40]`). The verifier ANCHORS those three PIs to the TRUSTED turn it holds
//! (`anchor_cap_open_turn_pins`, the deployment realization of the named `TurnIdentityAnchored`
//! predicate), exactly as the record-pin family anchors `dpis[38]` from the trusted post-cell.
//!
//! THE FORCING (the light-client-relevant tooth): a ledgerless light client, holding only the trusted
//! turn, can conclude the published turn's `actor`/`src`/`dst` MATCH the proven transition. This test
//! realizes that END-TO-END in Rust:
//!
//!   * an HONEST transfer TB cap-open proof verifies when the verifier anchors the three turn-identity
//!     PIs to the SAME `(src, actor, dst)` the prover published;
//!   * a proof whose published `actor`/`src`/`dst` PI does NOT match the trusted turn is REJECTED by
//!     `verify_vm_descriptor2` ALONE (the verifier overrides the PI from the trusted turn; the appended
//!     `.piBinding` gate then disagrees with the proof's bound, last-row-pinned column → UNSAT).
//!
//! This is `CapOpenTurnPins.effCapOpenV3TB_rejects_mismatched_src` made good on the deployed prover +
//! verifier: the gate is LOAD-BEARING for a ledgerless client.
//!
//! LAW #1: this test fills COLUMNS only; every constraint is the Lean-declared chip lookup / base gate
//! / pi_binding the IR-v2 interpreter realizes generically. No hand-authored Rust constraint semantics.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover cap_open_turn_bound -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_TB_ACTOR_COL, CAP_OPEN_TB_DST_COL, CAP_OPEN_TB_PI_ACTOR, CAP_OPEN_TB_PI_DST,
    CAP_OPEN_TB_PI_SRC, CAP_OPEN_TB_WIDTH, CapOpenWitness, FACET_MASK_HI, RotatedBlockWitness,
    SIGNATURE_AUTH_TAG, WRITE_MASK_LO, anchor_cap_open_turn_pins, cap_open_tb_dpis,
    generate_rotated_effect_vm_trace, transfer_caveat_manifest, widen_to_cap_open_tb,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

/// The LIVE turn-bound transfer cap-open descriptor (the #225 weld).
const CAP_OPEN_TB_KEY: &str = "transferCapOpenTBVmDescriptor2R24";

fn reg_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Build a proven rotated TRANSFER base trace + 38 PIs (a debit transfer — `direction = 1`), the live
/// rotated cohort path the deployed transfer cap-open widens. NO attenuate phase-B patch (transfer is
/// directly valid), the two-domain transfer caveat manifest (matching the live route).
fn build_transfer_base() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer { amount: 1_000, direction: 1 }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    // A debit transfer ticks the nonce and debits the balance on the after-cell.
    let after_cell = producer_cell(before_balance - 1_000, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = transfer_caveat_manifest();
    let (trace, pis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated Transfer base trace must generate");
    (trace, pis)
}

/// The cap-membership witness: a transfer-conferring leaf (genuine two-axis facet × tier — `mask_lo ==
/// EFFECT_TRANSFER`, `mask_hi == 0`, `auth_tag == Signature`) whose `target` IS the turn's `src` felt.
const SRC_FELT: u32 = 7_777;

fn cap_open_witness() -> CapOpenWitness {
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),            // slot_hash
        BabyBear::new(SRC_FELT),           // target (== src)
        BabyBear::new(SIGNATURE_AUTH_TAG), // auth_tag (== 1, Signature tier)
        BabyBear::new(WRITE_MASK_LO),      // mask_lo (== EFFECT_TRANSFER = 2)
        BabyBear::new(FACET_MASK_HI),      // mask_hi (== 0)
        BabyBear::new(0x00FF_FFFF),        // expiry
        BabyBear::new(42),                 // breadstuff
    ];
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(123),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds")
}

/// **THE DEPLOYMENT FORCING TEST (#225).** An honest transfer TB cap-open proof verifies under the
/// trusted-turn anchor; a proof whose published `src`/`actor`/`dst` disagrees with the trusted turn is
/// REJECTED by `verify_vm_descriptor2` ALONE (the verifier override realizes `TurnIdentityAnchored`).
#[test]
fn cap_open_turn_bound_verifier_forces_published_identity() {
    let desc = parse_vm_descriptor2(reg_json(CAP_OPEN_TB_KEY)).expect("TB cap-open descriptor parses");
    assert_eq!(desc.trace_width, CAP_OPEN_TB_WIDTH, "TB width 409");
    assert_eq!(desc.public_input_count, 41, "TB carries 41 PIs (38 rotated + 3 turn-identity)");

    // The TRUSTED turn the light client holds. `src` IS the cap-leaf target the targetBind roots; the
    // owner arm publishes `actor == dst == src` (the cap is a member of the actor's own c-list).
    let trusted_src = BabyBear::new(SRC_FELT);
    let trusted_actor = trusted_src;
    let trusted_dst = trusted_src;

    // The HONEST prover: build the transfer base, widen with the TB cap-open (fills src/actor/dst
    // columns), publish the 41-PI vector with the prover's OWN (honest) identity.
    let (mut trace, base_pis) = build_transfer_base();
    let w = cap_open_witness();
    widen_to_cap_open_tb(&mut trace, &w, trusted_actor, trusted_dst).expect("TB widen");
    let honest_pis = cap_open_tb_dpis(&base_pis, trusted_src, trusted_actor, trusted_dst);
    assert_eq!(honest_pis.len(), 41);
    // The published columns are pinned on the last row; sanity-check the fill landed.
    assert_eq!(trace[0][CAP_OPEN_TB_ACTOR_COL], trusted_actor);
    assert_eq!(trace[0][CAP_OPEN_TB_DST_COL], trusted_dst);

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &honest_pis, &mem_boundary, &map_heaps)
        .expect("honest transfer TB cap-open proves (and self-verifies)");

    // (A) THE VERIFIER ANCHOR — ACCEPT. The light client recomputes the three turn-identity PIs from
    //     the TRUSTED turn it holds and verifies. They match the honest proof → ACCEPT.
    let mut anchored_pis = honest_pis.clone();
    anchor_cap_open_turn_pins(&mut anchored_pis, trusted_src, trusted_actor, trusted_dst);
    verify_vm_descriptor2(&desc, &proof, &anchored_pis)
        .expect("honest TB cap-open verifies under the trusted-turn anchor");
    eprintln!(
        "TURN-IDENTITY ANCHOR ACCEPT: honest transfer TB cap-open verified; the verifier recomputed \
         src/actor/dst PIs (38/39/40) from the trusted turn and they MATCH the proven transition."
    );

    // (B) THE NEGATIVE TOOTH — a FORGED published SRC is rejected by the VERIFIER ALONE. The trusted
    //     turn's src is `trusted_src`; the verifier anchors PI[38] to it. The proof was bound to the
    //     honest src column (== trusted_src). We now anchor PI[38] to a DIFFERENT (forged) src the
    //     trusted turn does NOT carry → the last-row src pin disagrees with the bound column → UNSAT.
    {
        let mut forged = honest_pis.clone();
        let forged_src = BabyBear::new(SRC_FELT + 1);
        // The verifier holds a trusted turn whose src is `forged_src` (≠ the proof's src column).
        anchor_cap_open_turn_pins(&mut forged, forged_src, trusted_actor, trusted_dst);
        assert_ne!(forged[CAP_OPEN_TB_PI_SRC], honest_pis[CAP_OPEN_TB_PI_SRC]);
        let rejected = verify_vm_descriptor2(&desc, &proof, &forged).is_err();
        assert!(
            rejected,
            "a published src that does NOT match the trusted turn MUST be rejected by the verifier alone"
        );
    }

    // (C) THE NEGATIVE TOOTH — a FORGED published ACTOR is rejected by the VERIFIER ALONE (PI[39]).
    {
        let mut forged = honest_pis.clone();
        let forged_actor = BabyBear::new(0xDEAD);
        anchor_cap_open_turn_pins(&mut forged, trusted_src, forged_actor, trusted_dst);
        assert_ne!(forged[CAP_OPEN_TB_PI_ACTOR], honest_pis[CAP_OPEN_TB_PI_ACTOR]);
        let rejected = verify_vm_descriptor2(&desc, &proof, &forged).is_err();
        assert!(
            rejected,
            "a published actor that does NOT match the trusted turn MUST be rejected by the verifier alone"
        );
    }

    // (D) THE NEGATIVE TOOTH — a FORGED published DST is rejected by the VERIFIER ALONE (PI[40]).
    {
        let mut forged = honest_pis.clone();
        let forged_dst = BabyBear::new(0xBEEF_BEEF & 0x7FFF_FFFF);
        anchor_cap_open_turn_pins(&mut forged, trusted_src, trusted_actor, forged_dst);
        assert_ne!(forged[CAP_OPEN_TB_PI_DST], honest_pis[CAP_OPEN_TB_PI_DST]);
        let rejected = verify_vm_descriptor2(&desc, &proof, &forged).is_err();
        assert!(
            rejected,
            "a published dst that does NOT match the trusted turn MUST be rejected by the verifier alone"
        );
    }

    eprintln!(
        "TURN-IDENTITY NEGATIVE TEETH GREEN: a forged published src / actor / dst (one the trusted \
         turn does NOT carry) is REJECTED by verify_vm_descriptor2 alone — the #225 gate is \
         load-bearing for a ledgerless light client."
    );
}
