//! # THE SEALED-ESCROW SATISFACTION-WELD — first REAL STARK prove/verify (GENTIAN, STAGED).
//!
//! The keystone (commit `f68868022`) built the welded descriptor `settleEscrowSatVmDescriptor2R24`,
//! its selector (`ESCROW_SEL_COL = 70` / `ESCROW_SEL_PI = 46`), the Lean refinement rung + UNSAT
//! teeth, and a constraint-EVAL exerciser (`settle_escrow_capacity_weld.rs`). What it did NOT have:
//! a production producer emitting a SATISFYING rotated trace for the welded descriptor, and a full
//! STARK prove/verify against it. The exerciser's own doc named the gap — the teeth bit only at the
//! Lean-proof + constraint-eval level, not in a real proof.
//!
//! This closes that. `generate_rotated_settle_escrow_trace` emits a satisfying rotated trace (a
//! zero-amount settle carrier: the two leg STATUS fields flipped `Deposited → Consumed`, the
//! capacity selector ON on the settle row, every dependent commitment recomputed), and this test
//! proves + verifies the welded descriptor END-TO-END over it:
//!
//!   * an HONEST both-legs settle PROVES and VERIFIES (a real `BatchProof`, self-verified AND
//!     verified independently);
//!   * a FORGED PARTIAL settle (leg B left `Deposited` after) FAILS to prove — the welded leg-B
//!     AFTER gate is UNSAT; the rest of the trace is fully consistent, so the welded gate is the
//!     SOLE reason for refusal;
//!   * a FORGED PHANTOM settle (leg A never `Deposited` before) FAILS to prove — the welded leg-A
//!     BEFORE gate is UNSAT.
//!
//! So the escrow weld's teeth bite IN A REAL STARK PROOF, not only in `eval_lean_expr`. STILL STAGED:
//! the deployed cohort is untouched, no live path routes through this descriptor, and its VK is not
//! the deployed default — the flip remains gated (binding the selector to the committed declaration
//! in-AIR, the `DeclCommitBinds` §6 item 2, + committing the VK + routing).
//!
//! SLOW (a full batch STARK). Run with:
//!   `cargo test -p dregg-circuit --test settle_escrow_weld_prove -- --nocapture`

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::CellState;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::satisfaction_weld::{
    ESCROW_SEL_COL, after_field_col, before_field_col,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_settle_escrow_trace,
    generate_rotated_settle_escrow_trace_forged,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

const LEG_A: usize = 0;
const LEG_B: usize = 1;
const DEP: u32 = pi::SETTLE_ESCROW_STATUS_DEPOSITED;
const CON: u32 = pi::SETTLE_ESCROW_STATUS_CONSUMED;
const EMPTY: u32 = 0;

/// The committed welded escrow descriptor JSON from the staged registry TSV.
fn welded_escrow_json() -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("settleEscrowSatVmDescriptor2R24") {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("settleEscrowSatVmDescriptor2R24 in V3_STAGED_REGISTRY_TSV")
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

/// A residue-free producer cell (empty fields/caps — so `record_digest = ZERO` and the
/// `recommit_v1_block` ZERO-absorb is byte-identical to the descriptor's bound scheme).
fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// Bridge a producer `RotationWitness` into the circuit generator's `RotatedBlockWitness`.
fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// Build the (initial_state, before_w, after_w) for a zero-amount settle carrier over a residue-free
/// cell. The producer FORCES the leg fields itself, so the cell's own fields are irrelevant here;
/// the witnesses carry the turn-invariant limbs (cells_root / roots / iroot) and are identical
/// before/after (a zero-amount carrier moves no economic state).
fn carrier_inputs() -> (CellState, RotatedBlockWitness, RotatedBlockWitness) {
    let balance: i64 = 100_000;
    let initial_state = CellState::new(balance as u64, 0);

    let cell = producer_cell(balance);
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let w = rw::produce(
        &cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    (initial_state, bridge(&w), bridge(&w))
}

#[test]
fn honest_settle_proves_and_verifies_end_to_end() {
    let desc = parse_vm_descriptor2(welded_escrow_json()).expect("welded escrow descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "rotated 46 + the selector slot"
    );

    let (initial_state, before_w, after_w) = carrier_inputs();
    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_settle_escrow_trace(
        &initial_state,
        &before_w,
        &after_w,
        &caveat,
        LEG_A,
        LEG_B,
    )
    .expect("the satisfying settle carrier must generate");
    assert_eq!(dpis.len(), 47, "47 PIs (rotated 46 + selector)");

    // The welded gate reads exactly these columns; pin the satisfying assignment for clarity.
    let r0 = &trace[0];
    assert_eq!(
        r0[ESCROW_SEL_COL],
        BabyBear::ONE,
        "selector ON on the settle row"
    );
    assert_eq!(
        r0[before_field_col(LEG_A)],
        BabyBear::new(DEP),
        "leg A Deposited before"
    );
    assert_eq!(
        r0[before_field_col(LEG_B)],
        BabyBear::new(DEP),
        "leg B Deposited before"
    );
    assert_eq!(
        r0[after_field_col(LEG_A)],
        BabyBear::new(CON),
        "leg A Consumed after"
    );
    assert_eq!(
        r0[after_field_col(LEG_B)],
        BabyBear::new(CON),
        "leg B Consumed after"
    );
    assert_eq!(
        dpis[46],
        BabyBear::ONE,
        "PI 46 = the pinned escrow selector"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // THE FIRST REAL STARK PROVE/VERIFY of the escrow weld.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("the honest settle MUST prove end-to-end against the welded descriptor");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("the honest settle proof MUST verify independently");

    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "ESCROW SATISFACTION WELD: honest settle PROVED + VERIFIED (real BatchProof, {total} B / \
         ~{:.1} KiB). The teeth bite IN-PROOF.",
        total as f64 / 1024.0
    );
}

/// Attempt to prove a forged carrier; returns true iff proving REFUSES it (either the eager
/// pre-flight replay errs, the prover errs, or a panic is unwound).
fn proving_refuses(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
) -> bool {
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    match classify("proving_refuses", || {
        prove_vm_descriptor2(desc, trace, dpis, &mem_boundary, &map_heaps)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

#[test]
fn forged_partial_settle_fails_to_prove() {
    let desc = parse_vm_descriptor2(welded_escrow_json()).expect("descriptor parses");
    let (initial_state, before_w, after_w) = carrier_inputs();
    let caveat = empty_caveat_manifest();

    // PARTIAL settle: both legs Deposited before, but leg B left Deposited AFTER (the half-open
    // trade). Fully consistent commits/continuity — the welded leg-B AFTER gate is the ONLY thing
    // that fails.
    let (trace, dpis) = generate_rotated_settle_escrow_trace_forged(
        &initial_state,
        &before_w,
        &after_w,
        &caveat,
        LEG_A,
        LEG_B,
        (DEP, DEP),
        (CON, DEP),
    )
    .expect("the forged carrier still generates a consistent trace");
    // The forged assignment violates the welded gate but nothing else.
    assert_eq!(
        trace[0][after_field_col(LEG_B)],
        BabyBear::new(DEP),
        "leg B left Deposited after"
    );
    assert!(
        proving_refuses(&desc, &trace, &dpis),
        "a PARTIAL settle MUST fail to prove against the welded descriptor (the leg-B AFTER gate \
         bites in-proof)"
    );
    eprintln!("ESCROW WELD: forged PARTIAL settle REFUSED in a real STARK prove.");
}

#[test]
fn forged_phantom_settle_fails_to_prove() {
    let desc = parse_vm_descriptor2(welded_escrow_json()).expect("descriptor parses");
    let (initial_state, before_w, after_w) = carrier_inputs();
    let caveat = empty_caveat_manifest();

    // PHANTOM settle: leg A never Deposited before (Empty) — a consumption conjured from a leg that
    // never locked. The welded leg-A BEFORE gate is the ONLY thing that fails.
    let (trace, dpis) = generate_rotated_settle_escrow_trace_forged(
        &initial_state,
        &before_w,
        &after_w,
        &caveat,
        LEG_A,
        LEG_B,
        (EMPTY, DEP),
        (CON, CON),
    )
    .expect("the forged carrier still generates a consistent trace");
    assert_eq!(
        trace[0][before_field_col(LEG_A)],
        BabyBear::ZERO,
        "leg A never Deposited before"
    );
    assert!(
        proving_refuses(&desc, &trace, &dpis),
        "a PHANTOM settle MUST fail to prove against the welded descriptor (the leg-A BEFORE gate \
         bites in-proof)"
    );
    eprintln!("ESCROW WELD: forged PHANTOM settle REFUSED in a real STARK prove.");
}
