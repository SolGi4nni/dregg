//! # THE ROTATION FLIP — the rotated cohort proves+verifies end-to-end, LIVE-GENERATED.
//!
//! `docs/ROTATION-CUTOVER.md` §5 items 1,3-5,8: the staged Lean keystones
//! (`EffectVmEmitRotationV3.lean`) PROVE the rotated 26-descriptor cohort sound and the
//! staged probe measures the rotated SHAPE; what remained was (a) the per-turn PRODUCERS of
//! the witness-carried limbs (`cells_root`, `iroot`, `lifecycle`/`epoch`) — built in
//! `dregg_turn::rotation_witness` — and (b) a rotated TRACE GENERATOR that consumes them.
//!
//! G1: the rotated trace is now built by the LIVE generator
//! `dregg_circuit::effect_vm::generate_rotated_effect_vm_trace` (`effect_vm/trace_rotated.rs`),
//! NOT hand-welded in this test. The generator promotes the former in-test `fill_block` /
//! `fill_caveat` into genuine circuit machinery: from the v1 186-col trace + the producer
//! witness limbs it emits the 311-col rotated trace + the 38-PI vector the staged registry
//! descriptor (`transferVmDescriptor2R24`) pins.
//!
//! G3: the LIVE cell≡circuit binding — `dregg_cell::commitment::compute_canonical_state_
//! commitment_v9_felt` (the additive v9 rotated commitment) of the real before-cell EQUALS
//! the circuit row-0 `STATE_COMMIT` carrier the LIVE generator produced. This closes the
//! binding the cutover doc deferred ("the LIVE-WIRE differential (cell v9 == circuit)").
//!
//! What it asserts (all on the ROTATED R=24 shape):
//!
//!   1. **THE FULL ROTATED TRANSFER PROVES+VERIFIES** — `transferVmDescriptor2R24` (width
//!      311) over a real transfer witness, LIVE-generated, every chained `wireCommitR` digest
//!      genuine, the four appended PI pins published.
//!   2. **THE cell≡circuit ROTATED DIFFERENTIAL** — (a) the producer's limbs EQUAL the
//!      generated trace's limbs; (b) the producer's `state_commit` AND the cell's v9
//!      commitment EQUAL the trace's row-0 `STATE_COMMIT` carrier — three computations of the
//!      same object agree.
//!   3. **ANTI-GHOST** — a tampered rotated limb (heap_root), a tampered iroot, a tampered
//!      caveat key, and a forged appended PI each make proving REFUSE.
//!
//! Gated on `recursion` (compiles `descriptor_ir2`). SLOW; run with
//! `cargo test -p dregg-circuit --features recursion rotation_flip -- --nocapture`.

#![cfg(feature = "recursion")]

use dregg_cell::commitment::{V9RotationContext, compute_canonical_state_commitment_v9_felt};
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{STATE_BEFORE_BASE, state};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_COMMITTED_HEIGHT, B_IROOT, B_STATE_COMMIT, BEFORE_BASE, CAVEAT_BASE, C_SPAN,
    ROT_WIDTH, RotatedBlockWitness, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

const B_CAP_ROOT: usize = 25;
const NUM_PRE: usize = rw::NUM_PRE_LIMBS; // 31

/// Resolve the rotated transfer descriptor JSON from the staged registry TSV.
fn rotated_transfer_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some("transferVmDescriptor2R24") {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
}

/// Bridge a producer `RotationWitness` into the circuit generator's `RotatedBlockWitness`
/// (the two crates that depend on BOTH `dregg-turn` and `dregg-circuit` — here the test, in
/// production the sdk — own this bridge; the generator itself is pure-circuit).
fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
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

/// Build the producer cell for the transfer-out before/after cells from a real
/// `RecordKernelState`. The circuit `CellState` (felt fields) and the producer's
/// `dregg_cell::Cell` (32-byte fields) must agree on the welded scalars; this helper
/// constructs a `dregg_cell::Cell` carrying the same scalars (balance/nonce, empty fields,
/// empty caps) so the producer's welded limbs equal the circuit trace's state-block felts.
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

#[test]
fn rotated_transfer_proves_verifies_differential_and_refuses_ghost() {
    let desc = parse_vm_descriptor2(rotated_transfer_json())
        .expect("rotated transfer descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(desc.public_input_count, 38, "34 v1 PIs + 4 appended");

    // -- a real transfer: the validated v1 reference witness (transfer-out). --
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];

    // -- the producers, from the REAL before/after RecordKernelState. --
    // A real turn's receipt log → iroot; the ledger → cells_root.
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    // -- (G1) THE LIVE GENERATOR drives the rotated trace + PIs (NOT hand-built). --
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a 311-col trace + 38 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "311-col rotated trace");
    assert_eq!(dpis.len(), 38);

    // -- (2) THE cell≡circuit ROTATED DIFFERENTIAL: producer limbs == the generated trace's
    //    welded state-block felts (r0↔balance_lo, …, cap_root↔cap_root), on the first row. --
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    assert_eq!(
        before_w.pre_limbs[1],
        r0[STATE_BEFORE_BASE + state::BALANCE_LO],
        "differential: r0 == v1 balance_lo (before)"
    );
    assert_eq!(
        before_w.pre_limbs[2],
        r0[STATE_BEFORE_BASE + state::NONCE],
        "differential: r1 == v1 nonce (before)"
    );
    assert_eq!(
        before_w.pre_limbs[3],
        r0[STATE_BEFORE_BASE + state::BALANCE_HI],
        "differential: r2 == v1 balance_hi (before)"
    );
    for i in 0..8 {
        assert_eq!(
            before_w.pre_limbs[4 + i],
            r0[STATE_BEFORE_BASE + state::FIELD_BASE + i],
            "differential: r{} == v1 field[{i}] (before)",
            3 + i
        );
    }
    assert_eq!(
        before_w.pre_limbs[B_CAP_ROOT],
        r0[STATE_BEFORE_BASE + state::CAP_ROOT],
        "differential: cap_root limb == v1 cap_root (before)"
    );
    // THE WITNESS-CARRIED LIMBS — the genuinely-new producer outputs (cells_root · the map
    // roots · lifecycle · epoch · committed_height · iroot) — are turn-invariant, so the
    // producer's values must equal what the generated trace carries in BOTH blocks.
    for (idx, label) in [
        (0usize, "cells_root"),
        (26, "nullifier_root"),
        (27, "heap_root"),
        (28, "lifecycle"),
        (29, "epoch"),
        (30, "committed_height"),
    ] {
        assert_eq!(
            after_w.pre_limbs[idx], last[AFTER_BASE + idx],
            "differential: producer {label} limb == trace after-block limb"
        );
        assert_eq!(
            before_w.pre_limbs[idx], r0[BEFORE_BASE + idx],
            "differential: producer {label} limb == trace before-block limb"
        );
    }
    assert_eq!(
        after_w.iroot,
        last[AFTER_BASE + B_IROOT],
        "differential: producer iroot == trace after-block iroot carrier"
    );

    // THE PRODUCER-COMMIT DIFFERENTIAL: the producer's independently-computed `wire_commit`
    // EQUALS the row-0 before-block STATE_COMMIT carrier the LIVE generator wrote.
    assert_eq!(
        before_w.state_commit,
        r0[BEFORE_BASE + B_STATE_COMMIT],
        "differential: producer wire_commit(before) == row-0 trace STATE_COMMIT carrier"
    );

    // -- (G3) THE LIVE cell≡circuit DIFFERENTIAL: the CELL's v9 rotated commitment EQUALS the
    //    circuit row-0 STATE_COMMIT. The cell computes `wireCommitR` over its OWN
    //    RecordKernelState + the turn context (cells_root · nullifier_root · iroot); the
    //    circuit carries the same object on its row-0 carrier. This is the binding the
    //    cutover doc deferred to the flip — now CLOSED, additively (v9, v8 untouched). --
    let v9_ctx = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        iroot: before_w.iroot,
    };
    let cell_v9 = compute_canonical_state_commitment_v9_felt(&before_cell, &v9_ctx);
    assert_eq!(
        cell_v9,
        r0[BEFORE_BASE + B_STATE_COMMIT],
        "G3 LIVE: cell v9 rotated commitment == circuit row-0 STATE_COMMIT"
    );
    // and the cell's v9 agrees with the producer's wire_commit (two independent paths to the
    // same rotated commitment object).
    assert_eq!(
        cell_v9, before_w.state_commit,
        "G3 LIVE: cell v9 == producer wire_commit"
    );

    // -- the four appended PIs were already read by the generator; pin them for clarity. --
    assert_eq!(dpis[34], r0[BEFORE_BASE + B_STATE_COMMIT], "PI 34 = rotated OLD commit");
    assert_eq!(dpis[35], last[AFTER_BASE + B_STATE_COMMIT], "PI 35 = rotated NEW commit");
    assert_eq!(dpis[36], last[AFTER_BASE + B_COMMITTED_HEIGHT], "PI 36 = committed height");
    assert_eq!(dpis[37], last[CAVEAT_BASE + C_SPAN - 1], "PI 37 = caveat commit");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // -- (1) PROVE + VERIFY the WHOLE rotated transfer end-to-end. --
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("rotated transfer must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("rotated transfer proof must verify independently");
    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "ROTATED TRANSFER (R=24, width {ROT_WIDTH}, LIVE-GENERATED): proof {total} B \
         (~{:.1} KiB) — PROVED + VERIFIED",
        total as f64 / 1024.0
    );

    // -- (3) ANTI-GHOST: tamper teeth bite on the rotated shape. --
    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };
    // tampered heap_root limb (before block, offset 27).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[BEFORE_BASE + 27] = row[BEFORE_BASE + 27] + BabyBear::ONE;
        }
        assert!(refused(&t, &dpis), "tampered heap_root limb must refuse");
    }
    // tampered iroot (after block).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[AFTER_BASE + B_IROOT] = row[AFTER_BASE + B_IROOT] + BabyBear::ONE;
        }
        assert!(refused(&t, &dpis), "tampered iroot must refuse");
    }
    // tampered heap-key caveat (entry 1, key offset within the manifest).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAVEAT_BASE + 8 + 2] = row[CAVEAT_BASE + 8 + 2] + BabyBear::ONE;
        }
        assert!(refused(&t, &dpis), "tampered heap caveat key must refuse");
    }
    // forged appended PI (rotated NEW commit).
    {
        let mut p = dpis.clone();
        p[35] = p[35] + BabyBear::new(123);
        assert!(refused(&trace, &p), "forged rotated NEW-commit PI must refuse");
    }

    eprintln!(
        "ROTATION FLIP GATE GREEN (LIVE): the rotated cohort (transfer) proves+verifies on a \
         real turn through the LIVE generator, the cell v9 ≡ circuit STATE_COMMIT differential \
         holds, and every anti-ghost tooth bites."
    );
}
