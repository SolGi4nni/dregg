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

#![cfg(feature = "prover")]

use dregg_cell::commitment::{V9RotationContext, compute_canonical_state_commitment_v9_felt};
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_COMMITTED_HEIGHT, B_IROOT, B_STATE_COMMIT, BEFORE_BASE, C_SPAN, CAVEAT_BASE,
    ROT_WIDTH, RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
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

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
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

/// PATH-PRESERVE §4 — a NON-SYNTHETIC producer cell: identical to [`producer_cell`] but with a
/// NON-ZERO `fields[field_idx]` (the shape the pre-Phase-3 synthetic-shape gate REFUSED). The
/// field flows into `pre_limbs[4 + field_idx] = fold_bytes32_to_bb(field)`
/// (`cell/src/commitment.rs:894`) and so into the rotated OLD/NEW `wireCommitR` — making the
/// differential's commitment agreement LOAD-BEARING (non-vacuous) for a field-bearing cell.
fn producer_cell_with_field(balance: i64, nonce: u64, field_idx: usize, field: [u8; 32]) -> Cell {
    let mut cell = producer_cell(balance, nonce);
    assert!(
        cell.state.set_field(field_idx, field),
        "set_field must take on a fresh cell"
    );
    cell
}

#[test]
fn rotated_transfer_proves_verifies_differential_and_refuses_ghost() {
    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");
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
            after_w.pre_limbs[idx],
            last[AFTER_BASE + idx],
            "differential: producer {label} limb == trace after-block limb"
        );
        assert_eq!(
            before_w.pre_limbs[idx],
            r0[BEFORE_BASE + idx],
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
    assert_eq!(
        dpis[34],
        r0[BEFORE_BASE + B_STATE_COMMIT],
        "PI 34 = rotated OLD commit"
    );
    assert_eq!(
        dpis[35],
        last[AFTER_BASE + B_STATE_COMMIT],
        "PI 35 = rotated NEW commit"
    );
    assert_eq!(
        dpis[36],
        last[AFTER_BASE + B_COMMITTED_HEIGHT],
        "PI 36 = committed height"
    );
    assert_eq!(
        dpis[37],
        last[CAVEAT_BASE + C_SPAN - 1],
        "PI 37 = caveat commit"
    );

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
        assert!(
            refused(&trace, &p),
            "forged rotated NEW-commit PI must refuse"
        );
    }

    eprintln!(
        "ROTATION FLIP GATE GREEN (LIVE): the rotated cohort (transfer) proves+verifies on a \
         real turn through the LIVE generator, the cell v9 ≡ circuit STATE_COMMIT differential \
         holds, and every anti-ghost tooth bites."
    );
}

/// G4 COHORT GENERALIZATION (end-to-end): a SECOND cohort effect — `Burn` — proves+verifies
/// through the SAME live generator + the cohort-general resolver
/// (`rotated_descriptor_name_for_effect` → `burnVmDescriptor2R24`), with the v9 authority-bearing
/// commitment differential holding. This proves the generator widening is not transfer-only: the
/// rotated machinery proves any cohort member's real turn, and the cell v9 commitment (now binding
/// FULL authority state via the r23 digest) equals the circuit's STATE_COMMIT for it too.
#[test]
fn rotated_burn_cohort_member_proves_verifies_with_authority_commitment() {
    // The cohort-general resolver picks the burn descriptor for a Burn effect.
    let burn_effect = Effect::Burn {
        target_hash: BabyBear::new(0),
        amount_lo: BabyBear::new(30),
        amount_full: 30,
    };
    let name =
        rotated_descriptor_name_for_effect(&burn_effect).expect("Burn is a rotated cohort member");
    assert_eq!(name, "burnVmDescriptor2R24");

    // Resolve its rotated descriptor from the committed registry.
    let json = V3_STAGED_REGISTRY_TSV
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
        .expect("burnVmDescriptor2R24 in registry");
    let desc = parse_vm_descriptor2(json).expect("burn descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(desc.public_input_count, 38);

    // A real burn turn: a 30-unit balance debit (no destination credit).
    let before_balance: i64 = 80_000;
    let amount: u64 = 30;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![burn_effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    // The burn carries no in-circuit caveat operand → the EMPTY manifest (cohort default).
    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &RotatedBlockWitness::new(before_w.pre_limbs.clone(), before_w.iroot).unwrap(),
        &RotatedBlockWitness::new(after_w.pre_limbs.clone(), after_w.iroot).unwrap(),
        &caveat,
    )
    .expect("live rotated generator must produce a burn trace");
    assert_eq!(trace[0].len(), ROT_WIDTH);

    // The cell v9 (now binding FULL authority state via r23) == the circuit STATE_COMMIT.
    let v9_ctx = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        iroot: before_w.iroot,
    };
    let cell_v9 = compute_canonical_state_commitment_v9_felt(&before_cell, &v9_ctx);
    assert_eq!(
        cell_v9,
        trace[0][BEFORE_BASE + B_STATE_COMMIT],
        "G4 burn: cell v9 (full-authority) == circuit row-0 STATE_COMMIT"
    );
    // r23 (the authority digest limb, pre_limbs index 24) is genuinely carried on the wire.
    assert_eq!(
        before_w.pre_limbs[24],
        trace[0][BEFORE_BASE + 24],
        "G4 burn: the r23 authority-digest limb rides the rotated trace"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("rotated burn must prove");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("rotated burn proof must verify");
    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "ROTATED BURN (cohort member, R=24, LIVE-GENERATED): proof {total} B (~{:.1} KiB) — \
         PROVED + VERIFIED; cell v9 full-authority differential holds",
        total as f64 / 1024.0
    );
}

/// THE C4 LAST-FLIP-GATE (end-to-end, in-circuit): a real ROTATED note-spend turn proves +
/// verifies through the `noteSpendVmDescriptor2R24` descriptor (the FIFTH appended PI pin,
/// `EffectVmEmitRotationV3.noteSpendV3`), the rotated PI vector is 39 elements with the spent
/// nullifier at PI[38] = the spend row's folded `param0`, AND the SOUNDNESS TOOTH bites: a turn
/// that publishes a DIFFERENT nullifier in PI[38] than the one the spend row carries (or tampers
/// the nullifier column) is UNSAT. This is the rotated re-statement of the v1 hand-AIR D5
/// cross-binding (`s_notespend·(param0 − PI[NOTESPEND_NULLIFIER])`, offset 198) — now a first-row
/// pin of the rotated descriptor, so a note-spending turn rotates and `verify_full_turn` step 8
/// reads PI[38]. With the in-circuit pin proven UNSAT under tamper, the off-AIR no-double-spend
/// cross-check binds THIS turn's nullifier (the node `spend_freshness_for_wrong_item_is_rejected`
/// drives the off-AIR half through the rotated leg).
#[test]
fn rotated_note_spend_pins_nullifier_and_refuses_tamper() {
    use dregg_circuit::effect_vm::columns::{PARAM_BASE, param};

    // The note-spend cohort member's rotated descriptor — 39 PIs (38 prefix + the nullifier pin).
    let spend = Effect::NoteSpend {
        nullifier: BabyBear::new(0xBEEF),
        value: 500,
    };
    let name = rotated_descriptor_name_for_effect(&spend).expect("NoteSpend is a cohort member");
    assert_eq!(name, "noteSpendVmDescriptor2R24");
    let json = V3_STAGED_REGISTRY_TSV
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
        .expect("noteSpendVmDescriptor2R24 in the staged registry");
    let desc = parse_vm_descriptor2(json).expect("rotated note-spend descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(
        desc.public_input_count, 39,
        "the rotated note-spend carries 38 prefix PIs + the appended nullifier slot"
    );

    // A real note-spend turn: the EffectVM credits balance by `value` (the shielding convention),
    // so before = balance, after = balance + value; nonce ticks by one.
    let before_balance: i64 = 90_000;
    let value: u64 = 500;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![spend];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[7u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a note-spend trace + 39 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "311-col rotated trace");

    // THE FIFTH PI: 39 elements, and PI[38] == the row-0 spend's folded nullifier (param0).
    assert_eq!(
        dpis.len(),
        39,
        "note-spend rotated PI is 39 (the nullifier slot appended)"
    );
    let r0 = &trace[0];
    assert_eq!(
        dpis[38],
        r0[PARAM_BASE + param::NULLIFIER],
        "PI 38 = the spend row's folded nullifier (param0)"
    );
    // The four commit pins are undisturbed below it.
    assert_eq!(
        dpis[34],
        r0[BEFORE_BASE + B_STATE_COMMIT],
        "PI 34 = rotated OLD commit"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // PROVE + VERIFY the whole rotated note-spend end-to-end.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("rotated note-spend must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("rotated note-spend proof must verify independently");
    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "ROTATED NOTE-SPEND (R=24, 39-PI, LIVE-GENERATED): proof {total} B (~{:.1} KiB) — \
         PROVED + VERIFIED; the nullifier is pinned at PI[38]",
        total as f64 / 1024.0
    );

    // -- THE SOUNDNESS TOOTH (anti-ghost): a published nullifier ≠ the spend row's param0 is
    //    UNSAT. This is the rotated boundary's analog of the v1 `rejects_swap` test. --
    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };
    // (a) publish a DIFFERENT nullifier in PI[38] than the spend row carries ("prove N, spend M").
    {
        let mut p = dpis.clone();
        p[38] = p[38] + BabyBear::ONE;
        assert!(
            refused(&trace, &p),
            "a published PI[38] differing from the spend row's nullifier MUST be UNSAT \
             (the no-double-spend pin)"
        );
    }
    // (b) tamper the nullifier COLUMN (param0) so it no longer matches the (honest) PI[38].
    {
        let mut t = trace.clone();
        t[0][PARAM_BASE + param::NULLIFIER] = t[0][PARAM_BASE + param::NULLIFIER] + BabyBear::ONE;
        assert!(
            refused(&t, &dpis),
            "tampering the spend row's nullifier column away from PI[38] MUST be UNSAT"
        );
    }
}

/// THE C7 LAST-FLIP-GATE (end-to-end, in-circuit): a real ROTATED `SetField` turn AND a real
/// ROTATED `BridgeMint` turn each prove + verify through their rotated descriptors
/// (`setFieldVmDescriptor2-{slot}R24` / `mintVmDescriptor2R24`), and the NONCE-TICK SOUNDNESS
/// TOOTH bites: a forged nonce delta (the after-nonce NOT equal to before-nonce + 1) is UNSAT.
///
/// The model found the bug (`docs/_RUST-LEAN-DIVERGENCE-LEDGER`): the runtime trace generator
/// TICKS the per-cell nonce on every non-NoOp row (`trace.rs` `Effect::SetField` / `BridgeMint`
/// → `new_state.nonce += 1`), and `fill_block` copies that ticked nonce into the rotated `r1`
/// weld — but the rotated SetField/BridgeMint descriptors used to assert nonce PASSTHROUGH, so a
/// real such turn was UNSAT on the rotated leg (the node fell back to v1). The fix (Lean
/// `EffectVmEmitRotationV3.{setFieldTickFace,mintTickFace}`) swaps the freeze gate for the
/// transfer/noteSpend TICK gate `(after_nonce − before_nonce) − (1 − selector)`, so the honest
/// ticked trace PROVES and a forged passthrough is UNSAT. With this, EVERY cohort effect rotates
/// and C7's `generate_effect_vm_trace` is fully unblocked.
#[test]
fn rotated_set_field_and_bridge_mint_tick_nonce_and_refuse_forged_delta() {
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // A reusable refuser closure over a descriptor.
    let refused = |desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
                   t: &Vec<Vec<BabyBear>>,
                   p: &Vec<BabyBear>|
     -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };

    // ===== (A) ROTATED SETFIELD (slot 0): tick nonce, prove+verify, refuse forged delta. =====
    {
        let set_field = Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(0xABCD),
        };
        let name = rotated_descriptor_name_for_effect(&set_field)
            .expect("SetField is a rotated cohort member");
        assert_eq!(name, "setFieldVmDescriptor2-0R24");
        let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
            .expect("rotated setField descriptor parses");
        assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
        assert_eq!(
            desc.public_input_count, 38,
            "setField is a 38-PI cohort member"
        );

        // A real setField turn: the field write ticks the nonce (before 5 → after 6); the
        // economic block is frozen. (The producer cell carries the pre-write fields; the
        // generator writes `fields[0] = value` and ticks the nonce on row 0.)
        let before_balance: i64 = 70_000;
        let st = CellState::new(before_balance as u64, 5);
        let effects = vec![set_field];

        let mut ledger = Ledger::new();
        let before_cell = producer_cell(before_balance, 5);
        let after_cell = producer_cell(before_balance, 6); // nonce TICKED 5 → 6
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[9u8; 32]];

        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

        let caveat = empty_caveat_manifest();
        let (trace, dpis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .expect("live rotated generator must produce a setField trace + 38 PIs");
        assert_eq!(trace[0].len(), ROT_WIDTH, "311-col rotated trace");

        // THE NONCE TICK (the runtime ground truth): the rotated r1 weld carries before+1.
        let r0 = &trace[0];
        assert_eq!(
            r0[STATE_AFTER_BASE + state::NONCE] - r0[STATE_BEFORE_BASE + state::NONCE],
            BabyBear::ONE,
            "setField row: after_nonce − before_nonce == 1 (the runtime tick)"
        );
        assert_eq!(
            r0[BEFORE_BASE + 2],
            r0[STATE_BEFORE_BASE + state::NONCE],
            "the rotated r1 weld carries the v1 before-nonce"
        );

        // The field write lands the value at param1 (NEW_VALUE), the column the corrected
        // descriptor reads; the written field equals it.
        assert_eq!(
            r0[76 + 3], // field[0]_after (saCol FIELD_BASE)
            r0[PARAM_BASE + 1],
            "setField row: field[0]_after == param1 (the runtime NEW_VALUE column)"
        );

        // PROVE + VERIFY end-to-end (this is exactly what used to be UNSAT before the fixes).
        let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
            .expect("rotated setField (ticked nonce) must prove end-to-end");
        verify_vm_descriptor2(&desc, &proof, &dpis)
            .expect("rotated setField proof must verify independently");
        eprintln!("ROTATED SETFIELD (R=24, ticked nonce, LIVE-GENERATED) — PROVED + VERIFIED");

        // SOUNDNESS TOOTH 1 (nonce): forge the after-nonce so the delta is NOT the tick. The tick
        // gate `(after − before) − (1 − s_noop)` reads the v1 after-nonce column; a forged
        // passthrough (after := before, delta 0 on a non-NoOp row) FAILS it → UNSAT.
        {
            let mut t = trace.clone();
            for row in t.iter_mut() {
                row[STATE_AFTER_BASE + state::NONCE] = row[STATE_BEFORE_BASE + state::NONCE];
            }
            assert!(
                refused(&desc, &t, &dpis),
                "a forged setField nonce passthrough (after == before, not the tick) MUST be UNSAT"
            );
        }
        // SOUNDNESS TOOTH 2 (value column): forge the written field so it no longer matches param1
        // (the runtime NEW_VALUE column the corrected write gate reads) → UNSAT.
        {
            let mut t = trace.clone();
            for row in t.iter_mut() {
                row[76 + 3] = row[76 + 3] + BabyBear::ONE; // bump field[0]_after off param1
            }
            assert!(
                refused(&desc, &t, &dpis),
                "a setField row whose written field ≠ param1 (the value column) MUST be UNSAT"
            );
        }
    }

    // ===== (B) ROTATED BRIDGEMINT: tick nonce, prove+verify, refuse forged delta. =====
    {
        let bridge_mint = Effect::BridgeMint {
            value_lo: BabyBear::new(30),
            mint_hash: BabyBear::new(0),
            value_full: 30,
        };
        let name = rotated_descriptor_name_for_effect(&bridge_mint)
            .expect("BridgeMint is a rotated cohort member");
        assert_eq!(name, "mintVmDescriptor2R24");
        let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
            .expect("rotated bridgeMint descriptor parses");
        assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
        assert_eq!(
            desc.public_input_count, 38,
            "bridgeMint is a 38-PI cohort member"
        );

        // A real bridge-mint turn: credit bal_lo by `value` (100 → 130), the nonce ticks 5 → 6.
        let before_balance: i64 = 100;
        let value: i64 = 30;
        let st = CellState::new(before_balance as u64, 5);
        let effects = vec![bridge_mint];

        let mut ledger = Ledger::new();
        let before_cell = producer_cell(before_balance, 5);
        let after_cell = producer_cell(before_balance + value, 6); // credit + nonce TICK
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];

        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

        let caveat = empty_caveat_manifest();
        let (trace, dpis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .expect("live rotated generator must produce a bridgeMint trace + 38 PIs");

        let r0 = &trace[0];
        assert_eq!(
            r0[STATE_AFTER_BASE + state::NONCE] - r0[STATE_BEFORE_BASE + state::NONCE],
            BabyBear::ONE,
            "bridgeMint row: after_nonce − before_nonce == 1 (the runtime tick)"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
            .expect("rotated bridgeMint (ticked nonce) must prove end-to-end");
        verify_vm_descriptor2(&desc, &proof, &dpis)
            .expect("rotated bridgeMint proof must verify independently");
        eprintln!("ROTATED BRIDGEMINT (R=24, ticked nonce, LIVE-GENERATED) — PROVED + VERIFIED");

        // SOUNDNESS TOOTH 1 (nonce): forged nonce passthrough is UNSAT.
        {
            let mut t = trace.clone();
            for row in t.iter_mut() {
                row[STATE_AFTER_BASE + state::NONCE] = row[STATE_BEFORE_BASE + state::NONCE];
            }
            assert!(
                refused(&desc, &t, &dpis),
                "a forged bridgeMint nonce passthrough (after == before) MUST be UNSAT"
            );
        }
        // SOUNDNESS TOOTH 2 (credit column): forge the after-balance so it is NOT before + param1
        // (the runtime value_lo column the corrected credit gate reads) → UNSAT.
        {
            let mut t = trace.clone();
            for row in t.iter_mut() {
                row[76 + state::BALANCE_LO] = row[76 + state::BALANCE_LO] + BabyBear::ONE;
            }
            assert!(
                refused(&desc, &t, &dpis),
                "a bridgeMint row whose post-balance ≠ before + param1 (the credit) MUST be UNSAT"
            );
        }
    }

    eprintln!(
        "C7 NONCE-TICK GATE GREEN (LIVE): rotated SetField + BridgeMint prove+verify on real \
         ticked turns through the LIVE generator, and a forged nonce delta is UNSAT — every \
         cohort effect now rotates."
    );
}

/// THE ROTATED WIRE-COMMIT ↔ LEAN DIFFERENTIAL (the ACTUALLY-PUBLISHED commitment).
///
/// The Lean module `Dregg2.Circuit.RotatedCommitDifferential` pins the PUBLISHED rotated
/// commitment (the `OLD_COMMIT`/`NEW_COMMIT` the light client verifies) as
/// `wireCommitR(rotatedLimbs, iroot)` over the 31 pre-iroot limbs in the order
///   `[cells_root, r0..r23, cap_root, nullifier_root, heap_root, lifecycle, epoch, committed_height]`
/// with the authority residue (`compute_authority_digest_felt`) NAMED at index 24 (register r23),
/// and proves `rotatedCommit_binds_authority_digest`: tampering the authority residue MOVES the
/// published commitment.
///
/// This test is the Rust empirical twin in the SAME two forms the per-cell differential
/// (`effect_vm_commit_lean_differential.rs`) carries:
///
///   (a) THE INDEPENDENT RE-FOLD: an `independent_wire_commit` written here, byte-for-byte the
///       Lean `wireCommitR` chained absorption (4-wide head, 3-wide chip body while ≥ 3 pre-iroot
///       limbs remain, the iroot ALONE last), folded over the SAME limb order the real
///       `compute_rotated_pre_limbs` produces, EQUALS the deployed
///       `compute_canonical_state_commitment_v9_felt` (the actually-published value). The shape
///       MATCHES — no reorder, no dropped limb, no extra limb.
///
///   (b) THE P0-2 NON-VACUITY ON THE PUBLISHED COMMITMENT: a permission flip
///       (`send: None -> Impossible`) — authority state that lives ONLY in the r23 authority digest,
///       no named limb — MOVES the published rotated commitment. Two cells differing ONLY in a
///       permission PUBLISH different `OLD_COMMIT`s, so the light client cannot be shown a
///       wide-open cell as a locked-down one. (The pre-existing differential moved the per-cell
///       `compute_commitment`; THIS moves the rotated `wire_commit` the light client actually pins.)
#[test]
fn rotated_published_commit_lean_differential_and_permission_flip_moves_it() {
    use dregg_cell::commitment::{
        V9_NUM_PRE_LIMBS, compute_authority_digest_felt, compute_rotated_pre_limbs,
    };
    use dregg_circuit::poseidon2::hash_many;

    // An independent re-fold of the rotated wire-commit, written to match the Lean
    // `EffectVmEmitRotationR.wireCommitR` chained absorption EXACTLY (and the deployed
    // `cell::commitment::v9_wire_commit`): 4-wide head, 3-wide groups while ≥ 3 remain, the iroot
    // ALONE last. Independent of the deployed `v9_wire_commit` (re-derived here from the public
    // `hash_many` primitive + the pre-limb vector), so agreement is a genuine differential.
    fn independent_wire_commit(pre_limbs: &[BabyBear], iroot: BabyBear) -> BabyBear {
        assert_eq!(pre_limbs.len(), V9_NUM_PRE_LIMBS, "31 pre-iroot limbs at R=24");
        // 4-wide head over the first four limbs (cells_root, r0, r1, r2).
        let mut d = hash_many(&[pre_limbs[0], pre_limbs[1], pre_limbs[2], pre_limbs[3]]);
        let mut col = 4;
        while col < V9_NUM_PRE_LIMBS {
            let remaining = V9_NUM_PRE_LIMBS - col;
            if remaining >= 3 {
                d = hash_many(&[d, pre_limbs[col], pre_limbs[col + 1], pre_limbs[col + 2]]);
                col += 3;
            } else {
                d = hash_many(&[d, pre_limbs[col]]);
                col += 1;
            }
        }
        // the iroot rides its OWN arity-2 final site, LITERALLY last.
        hash_many(&[d, iroot])
    }

    // A residue-free baseline cell (default permissions / no VK) and a turn context.
    let plain = producer_cell(100_000, 0);
    let nullifier_root = [0u8; 32];
    let iroot = BabyBear::new(0x1234);
    let cells_root = BabyBear::new(0x5678);
    let ctx = V9RotationContext {
        cells_root,
        nullifier_root,
        iroot,
    };

    // -- (a) THE INDEPENDENT RE-FOLD == the deployed PUBLISHED commitment. --
    // The deployed pre-limb vector (the Lean `rotatedLimbs` order) and the deployed published felt.
    let pre = compute_rotated_pre_limbs(&plain, &ctx);
    assert_eq!(pre.len(), V9_NUM_PRE_LIMBS, "31 limbs");
    // The authority residue sits at index 24 (register r23) — the Lean `authority_digest_at_index_24`.
    assert_eq!(
        pre[24],
        compute_authority_digest_felt(&plain),
        "the rotated limb at index 24 IS compute_authority_digest_felt (the Lean r23 pin)"
    );
    let published = compute_canonical_state_commitment_v9_felt(&plain, &ctx);
    let refold = independent_wire_commit(&pre, iroot);
    assert_eq!(
        published, refold,
        "the deployed PUBLISHED rotated commitment == an independent re-fold over the Lean \
         rotatedLimbs order (wireCommitR shape MATCHES — no reorder / drop / extra limb)"
    );

    // -- (b) P0-2 NON-VACUITY on the PUBLISHED commitment: a permission flip MOVES it. --
    // The flip touches authority state that lives ONLY in the r23 authority digest (no named limb).
    let mut locked = producer_cell(100_000, 0);
    locked.permissions.send = AuthRequired::Impossible;

    // First, the authority residue felt itself moves (the limb is genuinely load-bearing).
    assert_ne!(
        compute_authority_digest_felt(&plain),
        compute_authority_digest_felt(&locked),
        "a permission change MOVES compute_authority_digest_felt — the r23 residue is genuinely \
         bound, not a constant stub"
    );

    // The pre-limb vectors differ ONLY at index 24 (the authority digest) — every OTHER named limb
    // (cells_root, balance/nonce/fields, cap_root, nullifier/heap roots, lifecycle/epoch/height) is
    // identical, since only `permissions.send` changed.
    let pre_locked = compute_rotated_pre_limbs(&locked, &ctx);
    for i in 0..V9_NUM_PRE_LIMBS {
        if i == 24 {
            assert_ne!(pre[i], pre_locked[i], "index 24 (authority digest) MUST move");
        } else {
            assert_eq!(
                pre[i], pre_locked[i],
                "limb {i} (a NAMED non-authority limb) must be unchanged by a permission flip"
            );
        }
    }

    // THE HEADLINE: the PUBLISHED rotated commitment (what the light client pins) MOVES.
    let published_locked = compute_canonical_state_commitment_v9_felt(&locked, &ctx);
    assert_ne!(
        published, published_locked,
        "P0-2 on the ACTUALLY-PUBLISHED commitment: a permission flip MOVES the rotated \
         OLD/NEW_COMMIT the light client verifies — a wide-open cell cannot be presented as a \
         locked-down one"
    );
    // The independent re-fold tracks the move too (the differential holds on the flipped cell).
    assert_eq!(
        published_locked,
        independent_wire_commit(&pre_locked, iroot),
        "the independent re-fold == the deployed published commitment on the flipped cell too"
    );

    eprintln!(
        "ROTATED WIRE-COMMIT LEAN DIFFERENTIAL GREEN: the PUBLISHED rotated commitment == an \
         independent re-fold over the Lean rotatedLimbs order, and a permission flip MOVES the \
         published OLD/NEW_COMMIT (P0-2 non-vacuity on the commitment the light client pins)."
    );
}

/// PATH-PRESERVE §4 / §6.1 — THE NON-SYNTHETIC-CELL DIFFERENTIAL (Phase 0, the §4-premise check).
///
/// The other differential tests in this file run a real public-key cell but with ZERO fields. §4's
/// lift drops the "pristine / zero-fields" gate so a FIELD-BEARING cell rotates — its premise is
/// that the rotated OLD/NEW `wireCommitR` commitments still agree between the CELL (`v9`) and the
/// CIRCUIT (the LIVE generator's row-0 / last-row `STATE_COMMIT` carrier) *regardless of the
/// non-zero field*, because the field is folded the SAME way on both sides
/// (`fold_bytes32_to_bb(&cell.state.fields[i]) == st.fields[i]`, then absorbed by `wireCommitR`).
/// This test establishes that fact EMPIRICALLY before the live cutover (Phase 4) relies on it.
///
/// It proves a single-run rotated transfer over a cell whose `fields[0]` is NON-ZERO (`0x07…`),
/// seeding the circuit `CellState.fields[0]` to the SAME folded felt so the v1-welded state block
/// and the cell's v9 commitment are consistent (the §4 seed obligation: `initial_vm_state` must
/// carry the real cell's `fields[0..8]`). It asserts:
///   - the field felt is genuinely NON-ZERO and equals the trace's before-block FIELD[0] carrier
///     (the load-bearing, NON-VACUOUS distinction from the zero-field tests);
///   - cell-v9(before) == circuit row-0 `STATE_COMMIT` == PI[34] (OLD_COMMIT agreement on a
///     field-bearing cell — the §4.2 premise);
///   - cell-v9(after) == circuit last-row `STATE_COMMIT` == PI[35] (NEW_COMMIT agreement);
///   - the whole rotated transfer PROVES + VERIFIES end-to-end on the field-bearing cell.
///
/// If OLD_COMMIT DISagreed here, §4's premise would be wrong and Phase 3 (already landed) would be
/// unsound — so this is a regression tooth for the lift, not just coverage.
#[test]
fn rotated_non_synthetic_field_bearing_cell_old_new_commit_agree() {
    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");

    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    // The non-zero field carried by the cell (and, to keep the v1-welded state block consistent
    // with the cell, by the circuit `CellState` the generator opens over).
    let field0_bytes = [0x07u8; 32];
    let field0_felt = fold_bytes32_to_bb(&field0_bytes);
    assert_ne!(
        field0_felt,
        BabyBear::ZERO,
        "the test field must fold to a NON-ZERO felt or the differential is vacuous"
    );

    // The circuit pre-state seeded with the SAME field[0] the cell carries (PATH-PRESERVE §4.1: the
    // prover seeds `initial_vm_state` from the real cell, NOT a zero-field `CellState::new`).
    let mut st = CellState::new(before_balance as u64, 0);
    st.fields[0] = field0_felt;
    st.refresh_commitment();
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];

    // The REAL field-bearing before/after producer cells. The transfer TICKS the nonce in-circuit
    // (`generate_effect_vm_trace` does `new_state.nonce += 1` on every effect row, `trace.rs:541`),
    // so the real after-cell carries nonce = pre_nonce + 1 = 1 — the after-cell must match the
    // circuit's ticked after-state for the v9(after) ≡ last-row STATE_COMMIT differential to hold
    // (the field is unchanged by a transfer, so it persists; only balance + nonce move).
    let mut ledger = Ledger::new();
    let before_cell = producer_cell_with_field(before_balance, 0, 0, field0_bytes);
    let after_cell = producer_cell_with_field(before_balance - amount as i64, 1, 0, field0_bytes);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce the field-bearing trace + 38 PIs");
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];

    // (a) THE FIELD IS LOAD-BEARING: the cell's non-zero field[0] is folded into the producer limb
    //     AND welded into the trace's before-block FIELD[0] carrier — both NON-ZERO and equal.
    assert_eq!(
        before_w.pre_limbs[4], field0_felt,
        "the producer must fold the real cell's field[0] into pre_limbs[4]"
    );
    assert_eq!(
        r0[STATE_BEFORE_BASE + state::FIELD_BASE],
        field0_felt,
        "the v1-welded before-block FIELD[0] must equal the seeded field felt (the §4 seed \
         obligation — initial_vm_state carries the real field)"
    );
    assert_ne!(
        r0[STATE_BEFORE_BASE + state::FIELD_BASE],
        BabyBear::ZERO,
        "the differential is NON-VACUOUS: the welded field[0] is genuinely non-zero"
    );

    // (b) OLD_COMMIT AGREEMENT (§4.2) on the field-bearing cell: cell-v9(before) == circuit row-0
    //     STATE_COMMIT == PI[34]. The non-zero field is absorbed by `wireCommitR` identically on
    //     both sides, so the agreement holds despite the field — the whole point of the lift.
    let v9_ctx_before = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        iroot: before_w.iroot,
    };
    let cell_v9_before = compute_canonical_state_commitment_v9_felt(&before_cell, &v9_ctx_before);
    assert_eq!(
        cell_v9_before,
        r0[BEFORE_BASE + B_STATE_COMMIT],
        "§4.2: field-bearing cell v9(before) == circuit row-0 STATE_COMMIT (OLD_COMMIT agree)"
    );
    assert_eq!(
        dpis[34],
        r0[BEFORE_BASE + B_STATE_COMMIT],
        "PI[34] (rotated OLD_COMMIT) == row-0 STATE_COMMIT on the field-bearing cell"
    );
    assert_eq!(
        cell_v9_before, before_w.state_commit,
        "field-bearing cell v9(before) == producer wire_commit(before)"
    );

    // (c) NEW_COMMIT AGREEMENT on the field-bearing after-cell: cell-v9(after) == circuit last-row
    //     STATE_COMMIT == PI[35]. (The after-cell's turn-invariant limbs ride the after-block; the
    //     welds carry the debited balance — the field is unchanged by a transfer, so it persists.)
    let v9_ctx_after = V9RotationContext {
        cells_root: after_w.pre_limbs[0],
        nullifier_root,
        iroot: after_w.iroot,
    };
    let cell_v9_after = compute_canonical_state_commitment_v9_felt(&after_cell, &v9_ctx_after);
    assert_eq!(
        cell_v9_after,
        last[AFTER_BASE + B_STATE_COMMIT],
        "§4.2: field-bearing cell v9(after) == circuit last-row STATE_COMMIT (NEW_COMMIT agree)"
    );
    assert_eq!(
        dpis[35],
        last[AFTER_BASE + B_STATE_COMMIT],
        "PI[35] (rotated NEW_COMMIT) == last-row STATE_COMMIT on the field-bearing cell"
    );

    // (d) THE WHOLE FIELD-BEARING ROTATED TRANSFER PROVES + VERIFIES end-to-end.
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("field-bearing rotated transfer must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("field-bearing rotated transfer proof must verify independently");

    eprintln!(
        "PATH-PRESERVE §4 DIFFERENTIAL GREEN: a FIELD-BEARING (non-synthetic) cell's rotated \
         OLD/NEW commitments agree cell-v9 ≡ circuit STATE_COMMIT ≡ PI[34/35], the non-zero field \
         is load-bearing, and the proof verifies — the lift's premise holds empirically."
    );
}

/// THE DEPLOYMENT-SOUNDNESS CLOSE (the record-forcing pin, end-to-end in-circuit): a real
/// ROTATED `CellSeal` turn proves + verifies through the `cellSealVmDescriptor2R24` descriptor
/// (the FIFTH appended PI pin, `EffectVmEmitRotationV3.cellSealV3` /
/// `rotateV3WithRecordPin B_LIFECYCLE`), the rotated PI vector is 39 elements with the
/// CORRECTLY-WRITTEN post lifecycle felt at PI[38] = the AFTER block's lifecycle limb (col
/// `AFTER_BASE + B_LIFECYCLE` = 258), AND the SOUNDNESS TOOTH bites: a trace that FREEZES the
/// lifecycle (AFTER limb still the PRE/Live value) while claiming the sealed PI[38] is UNSAT.
///
/// This is the gap the `RotatedKernelRefinementCellSeal` rung proved against a FIX descriptor
/// (`gLifecycleSeal` / `cellSeal_descriptorRefines_rejects_unsealed`), now BITING in the LIVE
/// deployed rotated descriptor. Before this pin the rotated cellSeal merely FROZE the economic
/// block + ticked the nonce; the lifecycle flip was OFF-ROW (`cellSeal_offrow_unenforced`), so a
/// prover could publish a commitment to an UN-SEALED post and the descriptor accepted — the
/// forgery the light client could not detect. The pin forces the committed lifecycle limb.
#[test]
fn rotated_cellseal_record_pin_forces_lifecycle_and_rejects_frozen_forgery() {
    use dregg_circuit::effect_vm::trace_rotated::B_LIFECYCLE;

    let seal_effect = Effect::CellSeal {
        target: [BabyBear::new(0); 8],
        reason_hash: [BabyBear::new(9); 8],
    };
    let name = rotated_descriptor_name_for_effect(&seal_effect)
        .expect("CellSeal is a rotated cohort member");
    assert_eq!(name, "cellSealVmDescriptor2R24");

    let json = rotated_descriptor_json(name);
    let desc = parse_vm_descriptor2(json).expect("rotated cellSeal descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(
        desc.public_input_count, 39,
        "cellSeal carries the appended record-forcing pin (39 PIs)"
    );

    // A real cellSeal turn: lifecycle Live -> Sealed, economic block frozen, nonce ticks.
    let balance: i64 = 50_000;
    let st = CellState::new(balance as u64, 0);
    let effects = vec![seal_effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(balance, 0);
    let mut after_cell = producer_cell(balance, 1); // nonce ticks
    after_cell
        .seal([9u8; 32], 0)
        .expect("Live cell must seal");
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    // The lifecycle limb genuinely MOVED Live -> Sealed (the forgery the pin forbids would freeze it).
    assert_ne!(
        before_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the producer witnesses a DISTINCT lifecycle felt for the sealed post (anti-omission)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a cellSeal trace + 39 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "311-col rotated trace");

    // THE FIFTH PI: 39 elements, and PI[38] == the LAST row's AFTER lifecycle limb (the
    // correctly-written sealed post the verifier recomputes), the column the pin binds.
    assert_eq!(dpis.len(), 39, "cellSeal rotated PI is 39 (the record-forcing slot appended)");
    let last = &trace[trace.len() - 1];
    assert_eq!(
        dpis[38],
        last[AFTER_BASE + B_LIFECYCLE],
        "PI 38 = the AFTER block's correctly-written (sealed) lifecycle limb"
    );
    assert_eq!(
        dpis[38], after_w.pre_limbs[B_LIFECYCLE],
        "PI 38 = lifecycle_felt(Sealed) from the post-state producer witness"
    );
    // The four commit pins are undisturbed below it.
    assert_eq!(dpis[34], trace[0][BEFORE_BASE + B_STATE_COMMIT], "PI 34 = rotated OLD commit");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // PROVE + VERIFY the honest sealed turn end-to-end.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("honest rotated cellSeal must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("honest rotated cellSeal proof must verify independently");

    // -- THE SOUNDNESS TOOTH (anti-ghost): the FROZEN-lifecycle forgery is UNSAT. --
    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };
    // (a) publish a DIFFERENT post in PI[38] than the AFTER block carries.
    {
        let mut p = dpis.clone();
        p[38] = p[38] + BabyBear::ONE;
        assert!(
            refused(&trace, &p),
            "a published PI[38] differing from the AFTER lifecycle limb MUST be UNSAT (the record pin)"
        );
    }
    // (b) THE CENTRAL FORGERY: FREEZE the AFTER lifecycle limb to the PRE (Live) value — the
    //     un-sealed post the deployed circuit USED to accept — while PI[38] stays the honest
    //     sealed felt. The pin (last.loc(258) == PI[38]) now bites: this is UNSAT.
    {
        let mut t = trace.clone();
        let last_row = t.len() - 1;
        t[last_row][AFTER_BASE + B_LIFECYCLE] = before_w.pre_limbs[B_LIFECYCLE]; // frozen Live
        assert!(
            refused(&t, &dpis),
            "FREEZING the AFTER lifecycle limb (un-sealed post) while claiming the sealed PI[38] \
             MUST be UNSAT — the deployment-soundness gap is closed (the forgery the light client \
             could not previously detect is now rejected in the LIVE descriptor)"
        );
    }

    eprintln!(
        "ROTATED CELLSEAL RECORD-PIN (R=24, 39-PI, LIVE-GENERATED): PROVED + VERIFIED; the \
         committed lifecycle limb is FORCED at PI[38], and a FROZEN-lifecycle forgery is UNSAT — \
         the binds-but-unforced deployment gap is closed for cellSeal."
    );
}

/// THE DEPLOYMENT-SOUNDNESS CLOSE for the field-NOT-bound AUDIT WRITES — `refusal` and
/// `receiptArchive`. Before this, these two effects wrote a cell audit slot (`"refusal"` /
/// `"lifecycle"` RECORD slots, `Spec.CellStateAudit.{RefusalSpec,ReceiptArchiveSpec}`) that the
/// deployed rotated commitment carried but the rotated descriptor did NOT FORCE: a prover could
/// publish a commitment to a post that CLAIMS a refusal / archive that did not happen, and the
/// descriptor accepted (`v3Of` had no record pin). The audit slot is a NAMED record field that
/// lands in the deployed cell's `fields_root` (the named-field map), which
/// `compute_authority_digest_felt` FOLDS into the r23 authority residue (`B_RECORD_DIGEST` = limb
/// 24). So a genuine audit write MOVES the AFTER `record_digest` limb; the record-forcing pin
/// (`EffectVmEmitRotationV3.{refusalV3,receiptArchiveV3}`, `rotateV3WithRecordPin B_RECORD_DIGEST`)
/// welds it to PI[38]. A FROZEN-audit-slot AFTER block (the forged refusal / archive) carries the
/// unchanged record digest, FAILS the pin, and is UNSAT — the gap closed for the LIVE descriptor.
#[test]
fn rotated_audit_record_pin_forces_record_digest_and_rejects_frozen_forgery() {
    use dregg_circuit::effect_vm::trace_rotated::B_RECORD_DIGEST;

    // An out-of-`fields[0..16]` audit key: writing it via `set_field_ext` lands in the cell's
    // `fields_root` (the named-field map), exactly where the `"refusal"` / `"lifecycle"` audit
    // slots live — so the after cell's authority digest (r23) genuinely moves. (Both slots use the
    // SAME `B_RECORD_DIGEST` limb; this audit key stands for either named slot.)
    const AUDIT_KEY: u64 = 4096;

    // The two audit effects, each routed to `B_RECORD_DIGEST` by `record_pin_offset`.
    let refusal = Effect::Refusal {
        target: [BabyBear::new(0); 8],
        reason_hash: [BabyBear::new(5); 8],
    };
    let archive = Effect::ReceiptArchive {
        target: [BabyBear::new(0); 8],
        archive_end_height: BabyBear::new(7),
        terminal_receipt_hash: [BabyBear::new(11); 8],
    };

    for (effect, expect_name) in [
        (refusal, "refusalVmDescriptor2R24"),
        (archive, "receiptArchiveVmDescriptor2R24"),
    ] {
        let name = rotated_descriptor_name_for_effect(&effect)
            .expect("audit effect is a rotated cohort member");
        assert_eq!(name, expect_name);

        let json = rotated_descriptor_json(name);
        let desc = parse_vm_descriptor2(json).expect("rotated audit descriptor parses");
        assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
        assert_eq!(
            desc.public_input_count, 39,
            "{name} carries the appended record-forcing pin (39 PIs)"
        );

        // A real audit turn: the audit slot is written (record_digest moves), nonce ticks, the
        // economic block is otherwise frozen.
        let balance: i64 = 50_000;
        let st = CellState::new(balance as u64, 0);
        let effects = vec![effect];

        let mut ledger = Ledger::new();
        let before_cell = producer_cell(balance, 0);
        let mut after_cell = producer_cell(balance, 1); // nonce ticks
        // The audit write: the named record slot flips to 1 (the audit commitment). This moves
        // `fields_root` and therefore `compute_authority_digest_felt` (the r23 limb).
        let mut one = [0u8; 32];
        one[0] = 1;
        assert!(
            after_cell.state.set_field_ext(AUDIT_KEY, one),
            "the audit-slot write must take"
        );
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

        // The record-digest limb genuinely MOVED (the forgery the pin forbids would freeze it):
        // the authority residue folds `fields_root`, which the audit write changed.
        assert_ne!(
            before_w.pre_limbs[B_RECORD_DIGEST], after_w.pre_limbs[B_RECORD_DIGEST],
            "{name}: the producer witnesses a DISTINCT record digest for the audit post \
             (the audit slot is bound by r23 — anti-omission)"
        );

        let caveat = empty_caveat_manifest();
        let (trace, dpis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .unwrap_or_else(|e| panic!("live rotated generator must produce a {name} trace + 39 PIs: {e}"));
        assert_eq!(trace[0].len(), ROT_WIDTH, "311-col rotated trace");

        // THE FIFTH PI: 39 elements, and PI[38] == the LAST row's AFTER record-digest limb.
        assert_eq!(dpis.len(), 39, "{name} rotated PI is 39 (the record-forcing slot appended)");
        let last = &trace[trace.len() - 1];
        assert_eq!(
            dpis[38],
            last[AFTER_BASE + B_RECORD_DIGEST],
            "PI 38 = the AFTER block's correctly-written (audit) record-digest limb"
        );
        assert_eq!(
            dpis[38], after_w.pre_limbs[B_RECORD_DIGEST],
            "PI 38 = compute_authority_digest_felt(post) from the post-state producer witness"
        );
        assert_eq!(dpis[34], trace[0][BEFORE_BASE + B_STATE_COMMIT], "PI 34 = rotated OLD commit");

        let mem_boundary = MemBoundaryWitness::default();
        let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

        // PROVE + VERIFY the honest audit turn end-to-end.
        let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
            .unwrap_or_else(|e| panic!("honest rotated {name} must prove end-to-end: {e}"));
        verify_vm_descriptor2(&desc, &proof, &dpis)
            .unwrap_or_else(|e| panic!("honest rotated {name} proof must verify: {e}"));

        // -- THE SOUNDNESS TOOTH (anti-ghost): the FROZEN-audit-slot forgery is UNSAT. --
        let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
            }));
            match r {
                Err(_) => true,
                Ok(res) => res.is_err(),
            }
        };
        // (a) publish a DIFFERENT post in PI[38] than the AFTER block carries.
        {
            let mut p = dpis.clone();
            p[38] = p[38] + BabyBear::ONE;
            assert!(
                refused(&trace, &p),
                "{name}: a published PI[38] differing from the AFTER record-digest limb MUST be \
                 UNSAT (the record pin)"
            );
        }
        // (b) THE CENTRAL FORGERY: FREEZE the AFTER record-digest limb to the PRE value — the
        //     audit-slot-NOT-written post the deployed circuit USED to accept (claiming a refusal /
        //     archive that did not happen) — while PI[38] stays the honest written felt. UNSAT.
        {
            let mut t = trace.clone();
            let last_row = t.len() - 1;
            t[last_row][AFTER_BASE + B_RECORD_DIGEST] = before_w.pre_limbs[B_RECORD_DIGEST]; // frozen
            assert!(
                refused(&t, &dpis),
                "{name}: FREEZING the AFTER record-digest limb (audit-slot-NOT-written post) while \
                 claiming the written PI[38] MUST be UNSAT — the forged refusal / archive a prover \
                 could previously publish (the commitment did not even bind the audit write) is now \
                 rejected in the LIVE deployed descriptor"
            );
        }

        eprintln!(
            "ROTATED AUDIT RECORD-PIN ({name}, R=24, 39-PI, LIVE-GENERATED): PROVED + VERIFIED; \
             the committed record-digest limb (r23, folding the audit slot via fields_root) is \
             FORCED at PI[38], and a FROZEN-audit-slot forgery is UNSAT — the field-NOT-bound \
             deployment gap is closed."
        );
    }
}

/// THE KERNEL-SET DEPLOYMENT-SOUNDNESS GAP, demonstrated as a LIVE-DESCRIPTOR ADMISSIBILITY witness
/// (the prompt's HONESTY bar — report the gap precisely, do NOT fake a binding).
///
/// ## What this proves (and what it deliberately does NOT)
///
/// The kernel-set effects (`createCell` / `createCellFromFactory` / `spawn` insert into the
/// `accounts` cell-table set; `noteCreate` inserts into the `commitments` set; `noteSpend` inserts
/// into the `nullifiers` set) mutate KERNEL-LEVEL sets, not per-cell state. The deployed rotated
/// commitment (`wireCommitR` over the 31 pre-iroot limbs) DOES absorb a turn-level `cells_root`
/// (`pre_limbs[0]`) and a `nullifier_root` (`pre_limbs[26]`) — but those limbs are TURN-INVARIANT
/// WITNESS limbs: `fill_block` (`trace_rotated.rs`) copies them verbatim and OVERRIDES only the
/// welded per-cell registers (r0..r10, cap_root) from the v1 state block. NO per-effect gate forces
/// `after.cells_root = insert(newCell, before.cells_root)` or `after.nullifier_root =
/// grow(before.nullifier_root)`. And there is NO `accounts_root` limb and NO `commitments_root` limb
/// in the deployed shape AT ALL.
///
/// This test makes that gap CONCRETE: it proves a real `noteCreate` rotated turn through the LIVE
/// `noteCreateVmDescriptor2R24` descriptor where the kernel-set witness is FROZEN — the before and
/// after blocks carry IDENTICAL `cells_root` / `nullifier_root` limbs (no growth), exactly as the
/// live full-turn path mints them (`produce` reads ONE ledger for both blocks). The live descriptor
/// VERIFIES it. Then it shows the descriptor STILL verifies after the `cells_root` / `nullifier_root`
/// limbs are tampered in LOCKSTEP across both blocks (a value the kernel never grew): because no gate
/// reads these limbs, only `wireCommitR` absorbs them, a self-consistent re-fill proves and verifies.
///
/// The honest reading: the deployed EffectVM apex binds these set-roots into the commitment but does
/// NOT FORCE the set-insert. The Lean `RotatedKernelRefinementBirth` (`accountsRoot` / `gAccountsGrow`)
/// and `RotatedKernelRefinementNotes` (`nullifiersRoot` / `commitmentsRoot` / `gNoteGrow`) rungs prove
/// soundness against a MODELED committed set-root limb + gate that the DEPLOYED circuit does not yet
/// carry (their own headers say "The Rust realization: `compute_commitment` absorbs an `accounts_root`
/// limb" — future tense; grep confirms no such limb exists). Closing the gap deployment-real requires
/// the flag-day NEW-limb addition (extend NUM_PRE_LIMBS 31→, re-balance `wireCommitR`, add a NOVEL
/// turn-level grow-gate kind the per-cell per-row descriptor cannot currently express, re-emit ALL
/// descriptor goldens, and rotate the VK). This test STANDS as the precise, undeniable record of the
/// residual until that flag-day lands.
#[test]
fn kernel_set_insert_is_not_forced_by_the_live_descriptor() {
    // The note-create cohort member's rotated descriptor (the `commitments`-set growth effect).
    let cm = BabyBear::new(0xC0FFEE);
    let create = Effect::NoteCreate {
        commitment: cm,
        value: 250,
    };
    let name =
        rotated_descriptor_name_for_effect(&create).expect("NoteCreate is a rotated cohort member");
    assert_eq!(name, "noteCreateVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated note-create descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");

    // A real note-create turn (EffectVM credits balance by `value`, the shielding convention).
    let before_balance: i64 = 60_000;
    let value: u64 = 250;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![create];

    // -- THE FROZEN-SET WITNESS: exactly how the live full-turn path mints it. `produce` reads ONE
    //    ledger for BOTH the before and after blocks (sdk/src/full_turn_proof.rs:2650-2651,
    //    3572-3573), so `cells_root` (pre_limbs[0]) and `nullifier_root` (pre_limbs[26]) are
    //    IDENTICAL before vs after — the kernel-set insert leaves NO delta on any limb. There is no
    //    `commitments_root` limb for the note-commitment insert to touch at all. --
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    // The set-limbs are turn-invariant: before-block and after-block carry the SAME value (no
    // representable delta). This is the structural shape of the gap.
    assert_eq!(
        before_w.pre_limbs[0], after_w.pre_limbs[0],
        "cells_root is turn-invariant — the live producer carries NO accounts/cell-set delta"
    );
    assert_eq!(
        before_w.pre_limbs[26], after_w.pre_limbs[26],
        "nullifier_root is turn-invariant — the live producer carries NO note-set delta"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a note-create trace");
    assert_eq!(trace[0].len(), ROT_WIDTH, "311-col rotated trace");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // -- (1) THE GAP: the live deployed descriptor PROVES + VERIFIES a note-create turn whose
    //    committed kernel-set witness was NOT grown (frozen `cells_root` / `nullifier_root`, no
    //    `commitments_root` limb). A circuit that FORCED the set-insert would have rejected this. --
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("note-create proves on a FROZEN kernel-set witness — the gap");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("note-create VERIFIES on a FROZEN kernel-set witness — the live descriptor does \
                 NOT force the set-insert");

    // -- (2) THE LIMBS ARE UNGATED: lockstep-tamper `cells_root` (limb 0) and `nullifier_root`
    //    (limb 26) to values the kernel never produced, re-fill the dependent `wireCommitR` chain +
    //    STATE_COMMIT consistently, and re-derive the appended commit PIs. If ANY per-effect gate
    //    read these limbs, the re-filled trace would be UNSAT. It is NOT — they enter only the
    //    commitment, which we recompute, so the tampered turn proves + verifies. This is the
    //    definitive both-polarity witness that the set-roots are commitment-absorbed but UNFORCED. --
    {
        let bump = BabyBear::new(0x9999);
        // Rebuild the two block witnesses with the set-limbs tampered, then RE-RUN the live generator
        // so the `wireCommitR` chain + STATE_COMMIT carriers are internally consistent on the forged
        // limbs (the generator recomputes them in `fill_block`).
        let mut tampered_before = before_w.pre_limbs.clone();
        let mut tampered_after = after_w.pre_limbs.clone();
        for limbs in [&mut tampered_before, &mut tampered_after] {
            limbs[0] = limbs[0] + bump; // cells_root — a cell-set the kernel never had
            limbs[26] = limbs[26] + bump; // nullifier_root — a nullifier-set the kernel never had
        }
        let bw = RotatedBlockWitness::new(tampered_before, before_w.iroot).unwrap();
        let aw = RotatedBlockWitness::new(tampered_after, after_w.iroot).unwrap();
        let (t2, p2) = generate_rotated_effect_vm_trace(&st, &effects, &bw, &aw, &caveat)
            .expect("the generator re-fills the chain on the forged set-limbs");
        // Sanity: the forged limbs really do ride the trace (they are not silently dropped).
        assert_eq!(
            t2[0][BEFORE_BASE + 0], before_w.pre_limbs[0] + bump,
            "the forged cells_root rides the before block"
        );
        assert_eq!(
            t2[0][BEFORE_BASE + 26], before_w.pre_limbs[26] + bump,
            "the forged nullifier_root rides the before block"
        );
        let proof2 = prove_vm_descriptor2(&desc, &t2, &p2, &mem_boundary, &map_heaps).expect(
            "a turn with FORGED kernel-set roots (a cell/nullifier set the kernel never produced) \
             still PROVES — the set-roots are absorbed but UNGATED",
        );
        verify_vm_descriptor2(&desc, &proof2, &p2).expect(
            "and VERIFIES — DEFINITIVE: the live deployed descriptor binds the set-roots into the \
             commitment but does NOT force the kernel-set insert (the Birth/Notes accountsRoot / \
             commitmentsRoot gate is MODELED in Lean, not yet deployed in Rust)",
        );
    }

    eprintln!(
        "KERNEL-SET GAP (R=24, LIVE noteCreate): the deployed descriptor PROVES + VERIFIES a turn \
         on a FROZEN kernel-set witness AND on FORGED set-roots — the cells_root / nullifier_root \
         limbs are commitment-ABSORBED but UNGATED, and there is no commitments_root limb at all. \
         The set-insert is NOT FORCED in the deployed EffectVM apex. The Lean Birth/Notes rungs \
         prove soundness against a MODELED set-root limb + gate (accountsRoot / gAccountsGrow / \
         nullifiersRoot / commitmentsRoot / gNoteGrow); closing the gap deployment-real is the \
         flag-day NEW-limb + turn-level-grow-gate addition (NAMED residual)."
    );
}
