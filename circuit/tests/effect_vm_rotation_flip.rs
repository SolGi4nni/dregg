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
//! witness limbs it emits the 315-col rotated trace + the 38-PI vector the staged registry
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
//!      315) over a real transfer witness, LIVE-generated, every chained `wireCommitR` digest
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
const NUM_PRE: usize = rw::NUM_PRE_LIMBS; // 32

/// Resolve a rotated descriptor JSON from the staged registry TSV by key.
fn rotated_json(key: &str) -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some(key) {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("{key} not in V3_STAGED_REGISTRY_TSV");
}

/// Resolve the rotated transfer descriptor JSON from the staged registry TSV.
fn rotated_transfer_json() -> &'static str {
    rotated_json("transferVmDescriptor2R24")
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
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    // -- (G1) THE LIVE GENERATOR drives the rotated trace + PIs (NOT hand-built). --
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a 315-col trace + 38 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");
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
        commitments_root,
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
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

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
        commitments_root,
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
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[7u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a note-spend trace + 39 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

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

    // -- THE DEPLOYMENT-REAL KERNEL-SET GROW-GATE: the live `noteSpendVmDescriptor2R24` now carries
    //    the two map-ops (`nullifierFreshOp` `.absent` + `nullifierInsertOp` `.write`) that FORCE
    //    the nullifier set-insert + freshness against the openable limb-26 accumulator. We wire the
    //    real BEFORE nullifier tree (the spent nullifier ABSENT) so limb 26 carries the deployed
    //    sorted-Poseidon2 root and the prover resolves both map-ops. --
    use dregg_circuit::effect_vm::trace_rotated::generate_rotated_note_spend_trace_with_nullifier_tree;
    use dregg_circuit::heap_root::HeapLeaf;
    // A non-empty BEFORE nullifier set (distinct from the spent nullifier `0xBEEF`).
    let before_nullifiers = vec![
        HeapLeaf { addr: BabyBear::new(0x1111), value: BabyBear::new(1) },
        HeapLeaf { addr: BabyBear::new(0x2222), value: BabyBear::new(1) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_spend_trace_with_nullifier_tree(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat, &before_nullifiers,
    )
    .expect("nullifier-tree wiring must produce a deployment-real note-spend trace");
    let r0 = &trace[0];

    // PROVE + VERIFY the whole rotated note-spend end-to-end — NOW with the set-insert FORCED.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("rotated note-spend (set-insert FORCED) must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("rotated note-spend proof must verify independently");
    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "ROTATED NOTE-SPEND (R=24, 39-PI, LIVE-GENERATED, SET-INSERT FORCED): proof {total} B \
         (~{:.1} KiB) — PROVED + VERIFIED; the nullifier is pinned at PI[38] AND the kernel-set \
         insert is forced in-circuit (limb-26 accumulator grow-gate)",
        total as f64 / 1024.0
    );

    // -- THE SET-INSERT TOOTH (the gap, now closed): FORGE the AFTER nullifier root (limb 26 of
    //    every after block) to a frozen value the kernel never grew, re-fill the dependent
    //    `wireCommitR` chain so the commitment is self-consistent, and re-derive the NEW commit PI.
    //    The `.write` map-op pins the after-root to the GENUINE sorted insert, so the forged root
    //    (which is NOT that insert) has no witness and the prover REFUSES it. This is exactly the
    //    forgery `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented for the OLD
    //    descriptor — now REJECTED on the noteSpend family. --
    {
        use dregg_circuit::effect_vm::trace_rotated::{
            AFTER_BASE as AB, B_NULLIFIER_ROOT, B_STATE_COMMIT as BSC,
        };
        let bump = BabyBear::new(0x9999);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut t = trace.clone();
            for row in t.iter_mut() {
                row[AB + B_NULLIFIER_ROOT] = row[AB + B_NULLIFIER_ROOT] + bump; // a set the kernel never grew
            }
            // re-derive the NEW commit PI from the (self-consistently re-filled) forged trace.
            // (the generator already re-fills the chain in-place via recompute_block_commit on a
            //  fresh trace; here we only need the prover to reject the forged after-root, so we
            //  fully re-fill below by re-running the wiring on a forged-after witness is overkill —
            //  instead recompute the commit pin from the forged last row directly.)
            let mut p = dpis.clone();
            // recompute the after-block chain for every row so STATE_COMMIT matches the forged limb,
            // then publish the new commit PI from the last row.
            dregg_circuit::effect_vm::trace_rotated::recompute_after_blocks_for_test(&mut t);
            p[35] = t[t.len() - 1][AB + BSC];
            prove_vm_descriptor2(&desc, &t, &p, &mem_boundary, &map_heaps)
        }));
        let rejected = match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        };
        assert!(
            rejected,
            "a FORGED after nullifier_root (a set the kernel never grew) MUST be REJECTED by the \
             live noteSpend grow-gate (the `.write` op pins the after-root to the genuine insert) \
             — the kernel-set-insert gap is CLOSED for noteSpend"
        );
    }

    // -- THE DOUBLE-SPEND TOOTH (in-circuit): a nullifier ALREADY in the BEFORE tree has no
    //    `.absent` bracketing witness, so the wiring REFUSES it before proving — the in-circuit
    //    no-double-spend gate bites. --
    {
        let spent = vec![HeapLeaf {
            addr: r0[PARAM_BASE + param::NULLIFIER], // the spent nullifier is ALREADY present
            value: BabyBear::new(1),
        }];
        let double = generate_rotated_note_spend_trace_with_nullifier_tree(
            &st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat, &spent,
        );
        assert!(
            double.is_err(),
            "a DOUBLE-SPEND (nullifier already in the BEFORE tree) MUST be refused by the \
             in-circuit freshness (`.absent`) op — the double-spend hole is closed"
        );
    }

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

/// **THE DEPLOYMENT-REAL createCell ACCOUNTS-SET grow-gate (the cells_root sibling of the noteSpend
/// tooth).** The live `createCellVmDescriptor2R24` now carries two map-ops gated by the createCell
/// selector — `cellsFreshOp` (`.absent`: the new-cell key is a NON-MEMBER of the BEFORE accounts tree
/// — no id collision) and `cellsInsertOp` (`.insert`: the AFTER `cells_root` IS the genuine sorted
/// insert of the new-cell key). These open the rotated `cells_root` limb (limb 0). This test proves
/// the set-insert is FORCED, and that a forged/frozen `cells_root` (a turn that claims a cell was
/// created but whose after-block accounts root is NOT the genuine insert) is REJECTED — exactly the
/// gap `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented for createCell, now closed.
/// factory/spawn follow the identical pattern (selectors 13/32; spawn's cap-handoff is orthogonal —
/// the named spawn residual).
#[test]
fn rotated_create_cell_pins_accounts_and_refuses_tamper() {
    use dregg_circuit::effect_vm::columns::PARAM_BASE;
    use dregg_circuit::effect_vm::trace_rotated::generate_rotated_create_cell_trace_with_accounts_tree;
    use dregg_circuit::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    // The createCell cohort member's rotated descriptor — 39 PIs (38 prefix + the new-cell-key pin).
    let new_cell_id = BabyBear::new(0xCE11);
    let create = Effect::CreateCell {
        create_hash: [new_cell_id; 8],
    };
    let name = rotated_descriptor_name_for_effect(&create).expect("CreateCell is a cohort member");
    assert_eq!(name, "createCellVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("rotated createCell parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
    assert_eq!(
        desc.public_input_count, 39,
        "rotated createCell carries 38 prefix PIs + the appended new-cell-key slot"
    );

    let before_balance: i64 = 40_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![create];

    // The before/after producer witnesses (the createCell actor row freezes the balance + ticks the
    // nonce; cells_root is then overridden by the accounts-tree wrapper).
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();

    // A non-empty BEFORE accounts set (distinct from the new-cell key `0xCE11`).
    let before_accounts = vec![
        HeapLeaf { addr: BabyBear::new(0xAA01), value: BabyBear::new(0xAA01) },
        HeapLeaf { addr: BabyBear::new(0xAA02), value: BabyBear::new(0xAA02) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_create_cell_trace_with_accounts_tree(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat, &before_accounts,
    )
    .expect("accounts-tree wiring must produce a deployment-real createCell trace");
    assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

    // THE FIFTH PI: 39 elements, and PI[38] == the row-0 new-cell key (param0 for createCell).
    assert_eq!(dpis.len(), 39, "createCell rotated PI is 39 (the new-cell-key slot appended)");
    assert_eq!(
        dpis[38], trace[0][PARAM_BASE],
        "PI 38 = the create row's new-cell key (param0)"
    );

    // PROVE + VERIFY the whole rotated createCell end-to-end — the set-insert FORCED.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("rotated createCell (set-insert FORCED) must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("rotated createCell proof must verify independently");
    eprintln!(
        "ROTATED createCell (R=24, 39-PI, LIVE-GENERATED, SET-INSERT FORCED): PROVED + VERIFIED; \
         the new-cell key is pinned at PI[38] AND the accounts-set insert is forced in-circuit \
         (limb-0 cells_root accumulator grow-gate)"
    );

    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>, mh: &Vec<Vec<HeapLeaf>>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, mh)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };

    // -- THE SET-INSERT TOOTH #1 (FORGED after-root): bump the AFTER cells_root (limb 0 of every
    //    after block) to a value the kernel never grew. The `.insert` map-op pins the after-root to
    //    the GENUINE sorted insert, so a forged after-root has no witness and the prover REFUSES. --
    {
        use dregg_circuit::effect_vm::trace_rotated::{AFTER_BASE as AB, B_STATE_COMMIT as BSC};
        let bump = BabyBear::new(0x9999);
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[AB + 0] = row[AB + 0] + bump; // forged after cells_root
        }
        let mut p = dpis.clone();
        p[35] = t[t.len() - 1][AB + BSC]; // a self-consistent (but forged) NEW commit PI
        assert!(
            refused(&t, &p, &map_heaps),
            "a FORGED after cells_root (not the genuine sorted insert) MUST be UNSAT — the \
             `.insert` grow-gate pins the after-root"
        );
    }

    // -- THE SET-INSERT TOOTH #2 (FROZEN cells_root): the after cells_root EQUALS the before (no
    //    growth — the OLD pre-grow-gate shape). The `.insert` op forces after = insert(before, key)
    //    ≠ before, so a frozen accounts root has no witness and is REJECTED. --
    {
        let frozen_before = CanonicalHeapTree::new(before_accounts.clone(), HEAP_TREE_DEPTH).root();
        use dregg_circuit::effect_vm::trace_rotated::{AFTER_BASE as AB, BEFORE_BASE as BB};
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[BB + 0] = frozen_before;
            row[AB + 0] = frozen_before; // FROZEN: after == before (no insert)
        }
        assert!(
            refused(&t, &dpis, &map_heaps),
            "a FROZEN cells_root (after == before, no growth) MUST be UNSAT — the `.insert` \
             grow-gate forces a genuine insert"
        );
    }

    // -- THE ANTI-GHOST TOOTH: a published PI[38] differing from the create row's new-cell key
    //    (param0) is UNSAT (the new-cell-key weld pin). --
    {
        let mut p = dpis.clone();
        p[38] = p[38] + BabyBear::ONE;
        assert!(
            refused(&trace, &p, &map_heaps),
            "a published PI[38] differing from the create row's new-cell key MUST be UNSAT"
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
        assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
        let commitments_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[9u8; 32]];

        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

        let caveat = empty_caveat_manifest();
        let (trace, dpis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .expect("live rotated generator must produce a setField trace + 38 PIs");
        assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

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
        assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
        let commitments_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];

        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

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
        assert_eq!(pre_limbs.len(), V9_NUM_PRE_LIMBS, "32 pre-iroot limbs at R=24");
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
    let commitments_root = [0u8; 32];
    let iroot = BabyBear::new(0x1234);
    let cells_root = BabyBear::new(0x5678);
    let ctx = V9RotationContext {
        cells_root,
        nullifier_root,
        commitments_root,
        iroot,
    };

    // -- (a) THE INDEPENDENT RE-FOLD == the deployed PUBLISHED commitment. --
    // The deployed pre-limb vector (the Lean `rotatedLimbs` order) and the deployed published felt.
    let pre = compute_rotated_pre_limbs(&plain, &ctx);
    assert_eq!(pre.len(), V9_NUM_PRE_LIMBS, "32 limbs");
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

    // -- (c) THE commitments_root FLIP (the flag-day's reason for the new limb): a note-commitment
    //    ADD — a DIFFERENT `commitments_root` context — MOVES the published commitment, AND moves it
    //    ONLY at index 27 (the new committed shielded-set root). This is the P0-2 non-vacuity on the
    //    note-commitments set: a turn that grew the commitments set publishes a DIFFERENT OLD/NEW
    //    commit than one that did not. The differential's Lean twin is
    //    `RotatedCommitDifferential.rotatedCommit_binds_commitments_root`. --
    let ctx_grown = V9RotationContext {
        commitments_root: [9u8; 32], // a note commitment the kernel inserted
        ..ctx
    };
    let pre_grown = compute_rotated_pre_limbs(&plain, &ctx_grown);
    for i in 0..V9_NUM_PRE_LIMBS {
        if i == 27 {
            assert_ne!(pre[i], pre_grown[i], "index 27 (commitments_root) MUST move on a note add");
        } else {
            assert_eq!(
                pre[i], pre_grown[i],
                "limb {i} must be unchanged by a commitments-set-only change"
            );
        }
    }
    let published_grown = compute_canonical_state_commitment_v9_felt(&plain, &ctx_grown);
    assert_ne!(
        published, published_grown,
        "P0-2 on the commitments set: a note-commitment ADD MOVES the published rotated commitment \
         (limb 27 is bound) — the kernel-set insert is now witnessed by the published commitment"
    );
    assert_eq!(
        published_grown,
        independent_wire_commit(&pre_grown, iroot),
        "the independent re-fold == the deployed published commitment on the grown-set context too"
    );

    eprintln!(
        "ROTATED WIRE-COMMIT LEAN DIFFERENTIAL GREEN: the PUBLISHED rotated commitment == an \
         independent re-fold over the Lean rotatedLimbs order; a permission flip MOVES it (P0-2 on \
         the authority residue, limb 24); and a note-commitment ADD MOVES it (P0-2 on the \
         commitments set, the flag-day limb 27)."
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
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

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
        commitments_root,
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
        commitments_root,
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
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    // The lifecycle limb genuinely MOVED Live -> Sealed (the forgery the pin forbids would freeze it).
    assert_ne!(
        before_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the producer witnesses a DISTINCT lifecycle felt for the sealed post (anti-omission)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a cellSeal trace + 39 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

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

/// THE WAVE-0 LIGHT-CLIENT CLOSE — the AUTHORITY-FROZEN CONTINUITY WELD on a VALUE effect.
///
/// The deployed commitment binds the authority residue `r23` (`B_RECORD_DIGEST` = limb 24, the
/// concrete realization of the Lean `StateCommit.RH` rest-hash) into `state_commit`/NEW_COMMIT. But
/// the rotated value descriptor's economic gate welds ONLY balance/nonce/fields[0..7]/cap_root —
/// NOT r23. So for a VALUE effect (here `Transfer`) the BEFORE-r23 and AFTER-r23 columns were
/// independent free felts: a prover could witness an AFTER-r23 folding ARBITRARY
/// permissions/VK/lifecycle/mode, the value gate still passed, NEW_COMMIT bound the FORGED authority
/// half, and a ledgerless light client (verifying the descriptor proof ALONE, no trusted post-cell)
/// could not tell. That is a LIVE, publishable forgery (silently rewriting the authority half during
/// an innocuous value move).
///
/// The frozen value descriptor (`v3OfFrozen`, registry `transferVmDescriptor2R24`) appends two
/// same-row `colEq` welds forcing AFTER-r23 == BEFORE-r23 (and AFTER lifecycle == BEFORE lifecycle).
/// By Lean `StateCommit.RestHashIffFrame` that equals "the 16 authority components are unchanged" —
/// exactly the frame the kernel leaves invariant on a value move. This test proves the honest frozen
/// transfer end-to-end, then witnesses an AFTER-r23 ≠ BEFORE-r23 trace (authority drift) and asserts
/// it is UNSAT via `prove`/`verify` ALONE — the deployment-soundness gap closed for the value cohort.
#[test]
fn rotated_transfer_frozen_authority_forces_r23_and_rejects_drift() {
    use dregg_circuit::effect_vm::trace_rotated::{B_LIFECYCLE, B_RECORD_DIGEST};

    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
    assert_eq!(desc.public_input_count, 38, "value descriptor keeps the 38-PI shape");

    // -- a real value (transfer-out) turn; the authority half is UNCHANGED (a value move). --
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce the frozen transfer trace + 38 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

    // THE FREEZE HOLDS HONESTLY: on a value move the kernel leaves the WHOLE authority residue
    // unchanged, so the producer's AFTER-r23 limb EQUALS the BEFORE-r23 limb — the column-equality
    // the two appended welds force. (Same for the lifecycle limb.) The welds are SATISFIABLE by the
    // genuine honest trace; the close is NOT vacuous.
    let last = &trace[trace.len() - 1];
    let r0 = &trace[0];
    assert_eq!(
        before_w.pre_limbs[B_RECORD_DIGEST], after_w.pre_limbs[B_RECORD_DIGEST],
        "a value move leaves the producer's r23 authority residue UNCHANGED (anti-vacuity)"
    );
    assert_eq!(
        r0[BEFORE_BASE + B_RECORD_DIGEST], last[AFTER_BASE + B_RECORD_DIGEST],
        "the honest frozen trace carries AFTER-r23 == BEFORE-r23 (the weld is satisfied)"
    );
    assert_eq!(
        r0[BEFORE_BASE + B_LIFECYCLE], last[AFTER_BASE + B_LIFECYCLE],
        "the honest frozen trace carries AFTER-lifecycle == BEFORE-lifecycle"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // (1) PROVE + VERIFY the honest frozen transfer end-to-end (no trusted post-cell).
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("honest frozen transfer must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("honest frozen transfer proof must verify independently");

    // (2) THE NEGATIVE TOOTH (the light-client bite): a trace whose AFTER-r23 differs from the
    //     BEFORE-r23 (authority drift smuggled into NEW_COMMIT during a value move) is UNSAT via
    //     `prove`/`verify` ALONE — the forgery the deployed descriptor USED to accept.
    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };
    // (a) THE CENTRAL FORGERY: drift the AFTER-r23 authority limb away from the BEFORE — a value
    //     turn rewriting the authority half (forged permissions/VK/lifecycle/mode) into NEW_COMMIT.
    {
        let mut t = trace.clone();
        let last_row = t.len() - 1;
        t[last_row][AFTER_BASE + B_RECORD_DIGEST] =
            t[last_row][AFTER_BASE + B_RECORD_DIGEST] + BabyBear::ONE;
        assert!(
            refused(&t, &dpis),
            "DRIFTING the AFTER-r23 authority residue (forged authority half) on a value move MUST \
             be UNSAT — the frozen-authority weld bites; the light-client forgery is rejected in the \
             LIVE descriptor with no trusted post-cell"
        );
    }
    // (b) the lifecycle drift (the second weld) bites too.
    {
        let mut t = trace.clone();
        let last_row = t.len() - 1;
        t[last_row][AFTER_BASE + B_LIFECYCLE] =
            t[last_row][AFTER_BASE + B_LIFECYCLE] + BabyBear::ONE;
        assert!(
            refused(&t, &dpis),
            "DRIFTING the AFTER lifecycle limb on a value move MUST be UNSAT (the lifecycle weld)"
        );
    }

    eprintln!(
        "ROTATED TRANSFER FROZEN-AUTHORITY (WAVE 0, LIVE-GENERATED): PROVED + VERIFIED; AFTER-r23 \
         is FORCED == BEFORE-r23, and an authority-drift forgery (AFTER-r23 != BEFORE-r23) is UNSAT \
         via prove/verify alone — the live light-client authority-drift forgery is closed."
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
    use dregg_circuit::effect_vm::trace_rotated::{B_LIFECYCLE, B_RECORD_DIGEST};

    // An out-of-`fields[0..16]` audit key: writing it via `set_field_ext` lands in the cell's
    // `fields_root` (the named-field map), exactly where the `"refusal"` audit slot lives — so the
    // after cell's authority digest (r23, `B_RECORD_DIGEST`) genuinely moves. (Used only by the
    // refusal arm; receiptArchive's genuine mover is the lifecycle limb, not `fields_root`.)
    const AUDIT_KEY: u64 = 4096;

    // The two audit effects. `record_pin_offset` routes them to DIFFERENT committed limbs (post
    // #218/#219): a genuine `Refusal` moves `fields_root` → folds into the r23 authority residue
    // (`B_RECORD_DIGEST`); a genuine `ReceiptArchive` transitions the cell lifecycle to `Archived`
    // → `lifecycle_felt` (`B_LIFECYCLE = 29`). Each effect's pin welds ITS limb to PI[38].
    let refusal = Effect::Refusal {
        target: [BabyBear::new(0); 8],
        reason_hash: [BabyBear::new(5); 8],
    };
    let archive = Effect::ReceiptArchive {
        target: [BabyBear::new(0); 8],
        archive_end_height: BabyBear::new(7),
        terminal_receipt_hash: [BabyBear::new(11); 8],
    };

    for (effect, expect_name, pin_limb) in [
        (refusal, "refusalVmDescriptor2R24", B_RECORD_DIGEST),
        (archive, "receiptArchiveVmDescriptor2R24", B_LIFECYCLE),
    ] {
        let name = rotated_descriptor_name_for_effect(&effect)
            .expect("audit effect is a rotated cohort member");
        assert_eq!(name, expect_name);

        let json = rotated_descriptor_json(name);
        let desc = parse_vm_descriptor2(json).expect("rotated audit descriptor parses");
        assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");
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
        // Move the AFTER cell's pinned limb by the effect's GENUINE mover (so `record_pin_offset`'s
        // limb truly changes pre→post and the pin is non-vacuous):
        match expect_name {
            // Refusal: the welded audit slot flips to 1 in `fields_root` → `compute_authority_
            // digest_felt` (the r23 `B_RECORD_DIGEST` limb) moves.
            "refusalVmDescriptor2R24" => {
                let mut one = [0u8; 32];
                one[0] = 1;
                assert!(
                    after_cell.state.set_field_ext(AUDIT_KEY, one),
                    "the audit-slot write must take"
                );
            }
            // ReceiptArchive: transition the lifecycle to `Archived` → `lifecycle_felt`
            // (`B_LIFECYCLE`) moves. This is the #219 re-route: the genuine mover is the lifecycle
            // limb, NOT `fields_root`.
            "receiptArchiveVmDescriptor2R24" => {
                let attestation = dregg_cell::ArchivalAttestation {
                    cell_id: after_cell.id(),
                    archive_start_height: 0,
                    archive_end_height: 7,
                    archive_blob_hash: [9u8; 32],
                    archive_terminal_commitment: [13u8; 32],
                    archive_terminal_receipt_hash: [11u8; 32],
                };
                after_cell
                    .archive(&attestation)
                    .expect("archiving the after cell moves the B_LIFECYCLE limb");
            }
            other => panic!("unexpected audit descriptor {other}"),
        }
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

        // The pinned limb genuinely MOVED pre→post (the forgery the pin forbids would freeze it):
        // refusal moves the r23 authority residue via `fields_root`; archive moves `lifecycle_felt`.
        assert_ne!(
            before_w.pre_limbs[pin_limb], after_w.pre_limbs[pin_limb],
            "{name}: the producer witnesses a DISTINCT pinned limb for the audit post \
             (the audit write is bound by the committed limb — anti-omission)"
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
        assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

        // THE FIFTH PI: 39 elements, and PI[38] == the LAST row's AFTER record-digest limb.
        assert_eq!(dpis.len(), 39, "{name} rotated PI is 39 (the record-forcing slot appended)");
        let last = &trace[trace.len() - 1];
        assert_eq!(
            dpis[38],
            last[AFTER_BASE + pin_limb],
            "PI 38 = the AFTER block's correctly-written audit limb (r23 record-digest for refusal, \
             lifecycle_felt for archive)"
        );
        assert_eq!(
            dpis[38], after_w.pre_limbs[pin_limb],
            "PI 38 = the post-state producer witness's pinned limb"
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
            t[last_row][AFTER_BASE + pin_limb] = before_w.pre_limbs[pin_limb]; // frozen
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

/// THE KERNEL-SET DEPLOYMENT-SOUNDNESS CLOSE for the whole family.
///
/// The kernel-set effects mutate KERNEL-LEVEL sets, each with its OWN committed openable
/// sorted-Poseidon2 accumulator limb the rotated commitment absorbs and a per-effect grow-gate
/// FORCES grown:
///   * `createCell` / `createCellFromFactory` / `spawn` → the `cells_root` accounts set (limb 0,
///     `cellsInsertOp`) — `rotated_create_cell_pins_accounts_and_refuses_tamper`;
///   * `noteSpend` → the `nullifier_root` set (limb 26, `nullifierInsertOp` + the `.absent`
///     double-spend tooth) — `rotated_note_spend_pins_nullifier_and_refuses_tamper`;
///   * `noteCreate` → the `commitments_root` set (limb 27, the flag-day NUM_PRE_LIMBS 31→32 limb,
///     `commitmentsInsertOp`) — `note_create_pins_commitments_and_refuses_tamper`.
/// Each gate pins `after_root = insert(before_root, key)` to the GENUINE sorted insert, so a frozen
/// or forged set-root (the kernel-set insert NOT grown) is REJECTED. The family is deployment-real
/// end to end; the historical residual narrative below is retained only for context.
///
/// This test makes that close CONCRETE for the FORMERLY-OPEN `noteCreate` residual: it proves a real
/// `noteCreate` rotated turn through the LIVE `noteCreateVmDescriptor2R24` descriptor over a GENUINE
/// grown commitments tree, then REJECTS a forged after-`commitments_root` (the `.insert` op pins the
/// after-root to the genuine sorted insert, so a kernel-set the prover never grew has no witness).
///
/// ## STATUS: the WHOLE kernel-set family (noteSpend · createCell/factory/spawn · noteCreate) is
/// CLOSED deployment-real.
///
/// The nullifier family is deployment-real: `noteSpendVmDescriptor2R24` carries the kernel-set
/// grow-gate — two map-ops (`nullifierFreshOp` `.absent` + `nullifierInsertOp` `.insert`,
/// `EffectVmEmitRotationV3.noteSpendV3`) that open the limb-26 nullifier accumulator. Proven
/// end-to-end in `rotated_note_spend_pins_nullifier_and_refuses_tamper`.
///
/// The cells family (`createCell`/`factory`/`spawn`) is ALSO now deployment-real:
/// `{createCell,factory,spawn}VmDescriptor2R24` carry `cellsFreshOp` (`.absent`) + `cellsInsertOp`
/// (`.insert`) on the openable `cells_root` limb (limb 0), keyed by a NEW published new-cell-key
/// PI[38] (`EffectVmEmitRotationV3.{createCellV3,factoryV3,spawnV3}` — param0 for createCell/spawn,
/// param1/CHILD_VK_DERIVED for factory). The set-insert is FORCED; a forged/frozen `cells_root` is
/// REJECTED. Proven end-to-end in `rotated_create_cell_pins_accounts_and_refuses_tamper`. spawn's
/// cap-handoff (the child cap-root MOVE + delegation snapshot) is ORTHOGONAL to the accounts-set
/// insert and is the NAMED spawn residual.
///
/// THIS test exercises `noteCreate` (the `commitments` set) — the LAST kernel-set residual, now
/// CLOSED deployment-real by the `commitments_root` flag-day (NUM_PRE_LIMBS 31→32, the new committed
/// shielded-set root at limb 27 + the `commitmentsInsertOp .insert` grow-gate keyed on the published
/// commitment `param0`, `EffectVmEmitRotationV3.noteCreateV3`). The deployed `noteCreateV3`
/// descriptor FORCES `after.commitments_root = insert(before.commitments_root, cm)` — the deployed
/// face of `RotatedKernelRefinementNotes.noteCreate_commitments_forced`. A frozen or forged
/// `commitments_root` (the kernel-set insert NOT grown, exactly the old residual) is REJECTED.
#[test]
fn note_create_pins_commitments_and_refuses_tamper() {
    use dregg_circuit::effect_vm::trace_rotated::{
        B_COMMITMENTS_ROOT, generate_rotated_note_create_trace_with_commitments_tree,
        recompute_after_blocks_for_test,
    };
    use dregg_circuit::heap_root::HeapLeaf;

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
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 315");

    // A real note-create turn (EffectVM credits balance by `value`, the shielding convention).
    let before_balance: i64 = 60_000;
    let value: u64 = 250;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![create];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let caveat = empty_caveat_manifest();
    let mem_boundary = MemBoundaryWitness::default();

    // -- THE SET-INSERT, FORCED: the commitments-tree wiring makes limb 27 the openable committed
    //    accumulator. The BEFORE tree holds the existing commitments; the AFTER tree is BEFORE + the
    //    inserted note commitment `cm`. The live `commitmentsInsertOp .insert` op pins the after-root
    //    to the GENUINE sorted insert, so the published commitment binds the grown set. --
    let before_commitments = vec![
        HeapLeaf { addr: BabyBear::new(0x111), value: BabyBear::new(1) },
        HeapLeaf { addr: BabyBear::new(0x222), value: BabyBear::new(1) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_create_trace_with_commitments_tree(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_commitments,
    )
    .expect("the commitments-tree wiring builds a genuine grown-set noteCreate trace");
    assert_eq!(trace[0].len(), ROT_WIDTH, "315-col rotated trace");

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("note-create PROVES on a GENUINE grown commitments-set witness — the gate is honored");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("and VERIFIES — the live noteCreate descriptor FORCES the commitments set-insert");

    // -- THE SET-INSERT TOOTH (the residual, now CLOSED): FORGE the AFTER commitments root (limb 27
    //    of every after-block) to a value the kernel never produced, recompute the dependent
    //    `wireCommitR` chain so the commitment is self-consistent, and re-derive the NEW commit PI.
    //    The `.insert` map-op pins the after-root to the GENUINE sorted insert, so the forged root
    //    (which is NOT that insert) has no witness and the prover REFUSES it — exactly the forgery
    //    the OLD `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented, now REJECTED. --
    {
        let bump = BabyBear::new(0x9999);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut t = trace.clone();
            for row in t.iter_mut() {
                row[AFTER_BASE + B_COMMITMENTS_ROOT] =
                    row[AFTER_BASE + B_COMMITMENTS_ROOT] + bump; // a commitments-set the kernel never grew
            }
            let mut p = dpis.clone();
            recompute_after_blocks_for_test(&mut t);
            p[35] = t[t.len() - 1][AFTER_BASE + B_STATE_COMMIT];
            prove_vm_descriptor2(&desc, &t, &p, &mem_boundary, &map_heaps)
        }));
        let rejected = matches!(r, Err(_)) || matches!(r, Ok(res) if res.is_err());
        assert!(
            rejected,
            "a FORGED after commitments_root (a set the kernel never grew) MUST be REJECTED by the \
             live noteCreate grow-gate (the `.insert` op pins the after-root to the genuine insert) \
             — the kernel-set-insert gap is CLOSED for noteCreate, the LAST residual of the family"
        );
    }

    eprintln!(
        "KERNEL-SET CLOSED (R=24, LIVE noteCreate): the deployed noteCreate descriptor FORCES the \
         commitments set-insert on the flag-day limb 27 (`commitmentsInsertOp .insert`); a genuine \
         grown-set witness PROVES+VERIFIES and a forged/frozen commitments_root is REJECTED. \
         noteSpend, createCell, factory, spawn, noteCreate are ALL CLOSED — the kernel-set family is \
         deployment-real end to end."
    );
}

/// THE LIGHT-CLIENT FEE TOOTH (trust-surface hole #5 close).
///
/// The deployed sovereign transfer debited `turn.fee` from the actor cell in executor PHASE 1,
/// BEFORE proving; the proof was built over the PRE-fee balance and the verifier blindly UNDID the
/// debit from the TRUSTED `turn.fee`. So the fee was NOT a constraint in the proven transition — a
/// ledgerless light client could not verify it. `transferFeeVmDescriptor2R24` closes that: the
/// balance-lo gate is augmented to debit the fee (`after = before − transfer − fee`), the fee rides
/// the after-block RESERVED column (col 89, NOT in the state commitment), and a last-row pin welds
/// that column to the published fee PI (slot 38).
///
/// This test exercises the bite with `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE — NO
/// executor, NO trusted `+ turn.fee` reconstruction:
///   1. an HONEST fee'd transfer PROVES + VERIFIES, and NEW_COMMIT (PI 35) binds the POST-fee
///      balance (the verifier reads the fee off PI 38, not off any trusted ledger value);
///   2. a proof claiming a SMALLER fee PI than the balance actually moved is UNSAT;
///   3. a proof whose published fee PI is forged (≠ the debited column) is UNSAT.
#[test]
fn fee_debit_is_proven_and_underclaimed_fee_is_unsat_for_a_ledgerless_client() {
    use dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace_with_fee;

    let desc = parse_vm_descriptor2(rotated_json("transferFeeVmDescriptor2R24"))
        .expect("rotated fee'd transfer descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "fee'd transfer keeps the rotated width 315");
    assert_eq!(
        desc.public_input_count, 39,
        "fee'd transfer: 38 rotated PIs + the appended fee PI (slot 38)"
    );

    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let fee: u64 = 7;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer { amount, direction: 1 }];

    // The producer's after-cell debits BOTH the transfer AND the fee (the proven post-fee state).
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64 - fee as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let caveat = transfer_caveat_manifest();

    let (trace, dpis) = generate_rotated_effect_vm_trace_with_fee(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        fee,
    )
    .expect("fee'd rotated generator produces a 315-col trace + 39 PIs");
    assert_eq!(dpis.len(), 39, "39 PIs (38 rotated + the fee)");
    assert_eq!(
        dpis[38],
        BabyBear::new(fee as u32),
        "PI 38 is the published fee"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // -- (1) the HONEST fee'd transfer proves + verifies, NEW_COMMIT binds the POST-fee balance. --
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("honest fee'd transfer must prove");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("honest fee'd transfer proof must verify independently (no trusted reconstruction)");

    // The PROVEN final balance (PI 14 = FINAL_BAL_LO, the last-row after bal_lo bound into
    // NEW_COMMIT) is the POST-fee balance `before − amount − fee` — the fee debit is INSIDE the
    // proven transition, NOT a trusted reconstruction. A ledgerless client reads the fee off PI 38.
    let (post_fee_lo, _post_fee_hi) =
        dregg_circuit::effect_vm::split_u64((before_balance - amount as i64 - fee as i64) as u64);
    assert_eq!(
        dpis[14], post_fee_lo,
        "FINAL_BAL_LO (bound into NEW_COMMIT) is the POST-fee balance `before − amount − fee` — the \
         fee debit is proven, not reconstructed"
    );
    // And NEW_COMMIT (PI 35) is the trace's last-row after-block STATE_COMMIT carrier (post-fee).
    assert_eq!(
        dpis[35],
        trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        "NEW_COMMIT binds the post-fee after-block STATE_COMMIT carrier"
    );

    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };
    let refused_verify = |p: &Vec<BabyBear>| -> bool {
        // Verify the HONEST proof against a TAMPERED published-PI vector (the proof's transcript
        // bound the honest PIs; a different PI vector fails Fiat–Shamir / the boundary pins).
        verify_vm_descriptor2(&desc, &proof, p).is_err()
    };

    // -- (2) UNDERCLAIMED FEE: a witness that moves the balance by `fee` but publishes a SMALLER
    //    fee PI (and writes the smaller fee into the after-block RESERVED column) is UNSAT. The
    //    balance-lo gate forces `after = before − amount − col89`; if col89 < the real fee the
    //    after-balance no longer matches the (post-fee) NEW_COMMIT-bound limb, and the last-row pin
    //    forces col89 = PI[38]. So publishing a smaller fee cannot satisfy the descriptor. --
    {
        let underclaim: u64 = 3; // < fee
        // Rebuild a trace whose fee column = the underclaim but whose ACTUAL balance moved by `fee`:
        // generate the honest fee'd trace, then overwrite col 89 (the fee carrier) on every row +
        // the published PI 38 with the underclaim. The bal-lo gate (`after = before − amount − col89`)
        // then demands the after-balance be `before − amount − underclaim`, but the trace's after
        // balance is `before − amount − fee` ≠ that — UNSAT.
        let fee_col = STATE_AFTER_BASE + state::RESERVED;
        let before_reserved = STATE_BEFORE_BASE + state::RESERVED;
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[fee_col] = BabyBear::new(underclaim as u32);
            row[before_reserved] = BabyBear::new(underclaim as u32);
        }
        let mut p = dpis.clone();
        p[38] = BabyBear::new(underclaim as u32);
        assert!(
            refused(&t, &p),
            "an UNDERCLAIMED fee (col 89 / PI 38 smaller than the balance actually moved) MUST be \
             UNSAT — the balance-lo fee gate `after = before − amount − fee` rejects it, with NO \
             trusted reconstruction"
        );
    }

    // -- (3) FORGED FEE PI: keep the honest trace but publish a DIFFERENT fee PI. The last-row pin
    //    `col 89 == PI[38]` forces the published fee to equal the proven column — a forged PI fails. --
    {
        let mut p = dpis.clone();
        p[38] = dpis[38] + BabyBear::new(11);
        assert!(
            refused_verify(&p),
            "a FORGED fee PI (≠ the debited after-block RESERVED column) MUST fail the last-row pin \
             (col 89 == PI[38]) — a ledgerless client cannot be told a fee the proof did not move"
        );
    }

    eprintln!(
        "FEE-IN-PROOF CLOSED (R=24, LIVE): the deployed sovereign transfer debits the fee INSIDE \
         the proven transition (transferFeeVmDescriptor2R24 — bal-lo gate `after = before − amount \
         − fee`, fee pinned to PI 38). An honest fee'd transfer PROVES+VERIFIES with NEW_COMMIT \
         binding the post-fee balance; an underclaimed or forged fee is UNSAT via \
         verify_vm_descriptor2 ALONE — NO trusted `+ turn.fee` reconstruction. Trust-surface hole \
         #5 is CLOSED for the sovereign actor cell."
    );
}
