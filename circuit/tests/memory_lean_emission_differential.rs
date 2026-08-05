//! **THE MEMORY OP LOG'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::Memory` was a hand-written Rust arm: the boolean guard and kind, the real-row prefix,
//! the positional serial chain, the read discipline, the serial-gap range check, the `ir2_mem_log`
//! receive, both `ir2_mem_check` Blum legs and the `ir2_mem_addrs` address-closure query.
//! Architectural law #1 says that object is authored in Lean and Rust only interprets. It was not.
//! **That arm is now DELETED**; its author is
//! `metatheory/Dregg2/Circuit/Emit/MemoryTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-memory-v1.json`, and `Ir2Air::LeanTable` walks it.
//!
//! # The three questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    op log, the serial chain and the gap witnesses OUT of the prover's own memory trace.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2 — a per-cell mutation sweep
//!    through the REAL deployed evaluator, with the undetected set pinned EXACTLY.)
//! 3. **Do both poles still hold at the deployed prover?** (§3.)
//!
//! # ⚑ What the port REFUTED, which the deleted arm asserted
//!
//! The arm's comments made three claims. Two are theorems in the Lean file
//! (`serial_is_positional`, `read_returns_its_claimed_value`). The third — *"prev_serial < serial
//! (Disciplined)"* — is **FALSE of the felts this AIR admits**. There is no magnitude gate on
//! `MEM_PREV_SERIAL`: the gap gate *defines* `prev_serial = serial − 1 − gap` in the FIELD, so at
//! serial 1 the admissible prior serials include `p − 5`, and
//! `wrapped_prev_serial_satisfies_every_gate` proves exactly that against the emitted gate list.
//! §3 measures the deployed twin: the ASSEMBLER refuses it (a completeness-of-refusal fact), the
//! GATES do not, and the thing that would refuse a gate-level forgery is the `ir2_mem_check`
//! multiset in a different AIR.
//!
//! ⚠ Naming which mechanism refuses what is the point. An assembler refusal quoted as a gate
//! verdict is how an accepting gate hides.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, MemOpSpec, VmConstraint2, mem_rows_for,
    prove_vm_descriptor2, table_air_gates_accept, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::must_refuse_or_unsat_panic;
use dregg_circuit::table_air::TableExpr;
use dregg_circuit::table_air::{BusOp, RowSel, memory_table_air};

// The deployed layout, transcribed ONCE here so the assertions below can name a column. These are
// the same numbers `MemoryTableEmit.lean` derives; a drift on either side reds §1.
const MEM_ADDR: usize = 0;
const MEM_VALUE: usize = 1;
const MEM_PREV_VALUE: usize = 2;
const MEM_PREV_SERIAL: usize = 3;
const MEM_KIND: usize = 4;
const MEM_SERIAL: usize = 5;
const MEM_IS_REAL: usize = 6;
const MEM_GAP: usize = 7;
const MEM_GAP_LIMB0: usize = 8;
const MEM_WIDTH: usize = 18;

const ADDRS: [u32; 3] = [5, 9, 40];
const INITS: [u32; 3] = [11, 22, 33];

/// A minimal descriptor with ONE guarded memory read — enough to make the memory pair present.
fn mem_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "memory-lean-emission-differential".to_string(),
        trace_width: 5,
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MemOp(MemOpSpec {
            guard: LeanExpr::Var(4),
            addr: LeanExpr::Var(0),
            value: LeanExpr::Var(1),
            prev_value: LeanExpr::Var(2),
            prev_serial: LeanExpr::Var(3),
            kind: MemKind::Read,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// Three honest reads, then a pad row. Op `i` carries serial `i + 1`, so the third read (a second
/// touch of address 5) claims prev serial 1 — the serial the first read left behind. That third
/// row is the one with a NONZERO serial gap, which is what makes the range check load-bearing
/// here rather than decorative.
fn mem_trace() -> Vec<Vec<BabyBear>> {
    let row = |addr: u32, val: u32, prev_v: u32, prev_s: u32, guard: u32| {
        vec![
            BabyBear::new(addr),
            BabyBear::new(val),
            BabyBear::new(prev_v),
            BabyBear::new(prev_s),
            BabyBear::new(guard),
        ]
    };
    vec![
        row(5, 11, 11, 0, 1),
        row(9, 22, 22, 0, 1),
        row(5, 11, 11, 1, 1),
        row(0, 0, 0, 0, 0),
    ]
}

fn boundary() -> MemBoundaryWitness {
    MemBoundaryWitness {
        addrs: ADDRS.to_vec(),
        init_vals: INITS.to_vec(),
    }
}

fn honest_mem_rows() -> Vec<Vec<BabyBear>> {
    mem_rows_for(&mem_desc(), &mem_trace(), &boundary())
        .expect("the deployed prover assembles a memory op-log table")
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The emitted table declares width 18 and reads the address at
/// column 0, the claimed prior serial at 3, the kind at 4, the positional serial at 5, the guard
/// at 6 and the gap at 7. The prover's OWN trace builder writes those columns; this reads them
/// back out and checks each against the base trace, recovered independently rather than off the
/// same row.
///
/// If the Lean emission had transcribed one offset wrong, the honest witness would still prove
/// (the gate would read a zero column and vanish) but this round-trip would fail.
#[test]
fn the_emitted_columns_round_trip_the_memory_op_log() {
    let rows = honest_mem_rows();
    let t = memory_table_air();
    let base = mem_trace();

    assert_eq!(t.width, MEM_WIDTH);
    assert!(rows.iter().all(|r| r.len() == t.width));
    // ⓘ MEASURED, not assumed: three GUARDED ops out of four base rows, and the height is
    // `next_pow2(3)` FLOORED AT `MIN_TABLE_HEIGHT = 8` — so three real rows are followed by FIVE
    // pads, the padded shape that is the whole reason a table AIR needs a per-row multiplicity
    // expression rather than a constant.
    assert_eq!(rows.len(), 8);
    assert!(rows.len().is_power_of_two());
    assert!(rows.len() > 3, "the witness must exercise pad rows");

    for i in 0..3 {
        assert_eq!(rows[i][MEM_ADDR], base[i][0], "op {i} address");
        assert_eq!(rows[i][MEM_VALUE], base[i][1]);
        assert_eq!(rows[i][MEM_PREV_VALUE], base[i][2]);
        assert_eq!(
            rows[i][MEM_PREV_SERIAL], base[i][3],
            "op {i} claimed prior serial"
        );
        assert_eq!(rows[i][MEM_KIND], BabyBear::ZERO, "every op here is a READ");
        assert_eq!(rows[i][MEM_IS_REAL], BabyBear::ONE, "row {i} is real");
        // ⚑ The POSITIONAL serial: row i carries i + 1, which is the claim
        // `MemoryTableEmit.serial_is_positional` proves from the `.first` + `.transition` gates.
        assert_eq!(rows[i][MEM_SERIAL], BabyBear::new((i + 1) as u32));
        // …and the gap is `serial − 1 − prev_serial`, recovered from the base trace.
        let prev = base[i][3].as_u32();
        assert_eq!(rows[i][MEM_GAP], BabyBear::new((i as u32 + 1) - 1 - prev));
    }
    // The third op is the one that exercises the range check with a nonzero gap: serial 3,
    // claimed prior serial 1, gap 1.
    assert_eq!(rows[2][MEM_GAP], BabyBear::ONE);
    assert_eq!(rows[2][MEM_GAP_LIMB0], BabyBear::ONE, "limb 0 of the gap");

    // Every pad row is a pad, and the serial chain CONTINUES through them (the increment gate is
    // unconditional on the transition domain, so a pad may not restart the count).
    for (i, r) in rows.iter().enumerate().skip(3) {
        assert_eq!(r[MEM_IS_REAL], BabyBear::ZERO, "row {i} is a pad");
        assert_eq!(r[MEM_SERIAL], BabyBear::new((i + 1) as u32));
        assert_eq!(r[MEM_GAP], BabyBear::ZERO);
    }

    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every row and every one of the 18 columns, bump the value and ask the
/// REAL deployed evaluator whether the table still accepts.
///
/// The undetected set is pinned EXACTLY, and every member of it is named with the mechanism that
/// protects it instead:
///
/// * `MEM_ADDR` — bound by the `ir2_mem_addrs` LOOKUP (closure against the declared list) and the
///   `ir2_mem_check` MULTISET, neither of which a single-AIR gate check can decide.
/// * `MEM_VALUE`, `MEM_PREV_VALUE` on a real WRITE row — bound by the same multiset. ⓘ At THIS
///   witness every op is a READ, so the read-discipline gate ties the two together and a bump of
///   either is caught; both land in the DETECTED set, which is why the expectation below does not
///   list them.
/// * ⚠ `(pad row, MEM_VALUE | MEM_PREV_VALUE | MEM_PREV_SERIAL)` — a pad row's payload, on ALL
///   FIVE pads: every gate that reads those columns is multiplied by `is_real`. Contained by the
///   multiset (a pad rides at multiplicity zero, so it publishes and consumes nothing) — a
///   containment about the BUS legs, not the gates. ⓘ `MEM_KIND` is deliberately NOT in this set:
///   its boolean gate is UNCONDITIONAL, so a pad's kind is caught like the guard itself. That
///   asymmetry is measured here rather than assumed.
///
/// Anything else landing in the undetected set means the re-emission lost a gate.
#[test]
fn every_gated_memory_cell_is_still_gated_after_the_cutover() {
    let rows = honest_mem_rows();
    let t = memory_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    let mut detected: Vec<(usize, usize)> = Vec::new();
    let mut undetected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
            // TWO bumps, for the reason the map-absent sweep uses two: a `+1` on a boolean column
            // that is honestly ZERO lands on 1, which the boolean gate still accepts.
            let caught = [1u32, 2u32].iter().any(|&d| {
                let mut mutated = rows.clone();
                mutated[row][col] = mutated[row][col] + BabyBear::new(d);
                !table_air_gates_accept(&t, &mutated)
            });
            if caught {
                detected.push((row, col));
            } else {
                undetected.push((row, col));
            }
        }
    }

    let reals = 3usize;
    let mut expected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
            // The address is bound by the closure lookup + the multiset on EVERY row.
            let bus_bound = col == MEM_ADDR;
            // A pad row's payload is gated off by `is_real`. ⓘ MEASURED, and `MEM_KIND` is NOT
            // in this set: the kind boolean gate is UNCONDITIONAL, so a pad's kind column is
            // caught on every row like the guard itself.
            let pad_payload =
                row >= reals && matches!(col, MEM_VALUE | MEM_PREV_VALUE | MEM_PREV_SERIAL);
            if bus_bound || pad_payload {
                expected.push((row, col));
            }
        }
    }
    assert_eq!(
        undetected, expected,
        "the undetected set is not exactly {{the closure/multiset-bound address}} ∪ {{the pad \
         row's gated-off payload}} — either a gate was lost in the Lean re-emission, or a gate \
         appeared where a bus is supposed to be the mechanism. undetected: {undetected:?}"
    );

    // ⚑ The columns that MUST be caught on EVERY row, named with the gate that catches them.
    for row in 0..rows.len() {
        // the boolean guard, plus the prefix gate on the pad row.
        assert!(detected.contains(&(row, MEM_IS_REAL)), "row {row}: is_real");
        // the positional serial chain (`.first` anchor + `.transition` increment).
        assert!(detected.contains(&(row, MEM_SERIAL)), "row {row}: serial");
        // the gap definition + its 30-bit decomposition.
        assert!(detected.contains(&(row, MEM_GAP)), "row {row}: gap");
        for col in MEM_GAP_LIMB0..MEM_WIDTH {
            assert!(detected.contains(&(row, col)), "row {row}: gap limb {col}");
        }
    }
    // …and on every REAL row the read-discipline gate ties value, prev_value and kind.
    for row in 0..rows.len() {
        // the kind boolean, on every row including the pads.
        assert!(detected.contains(&(row, MEM_KIND)), "row {row}: kind");
    }
    for row in 0..reals {
        assert!(detected.contains(&(row, MEM_VALUE)), "row {row}: value");
        assert!(
            detected.contains(&(row, MEM_PREV_VALUE)),
            "row {row}: prev_value"
        );
        assert!(
            detected.contains(&(row, MEM_PREV_SERIAL)),
            "row {row}: prev_serial (the gap DEFINITION moves with it)"
        );
    }

    println!(
        "MEASURED: {}/{} op-log cells are gated by the Lean emission; the undetected {} are the \
         closure/multiset-bound address plus the pad row's gated-off payload",
        detected.len(),
        detected.len() + undetected.len(),
        undetected.len()
    );
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** An honest memory witness proves and verifies through the Lean-emitted AIR.
#[test]
fn an_honest_memory_witness_proves_and_verifies_through_the_lean_emission() {
    let desc = mem_desc();
    let proof = prove_vm_descriptor2(&desc, &mem_trace(), &[], &boundary(), &[])
        .expect("an honest memory witness must prove through the Lean-emitted op-log AIR");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES.**
///
/// Each forgery keeps the shape (4 rows, 18 columns) and changes only what the table SAYS. The
/// gate that refuses each is named where it is attributable, and where two gates both fire that
/// is said rather than glossed.
#[test]
fn a_forged_op_log_is_refused_by_the_emitted_gates() {
    let rows = honest_mem_rows();
    let t = memory_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // (a) ⚑ A READ THAT DOES NOT RETURN WHAT IT CLAIMS. Refused by the read-discipline gate
    //     `is_real·(1 − kind)·(value − prev_value)` — the second conjunct of
    //     `MemoryChecking.Disciplined`, which `read_returns_its_claimed_value` proves.
    let mut lying_read = rows.clone();
    lying_read[0][MEM_VALUE] = lying_read[0][MEM_VALUE] + BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &lying_read),
        "the emitted read-discipline gate must refuse a read returning other than its claim"
    );

    // (b) ⚑ RESTART THE SERIAL COUNT on the pad row. Refused by the `.transition` increment gate:
    //     the chain is positional and unconditional, so a pad may not renumber.
    let mut renumbered = rows.clone();
    renumbered[3][MEM_SERIAL] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &renumbered),
        "the emitted serial increment must refuse a restarted count"
    );

    // (c) ⚑ ANCHOR THE CHAIN SOMEWHERE ELSE: move row 0 off serial 1, keeping the rest. Both the
    //     `.first` anchor and the row-0 `.transition` increment fire. ⚠ Two gates; the refusal is
    //     not attributable to the anchor ALONE by this test, and saying so is the point.
    let mut moved_anchor = rows.clone();
    moved_anchor[0][MEM_SERIAL] = BabyBear::new(7);
    assert!(
        !table_air_gates_accept(&t, &moved_anchor),
        "the emitted first-row anchor + increment must refuse a chain that starts elsewhere"
    );

    // (d) ⚑ PROMOTE THE PAD TO A REAL ROW while its payload stays zero. Refused by the GAP
    //     definition at row 3: `gap = is_real·(serial − 1 − prev_serial)` was `0` at `is_real = 0`
    //     and becomes `0 − (4 − 1 − 0) ≠ 0`.
    let mut promoted = rows.clone();
    promoted[3][MEM_IS_REAL] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &promoted),
        "the emitted gap definition must refuse a promoted pad whose gap column stays zero"
    );

    // (e) ⚑ WIDEN THE GAP WITHOUT ITS WITNESS. Refused by the 30-bit RECOMPOSITION gate, which is
    //     what makes the gap a BOUNDED integer rather than merely a field element.
    let mut widened = rows.clone();
    widened[2][MEM_GAP] = widened[2][MEM_GAP] + BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &widened),
        "the emitted gap decomposition must refuse a gap with no limb witness"
    );
}

/// ⚑ **THE REFUTED CLAIM, MEASURED AT THE DEPLOYED EVALUATOR.**
///
/// `MemoryTableEmit.wrapped_prev_serial_satisfies_every_gate` proves in Lean that a claimed prior
/// serial of `p − 5` at serial 1 satisfies every emitted gate. This is the same statement run
/// through the REAL `Ir2Air::LeanTable` evaluator on a real-shaped trace, so the Lean theorem and
/// the deployed constraint system agree about the hole rather than only about the fix.
///
/// ⚠ Read the direction. This is NOT a defect the deployed prover admits: §3's assembler test
/// below shows `build_traces` refuses the witness outright, and the `ir2_mem_check` multiset
/// refuses it at the constraint level. What it shows is that the refusal lives in those two places
/// and NOT in the row algebra — so "prev_serial < serial (Disciplined)", which the deleted arm
/// asserted in a comment right next to the gate, is not something this table decides.
#[test]
fn the_gap_gate_admits_a_wrapped_prior_serial() {
    let rows = honest_mem_rows();
    let t = memory_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // Row 0 claims a prior serial of `p − 5` and carries the matching gap of 5, honestly
    // decomposed: gap 5 is one nibble, so only limb 0 moves.
    let mut wrapped = rows.clone();
    wrapped[0][MEM_PREV_SERIAL] = BabyBear::ZERO - BabyBear::new(5);
    wrapped[0][MEM_GAP] = BabyBear::new(5);
    wrapped[0][MEM_GAP_LIMB0] = BabyBear::new(5);
    assert!(
        table_air_gates_accept(&t, &wrapped),
        "MEASURED: the emitted gates ACCEPT a claimed prior serial of p − 5 at serial 1 — the gap \
         gate DEFINES prev_serial, it does not bound it (MemoryTableEmit §4c)"
    );
    // …and the claimed serial really is above every serial this table can ever publish.
    assert!(
        wrapped[0][MEM_PREV_SERIAL].as_u32() > (1u32 << 30),
        "the wrapped claim must be above 2^30 for the point to be the point"
    );
}

/// The prover-level pole, stated at ITS OWN resolution: the ASSEMBLER refuses a claimed prior
/// serial that is not below the op's own. ⚠ That is a completeness-of-refusal fact about
/// `build_traces`, NOT a gate verdict — the gate verdicts are the two tests above, and the test
/// directly above shows this exact witness passing the gates.
#[test]
fn a_future_claiming_prior_serial_is_refused_by_the_deployed_assembler() {
    let desc = mem_desc();
    let mut bad = mem_trace();
    // Op 0 (serial 1) claims prior serial 5 — a serial from the future.
    bad[0][3] = BabyBear::new(5);
    let refused = must_refuse_or_unsat_panic("a claimed prior serial from the future", || {
        prove_vm_descriptor2(&desc, &bad, &[], &boundary(), &[]).map(|_| ())
    });
    assert!(
        refused.reason().contains("not before own serial"),
        "the refusal must name the reason: {}",
        refused.reason()
    );
}

/// The emitted bus legs are the SIDES the memory argument needs. ⚠ This is the half the mutation
/// sweep is structurally blind to: no gate reads the bus multiplicities or directions, so a
/// `.provide`-instead-of-`.query` slip on the closure table or a send/receive swap on the Blum
/// legs would leave every gate green and break the argument silently. It is checked HERE, on the
/// emitted object.
#[test]
fn the_op_log_queries_the_closure_table_and_rides_the_blum_chain() {
    let t = memory_table_air();

    // The closure table: this AIR is the CLIENT; `dregg-ir2-mem-boundary-v1` is the server.
    assert_eq!(t.bus_count_op("ir2_mem_addrs", BusOp::Query), 1);
    assert_eq!(t.bus_count_op("ir2_mem_addrs", BusOp::Provide), 0);
    let closure = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_mem_addrs")
        .expect("one closure query");
    assert_eq!(closure.tuple, vec![TableExpr::Loc(MEM_ADDR)]);
    assert_eq!(closure.mult, TableExpr::Loc(MEM_IS_REAL));

    // The Blum pair: PUBLISH my own image at MY serial, CONSUME the prior image at the CLAIMED
    // one. A swap of the two serial columns here reverses the whole read-consistency argument.
    let send = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Send)
        .expect("one publish");
    assert_eq!(
        send.tuple,
        vec![
            TableExpr::Loc(MEM_ADDR),
            TableExpr::Loc(MEM_VALUE),
            TableExpr::Loc(MEM_SERIAL)
        ]
    );
    let recv = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Receive)
        .expect("one consume");
    assert_eq!(
        recv.tuple,
        vec![
            TableExpr::Loc(MEM_ADDR),
            TableExpr::Loc(MEM_PREV_VALUE),
            TableExpr::Loc(MEM_PREV_SERIAL)
        ],
        "the consumed tuple carries the CLAIMED prior serial — which is exactly why the multiset, \
         not the gap gate, is what refuses a wrapped claim"
    );
    // Both ride at `is_real`, so a pad row contributes NOTHING to the multiset.
    assert_eq!(send.mult, TableExpr::Loc(MEM_IS_REAL));
    assert_eq!(recv.mult, TableExpr::Loc(MEM_IS_REAL));

    // The gathered op log is a RECEIVE (the main AIR sends).
    assert_eq!(t.bus_count_op("ir2_mem_log", BusOp::Receive), 1);
    assert_eq!(t.bus_count_op("ir2_mem_log", BusOp::Send), 0);

    // Two transition-scoped gates (prefix, serial increment), one first-scoped (the anchor).
    assert_eq!(t.gate_count_sel(RowSel::Transition), 2);
    assert_eq!(t.gate_count_sel(RowSel::First), 1);
    assert_eq!(t.gate_count_sel(RowSel::All), 8);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
}
