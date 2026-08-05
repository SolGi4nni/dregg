//! **THE COHORT UNIVERSAL BOUNDARY'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::UMemBoundaryCohort` was a hand-written Rust arm: three booleans, the single-row tooth,
//! two canonical-`none` legs, the domain nibble query, both `ir2_umem_check` Blum legs and the
//! served `ir2_umem_addrs` closure entry. Architectural law #1 says that object is authored in Lean
//! and Rust only interprets. It was not. **That arm is now DELETED**; its author is
//! `metatheory/Dregg2/Circuit/Emit/UMemBoundaryCohortTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-umem-boundary-cohort-v1.json`, and
//! `Ir2Air::LeanTable` walks it.
//!
//! # ⚑ Why this arm's comment mattered more than most
//!
//! This table exists to DROP a `Nodup`-establishing lexicographic comparator — 29 of the general
//! boundary's 38 columns. The entire licence for that is one sentence the arm asserted in prose:
//! *"at most one real row (row 0) … so the declared address list has length ≤ 1 ⇒ `Nodup` is
//! free"*. The Lean file proves it (`every_row_after_the_first_is_a_pad`, under `Coherent`) and
//! then draws the line the prose does not: the tooth bounds the **multiset's** declared list, whose
//! legs ride at `is_real`. It does NOT bound the **served `ir2_umem_addrs` closure table**, whose
//! multiplicity column no gate reads on any row — so a pad row can serve a second `(domain, key)`
//! and every gate stays green. §3 measures that at the deployed evaluator.
//!
//! ⚠ Direction: the containment is the `ir2_umem_check` multiset in a different AIR (a pad
//! publishes no serial-0 cell, so an op at a pad-served key has nothing to consume). Naming which
//! mechanism refuses what is the point.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, TID_UMEM_BOUNDARY, TID_UMEMORY, TableDef2,
    TableSem, UMemBoundaryWitness, UMemOpSpec, VmConstraint2, prove_vm_descriptor2_umem,
    table_air_gates_accept, umem_boundary_rows_for, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::must_refuse_or_unsat_panic;
use dregg_circuit::table_air::TableExpr;
use dregg_circuit::table_air::{BusOp, RowSel, umem_boundary_cohort_table_air};

// The deployed layout, transcribed ONCE here so the assertions below can name a column. These are
// the same numbers `UMemBoundaryCohortTableEmit.lean` derives; a drift on either side reds §1.
const UBC_DOMAIN: usize = 0;
const UBC_KEY: usize = 1;
const UBC_INIT_PRESENT: usize = 2;
const UBC_INIT_VALUE: usize = 3;
const UBC_FIN_PRESENT: usize = 4;
const UBC_FIN_VALUE: usize = 5;
const UBC_FIN_SERIAL: usize = 6;
const UBC_IS_REAL: usize = 7;
const UBC_ADDR_MULT: usize = 8;
const UBC_WIDTH: usize = 9;

/// A single-domain, single-address COHORT descriptor: one `umemOp` write declaring the
/// `umem_boundary_cohort` table sem (the width-9 single-row boundary).
fn cohort_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "umem-cohort-lean-emission-differential".to_string(),
        trace_width: 3,
        public_input_count: 0,
        challenges: 0,
        tables: vec![
            TableDef2 {
                id: TID_UMEMORY,
                name: "umemory".to_string(),
                arity: 8,
                sem: TableSem::UMemory,
            },
            TableDef2 {
                id: TID_UMEM_BOUNDARY,
                name: "umem_boundary_cohort".to_string(),
                arity: 7,
                sem: TableSem::UMemBoundaryCohort,
            },
        ],
        constraints: vec![VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(2),
            domain: 0,
            key: LeanExpr::Var(0),
            present: LeanExpr::Const(1),
            value: LeanExpr::Var(1),
            prev_present: LeanExpr::Const(0),
            prev_value: LeanExpr::Const(0),
            prev_serial: LeanExpr::Const(0),
            kind: MemKind::Write,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// col0 = key, col1 = value, col2 = guard (row 0 only — one declared address).
fn cohort_trace() -> Vec<Vec<BabyBear>> {
    let row = vec![BabyBear::new(5), BabyBear::new(42), BabyBear::ZERO];
    let mut rows = vec![row; 4];
    rows[0][2] = BabyBear::ONE;
    rows
}

/// One declared `(domain 0, key 5)` whose INIT image is `none` — so the canonical-`none` gate is
/// exercised on a real row rather than only on pads.
fn cohort_boundary() -> UMemBoundaryWitness {
    UMemBoundaryWitness {
        addrs: vec![(0, BabyBear::new(5))],
        init_vals: vec![None],
    }
}

fn honest_rows() -> Vec<Vec<BabyBear>> {
    umem_boundary_rows_for(&cohort_desc(), &cohort_trace(), &cohort_boundary())
        .expect("the deployed prover assembles a cohort universal boundary")
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The emitted table declares width 9 and reads the domain at 0,
/// the key at 1, the presence bits at 2/4, the guard at 7 and the served multiplicity at 8. The
/// prover's OWN trace builder writes those columns; this reads them back and checks each against
/// the DECLARED witness, recovered independently rather than off the same row.
///
/// ⚑ The width assertion is the whole point of the specialization: the cohort is a quarter of the
/// general boundary, and that is only sound because of the tooth §3 exercises.
#[test]
fn the_emitted_columns_round_trip_the_single_declared_address() {
    let rows = honest_rows();
    let t = umem_boundary_cohort_table_air();

    assert_eq!(t.width, UBC_WIDTH);
    assert!(rows.iter().all(|r| r.len() == t.width));
    // ⓘ MEASURED, not assumed: one declared address, and the height is `next_pow2(1)` FLOORED AT
    // `MIN_TABLE_HEIGHT = 8` — so ONE real row is followed by SEVEN pads. ⚑ That is what makes the
    // single-row tooth genuinely exercised here rather than vacuous: there are seven successors
    // for it to pin, not zero.
    assert_eq!(rows.len(), 8);
    assert!(rows.len().is_power_of_two());

    assert_eq!(rows[0][UBC_DOMAIN], BabyBear::ZERO, "declared domain");
    assert_eq!(rows[0][UBC_KEY], BabyBear::new(5), "declared key");
    assert_eq!(rows[0][UBC_IS_REAL], BabyBear::ONE);
    // The INIT image is `none`: present = 0 AND the payload is the canonical zero. That pairing is
    // exactly what `canonical_none_is_forced` proves the gate makes mandatory.
    assert_eq!(rows[0][UBC_INIT_PRESENT], BabyBear::ZERO);
    assert_eq!(rows[0][UBC_INIT_VALUE], BabyBear::ZERO);
    // …and the FINAL image is the replayed write: present, value 42, at serial 1.
    assert_eq!(rows[0][UBC_FIN_PRESENT], BabyBear::ONE);
    assert_eq!(rows[0][UBC_FIN_VALUE], BabyBear::new(42));
    assert_eq!(rows[0][UBC_FIN_SERIAL], BabyBear::ONE);
    // The served count is the genuine per-address op count: one write.
    assert_eq!(rows[0][UBC_ADDR_MULT], BabyBear::ONE);

    // …and every pad is a pad, with a zero served count — the discipline the AIR does NOT force
    // (see `a_pad_row_can_still_serve_the_closure_table`) but the honest producer keeps.
    for (i, r) in rows.iter().enumerate().skip(1) {
        assert_eq!(r[UBC_IS_REAL], BabyBear::ZERO, "row {i} is a pad");
        assert_eq!(r[UBC_ADDR_MULT], BabyBear::ZERO, "row {i} serves nothing");
    }

    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every row and every one of the 9 columns, bump the value and ask the
/// REAL deployed evaluator whether the table still accepts.
///
/// The undetected set is pinned EXACTLY, and every member of it is named with the mechanism that
/// protects it instead:
///
/// * `UBC_DOMAIN` — bound by the `ir2_byte` NIBBLE LOOKUP (a domain is `[0, 16)`), which is a bus,
///   not a gate.
/// * `UBC_KEY`, `UBC_FIN_SERIAL`, `UBC_ADDR_MULT` — bound by the `ir2_umem_check` MULTISET and the
///   `ir2_umem_addrs` LogUp balance. ⚑ `UBC_KEY` is read by NO gate at all
///   (`key_is_read_by_no_gate`): the cohort dropped the comparator that used to read it, which is
///   precisely the trade the specialization makes.
/// * `UBC_FIN_VALUE` — the final image's payload. Its canonical-`none` gate is
///   `is_real·(1 − fin_present)·fin_value`, and `fin_present = 1` on the real row, so the gate is
///   off there; on a pad `is_real = 0` turns it off as well. Bound by the multiset.
/// * ⚠ `(pad row, UBC_INIT_VALUE)` — on all SEVEN pads. The canonical-`none` gate rides at
///   `is_real`, so a pad's init payload is bound by nothing. Contained by the multiset (a pad
///   publishes at multiplicity zero). ⓘ On the REAL row that same column IS gated, because this
///   witness declares an ABSENT init cell — the asymmetry is measured, not assumed.
///
/// Anything else landing in the undetected set means the re-emission lost a gate.
#[test]
fn every_gated_cohort_cell_is_still_gated_after_the_cutover() {
    let rows = honest_rows();
    let t = umem_boundary_cohort_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    let mut detected: Vec<(usize, usize)> = Vec::new();
    let mut undetected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
            // TWO bumps: a `+1` on a boolean column that is honestly ZERO lands on 1, which the
            // boolean gate still accepts.
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

    let mut expected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
            // Bound by a BUS on every row: the domain nibble lookup, the key + final image + the
            // served count on the multiset / LogUp balance.
            let bus_bound = matches!(
                col,
                UBC_DOMAIN | UBC_KEY | UBC_FIN_VALUE | UBC_FIN_SERIAL | UBC_ADDR_MULT
            );
            // ⓘ On a PAD the init payload is un-gated too: its canonical-`none` leg rides at
            // `is_real`. On the REAL row it IS gated, because that row declares an ABSENT init
            // cell — which is why the witness was chosen with `init_vals: vec![None]`.
            let pad_init = row > 0 && col == UBC_INIT_VALUE;
            if bus_bound || pad_init {
                expected.push((row, col));
            }
        }
    }
    assert_eq!(
        undetected, expected,
        "the undetected set is not exactly {{the nibble-, multiset- and LogUp-bound columns}} — \
         either a gate was lost in the Lean re-emission, or a gate appeared where a bus is \
         supposed to be the mechanism. undetected: {undetected:?}"
    );

    // ⚑ The columns that MUST be caught, named with the gate that catches them.
    assert!(
        detected.contains(&(0, UBC_IS_REAL)),
        "the row guard's boolean gate"
    );
    assert!(
        detected.contains(&(0, UBC_INIT_PRESENT)),
        "the init presence boolean + the canonical-`none` leg"
    );
    assert!(
        detected.contains(&(0, UBC_FIN_PRESENT)),
        "the final presence boolean"
    );
    assert!(
        detected.contains(&(0, UBC_INIT_VALUE)),
        "the canonical-`none` gate on the ABSENT init image — the one that makes (present, value) \
         a faithful `Option`"
    );

    println!(
        "MEASURED: {}/{} cohort cells are gated by the Lean emission; the undetected {} are the \
         nibble-, multiset- and LogUp-bound columns",
        detected.len(),
        detected.len() + undetected.len(),
        undetected.len()
    );
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** An honest single-address cohort witness proves and verifies through the
/// Lean-emitted AIR — and the instance set really is the SPECIALIZED one (4 committed tables, no
/// chip), so this measures the perf lever the cohort exists for and not the general boundary.
#[test]
fn an_honest_cohort_proves_and_verifies_through_the_lean_emission() {
    let desc = cohort_desc();
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &cohort_trace(),
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &cohort_boundary(),
    )
    .expect("an honest cohort witness must prove through the Lean-emitted boundary AIR");
    assert_eq!(
        proof.degree_bits.len(),
        4,
        "cohort commits main + byte + umemory + umem_boundary_cohort (no chip)"
    );
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES.** Each forgery keeps the shape and changes only
/// what the table SAYS.
#[test]
fn a_forged_cohort_declaration_is_refused_by_the_emitted_gates() {
    let rows = honest_rows();
    let t = umem_boundary_cohort_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // (a) ⚑ A NON-CANONICAL `none`: claim the init cell absent while its payload is nonzero. That
    //     would make (present, value) a two-to-one encoding of `Option`, and the canonical-`none`
    //     gate `is_real·(1 − init_present)·init_value` refuses it.
    let mut non_canonical = rows.clone();
    non_canonical[0][UBC_INIT_VALUE] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &non_canonical),
        "the emitted canonical-`none` gate must refuse an absent cell with a payload"
    );

    // (b) ⚑ A NON-BOOLEAN GUARD. The row guard multiplies every Blum leg; a guard of 2 would let
    //     one declared address publish its init image TWICE into the multiset.
    let mut doubled = rows.clone();
    doubled[0][UBC_IS_REAL] = BabyBear::new(2);
    assert!(
        !table_air_gates_accept(&t, &doubled),
        "the emitted boolean gate must refuse a guard of 2"
    );

    // (c) ⚑ THE SINGLE-ROW TOOTH, at the evaluator. Two rows, the second real — the shape the
    //     specialization must never admit, because `Nodup` of a two-address list is not free.
    //     ⓘ Built by DUPLICATING the prover's own honest row rather than hand-assembling one, so
    //     every other column stays exactly what `build_traces` wrote.
    let mut two_real = vec![rows[0].clone(), rows[0].clone()];
    two_real[1][UBC_KEY] = BabyBear::new(9);
    assert!(
        !table_air_gates_accept(&t, &two_real),
        "the emitted single-row tooth must refuse a SECOND real row — this gate is the entire \
         licence for dropping the general boundary's Nodup comparator"
    );
}

/// ⚑ **THE LINE THE ARM'S COMMENT DID NOT DRAW, MEASURED AT THE DEPLOYED EVALUATOR.**
///
/// `UMemBoundaryCohortTableEmit.a_pad_row_can_still_serve_the_closure_table` proves in Lean that a
/// PAD row may serve a second `(domain, key)` to `ir2_umem_addrs` at a nonzero multiplicity while
/// every gate holds. This is the same statement through the REAL `Ir2Air::LeanTable` evaluator.
///
/// ⚠ Read the direction. The single-row tooth is not weakened: the pad's `is_real` is still 0, so
/// it declares NOTHING to the `ir2_umem_check` multiset and the `Nodup` argument the cohort rests
/// on is untouched. What this shows is that "the declared address list has length ≤ 1" is a
/// statement about the MULTISET, not about the closure table this AIR serves — and the containment
/// for the latter is the multiset one object further out (an op at a pad-served key has no serial-0
/// cell to consume). A soundness story that read the tooth as bounding the served table would be
/// resting on a leg this AIR does not have.
#[test]
fn a_pad_row_can_still_serve_the_closure_table() {
    let rows = honest_rows();
    let t = umem_boundary_cohort_table_air();

    // Row 0 is the prover's own honest real row; row 1 is a PAD that serves a different key at
    // multiplicity 7.
    let mut pad = vec![BabyBear::ZERO; UBC_WIDTH];
    pad[UBC_DOMAIN] = BabyBear::ZERO;
    pad[UBC_KEY] = BabyBear::new(9);
    pad[UBC_ADDR_MULT] = BabyBear::new(7);
    let two = vec![rows[0].clone(), pad];
    assert!(
        table_air_gates_accept(&t, &two),
        "MEASURED: the emitted gates ACCEPT a pad row serving a SECOND (domain, key) at \
         multiplicity 7 — the single-row tooth bounds the multiset's declared list, not the served \
         closure table (UMemBoundaryCohortTableEmit §4b)"
    );
    assert_eq!(two[1][UBC_IS_REAL], BabyBear::ZERO, "…and it is a PAD");
}

/// The prover-level pole, stated at ITS OWN resolution: the ASSEMBLER refuses a two-address cohort
/// witness. ⚠ That is a completeness-of-refusal fact about `build_traces`, NOT a gate verdict — the
/// gate verdict for the same shape is `a_forged_cohort_declaration_is_refused_by_the_emitted_gates`
/// case (c). Both exist because they refuse for different reasons and either could rot alone.
#[test]
fn a_two_address_cohort_is_refused_by_the_deployed_assembler() {
    let desc = cohort_desc();
    let refused = must_refuse_or_unsat_panic("a two-address cohort boundary witness", || {
        prove_vm_descriptor2_umem(
            &desc,
            &cohort_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness {
                addrs: vec![(0, BabyBear::new(5)), (0, BabyBear::new(6))],
                init_vals: vec![None, None],
            },
        )
        .map(|_| ())
    });
    assert!(
        refused.reason().contains("at most one"),
        "the refusal must name the single-row discipline: {}",
        refused.reason()
    );
}

/// The emitted bus legs are the SIDES the universal-memory argument needs. ⚠ This is the half the
/// mutation sweep is structurally blind to.
#[test]
fn the_cohort_serves_the_closure_table_and_anchors_the_blum_chain() {
    let t = umem_boundary_cohort_table_air();

    // The closure table: this AIR is the SERVER, `Ir2Air::UMemory` is the client.
    assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Provide), 1);
    assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Query), 0);
    let serve = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_addrs")
        .expect("one served address entry");
    assert_eq!(
        serve.tuple,
        vec![TableExpr::Loc(UBC_DOMAIN), TableExpr::Loc(UBC_KEY)]
    );
    assert_eq!(serve.mult, TableExpr::Loc(UBC_ADDR_MULT));

    // The Blum pair, in the right directions and at the right anchor.
    let send = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Send)
        .expect("one init publish");
    assert_eq!(
        send.tuple,
        vec![
            TableExpr::Loc(UBC_DOMAIN),
            TableExpr::Loc(UBC_KEY),
            TableExpr::Loc(UBC_INIT_PRESENT),
            TableExpr::Loc(UBC_INIT_VALUE),
            TableExpr::Const(0)
        ],
        "the INIT cell is published at serial ZERO — the anchor every read chain bottoms out in"
    );
    let recv = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Receive)
        .expect("one final consume");
    assert_eq!(recv.tuple.len(), 5);
    assert_eq!(recv.tuple[4], TableExpr::Loc(UBC_FIN_SERIAL));
    // ⚑ BOTH ride at `is_real`, which is what makes a pad declare NOTHING — the fact the
    // single-row tooth's `Nodup` argument actually rests on.
    assert_eq!(send.mult, TableExpr::Loc(UBC_IS_REAL));
    assert_eq!(recv.mult, TableExpr::Loc(UBC_IS_REAL));

    // The domain nibble query rides at a CONSTANT: a pad's domain is range-bound too.
    let nibble = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_byte")
        .expect("one domain nibble query");
    assert_eq!(nibble.op, BusOp::Query);
    assert_eq!(nibble.mult, TableExpr::Const(1));

    // Exactly one transition-scoped gate — the single-row tooth — and five unfiltered ones.
    assert_eq!(t.gate_count_sel(RowSel::Transition), 1);
    assert_eq!(t.gate_count_sel(RowSel::All), 5);
    assert_eq!(t.gate_count_sel(RowSel::First), 0);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
}
