//! **THE ELEVENTH AND LAST HAND-WRITTEN TABLE ARM NOW COMES FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::ExactPublicTable` was a hand-written Rust arm: one `assert_zero` pinning a committed
//! capacity column to a preprocessed one, plus a `table_entry` leg serving the manifest tuple.
//! Architectural law #1 says that object is authored in Lean and Rust only interprets. It was not.
//! **That arm is now DELETED — the enum VARIANT, not just its body** — and `Ir2Air` is
//! `Main | LeanTable`. Its author is
//! `metatheory/Dregg2/Circuit/Emit/ExactPublicTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-exact-public-v1.json`, and `Ir2Air::LeanTable` walks
//! it.
//!
//! ⚑ **THIS IS THE FIRST PREPROCESSED-READING TABLE AIR, so this is the first differential that
//! sweeps the PREPROCESSED MATRIX.** Every earlier sweep in this burn-down ran over the committed
//! trace alone, which was complete for the ten singleton tables (they declare zero preprocessed
//! columns, pinned in `ir2_preprocessed_sweep_harness.rs`) and would have been BLIND here: this
//! table's manifest values, its table id and its pinned multiplicities live *entirely* in the
//! preprocessed matrix, and its one gate reads nothing else. A committed-only sweep would have
//! reported one gated column out of one and seen none of the object.
//!
//! # The four questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    capacity column and the whole preprocessed row OUT of the deployed instance builder.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2/§3 — per-cell mutation
//!    sweeps over BOTH matrices through the REAL deployed evaluator, with the undetected set pinned
//!    EXACTLY rather than bounded.)
//! 3. **Do both poles hold at the deployed prover?** (§4.)
//! 4. ⚑ **Does the new bus shape separate two tables that now SHARE a bus?** (§5 — the tooth the
//!    port's one design change has to buy.)
//!
//! # ⚑ WHAT THE PORT CHANGED ON THE WIRE, and why
//!
//! The deployed shape spent one LogUp bus per declared table, `ir2_exact_public_{table_id}`, and
//! the served tuple was the manifest row. A table id is a number no Lean artifact can know, so a
//! per-arity emitted family could not name its own bus — which `TableAirIR` §7 item 3 recorded as
//! the reason "emit 64 fixed artifacts" was not a way out.
//!
//! The fix is not a substitution hole in a wire string. It is to stop spending a STRING on a
//! separation a FIELD can carry: the bus is now `ir2_exact_public_a{arity}` and the TABLE ID is
//! preprocessed column 0, the first field of every served tuple and of every query.
//! `the_id_field_separates_two_tables_sharing_one_bus` is the measurement that this is a
//! translation and not a weakening — and it is the tooth that would go red if the id were dropped
//! from the tuple, which is the one edit that would make the two tables' capacity pool.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, LookupSpec, TableDef2, TableSem, VmConstraint2,
    exact_public_instance_for, ir2_air_gates_accept, prove_vm_descriptors2_batch,
    verify_vm_descriptors2_batch,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{
    Refusal, assert_bus_imbalance_not_constraint, must_refuse_or_unsat_panic,
};
use dregg_circuit::table_air::{BusOp, RowSel, TableExpr, exact_public_table_air_for};
use p3_air::BaseAir;

/// Two declared exact-public tables, both at ARITY 2 — which since the port means both on the SAME
/// bus (`ir2_exact_public_a2`), separated only by the id field. Ids are above `TID_P2_STATE16`,
/// which `check_descriptor2` requires.
const TID_A: usize = 100;
const TID_B: usize = 101;

/// The committed preprocessed layout of an arity-2 member: `[table_id, v0, v1, multiplicity]`.
const EP_ID: usize = 0;
const EP_V0: usize = 1;
const EP_V1: usize = 2;
const EP_MULT: usize = 3;
const EP_PREP_WIDTH: usize = 4;

/// The main trace height, and therefore the query count on EACH table: `Ir2Air::Main` emits a
/// declared exact-public lookup on every row at multiplicity one, so a balanced manifest declares
/// exactly `HEIGHT` rows.
const HEIGHT: usize = 4;

/// A descriptor declaring TWO arity-2 exact-public manifests and querying each once per row.
///
/// Table A serves `(3, 4)` four times; table B serves `(5, 6)` four times. Both manifests declare a
/// DUPLICATE row on purpose, so the pinned multiplicity is genuinely `4` rather than `1`: against a
/// manifest of distinct rows the pin gate reads `committed − 1` and a sweep cannot tell a pinned
/// column from a constant one.
fn two_table_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "exactpublic-lean-emission-differential".to_string(),
        trace_width: 4,
        public_input_count: 0,
        challenges: 0,
        tables: vec![
            TableDef2 {
                id: TID_A,
                name: "manifest_a".to_string(),
                arity: 2,
                sem: TableSem::ExactPublicRows {
                    rows: vec![vec![3, 4]; HEIGHT],
                },
            },
            TableDef2 {
                id: TID_B,
                name: "manifest_b".to_string(),
                arity: 2,
                sem: TableSem::ExactPublicRows {
                    rows: vec![vec![5, 6]; HEIGHT],
                },
            },
        ],
        constraints: vec![
            VmConstraint2::Lookup(LookupSpec {
                table: TID_A,
                tuple: vec![LeanExpr::Var(0), LeanExpr::Var(1)],
            }),
            VmConstraint2::Lookup(LookupSpec {
                table: TID_B,
                tuple: vec![LeanExpr::Var(2), LeanExpr::Var(3)],
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// The honest main trace: every row offers A's tuple in columns 0/1 and B's in columns 2/3.
fn honest_trace() -> Vec<Vec<BabyBear>> {
    vec![
        vec![
            BabyBear::new(3),
            BabyBear::new(4),
            BabyBear::new(5),
            BabyBear::new(6),
        ];
        HEIGHT
    ]
}

// -------------------------------------------------------------------------------------------
// §0 — THE EMITTED FAMILY, AT THE DEPLOYED DECODER.
// -------------------------------------------------------------------------------------------

/// The Lean-emitted family decodes at the shape the deleted arm had, at every arity: ONE gate, ONE
/// bus leg on the SERVING side, one committed column, and `arity + 2` preprocessed ones.
///
/// ⚠ `.query` here instead of `.provide` would make the bus unsatisfiable in one direction and
/// vacuous in the other with NO gate involved, which is why the side is pinned and not assumed.
#[test]
fn the_emitted_family_has_the_deleted_arms_shape_at_every_arity() {
    let family = dregg_circuit::table_air::exact_public_table_air_family();
    assert_eq!(family.len(), 97, "one member per admissible arity");

    for (i, t) in family.iter().enumerate() {
        let arity = i + 1;
        assert_eq!(t.name, format!("dregg-ir2-exact-public-a{arity}-v1"));
        assert_eq!(t.width, 1, "one committed column: the capacity");
        assert_eq!(t.prep_width, arity + 2, "[id, values.., multiplicity]");
        assert_eq!(t.def_count(), 0, "no sharing in a one-gate table");
        assert_eq!(t.gates.len(), 1, "the pin, and nothing else");
        assert_eq!(t.gate_count_sel(RowSel::All), 1, "unfiltered");
        assert_eq!(t.interactions.len(), 1);

        let bus = format!("ir2_exact_public_a{arity}");
        assert_eq!(t.bus_count_op(&bus, BusOp::Provide), 1, "it SERVES");
        assert_eq!(t.bus_count_op(&bus, BusOp::Query), 0, "it does not ask");

        // The served tuple is the id then the values — `arity + 1` fields, which is the LogUp
        // field count the query side must present.
        let leg = &t.interactions[0];
        assert_eq!(leg.tuple.len(), arity + 1);
        for (c, e) in leg.tuple.iter().enumerate() {
            assert_eq!(
                *e,
                TableExpr::Prep(c),
                "tuple field {c} of arity {arity} must be preprocessed column {c}"
            );
        }
        // …and the capacity it rides at is the COMMITTED column.
        assert_eq!(leg.mult, TableExpr::Loc(0));
    }

    // The arity ceiling is fail-closed in both directions. ⚑ MOVED 64 -> 97 on 2026-08-06: this
    // boundary pin is the thing that went red when the family was widened, which is what a pin is
    // for. `descriptor_ir2::MAX_EXACT_PUBLIC_ARITY` is the other side.
    assert!(exact_public_table_air_for(0).is_err(), "arity 0");
    assert!(exact_public_table_air_for(98).is_err(), "past the family");
    assert!(exact_public_table_air_for(97).is_ok(), "the last member");
    assert!(
        exact_public_table_air_for(64).is_ok(),
        "and the OLD ceiling is still served — the raise widened, it did not move"
    );
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP, out of the deployed instance builder.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY.** The instance the deployed batch assembler builds — the committed capacity
/// column and the preprocessed matrix the VERIFIER recomputes — is accepted by the REAL evaluator,
/// and the preprocessed row really carries `[id, values, multiplicity]`.
#[test]
fn the_deployed_instance_round_trips_through_the_lean_emission() {
    let desc = two_table_desc();
    let (air, main_rows, prep_rows) =
        exact_public_instance_for(&desc, TID_A).expect("the descriptor declares it");

    // ⚑ IT IS A LEAN TABLE NOW. The hand-written arm is gone, so this is the emitted artifact.
    let t = air
        .lean_table_air()
        .expect("the exact-public instance is a Lean-authored table AIR");
    assert_eq!(t.name, "dregg-ir2-exact-public-a2-v1");
    assert_eq!(
        <Ir2Air as BaseAir<p3_baby_bear::BabyBear>>::preprocessed_width(&air),
        EP_PREP_WIDTH,
        "the AIR's own declaration is what the sweep oracle keys on"
    );

    // ONE distinct row declared four times ⇒ committed height is the `MIN_EXACT_PUBLIC_HEIGHT`
    // floor of 2: one real row and one pad.
    assert_eq!(main_rows.len(), 2);
    assert_eq!(prep_rows.len(), main_rows.len());
    assert!(main_rows.iter().all(|r| r.len() == 1));
    assert!(prep_rows.iter().all(|r| r.len() == EP_PREP_WIDTH));

    // ⚑ THE ROUND-TRIP. The real row carries the table id, the declared tuple, and the DEDUPLICATED
    // multiplicity; the committed capacity column MIRRORS the pin.
    assert_eq!(prep_rows[0][EP_ID], BabyBear::new(TID_A as u32));
    assert_eq!(prep_rows[0][EP_V0], BabyBear::new(3));
    assert_eq!(prep_rows[0][EP_V1], BabyBear::new(4));
    assert_eq!(
        prep_rows[0][EP_MULT],
        BabyBear::new(HEIGHT as u32),
        "declared four times"
    );
    assert_eq!(main_rows[0][0], prep_rows[0][EP_MULT]);

    // …and the pad row is all zeros on both sides, so it offers no capacity and names no real
    // table's tuple (id 0 is not an admissible exact-public wire id).
    assert!(prep_rows[1].iter().all(|&x| x == BabyBear::ZERO));
    assert_eq!(main_rows[1][0], BabyBear::ZERO);

    assert!(
        ir2_air_gates_accept(&air, &main_rows, &prep_rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the deployed instance"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE COMMITTED SWEEP.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS THE PIN LOST?** Every cell of the one committed column is CAUGHT — including the PAD
/// row's, where the declared multiplicity is zero.
///
/// ⓘ Free capacity here would demote the exact-public permutation to a CONTAINMENT
/// (`ExactPublicManifest`'s own doc), so "the committed column is pinned" is a soundness claim.
/// The Lean side proves it in both directions and proves the gate is an EQUALITY rather than a
/// `≤` (`the_pin_refuses_a_short_capacity`); this is the same statement at the deployed evaluator.
#[test]
fn every_committed_capacity_cell_is_caught() {
    let desc = two_table_desc();
    let (air, main_rows, prep_rows) = exact_public_instance_for(&desc, TID_A).expect("declared");
    assert!(
        ir2_air_gates_accept(&air, &main_rows, &prep_rows),
        "baseline"
    );

    let mut undetected: Vec<usize> = Vec::new();
    for row in 0..main_rows.len() {
        let caught = [1u32, 2u32].iter().any(|&d| {
            let mut mutated = main_rows.clone();
            mutated[row][0] = mutated[row][0] + BabyBear::new(d);
            !ir2_air_gates_accept(&air, &mutated, &prep_rows)
        });
        if !caught {
            undetected.push(row);
        }
    }
    assert!(
        undetected.is_empty(),
        "rows {undetected:?} may offer free capacity — the pin gate was lost in the re-emission"
    );
}

// -------------------------------------------------------------------------------------------
// §3 — ⚑ THE PREPROCESSED SWEEP. The only thing this table reads, and the first time a sweep in
//      this burn-down reaches it.
// -------------------------------------------------------------------------------------------

/// **⚑ THE MEASUREMENT NO EARLIER SWEEP COULD MAKE.** Per row, per PREPROCESSED column, bump the
/// cell and ask the REAL deployed evaluator whether the instance still accepts.
///
/// The undetected set is pinned EXACTLY, and it is the interesting half:
///
/// * **the multiplicity column is gated on every row** — that is the one gate, read from the other
///   side. A sweep of the committed column alone (§2) cannot distinguish "the gate reads the
///   preprocessed pin" from "the gate reads a constant".
/// * **the table id and every manifest VALUE column are gated on NO row** — and that is correct,
///   not a hole. They are BUS-bound: their whole discipline is that the verifier recomputes this
///   matrix from the descriptor and commits it, so no single-AIR gate check can decide them. The
///   Lean side says the same thing about the emitted object rather than about a witness
///   (`the_gates_bind_no_manifest_value`, `the_gates_bind_no_table_id`).
///
/// ⚠ Stating that exactly is the point. An instrument reporting "4 of 4 preprocessed columns
/// gated" would be lying about which mechanism protects what — and one reporting "0 of 4", which
/// is what an empty preprocessed window produced before `ir2_air_gates_accept` learned to refuse
/// one, would have been lying about all of it while looking clean.
#[test]
fn the_preprocessed_sweep_pins_the_undetected_set_exactly() {
    let desc = two_table_desc();
    let (air, main_rows, prep_rows) = exact_public_instance_for(&desc, TID_A).expect("declared");
    assert!(
        ir2_air_gates_accept(&air, &main_rows, &prep_rows),
        "baseline"
    );

    let mut detected: Vec<(usize, usize)> = Vec::new();
    let mut undetected: Vec<(usize, usize)> = Vec::new();
    for row in 0..prep_rows.len() {
        for col in 0..EP_PREP_WIDTH {
            // TWO bumps, as every sweep in this burn-down uses: a `+1` on a column whose honest
            // value is adjacent to another admissible one reports a live gate as dead.
            let caught = [1u32, 2u32].iter().any(|&d| {
                let mut mutated = prep_rows.clone();
                mutated[row][col] = mutated[row][col] + BabyBear::new(d);
                !ir2_air_gates_accept(&air, &main_rows, &mutated)
            });
            if caught {
                detected.push((row, col));
            } else {
                undetected.push((row, col));
            }
        }
    }

    // ⚑ THE PIN BITES ON EVERY ROW, pad included.
    for row in 0..prep_rows.len() {
        assert!(
            detected.contains(&(row, EP_MULT)),
            "row {row}'s pinned multiplicity is not read by any gate — detected: {detected:?}"
        );
    }

    // ⚑ AND THE UNDETECTED SET IS EXACTLY THE BUS-BOUND COLUMNS: the id and the two values, on
    // every row. Nothing else may be undetected, and nothing else may be detected.
    let expected: Vec<(usize, usize)> = (0..prep_rows.len())
        .flat_map(|r| [(r, EP_ID), (r, EP_V0), (r, EP_V1)])
        .collect();
    assert_eq!(
        undetected, expected,
        "the undetected preprocessed set is not exactly {{id, values}} — either the pin was lost \
         or a gate appeared where the LogUp balance is supposed to be the mechanism"
    );

    println!(
        "MEASURED: preprocessed sweep over {} rows x {EP_PREP_WIDTH} columns — {} gated, {} \
         bus-bound",
        prep_rows.len(),
        detected.len(),
        undetected.len()
    );
}

// -------------------------------------------------------------------------------------------
// §4 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

fn prove_and_verify(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let refs: Vec<&[Vec<BabyBear>]> = vec![trace];
    let pis = vec![vec![]];
    let proof = prove_vm_descriptors2_batch(std::slice::from_ref(desc), &refs, &pis)?;
    verify_vm_descriptors2_batch(std::slice::from_ref(desc), &proof, &pis)
}

/// **THE TRUE POLE.** The honest witness proves AND the DEPLOYED verifier accepts, with both
/// manifests served by Lean-emitted AIRs on one shared arity-2 bus.
#[test]
fn the_honest_two_manifest_batch_proves_and_verifies() {
    prove_and_verify(&two_table_desc(), &honest_trace())
        .expect("the honest exact-public batch must prove and verify");
}

/// **THE FALSE POLE.** A row querying a tuple NO manifest declares is refused at the deployed
/// prover — by the bus, which is the mechanism §3 says owns the manifest values.
#[test]
fn an_undeclared_tuple_is_refused() {
    let desc = two_table_desc();
    let mut trace = honest_trace();
    trace[1][0] = BabyBear::new(99); // A is queried for (100, 99, 4), which nothing serves.

    let refused = must_refuse_or_unsat_panic("a query for an undeclared manifest row", || {
        prove_and_verify(&desc, &trace)
    });
    let reason = match &refused {
        Refusal::Err(e) => e.clone(),
        Refusal::UnsatPanic(m) => m.clone(),
    };
    assert_bus_imbalance_not_constraint("a query for an undeclared manifest row", &reason);
}

/// **THE FALSE POLE, THE OTHER MECHANISM.** A committed capacity column that does not mirror the
/// declared multiplicity is refused by the GATE — the pin, at the deployed prover rather than at
/// the row-local oracle.
///
/// ⚠ The prover builds that column itself from the descriptor, so this forgery is reached by
/// declaring a manifest whose multiplicity the trace does not match: the descriptor declares three
/// copies of A's row while the trace queries four, so the served capacity and the query count
/// disagree. `assert_violated_constraint_not_bus` is deliberately NOT applied — this is a BUS
/// verdict and saying which one it is, is the point.
#[test]
fn a_manifest_whose_capacity_does_not_cover_the_queries_is_refused() {
    let mut desc = two_table_desc();
    match &mut desc.tables[0].sem {
        TableSem::ExactPublicRows { rows } => rows.truncate(HEIGHT - 1),
        _ => unreachable!(),
    }
    let refused = must_refuse_or_unsat_panic("a manifest one capacity short", || {
        prove_and_verify(&desc, &honest_trace())
    });
    let reason = match &refused {
        Refusal::Err(e) => e.clone(),
        Refusal::UnsatPanic(m) => m.clone(),
    };
    assert_bus_imbalance_not_constraint("a manifest one capacity short", &reason);
}

/// **THE GATE'S OWN FALSE POLE, at the deployed evaluator rather than the prover.** The pin is a
/// constraint, so a forged capacity column must be refused by a VIOLATED CONSTRAINT and not by a
/// bus verdict — the distinction `assert_violated_constraint_not_bus` exists to keep honest.
///
/// The deployed prover rebuilds the committed column from the descriptor, so a forged one cannot
/// be handed to `prove_vm_descriptors2_batch`; the deployed EVALUATOR can be handed one, and
/// `ir2_air_gates_accept` is that evaluator. This is the same split every table differential in
/// this burn-down draws between the gate arm and the bus arm.
#[test]
fn a_forged_capacity_column_violates_the_pin_at_the_deployed_evaluator() {
    let desc = two_table_desc();
    let (air, main_rows, prep_rows) = exact_public_instance_for(&desc, TID_A).expect("declared");

    let mut forged = main_rows.clone();
    forged[0][0] = forged[0][0] + BabyBear::ONE;
    assert!(
        !ir2_air_gates_accept(&air, &forged, &prep_rows),
        "a capacity column that does not mirror the declared multiplicity must be refused"
    );

    // …and the pad row, which is where a "pads contribute nothing" reading would be weakest: the
    // Lean file's `a_pad_shaped_row_is_admitted_at_any_capacity_the_matrix_declares` says the AIR
    // has no opinion about which rows are pads, and this says the matrix's zero still binds.
    let mut forged_pad = main_rows.clone();
    forged_pad[1][0] = BabyBear::ONE;
    assert!(
        !ir2_air_gates_accept(&air, &forged_pad, &prep_rows),
        "a pad row offering capacity must be refused — the pin reads the matrix's zero"
    );
}

// -------------------------------------------------------------------------------------------
// §5 — ⚑ THE TOOTH THE ONE DESIGN CHANGE HAS TO BUY.
// -------------------------------------------------------------------------------------------

/// **⚑ TWO TABLES NOW SHARE A BUS, AND THE ID FIELD IS WHAT KEEPS THEM APART.**
///
/// Before the port each declared exact-public table had its own bus, `ir2_exact_public_{table_id}`.
/// After it, every arity-2 table sits on `ir2_exact_public_a2` and the table id is the first field
/// of the tuple. That is a translation of the separation from a STRING into a FIELD, and it is only
/// a translation if a query tagged for table A cannot be balanced by table B's capacity.
///
/// This measures exactly that: the trace queries A with a tuple only B declares. Under the deployed
/// shape it is REFUSED. ⚠ Under a version of the port that dropped the id from the tuple — the one
/// edit that makes the change a weakening rather than a translation — A's query would read `(5, 6)`
/// on `ir2_exact_public_a2` and B's server offers exactly `(5, 6)` on the same bus, so the batch
/// would BALANCE and this forgery would be ACCEPTED.
#[test]
fn the_id_field_separates_two_tables_sharing_one_bus() {
    let desc = two_table_desc();

    // Sanity: they really are on ONE bus now, and they really are different tables.
    let (air_a, _, prep_a) = exact_public_instance_for(&desc, TID_A).expect("A");
    let (air_b, _, prep_b) = exact_public_instance_for(&desc, TID_B).expect("B");
    let bus_of = |a: &Ir2Air| {
        a.lean_table_air().expect("Lean table").interactions[0]
            .bus
            .clone()
    };
    assert_eq!(bus_of(&air_a), "ir2_exact_public_a2");
    assert_eq!(bus_of(&air_a), bus_of(&air_b), "ONE bus, two tables");
    assert_ne!(
        prep_a[0][EP_ID], prep_b[0][EP_ID],
        "…and the id field is what tells them apart"
    );

    // ⚑ THE FORGERY: every row queries A with B's tuple. A's own capacity goes unconsumed and A's
    // queries go unserved; B cannot cover them, because B serves `(101, 5, 6)` and A asks for
    // `(100, 5, 6)`.
    let mut trace = honest_trace();
    for row in &mut trace {
        row[0] = BabyBear::new(5);
        row[1] = BabyBear::new(6);
    }
    let refused = must_refuse_or_unsat_panic("table A querying table B's row", || {
        prove_and_verify(&desc, &trace)
    });
    let reason = match &refused {
        Refusal::Err(e) => e.clone(),
        Refusal::UnsatPanic(m) => m.clone(),
    };
    assert_bus_imbalance_not_constraint("table A querying table B's row", &reason);
}

/// ⚠ **A COMMENT-ONLY CLAIM THE PORT SURFACED, AND IT IS FALSE BY 2x — AND WAS ALREADY FALSE.**
///
/// `MAX_EXACT_PUBLIC_CELLS`'s doc said *"`2^25` cells bounds the preprocessed commitment at ~134 MB
/// of `BabyBear`"*. It does not. The cap counts `rows.len() * arity`; the matrix the verifier
/// actually materializes and commits is `next_pow2(distinct) * prep_width`, which is WIDER than
/// `arity` (the pinned multiplicity, and since the port the table id) and TALLER than `rows.len()`
/// (`next_pow2` rounds a cap-saturating row count up to the next power of two).
///
/// This computes the worst admissible case from the three constants rather than asserting the
/// sentence, so a change to any of them re-states the real figure instead of leaving a stale one.
/// ⓘ The bound is an ALLOCATION bound, not a soundness one, and the cap is deliberately left where
/// it is: tightening it to the materialized size would refuse manifests the four-way `⟨s, srs.g⟩`
/// cut is sized for, which is a workload decision and not this port's.
#[test]
fn the_preprocessed_allocation_bound_is_measured_not_asserted() {
    const MAX_ROWS: usize = 1 << 21;
    const MAX_CELLS: usize = 1 << 25;
    const MAX_ARITY: usize = 64;

    let worst = |extra_cols: usize| -> (usize, usize) {
        let mut best = (0usize, 0usize);
        for arity in 1..=MAX_ARITY {
            let rows = MAX_ROWS.min(MAX_CELLS / arity);
            let height = rows.next_power_of_two().max(2);
            let cells = height * (arity + extra_cols);
            if cells > best.0 {
                best = (cells, arity);
            }
        }
        best
    };

    // The deployed layout: `[id, values.., mult]` — `arity + 2`.
    let (cells, arity) = worst(2);
    assert_eq!(
        (cells, arity),
        (69_206_016, 31),
        "the worst admissible preprocessed commitment moved; re-state the real figure in \
         `MAX_EXACT_PUBLIC_CELLS`'s doc rather than leaving the old one"
    );
    assert!(
        cells > 2 * MAX_CELLS,
        "the cap does not bound the committed matrix — it is {:.2}x it",
        cells as f64 / MAX_CELLS as f64
    );

    // …and the pre-port layout, so the claim "this port widened an already-wrong bound by 3%" is
    // measured rather than remembered. The sentence was wrong before the table id existed.
    let (before, _) = worst(1);
    assert_eq!(before, 67_108_864, "the pre-port worst case");
    assert_eq!(
        before,
        2 * MAX_CELLS,
        "the pre-port worst case was EXACTLY 2x the cap, not merely over it — the port did not \
         introduce this wound, it widened it by one column"
    );

    println!(
        "MEASURED: worst admissible preprocessed commitment {cells} cells ({:.1} MB) at arity \
         {arity} — against the {MAX_CELLS}-cell cap's stated {:.1} MB",
        cells as f64 * 4.0 / 1e6,
        MAX_CELLS as f64 * 4.0 / 1e6
    );
}

/// ⓘ **AND THE HAZARD THAT WAS ALREADY THERE IS STILL THERE, NOT WIDER.**
///
/// `prove_vm_descriptors2_batch` documents it: two descriptors in ONE batch declaring the same
/// exact-public WIRE ID share a bus, so one's spare capacity can cancel the other's extra query.
/// The port does not touch that — same id still means the same tuples — and this asserts the shape
/// of the claim rather than leaving it as prose: two instances at the same arity and the same id
/// offer IDENTICAL tuples, while two at the same arity and different ids never do.
#[test]
fn the_co_batch_pooling_hazard_is_preserved_not_widened() {
    let desc = two_table_desc();
    let (_, _, prep_a) = exact_public_instance_for(&desc, TID_A).expect("A");
    let (_, _, prep_b) = exact_public_instance_for(&desc, TID_B).expect("B");

    // Different ids at the same arity: the served tuples differ in field 0, so they cannot pool.
    assert_ne!(prep_a[0][..=EP_V1], prep_b[0][..=EP_V1]);

    // The SAME id at the same arity, in a second descriptor: identical tuples, which is the
    // documented pooling. Nothing here fixes it; it is asserted so the claim is measured.
    let mut twin = two_table_desc();
    twin.name = "exactpublic-lean-emission-differential-twin".to_string();
    let (_, _, prep_twin) = exact_public_instance_for(&twin, TID_A).expect("the twin's A");
    assert_eq!(
        prep_a[0][..=EP_V1],
        prep_twin[0][..=EP_V1],
        "two descriptors declaring one wire id still pool — the documented hazard, unchanged"
    );
}

/// ⚠ **AND THE THING THIS FILE CANNOT MEASURE, SAID RATHER THAN LEFT IMPLIED.**
///
/// Every other table differential in this burn-down pairs a bus-verdict tooth with a
/// CONSTRAINT-verdict one (`assert_violated_constraint_not_bus`), because a forged witness can
/// violate a gate at the deployed prover. **This arm has no such forgery, and the reason is
/// structural**: its one gate compares a committed column to a preprocessed one, and
/// `batch_airs_and_matrices` derives BOTH from the descriptor — the committed capacities from
/// `ExactPublicManifest::main_trace`, the preprocessed pin from `preprocessed_cells`, in the same
/// walk. A prover cannot make them disagree without editing the library, so at the deployed prover
/// this table's gate is UNREACHABLE as a refusal and every forgery lands on the bus.
///
/// That is not a hole in the table: the gate is what stops a *hypothetical* free capacity column,
/// and §2/§4's evaluator-level poles are where it is measured. But an instrument that quietly
/// reported only bus verdicts would leave a reader thinking the gate had been exercised at the
/// prover. It has not, and this test is the record — it asserts the mechanism split rather than
/// asserting a bus verdict a third time.
#[test]
fn the_pin_gate_is_unreachable_as_a_prover_refusal_and_that_is_structural() {
    let desc = two_table_desc();
    let (air, main_rows, prep_rows) = exact_public_instance_for(&desc, TID_A).expect("declared");

    // The two matrices the deployed assembler builds AGREE by construction, column for column.
    for (row, (m, p)) in main_rows.iter().zip(prep_rows.iter()).enumerate() {
        assert_eq!(
            m[0], p[EP_MULT],
            "row {row}: the committed capacity and the pinned multiplicity are two reads of one              descriptor, so the prover cannot make them disagree"
        );
    }

    // …so the gate's false pole is only reachable at the EVALUATOR, where a preprocessed pin the
    // prover did not write can be substituted.
    let mut forged = prep_rows.clone();
    forged[0][EP_MULT] = forged[0][EP_MULT] + BabyBear::ONE;
    assert!(
        !ir2_air_gates_accept(&air, &main_rows, &forged),
        "a preprocessed multiplicity disagreeing with the committed one must be refused"
    );
}
