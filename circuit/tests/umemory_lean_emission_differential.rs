//! **THE UNIVERSAL MEMORY OP LOG'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::UMemory` was a hand-written Rust arm: five booleans, the real-row prefix, the positional
//! serial chain, a read discipline over BOTH components of the `Option` cell, canonical-`none` on
//! both images, the serial-gap range check, the domain nibble query, the NULLIFIER insert-only
//! tooth, the `ir2_umem_log` receive, both `ir2_umem_check` Blum legs and the `ir2_umem_addrs`
//! address-closure query. Architectural law #1 says that object is authored in Lean and Rust only
//! interprets. It was not. **That arm is now DELETED**; its author is
//! `metatheory/Dregg2/Circuit/Emit/UMemoryTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-umemory-v1.json`, and `Ir2Air::LeanTable` walks it.
//!
//! # The three questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the op
//!    log, the serial chain, the gap witnesses and the nullifier indicator OUT of the prover's own
//!    universal-memory trace.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2 — a per-cell mutation sweep
//!    through the REAL deployed evaluator, with the undetected set pinned EXACTLY.)
//! 3. **Do both poles still hold at the deployed prover?** (§3.)
//!
//! # ⚑ What the port REFUTED, and there are TWO
//!
//! * *"`prev_serial < serial` (Disciplined), exactly the flat memory's gap shape."* The second
//!   clause is true and it is the refutation. There is no magnitude gate on `UM_PREV_SERIAL`: the
//!   gap gate *defines* `prev_serial = serial − 1 − gap` in the FIELD, so a nullifier-domain
//!   freshness read at serial 1 may claim a prior serial of `p − 5`.
//!   `UMemoryTableEmit.wrapped_prev_serial_satisfies_every_gate` proves it against the emitted gate
//!   list; §3 measures the same witness through the deployed evaluator.
//! * *"a nullifier-domain write installing `none` is UNSAT."* True of REAL rows only. The tooth
//!   `is_null·kind·(1 − present)` carries no `is_real` factor of its own — the gating arrives two
//!   gates away, through the inverse-witness gate that forces `is_null = is_real` at the nullifier
//!   domain — so a PAD row spelling exactly the forbidden op satisfies every gate
//!   (`a_pad_row_spells_the_forbidden_nullifier_write`). §3 measures that too, alongside the REAL
//!   row where the tooth genuinely bites in both spellings of the indicator.
//!
//! ⚠ Both containments live OUTSIDE this table, in the `ir2_umem_log` / `ir2_umem_check` legs that
//! ride at `is_real`. Naming which mechanism refuses what is the point: an assembler refusal or a
//! multiset imbalance quoted as a gate verdict is how an accepting gate hides.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, UMemBoundaryWitness, UMemOpSpec,
    VmConstraint2, prove_vm_descriptor2_umem, table_air_gates_accept, umem_rows_for,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};
use dregg_circuit::table_air::TableExpr;
use dregg_circuit::table_air::{BusOp, RowSel, umemory_table_air};

// The deployed layout, transcribed ONCE here so the assertions below can name a column. These are
// the same numbers `UMemoryTableEmit.lean` derives; a drift on either side reds §1.
const UM_DOMAIN: usize = 0;
const UM_KEY: usize = 1;
const UM_PRESENT: usize = 2;
const UM_VALUE: usize = 3;
const UM_PREV_PRESENT: usize = 4;
const UM_PREV_VALUE: usize = 5;
const UM_PREV_SERIAL: usize = 6;
const UM_KIND: usize = 7;
const UM_SERIAL: usize = 8;
const UM_IS_REAL: usize = 9;
const UM_GAP: usize = 10;
const UM_GAP_LIMB0: usize = 11;
const UM_IS_NULL: usize = 21;
const UM_NULL_INV: usize = 22;
const UM_WIDTH: usize = 23;

/// The nullifier domain (`NULLIFIER_DOMAIN`), which the insert-only tooth keys off.
const NULLIFIER_DOMAIN: u32 = 3;

/// A THREE-op descriptor spanning TWO domains: a nullifier INSERT, a nullifier FRESHNESS READ, and a
/// register write outside the nullifier domain.
///
/// ⚑ The two domains are what makes the nullifier forcing load-bearing on real rows in BOTH
/// directions at once: rows 0–1 take the `domain = 3` branch (indicator forced ON, inverse witness
/// dead) and row 2 takes the `domain ≠ 3` branch (indicator forced OFF, inverse witness the only
/// thing that can satisfy the gate). A single-domain witness would leave one branch untested.
fn umem_desc() -> EffectVmDescriptor2 {
    let op = |domain: u32, key: LeanExpr, present: LeanExpr, value: LeanExpr, kind: MemKind| {
        VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(4),
            domain,
            key,
            present,
            value,
            prev_present: LeanExpr::Const(0),
            prev_value: LeanExpr::Const(0),
            prev_serial: LeanExpr::Const(0),
            kind,
        })
    };
    EffectVmDescriptor2 {
        name: "umemory-lean-emission-differential".to_string(),
        trace_width: 5,
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints: vec![
            // A nullifier INSERT (serial 1): a WRITE installing a PRESENT cell — the one shape the
            // insert-only tooth permits at the nullifier domain.
            op(
                NULLIFIER_DOMAIN,
                LeanExpr::Var(0),
                LeanExpr::Const(1),
                LeanExpr::Const(1),
                MemKind::Write,
            ),
            // THE FRESHNESS READ (serial 2): `present = 0`, i.e. `none`. This is the row whose
            // meaning the whole insert-only discipline exists to underwrite.
            op(
                NULLIFIER_DOMAIN,
                LeanExpr::Var(1),
                LeanExpr::Const(0),
                LeanExpr::Const(0),
                MemKind::Read,
            ),
            // A register write (serial 3) in a SECOND domain — the `domain ≠ 3` branch.
            op(
                0,
                LeanExpr::Var(2),
                LeanExpr::Const(1),
                LeanExpr::Var(3),
                MemKind::Write,
            ),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

fn umem_trace() -> Vec<Vec<BabyBear>> {
    let row = vec![
        BabyBear::new(7),  // inserted nullifier key
        BabyBear::new(11), // fresh-checked nullifier key
        BabyBear::new(0),  // register key
        BabyBear::new(42), // register value
        BabyBear::ZERO,    // guard (row 0 only)
    ];
    let mut rows = vec![row; 4];
    rows[0][4] = BabyBear::ONE;
    rows
}

/// The declared `(domain, key)` list, DOMAIN-MAJOR increasing — every op's address must be a member
/// or the `ir2_umem_addrs` closure query has nothing to balance against.
fn umem_boundary() -> UMemBoundaryWitness {
    UMemBoundaryWitness {
        addrs: vec![
            (0, BabyBear::new(0)),
            (NULLIFIER_DOMAIN, BabyBear::new(7)),
            (NULLIFIER_DOMAIN, BabyBear::new(11)),
        ],
        init_vals: vec![None, None, None],
    }
}

fn honest_umem_rows() -> Vec<Vec<BabyBear>> {
    umem_rows_for(&umem_desc(), &umem_trace(), &umem_boundary())
        .expect("the deployed prover assembles a universal memory op-log table")
}

/// The number of REAL op rows this witness produces.
const REALS: usize = 3;

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The emitted table declares width 23 and reads the eight-felt
/// `ir2_umem_log` tuple at columns 0–7, the positional serial at 8, the guard at 9, the gap at 10
/// and the nullifier indicator + its inverse witness at 21/22. The prover's OWN trace builder writes
/// those columns; this reads them back and checks each against the descriptor and the base trace,
/// recovered independently rather than off the same row.
///
/// If the Lean emission had transcribed one offset wrong, the honest witness would still prove (the
/// gate would read a zero column and vanish) but this round-trip would fail.
#[test]
fn the_emitted_columns_round_trip_the_universal_op_log() {
    let rows = honest_umem_rows();
    let t = umemory_table_air();
    let base = umem_trace();

    assert_eq!(t.width, UM_WIDTH);
    assert!(rows.iter().all(|r| r.len() == t.width));
    // ⓘ MEASURED, not assumed: three guarded ops out of four base rows, and the height is
    // `next_pow2(3)` FLOORED AT `MIN_TABLE_HEIGHT = 8` — so three real rows are followed by FIVE
    // pads, the padded shape that is the whole reason a table AIR needs a per-row multiplicity
    // expression rather than a constant.
    assert_eq!(rows.len(), 8);
    assert!(rows.len().is_power_of_two());
    assert!(rows.len() > REALS, "the witness must exercise pad rows");

    // Row 0 — the nullifier INSERT.
    assert_eq!(rows[0][UM_DOMAIN], BabyBear::new(NULLIFIER_DOMAIN));
    assert_eq!(rows[0][UM_KEY], base[0][0], "the inserted nullifier key");
    assert_eq!(rows[0][UM_PRESENT], BabyBear::ONE);
    assert_eq!(rows[0][UM_VALUE], BabyBear::ONE);
    assert_eq!(rows[0][UM_KIND], BabyBear::ONE, "a WRITE");
    // Row 1 — the FRESHNESS READ: an absent cell, canonically (payload 0 too).
    assert_eq!(rows[1][UM_DOMAIN], BabyBear::new(NULLIFIER_DOMAIN));
    assert_eq!(rows[1][UM_KEY], base[0][1], "the fresh-checked key");
    assert_eq!(rows[1][UM_PRESENT], BabyBear::ZERO);
    assert_eq!(rows[1][UM_VALUE], BabyBear::ZERO);
    assert_eq!(rows[1][UM_KIND], BabyBear::ZERO, "a READ");
    // Row 2 — the register write, OUTSIDE the nullifier domain.
    assert_eq!(rows[2][UM_DOMAIN], BabyBear::ZERO);
    assert_eq!(rows[2][UM_KEY], base[0][2]);
    assert_eq!(rows[2][UM_VALUE], base[0][3], "the register value");

    for i in 0..REALS {
        assert_eq!(rows[i][UM_IS_REAL], BabyBear::ONE, "row {i} is real");
        // ⚑ The POSITIONAL serial: row i carries i + 1, which is the claim
        // `UMemoryTableEmit.serial_is_positional` proves from the `.first` + `.transition` gates.
        assert_eq!(rows[i][UM_SERIAL], BabyBear::new((i + 1) as u32));
        // Every op here claims prior serial 0, so the gap is `serial − 1 − 0 = i`.
        assert_eq!(rows[i][UM_PREV_SERIAL], BabyBear::ZERO);
        assert_eq!(rows[i][UM_GAP], BabyBear::new(i as u32));
        assert_eq!(rows[i][UM_PREV_PRESENT], BabyBear::ZERO);
        assert_eq!(rows[i][UM_PREV_VALUE], BabyBear::ZERO);
    }
    // The third op is the one with a two-nibble-free gap; limb 0 carries it whole.
    assert_eq!(rows[2][UM_GAP_LIMB0], BabyBear::new(2), "limb 0 of the gap");

    // ⚑ THE NULLIFIER INDICATOR, both branches, read off the prover's own rows. On the two
    // nullifier-domain rows it is 1 and the inverse witness is DEAD (its gate coefficient is
    // `domain − 3 = 0`); on the register row it is 0 and the inverse witness is the ONLY thing that
    // can satisfy the forcing gate, so it is the genuine inverse.
    assert_eq!(rows[0][UM_IS_NULL], BabyBear::ONE);
    assert_eq!(rows[1][UM_IS_NULL], BabyBear::ONE);
    assert_eq!(rows[0][UM_NULL_INV], BabyBear::ZERO);
    assert_eq!(rows[1][UM_NULL_INV], BabyBear::ZERO);
    assert_eq!(rows[2][UM_IS_NULL], BabyBear::ZERO);
    assert_eq!(
        rows[2][UM_NULL_INV] * (rows[2][UM_DOMAIN] - BabyBear::new(NULLIFIER_DOMAIN)),
        BabyBear::ONE,
        "the register row's witness is the genuine inverse of `domain − 3`"
    );

    // Every pad row is a pad, and the serial chain CONTINUES through them (the increment gate is
    // unconditional on the transition domain, so a pad may not restart the count). ⚑ A pad's
    // indicator is ZERO — which the forcing gate does not merely permit but FORCES, and which is
    // exactly what disarms the insert-only tooth there (§3).
    for (i, r) in rows.iter().enumerate().skip(REALS) {
        assert_eq!(r[UM_IS_REAL], BabyBear::ZERO, "row {i} is a pad");
        assert_eq!(r[UM_SERIAL], BabyBear::new((i + 1) as u32));
        assert_eq!(r[UM_GAP], BabyBear::ZERO);
        assert_eq!(r[UM_IS_NULL], BabyBear::ZERO);
        assert_eq!(r[UM_NULL_INV], BabyBear::ZERO);
    }

    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every row and every one of the 23 columns, bump the value and ask the
/// REAL deployed evaluator whether the table still accepts.
///
/// The undetected set is pinned EXACTLY, and every member of it is named with the mechanism that
/// protects it instead:
///
/// * `UM_KEY` on EVERY row — ⚑ read by NO gate at all (`UMemoryTableEmit.key_is_read_by_no_gate`).
///   The column that says WHICH cell of `Domain × κ` an op touches is bound by the `ir2_umem_addrs`
///   closure lookup and the `ir2_umem_check` multiset, both bus legs. This sweep is structurally
///   blind to it, and that is a fact about the mechanism rather than a gap in the instrument.
/// * `UM_VALUE` on a real row that is a WRITE of a PRESENT cell (rows 0 and 2 here) — both gates
///   that read the payload are gated off: the read-discipline gate by `1 − kind` and the
///   canonical-`none` gate by `1 − present`. What binds a written value is the `ir2_umem_log`
///   receive and the `ir2_umem_check` publish. ⓘ On the READ row (1) the discipline gate ties value
///   to `prev_value` and the bump IS caught, which is why row 1 is not in the set.
/// * `UM_DOMAIN` on a PAD row — the two nullifier-forcing gates are inert at `is_real = 0`
///   (`(d−3)·is_null` with `is_null = 0`, and `(d−3)·null_inv` with `null_inv = 0`). ⚠ The `ir2_byte`
///   nibble query still fires on a pad at multiplicity 1, so a pad's domain is range-bound to
///   `[0,16)` — but that is a BUS leg and it does not pin the value.
/// * `UM_VALUE` / `UM_PREV_VALUE` / `UM_PREV_SERIAL` on a PAD row — every gate that reads them
///   carries an `is_real` factor. Contained by the multiset and the log, which ride at `is_real`, so
///   a pad publishes and declares nothing.
/// * `UM_NULL_INV` on a NULLIFIER-domain row — its only gate multiplies it by `domain − 3`, which is
///   ZERO there. The column carries no information at the nullifier domain, because the same gate
///   already reads `is_null = is_real` outright.
///
/// ⓘ `UM_PRESENT`, `UM_PREV_PRESENT`, `UM_KIND`, `UM_IS_REAL` and `UM_IS_NULL` are deliberately NOT
/// in the set on any row: their boolean gates are UNCONDITIONAL, so a pad's flags are caught exactly
/// like a real row's. That asymmetry against the payload columns is measured here, not assumed.
///
/// Anything else landing in the undetected set means the re-emission lost a gate.
#[test]
fn every_gated_universal_memory_cell_is_still_gated_after_the_cutover() {
    let rows = honest_umem_rows();
    let t = umemory_table_air();
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

    let mut expected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        let is_pad = row >= REALS;
        let nullifier_row = rows[row][UM_DOMAIN] == BabyBear::new(NULLIFIER_DOMAIN);
        // A real write of a PRESENT cell leaves its payload to the log + multiset.
        let written_payload = !is_pad
            && rows[row][UM_KIND] == BabyBear::ONE
            && rows[row][UM_PRESENT] == BabyBear::ONE;
        for col in 0..t.width {
            let bus_bound = col == UM_KEY
                || (written_payload && col == UM_VALUE)
                || (is_pad && matches!(col, UM_DOMAIN | UM_VALUE | UM_PREV_VALUE | UM_PREV_SERIAL))
                || (nullifier_row && col == UM_NULL_INV);
            if bus_bound {
                expected.push((row, col));
            }
        }
    }
    assert_eq!(
        undetected, expected,
        "the undetected set is not exactly {{the bus-bound key}} ∪ {{a written payload}} ∪ {{the \
         pad row's is_real-gated payload and domain}} ∪ {{the dead inverse witness at the \
         nullifier domain}} — either a gate was lost in the Lean re-emission, or a gate appeared \
         where a bus is supposed to be the mechanism. undetected: {undetected:?}"
    );

    // ⚑ The columns that MUST be caught on EVERY row, named with the gate that catches them.
    for row in 0..rows.len() {
        // the four boolean flags, all UNCONDITIONAL — plus the prefix gate on the pad rows.
        for col in [UM_IS_REAL, UM_KIND, UM_PRESENT, UM_PREV_PRESENT, UM_IS_NULL] {
            assert!(detected.contains(&(row, col)), "row {row}: flag {col}");
        }
        // the positional serial chain (`.first` anchor + `.transition` increment).
        assert!(detected.contains(&(row, UM_SERIAL)), "row {row}: serial");
        // the gap definition + its 30-bit decomposition.
        assert!(detected.contains(&(row, UM_GAP)), "row {row}: gap");
        for col in UM_GAP_LIMB0..UM_IS_NULL {
            assert!(detected.contains(&(row, col)), "row {row}: gap limb {col}");
        }
    }
    // …and on every REAL row the claimed prior cell is tied down: `prev_value` by canonical-`none`
    // (every claimed prior image here is absent) and `prev_serial` by the gap DEFINITION.
    for row in 0..REALS {
        assert!(
            detected.contains(&(row, UM_PREV_VALUE)),
            "row {row}: prev_value"
        );
        assert!(
            detected.contains(&(row, UM_PREV_SERIAL)),
            "row {row}: prev_serial (the gap DEFINITION moves with it)"
        );
        // …and the DOMAIN, through whichever branch of the nullifier forcing that row takes.
        assert!(detected.contains(&(row, UM_DOMAIN)), "row {row}: domain");
    }
    // The READ row's payload is caught by the read-discipline gate; the two WRITE rows' is not.
    assert!(detected.contains(&(1, UM_VALUE)), "the read row's value");

    println!(
        "MEASURED: {}/{} universal op-log cells are gated by the Lean emission; the undetected {} \
         are the bus-bound key, the written payloads, the pad rows' is_real-gated payload/domain, \
         and the dead inverse witness at the nullifier domain",
        detected.len(),
        detected.len() + undetected.len(),
        undetected.len()
    );
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** An honest universal-memory witness proves and verifies through the Lean-emitted
/// AIR.
#[test]
fn an_honest_umem_witness_proves_and_verifies_through_the_lean_emission() {
    let desc = umem_desc();
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &umem_trace(),
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &umem_boundary(),
    )
    .expect("an honest umem witness must prove through the Lean-emitted op-log AIR");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES.**
///
/// Each forgery keeps the shape (8 rows, 23 columns) and changes only what the table SAYS. The gate
/// that refuses each is named where it is attributable, and where two gates both fire that is said
/// rather than glossed.
#[test]
fn a_forged_universal_op_log_is_refused_by_the_emitted_gates() {
    let rows = honest_umem_rows();
    let t = umemory_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // (a) ⚑ A READ THAT INVENTS A PRESENCE BIT. Row 1 is the freshness read; flipping its
    //     `present` to 1 while the claimed prior cell stays absent is refused by the read-discipline
    //     gate on the `Option`'s FIRST component — the gate the flat memory has no counterpart for.
    let mut lying_presence = rows.clone();
    lying_presence[1][UM_PRESENT] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &lying_presence),
        "the emitted read-discipline gate must refuse a read inventing a presence bit"
    );

    // (b) ⚑ A NON-CANONICAL `none`: an absent cell carrying a payload. Refused by the
    //     canonical-`none` gate, which is what makes `(present, value)` a faithful `optOf`.
    let mut nonc = rows.clone();
    nonc[1][UM_VALUE] = BabyBear::new(9);
    assert!(
        !table_air_gates_accept(&t, &nonc),
        "the emitted canonical-`none` gate must refuse an absent cell with a payload"
    );

    // (c) ⚑ RESTART THE SERIAL COUNT on a pad row. Refused by the `.transition` increment gate: the
    //     chain is positional and unconditional, so a pad may not renumber.
    let mut renumbered = rows.clone();
    renumbered[REALS][UM_SERIAL] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &renumbered),
        "the emitted serial increment must refuse a restarted count"
    );

    // (d) ⚑ PROMOTE THE PAD TO A REAL ROW while its payload stays zero. Refused by the GAP
    //     definition at that row: `gap = is_real·(serial − 1 − prev_serial)` was `0` at
    //     `is_real = 0` and becomes `0 − (4 − 1 − 0) ≠ 0`.
    let mut promoted = rows.clone();
    promoted[REALS][UM_IS_REAL] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &promoted),
        "the emitted gap definition must refuse a promoted pad whose gap column stays zero"
    );

    // (e) ⚑ WIDEN THE GAP WITHOUT ITS WITNESS. Refused by the 30-bit RECOMPOSITION gate, which is
    //     what makes the gap a BOUNDED integer rather than merely a field element.
    let mut widened = rows.clone();
    widened[2][UM_GAP] = widened[2][UM_GAP] + BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &widened),
        "the emitted gap decomposition must refuse a gap with no limb witness"
    );

    // (f) ⚑ SWITCH THE NULLIFIER INDICATOR OFF on a real nullifier-domain row — the move that would
    //     disarm the insert-only tooth. Refused by the INVERSE-WITNESS gate, which at `domain = 3`
    //     reads `is_null = is_real` outright and leaves the prover no witness to rescue it.
    let mut disarmed = rows.clone();
    disarmed[0][UM_IS_NULL] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &disarmed),
        "the emitted forcing gate must refuse a real nullifier row claiming `is_null = 0`"
    );
}

/// ⚑ **REFUTATION ONE, MEASURED AT THE DEPLOYED EVALUATOR.**
///
/// `UMemoryTableEmit.wrapped_prev_serial_satisfies_every_gate` proves in Lean that a claimed prior
/// serial of `p − 5` satisfies every emitted gate. This is the same statement run through the REAL
/// `Ir2Air::LeanTable` evaluator on the prover's own rows, so the Lean theorem and the deployed
/// constraint system agree about the hole rather than only about the fix.
///
/// ⚠ Read the direction. This is NOT a defect the deployed prover admits: the assembler refuses the
/// witness outright (below) and the `ir2_umem_check` multiset refuses it at the constraint level.
/// What it shows is that the refusal lives in those two places and NOT in the row algebra — so
/// *"`prev_serial < serial` (Disciplined)"*, which the deleted arm asserted in a comment right next
/// to the gate, is not something this table decides.
#[test]
fn the_gap_gate_admits_a_wrapped_prior_serial() {
    let rows = honest_umem_rows();
    let t = umemory_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // Row 0 (the nullifier insert, serial 1) claims a prior serial of `p − 5` and carries the
    // matching gap of 5, honestly decomposed: gap 5 is one nibble, so only limb 0 moves.
    let mut wrapped = rows.clone();
    wrapped[0][UM_PREV_SERIAL] = BabyBear::ZERO - BabyBear::new(5);
    wrapped[0][UM_GAP] = BabyBear::new(5);
    wrapped[0][UM_GAP_LIMB0] = BabyBear::new(5);
    assert!(
        table_air_gates_accept(&t, &wrapped),
        "MEASURED: the emitted gates ACCEPT a claimed prior serial of p − 5 at serial 1 — the gap \
         gate DEFINES prev_serial, it does not bound it (UMemoryTableEmit §4c)"
    );
    assert!(
        wrapped[0][UM_PREV_SERIAL].as_u32() > (1u32 << 30),
        "the wrapped claim must be above 2^30 for the point to be the point"
    );
}

/// ⚑ **REFUTATION TWO, MEASURED AT THE DEPLOYED EVALUATOR.**
///
/// `UMemoryTableEmit.a_pad_row_spells_the_forbidden_nullifier_write` proves in Lean that a PAD row
/// spelling exactly the op the insert-only tooth exists to refuse — nullifier domain, `kind = 1`,
/// `present = 0`, over a cell it claims WAS present — satisfies every emitted gate. Here it is at
/// the deployed evaluator, on the prover's own rows.
///
/// ⚑ The contrast is in the same test, because the refutation without it would read as "the tooth
/// does not work": on a REAL row the same op is refused in BOTH spellings of the indicator. With
/// `is_null = 1` the tooth fires; with `is_null = 0` the forcing gate fires instead. A prover has no
/// third choice — which is exactly what `a_nullifier_write_cannot_install_none` proves and what
/// makes the tooth real *where the bus legs are alive*.
///
/// ⚠ The containment for the pad: every `ir2_umem_log` / `ir2_umem_check` / `ir2_umem_addrs` leg
/// rides at `is_real`, so a pad declares NOTHING, publishes NOTHING and asks NOTHING.
#[test]
fn a_pad_row_spells_the_forbidden_nullifier_write_and_a_real_row_cannot() {
    let rows = honest_umem_rows();
    let t = umemory_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // The pad at index REALS, rewritten into the forbidden op. Its indicator stays 0 — which the
    // forcing gate does not merely permit at `is_real = 0` but FORCES.
    let mut pad = rows.clone();
    pad[REALS][UM_DOMAIN] = BabyBear::new(NULLIFIER_DOMAIN);
    pad[REALS][UM_KIND] = BabyBear::ONE;
    pad[REALS][UM_PRESENT] = BabyBear::ZERO;
    pad[REALS][UM_PREV_PRESENT] = BabyBear::ONE;
    pad[REALS][UM_PREV_VALUE] = BabyBear::new(9);
    assert!(
        table_air_gates_accept(&t, &pad),
        "MEASURED: a PAD row spelling a nullifier-domain write that installs `none` satisfies every \
         emitted gate — the tooth carries no `is_real` factor of its own, and the `is_null` that \
         disarms it is forced to zero two gates away (UMemoryTableEmit §4c)"
    );

    // …and the same op on a REAL row is refused, whichever way the indicator is spelled.
    for indicator in [BabyBear::ONE, BabyBear::ZERO] {
        let mut real = rows.clone();
        real[0][UM_KIND] = BabyBear::ONE;
        real[0][UM_PRESENT] = BabyBear::ZERO;
        real[0][UM_VALUE] = BabyBear::ZERO;
        real[0][UM_PREV_PRESENT] = BabyBear::ONE;
        real[0][UM_PREV_VALUE] = BabyBear::new(9);
        real[0][UM_IS_NULL] = indicator;
        assert!(
            !table_air_gates_accept(&t, &real),
            "a REAL nullifier-domain write installing `none` must be refused with is_null = \
             {indicator:?} — the tooth on 1, the forcing gate on 0"
        );
    }
}

/// The prover-level pole for refutation TWO, stated at ITS OWN resolution: the ASSEMBLER refuses a
/// nullifier-domain write that installs an absent cell. ⚠ That is a completeness-of-refusal fact
/// about `build_traces`, NOT a gate verdict — the gate verdicts are the test directly above.
#[test]
fn a_nullifier_delete_is_refused_by_the_deployed_assembler() {
    let mut desc = umem_desc();
    // Rewrite op 0 into a WRITE installing `none` at the nullifier domain.
    desc.constraints[0] = VmConstraint2::UMemOp(UMemOpSpec {
        guard: LeanExpr::Var(4),
        domain: NULLIFIER_DOMAIN,
        key: LeanExpr::Var(0),
        present: LeanExpr::Const(0),
        value: LeanExpr::Const(0),
        prev_present: LeanExpr::Const(0),
        prev_value: LeanExpr::Const(0),
        prev_serial: LeanExpr::Const(0),
        kind: MemKind::Write,
    });
    let refused = must_refuse_or_unsat_panic("a nullifier-domain write installing `none`", || {
        prove_vm_descriptor2_umem(
            &desc,
            &umem_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &umem_boundary(),
        )
        .map(|_| ())
    });
    assert!(
        refused.reason().contains("insert-only"),
        "the refusal must name the discipline: {}",
        refused.reason()
    );
}

/// The prover-level pole for refutation ONE: the ASSEMBLER refuses a claimed prior serial that is
/// not below the op's own. ⚠ Again a `build_traces` fact, not a gate verdict — `the_gap_gate_admits_
/// a_wrapped_prior_serial` shows this exact shape passing the gates.
#[test]
fn a_future_claiming_prior_serial_is_refused_by_the_deployed_assembler() {
    let mut desc = umem_desc();
    desc.constraints[0] = VmConstraint2::UMemOp(UMemOpSpec {
        guard: LeanExpr::Var(4),
        domain: NULLIFIER_DOMAIN,
        key: LeanExpr::Var(0),
        present: LeanExpr::Const(1),
        value: LeanExpr::Const(1),
        prev_present: LeanExpr::Const(0),
        prev_value: LeanExpr::Const(0),
        // Op 0 carries serial 1 and claims prior serial 5 — a serial from the future.
        prev_serial: LeanExpr::Const(5),
        kind: MemKind::Write,
    });
    let refused = must_refuse_or_unsat_panic("a claimed prior serial from the future", || {
        prove_vm_descriptor2_umem(
            &desc,
            &umem_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &umem_boundary(),
        )
        .map(|_| ())
    });
    assert!(
        refused.reason().contains("not before own serial"),
        "the refusal must name the reason: {}",
        refused.reason()
    );
}

/// **SOUNDNESS AT THE DEPLOYED PROVER, refused by a CONSTRAINT and not by a bus.** An op at an
/// address the boundary never declared would be caught by the `ir2_umem_addrs` LOOKUP — a bus leg —
/// so it is not the shape this asserts. What this asserts is a GATE verdict: a read whose returned
/// cell disagrees with the cell it claims was there is refused by the read-discipline gate, all the
/// way through the deployed prover, and `assert_violated_constraint_not_bus` is the tooth that keeps
/// a LogUp imbalance from being quoted as that verdict.
#[test]
fn a_lying_read_is_refused_by_a_violated_constraint_at_the_deployed_prover() {
    let mut desc = umem_desc();
    // Op 1 is the freshness READ. Make it return a PRESENT cell while still claiming its prior
    // image was absent — the read-discipline gate on the `Option`'s first component.
    desc.constraints[1] = VmConstraint2::UMemOp(UMemOpSpec {
        guard: LeanExpr::Var(4),
        domain: NULLIFIER_DOMAIN,
        key: LeanExpr::Var(1),
        present: LeanExpr::Const(1),
        value: LeanExpr::Const(1),
        prev_present: LeanExpr::Const(0),
        prev_value: LeanExpr::Const(0),
        prev_serial: LeanExpr::Const(0),
        kind: MemKind::Read,
    });
    let refused =
        must_refuse_or_unsat_panic("a read that does not return its claimed cell", || {
            prove_vm_descriptor2_umem(
                &desc,
                &umem_trace(),
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &umem_boundary(),
            )
            .map(|_| ())
        });
    assert_violated_constraint_not_bus(
        "a universal read that does not return its claimed cell",
        &refused.reason(),
    );
}

/// The emitted bus legs are the SIDES the universal-memory argument needs. ⚠ This is the half the
/// mutation sweep is structurally blind to: no gate reads the bus multiplicities or directions, so a
/// `.provide`-instead-of-`.query` slip on the closure table or a send/receive swap on the Blum legs
/// would leave every gate green and break the argument silently. It is checked HERE, on the emitted
/// object.
#[test]
fn the_universal_op_log_queries_the_closure_table_and_rides_the_blum_chain() {
    let t = umemory_table_air();

    // The closure table: this AIR is the CLIENT; both boundary forms are the server.
    assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Query), 1);
    assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Provide), 0);
    let closure = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_addrs")
        .expect("one closure query");
    assert_eq!(
        closure.tuple,
        vec![TableExpr::Loc(UM_DOMAIN), TableExpr::Loc(UM_KEY)]
    );
    assert_eq!(closure.mult, TableExpr::Loc(UM_IS_REAL));

    // The Blum pair: PUBLISH my own `Option` image at MY serial, CONSUME the prior image at the
    // CLAIMED one. A swap of the two serial columns here reverses the whole read-consistency
    // argument.
    let send = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Send)
        .expect("one publish");
    assert_eq!(
        send.tuple,
        vec![
            TableExpr::Loc(UM_DOMAIN),
            TableExpr::Loc(UM_KEY),
            TableExpr::Loc(UM_PRESENT),
            TableExpr::Loc(UM_VALUE),
            TableExpr::Loc(UM_SERIAL),
        ]
    );
    let recv = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Receive)
        .expect("one consume");
    assert_eq!(
        recv.tuple,
        vec![
            TableExpr::Loc(UM_DOMAIN),
            TableExpr::Loc(UM_KEY),
            TableExpr::Loc(UM_PREV_PRESENT),
            TableExpr::Loc(UM_PREV_VALUE),
            TableExpr::Loc(UM_PREV_SERIAL),
        ],
        "the consumed tuple carries the CLAIMED prior serial — which is exactly why the multiset, \
         not the gap gate, is what refuses a wrapped claim"
    );
    assert_eq!(send.mult, TableExpr::Loc(UM_IS_REAL));
    assert_eq!(recv.mult, TableExpr::Loc(UM_IS_REAL));

    // The gathered op log is a RECEIVE (the main AIR sends), and it is the table's first EIGHT
    // columns verbatim — the reason the witness producer can write the tuple by name.
    assert_eq!(t.bus_count_op("ir2_umem_log", BusOp::Receive), 1);
    assert_eq!(t.bus_count_op("ir2_umem_log", BusOp::Send), 0);
    let log = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_log")
        .expect("one log receive");
    assert_eq!(
        log.tuple,
        (0..8).map(TableExpr::Loc).collect::<Vec<_>>(),
        "the eight-felt log tuple IS columns 0..8"
    );

    // Two transition-scoped gates (prefix, serial increment), one first-scoped (the anchor).
    assert_eq!(t.gate_count_sel(RowSel::Transition), 2);
    assert_eq!(t.gate_count_sel(RowSel::First), 1);
    assert_eq!(t.gate_count_sel(RowSel::All), 17);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
}
