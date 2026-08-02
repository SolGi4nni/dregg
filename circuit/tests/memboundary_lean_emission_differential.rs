//! **THE MEMORY BOUNDARY'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::MemBoundary` was a hand-written Rust arm: the boolean guard, the real-row prefix, the
//! strictly-increasing gap, the address magnitude bound, two 30-bit decompositions, the Blum
//! init/final legs and the `ir2_mem_addrs` table it SERVES. Architectural law #1 says that object
//! is authored in Lean and Rust only interprets. It was not. **That arm is now DELETED**; its
//! author is `metatheory/Dregg2/Circuit/Emit/MemBoundaryTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-mem-boundary-v1.json`, and `Ir2Air::LeanTable` walks
//! it.
//!
//! # The three questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    declared address list, the real prefix, the gaps and the magnitude witnesses OUT of the
//!    prover's own boundary trace.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2 — a per-cell mutation sweep
//!    through the REAL deployed evaluator, with the undetected set pinned EXACTLY.)
//! 3. **Do both poles still hold at the deployed prover?** (§3.)
//!
//! # ⚑ What the port PROVED, which the deleted arm only asserted
//!
//! The arm said, in a parenthesis, "strictly increasing declared addresses (⇒ Nodup)" and
//! "address magnitude bound (so the increasing chain cannot wrap the field)". The Lean file proves
//! both AND separates them: `addrs_distinct_as_felts` is the property the memory argument needs
//! (the lookup and the multiset compare FELTS, not integers), and
//! `wrap_witness_without_the_magnitude_bound` exhibits a three-row witness — addresses
//! `0 → 2^30 → p` — that satisfies the gap gate at every step and whose first and last declared
//! addresses are THE SAME FELT. So the magnitude gate is load-bearing and "strictly increasing"
//! alone does NOT give `Nodup`.
//!
//! # ⚠ The named residual this measures rather than fixes
//!
//! §2's undetected set contains `(pad row, MB_ADDR)` for EVERY pad row — five of the eight, at
//! this witness: a PAD row's address is bound by nothing (`achk = 0·addr = 0`), and
//! `MB_ADDR_MULT` is bound by nothing on any row. That is measured here, not glossed. What contains it is the `ir2_mem_check` Blum multiset in a different AIR —
//! an op at an address with no REAL boundary row has no serial-0 init send to consume — and that
//! is a containment argument about a different object, stated in the Lean file's §4c.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, MemOpSpec, VmConstraint2,
    mem_boundary_rows_for, prove_vm_descriptor2, table_air_gates_accept, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::must_refuse_or_unsat_panic;
use dregg_circuit::table_air::TableExpr;
use dregg_circuit::table_air::{BusOp, RowSel, mem_boundary_table_air};

// The deployed layout, transcribed ONCE here so the assertions below can name a column. These are
// the same numbers `MemBoundaryTableEmit.lean` derives; a drift on either side reds §1.
const MB_ADDR: usize = 0;
const MB_INIT_VAL: usize = 1;
const MB_FIN_VAL: usize = 2;
const MB_FIN_SERIAL: usize = 3;
const MB_IS_REAL: usize = 4;
const MB_ADDR_MULT: usize = 5;
const MB_AGAP: usize = 6;
const MB_ACHK: usize = 17;
const MB_WIDTH: usize = 28;

/// The declared address list this differential uses. Deliberately NOT contiguous, so the gap
/// column carries genuine nonzero values and the range check is actually exercised.
const ADDRS: [u32; 3] = [5, 9, 40];
const INITS: [u32; 3] = [11, 22, 33];

/// A minimal descriptor with ONE guarded memory read — enough to make the memory pair present.
fn mem_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "memboundary-lean-emission-differential".to_string(),
        trace_width: 5,
        public_input_count: 0,
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
/// touch of address 5) claims prev serial 1 — the serial the first read left behind.
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

fn honest_boundary_rows() -> Vec<Vec<BabyBear>> {
    mem_boundary_rows_for(&mem_desc(), &mem_trace(), &boundary())
        .expect("the deployed prover assembles a memory boundary table")
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The emitted table declares width 28 and reads the address at
/// column 0, the real guard at 4, the gap at 6 and the magnitude witness at 17. The prover's OWN
/// trace builder writes those columns; this reads them back out and checks each against the
/// DECLARED list, recovered independently rather than off the same row.
///
/// If the Lean emission had transcribed one offset wrong, the honest witness would still prove
/// (the gate would read a zero column and vanish) but this round-trip would fail. That is the
/// failure mode a shape count cannot see.
#[test]
fn the_emitted_columns_round_trip_the_declared_address_list() {
    let rows = honest_boundary_rows();
    let t = mem_boundary_table_air();

    assert_eq!(t.width, MB_WIDTH);
    assert!(rows.iter().all(|r| r.len() == t.width));
    // ⓘ MEASURED, not assumed: the height is `next_pow2(3)` FLOORED AT `MIN_TABLE_HEIGHT = 8`, so
    // three real rows are followed by FIVE pads — the padded shape that is the whole reason a
    // table AIR needs a per-row multiplicity expression rather than a constant.
    assert_eq!(rows.len(), 8);
    assert!(rows.len().is_power_of_two());
    assert!(
        rows.len() > ADDRS.len(),
        "the witness must exercise pad rows"
    );

    for (i, &a) in ADDRS.iter().enumerate() {
        assert_eq!(rows[i][MB_ADDR], BabyBear::new(a), "declared address {i}");
        assert_eq!(rows[i][MB_INIT_VAL], BabyBear::new(INITS[i]));
        assert_eq!(rows[i][MB_IS_REAL], BabyBear::ONE, "row {i} is real");
        // The magnitude witness IS the address on a real row — the gate `achk = is_real·addr`.
        assert_eq!(rows[i][MB_ACHK], BabyBear::new(a));
    }
    // …and every pad row is a pad, with a zero magnitude witness.
    for r in rows.iter().skip(ADDRS.len()) {
        assert_eq!(r[MB_IS_REAL], BabyBear::ZERO);
        assert_eq!(r[MB_ACHK], BabyBear::ZERO);
    }

    // The GAP column carries `next.addr − addr − 1` on real→real steps and zero at the end —
    // recovered from ADDRS, not from the row.
    assert_eq!(rows[0][MB_AGAP], BabyBear::new(ADDRS[1] - ADDRS[0] - 1));
    assert_eq!(rows[1][MB_AGAP], BabyBear::new(ADDRS[2] - ADDRS[1] - 1));
    assert_eq!(rows[2][MB_AGAP], BabyBear::ZERO, "the last real→pad step");
    assert_ne!(
        rows[0][MB_AGAP],
        BabyBear::ZERO,
        "the declared list must be non-contiguous, or the gap range check is never exercised"
    );

    // The served multiplicity is the genuine per-address op count: address 5 is read twice,
    // address 9 once, address 40 never.
    assert_eq!(rows[0][MB_ADDR_MULT], BabyBear::new(2));
    assert_eq!(rows[1][MB_ADDR_MULT], BabyBear::new(1));
    assert_eq!(rows[2][MB_ADDR_MULT], BabyBear::ZERO);

    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every row and every one of the 28 columns, bump the value and ask the
/// REAL deployed evaluator whether the table still accepts.
///
/// The undetected set is pinned EXACTLY, and every member of it is named with the mechanism that
/// protects it instead:
///
/// * `MB_INIT_VAL`, `MB_FIN_VAL`, `MB_FIN_SERIAL` — the Blum images. Bound by the `ir2_mem_check`
///   MULTISET, which no single-AIR gate check can decide.
/// * `MB_ADDR_MULT` — the served count. Bound by the `ir2_mem_addrs` LogUp balance, same split.
/// * ⚠ `(pad row, MB_ADDR)` — the residual, on EVERY pad row, not just the last. A pad row's
///   address is bound by NOTHING here: `achk = 0·addr = 0` says nothing, and the gap gate that
///   would compare it to its predecessor is itself gated by `next.is_real`, which is 0. So the
///   deployed table has five rows whose address column is free. Contained by the `ir2_mem_check`
///   Blum multiset in `Ir2Air::Memory` — an op at an address with no REAL boundary row has no
///   serial-0 init send to consume — which is a containment argument about a DIFFERENT AIR.
///   Stated in `MemBoundaryTableEmit.lean` §4c and measured here.
///
/// Anything else landing in the undetected set means the re-emission lost a gate.
#[test]
fn every_gated_boundary_cell_is_still_gated_after_the_cutover() {
    let rows = honest_boundary_rows();
    let t = mem_boundary_table_air();
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

    let reals = ADDRS.len();
    let mut expected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
            let bus_bound = matches!(col, MB_INIT_VAL | MB_FIN_VAL | MB_FIN_SERIAL | MB_ADDR_MULT);
            let pad_addr = row >= reals && col == MB_ADDR;
            if bus_bound || pad_addr {
                expected.push((row, col));
            }
        }
    }
    assert_eq!(
        undetected, expected,
        "the undetected set is not exactly {{the Blum/lookup columns}} ∪ {{the pad row's \
         address}} — either a gate was lost in the Lean re-emission, or a gate appeared where a \
         bus is supposed to be the mechanism. undetected: {undetected:?}"
    );

    // ⚑ The columns that MUST be caught on EVERY row, named with the gate that catches them.
    for row in 0..rows.len() {
        // the boolean guard, and (on the pad row) the prefix + gap gates, which refuse a pad
        // promoted to real behind a real row it does not exceed.
        assert!(detected.contains(&(row, MB_IS_REAL)), "row {row}: is_real");
        // the gap definition + its 30-bit decomposition.
        assert!(detected.contains(&(row, MB_AGAP)), "row {row}: agap");
        // the magnitude definition + its 30-bit decomposition. ⚑ This is the gate the Lean file's
        // `wrap_witness_without_the_magnitude_bound` shows cannot be dropped.
        assert!(detected.contains(&(row, MB_ACHK)), "row {row}: achk");
        // every limb of both decompositions.
        for col in 7..17 {
            assert!(detected.contains(&(row, col)), "row {row}: agap limb {col}");
        }
        for col in 18..28 {
            assert!(detected.contains(&(row, col)), "row {row}: achk limb {col}");
        }
    }
    // …and the address on every REAL row (the magnitude gate ties it to `achk`).
    for row in 0..reals {
        assert!(detected.contains(&(row, MB_ADDR)), "row {row}: addr");
    }

    println!(
        "MEASURED: {}/{} boundary cells are gated by the Lean emission; the undetected {} are the \
         Blum/lookup columns plus the pad row's unbounded address",
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
        .expect("an honest memory witness must prove through the Lean-emitted boundary AIR");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES.**
///
/// Each forgery keeps the shape (4 rows, 28 columns) and changes only what the table SAYS. The
/// gate that refuses each is named where it is attributable, and where two gates both fire that
/// is said rather than glossed — a refusal credited to the wrong gate is how a lost gate hides.
#[test]
fn a_forged_declaration_is_refused_by_the_emitted_gates() {
    let rows = honest_boundary_rows();
    let t = mem_boundary_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // (a) ⚑ DECLARE A FOURTH ADDRESS BY PROMOTING THE PAD. The pad row carries address 0, which
    //     is BELOW the last real address 40 — so promoting it declares a non-increasing list.
    //     Refused by the GAP gate at row 2: `agap_2 = next.is_real · (addr_3 − addr_2 − 1)` was
    //     0 with `next.is_real = 0` and becomes `0 − 41 ≠ 0`. This is "strictly increasing",
    //     firing.
    let mut promoted = rows.clone();
    promoted[3][MB_IS_REAL] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &promoted),
        "the emitted gap gate must refuse a declared address that does not exceed its predecessor"
    );

    // (b) ⚑ DEMOTE A REAL ROW TO A PAD, keeping its magnitude witness. Refused by the MAGNITUDE
    //     gate: `achk − is_real·addr` becomes `40 − 0 ≠ 0`. A prover cannot quietly drop a
    //     declared address out of the list while its `achk` still says 40.
    let mut demoted = rows.clone();
    demoted[2][MB_IS_REAL] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &demoted),
        "the emitted magnitude gate must refuse a demoted row whose achk still witnesses its \
         address"
    );

    // (c) ⚑ BREAK THE PREFIX: make row 0 a pad while row 1 stays real, so the real rows are no
    //     longer an initial segment. The PREFIX gate fires — `(1 − is_real_0)·is_real_1 = 1` —
    //     and so does the magnitude gate at row 0 (`5 − 0 ≠ 0`), because a real address cannot be
    //     zeroed by the guard alone. ⚠ Both fire; the refusal is not attributable to the prefix
    //     gate ALONE by this test, and saying so is the point.
    let mut broken = rows.clone();
    broken[0][MB_IS_REAL] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &broken),
        "the emitted prefix + magnitude gates must refuse a real row hiding behind a pad"
    );

    // (d) ⚑ WIDEN THE GAP WITHOUT ITS WITNESS: bump the gap column, leaving the limbs. Refused by
    //     the 30-bit RECOMPOSITION gate — which is what makes the gap a BOUNDED integer and hence
    //     "increasing" rather than "different mod p".
    let mut widened = rows.clone();
    widened[0][MB_AGAP] = widened[0][MB_AGAP] + BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &widened),
        "the emitted gap decomposition must refuse a gap with no limb witness"
    );
}

/// The prover-level pole, stated at ITS OWN resolution: a non-increasing declared list and an
/// out-of-range address are refused by the ASSEMBLER. ⚠ That is a completeness-of-refusal fact,
/// not a constraint verdict — the constraint verdicts are the test above. Naming which is which
/// is the point: an assembler refusal quoted as a gate verdict is how an accepting gate hides.
#[test]
fn a_non_increasing_declaration_is_refused_by_the_deployed_prover() {
    let desc = mem_desc();

    let refused = must_refuse_or_unsat_panic("a non-increasing declared address list", || {
        prove_vm_descriptor2(
            &desc,
            &mem_trace(),
            &[],
            &MemBoundaryWitness {
                addrs: vec![9, 5, 40],
                init_vals: INITS.to_vec(),
            },
            &[],
        )
        .map(|_| ())
    });
    assert!(
        refused.reason().contains("strictly increasing"),
        "the refusal must name the reason: {}",
        refused.reason()
    );

    // ⚑ …and the MAGNITUDE bound, at the assembler. This is the deployed twin of the Lean file's
    // `wrap_witness_without_the_magnitude_bound`: an address at or above 2^30 is what a wrapping
    // chain needs, and it is refused before any constraint runs.
    let refused = must_refuse_or_unsat_panic("a declared address at or above 2^30", || {
        prove_vm_descriptor2(
            &desc,
            &mem_trace(),
            &[],
            &MemBoundaryWitness {
                addrs: vec![5, 9, 1 << 30],
                init_vals: INITS.to_vec(),
            },
            &[],
        )
        .map(|_| ())
    });
    assert!(
        refused.reason().contains(">= 2^30"),
        "the refusal must name the magnitude bound: {}",
        refused.reason()
    );
}

/// The emitted bus legs are the SIDES the memory argument needs. ⚠ This is the half the mutation
/// sweep is structurally blind to: no gate reads `MB_ADDR_MULT` or the Blum image columns, so a
/// `.query`-instead-of-`.provide` slip or a send/receive swap would leave every gate green and
/// break the argument silently. It is checked HERE, on the emitted object.
#[test]
fn the_boundary_serves_the_address_table_and_anchors_the_blum_chain() {
    let t = mem_boundary_table_air();

    // The closure table: this AIR is the SERVER, `Ir2Air::Memory` is the client.
    assert_eq!(t.bus_count_op("ir2_mem_addrs", BusOp::Provide), 1);
    assert_eq!(t.bus_count_op("ir2_mem_addrs", BusOp::Query), 0);
    let serve = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_mem_addrs")
        .expect("one served address entry");
    assert_eq!(serve.tuple, vec![TableExpr::Loc(MB_ADDR)]);
    assert_eq!(
        serve.mult,
        TableExpr::Loc(MB_ADDR_MULT),
        "the served count is the multiplicity COLUMN — a constant would refuse every witness \
         whose per-address op counts are not flat"
    );

    // The Blum pair, in the right directions and at the right anchor.
    let send = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Send)
        .expect("one init send");
    assert_eq!(
        send.tuple,
        vec![
            TableExpr::Loc(MB_ADDR),
            TableExpr::Loc(MB_INIT_VAL),
            TableExpr::Const(0)
        ],
        "the INIT image is published at serial ZERO — the anchor every read chain bottoms out in"
    );
    let recv = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Receive)
        .expect("one final receive");
    assert_eq!(
        recv.tuple,
        vec![
            TableExpr::Loc(MB_ADDR),
            TableExpr::Loc(MB_FIN_VAL),
            TableExpr::Loc(MB_FIN_SERIAL)
        ]
    );
    // Both ride at `is_real`, so a pad row contributes NOTHING to the multiset — the reason the
    // per-row multiplicity expression exists at all.
    assert_eq!(send.mult, TableExpr::Loc(MB_IS_REAL));
    assert_eq!(recv.mult, TableExpr::Loc(MB_IS_REAL));

    // Two transition-scoped gates (prefix, gap) and ten unfiltered ones.
    assert_eq!(t.gate_count_sel(RowSel::Transition), 2);
    assert_eq!(t.gate_count_sel(RowSel::All), 10);
    assert_eq!(t.gate_count_sel(RowSel::First), 0);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
}
