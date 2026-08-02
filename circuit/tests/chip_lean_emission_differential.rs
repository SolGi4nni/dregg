//! **THE SHARED HASH CHIP'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::Chip | Ir2Air::ChipState16` was the largest hand-written Rust arm in IR-v2: ~280 lines
//! of `builder.assert_zero(..)` for the arity/selector algebra, the seeding and the output binding,
//! plus the 352 constraints `poseidon2_permute_expr_lanes` emitted inline. Architectural law #1
//! says that object is authored in Lean and Rust only INTERPRETS. It was not. **That arm is now
//! DELETED**; its authors are `metatheory/Dregg2/Circuit/Emit/{ChipTableEmit,Poseidon2RoundGates}.lean`,
//! its emissions are `circuit/descriptors/table-airs/dregg-ir2-chip{,-state16}-v1.json`, and
//! `Ir2Air::LeanTable` walks them.
//!
//! ⚑ **WHY THIS TABLE MATTERS MORE THAN ANY OTHER.** Every IR-v2 proof carries a chip instance, and
//! ONE table serves every hash fact in the batch: the main trace's hash-site lookups, the map-ops
//! and map-absent leaf absorbs, the Merkle-chain node compressions. Its arity column IS the
//! domain separation between them.
//!
//! # ⚑ AND IT IS THE TABLE THE SHARING NODE EXISTS FOR
//!
//! A previous pass authored this AIR in Lean, measured that a TREE IR costs the prover **44×** what
//! the hand-written arm costs it — the arm holds each round's 16 S-box values as `AB::Expr` VALUES
//! and the linear layer reads each 35 times; a tree duplicates them — and STOPPED rather than
//! cutting an artifact that would have made the deployed chip that much heavier. `TableAirIR.TExpr`
//! now has a `shr` leaf and `TableAir` a `defs` list, so the emission carries the SAME sharing the
//! deleted arm had:
//!
//! |                    | TREE spelling | SHARED (emitted) | ratio |
//! |--------------------|---------------|------------------|-------|
//! | expression nodes   | 141,439       | 7,355            | 19.2× |
//! | arithmetic ops     | 70,524        | 2,943            | 24.0× |
//! | artifact bytes     | 3,098,882     | 159,180          | 19.5× |
//! | per-row evaluation | 3.570 ms      | 146.2 µs         | 24.4× |
//!
//! The last row is measured HERE, on the deployed evaluator, on the prover's own honest row.
//!
//! # The questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    arity, the inputs and all eight output lanes OUT of the prover's own chip row.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2 — a per-column mutation
//!    sweep through the REAL deployed evaluator, with the undetected set pinned EXACTLY.)
//! 3. **Is the SHARING semantics-preserving, or did the emission shrink and change?** (§3.)
//! 4. **Do both poles still hold at the deployed prover?** (§4.)
//!
//! # ⚠ FOUR OF THE DELETED ARM'S COMMENTS WERE FALSE, and the refutations are the load-bearing half
//!
//! Proved on the emitted object in `ChipTableEmit.lean` §7, restated here so a reader of the Rust
//! side finds them:
//!
//! 1. **`p7`/`p11`/`p16` were described BACKWARDS, three times** (`descriptor_ir2.rs:3255/3269/3283`
//!    before deletion). *"p7 ≠ 0 ⇔ arity ∈ {0,2,3,4,11,16} (= 0 exactly at arity 7)"* is exactly
//!    inverted: `p7` is the product over every declared arity EXCEPT 7, so it VANISHES on all six
//!    named and is nonzero ONLY at 7 — which is what makes `p7·(1−big)` force `big` high there.
//!    Read literally the comment says the gate forces `big` HIGH on the pad row. The CODE was
//!    right. (`forcing_products_vanish_off_their_own_arity`, `p7_comment_is_inverted`;
//!    §2b below measures the same thing at the deployed evaluator.)
//! 2. **`seed456 ∈ {0,1}` was credited to the wrong gate.** The comment said *"the membership gate
//!    forces distinct arity values 7/11/16"*; `seed456_is_boolean` never touches it — the three
//!    `flag·(arity − c)` pins alone do it. It matters because the membership gate is the one a
//!    future narrowing of the arity set would edit.
//! 3. **`arity ∈ {0,2,3,4,7,11,16}` is a claim about RESIDUES, not integers.**
//!    `accepts_arity_equal_to_p` exhibits an ACCEPTED row carrying `arity = 2013265921`. Nothing is
//!    broken by it (the bus matches field elements too), but a range check that trusted the
//!    sentence would check the wrong thing.
//! 4. **The `(1 − is_fact)` factor on the state16 bus multiplicity is DEAD.**
//!    `state16_bus_guard_is_dead`: no satisfying row has `mult_state16 ≢ 0` and `is_fact ≡ 1`, so
//!    the factor never differs from `1` where it could matter. §5 measures it here.

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, chip_absorb_all_lanes, chip_honest_row, table_air_gates_accept,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::table_air::{
    BusOp, RowSel, TableExpr, chip_state16_table_air, chip_table_air, parse_table_air,
};

/// The deployed layout, transcribed ONCE here so the assertions below can name a column. Derived
/// from the same arithmetic `ChipTableEmit.lean` §1 derives it from, not copied from the Lean
/// `#guard`s, so the two sides stay independent.
const CHIP_ARITY: usize = 0;
const CHIP_IN0: usize = 1;
const CHIP_OUT: usize = CHIP_IN0 + CHIP_RATE;
const CHIP_MULT: usize = CHIP_OUT + CHIP_OUT_LANES;
const CHIP_IS_FACT: usize = CHIP_MULT + 1;
const CHIP_BIG: usize = CHIP_IS_FACT + 1;
const CHIP_S4: usize = CHIP_BIG + 1;
const CHIP_S6: usize = CHIP_S4 + 2;
const CHIP_WIDE: usize = CHIP_S6 + 1;
const CHIP_NODE8: usize = CHIP_WIDE + 1;
const CHIP_AUX0: usize = CHIP_NODE8 + 1;
const CHIP_MULT_NARROW: usize = CHIP_AUX0 + 352;
const CHIP_WIDTH: usize = CHIP_MULT_NARROW + 1;

/// The honest arity-16 `node8` compression row the deployed witness generator emits — every one of
/// the sixteen input lanes genuinely used, so no lane is inert for a structural reason.
fn honest_node8_row() -> Vec<BabyBear> {
    let ins: Vec<BabyBear> = (0..CHIP_RATE as u32)
        .map(|i| BabyBear::new(3 + 7 * i))
        .collect();
    chip_honest_row(16, &ins)
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP: the emitted algebra reads the columns the prover writes.
// -------------------------------------------------------------------------------------------

/// ⚑ The arity, all sixteen inputs and all EIGHT output lanes round-trip out of the prover's own
/// row, and the deployed evaluator accepts it.
///
/// The output half is the one that matters: `out[1..8]` were added by the tuple-widening pass and
/// are equality-bound to the permutation's genuine distinct final lanes, not to copies of `out[0]`.
/// A re-emission that bound them to lane 0 would still accept an honest row where the lanes
/// happened to be read back — so the check is against `chip_absorb_all_lanes`, the deployed
/// generator's own eight-lane squeeze, computed independently of the AIR.
#[test]
fn the_chip_row_round_trips_out_of_the_provers_own_witness() {
    let t = chip_table_air();
    assert_eq!(t.name, "dregg-ir2-chip-v1");
    assert_eq!(t.width, CHIP_WIDTH);
    assert_eq!(t.width, 386);

    let ins: Vec<BabyBear> = (0..CHIP_RATE as u32)
        .map(|i| BabyBear::new(3 + 7 * i))
        .collect();
    let row = honest_node8_row();
    assert_eq!(row.len(), t.width, "the prover's row is the emitted width");

    assert_eq!(row[CHIP_ARITY], BabyBear::new(16));
    for (i, v) in ins.iter().enumerate() {
        assert_eq!(row[CHIP_IN0 + i], *v, "input lane {i}");
    }
    // The eight output lanes, against an INDEPENDENT source: the deployed absorb.
    let lanes = chip_absorb_all_lanes(16, &ins);
    for i in 0..CHIP_OUT_LANES {
        assert_eq!(row[CHIP_OUT + i], lanes[i], "output lane {i}");
    }
    // …and they are genuinely EIGHT DISTINCT values, not eight copies of the digest.
    let distinct: std::collections::BTreeSet<u32> = (0..CHIP_OUT_LANES)
        .map(|i| row[CHIP_OUT + i].as_u32())
        .collect();
    assert_eq!(
        distinct.len(),
        CHIP_OUT_LANES,
        "the exposed lanes are not distinct — a differential against them would be vacuous"
    );

    assert!(
        table_air_gates_accept(&t, &[row]),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest chip row"
    );
}

/// The four other admitted arities round-trip too, so the differential is not a statement about
/// one branch of a seven-way selector.
#[test]
fn every_admitted_arity_round_trips() {
    let t = chip_table_air();
    for arity in [0u32, 2, 3, 4, 7, 11, 16] {
        let ins: Vec<BabyBear> = (0..arity).map(|i| BabyBear::new(11 + 5 * i)).collect();
        let row = chip_honest_row(arity, &ins);
        assert_eq!(row[CHIP_ARITY], BabyBear::new(arity), "arity {arity}");
        let lanes = chip_absorb_all_lanes(arity as usize, &ins);
        for i in 0..CHIP_OUT_LANES {
            assert_eq!(row[CHIP_OUT + i], lanes[i], "arity {arity} output lane {i}");
        }
        assert!(
            table_air_gates_accept(&t, &[row]),
            "the emitted chip AIR must accept the honest arity-{arity} row"
        );
    }
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP: no gate was lost, and the undetected set is pinned EXACTLY.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every one of the 386 columns, bump the honest row and ask the REAL
/// deployed evaluator whether the table still accepts.
///
/// TWO bumps, for the reason the map-absent sweep uses two: a `+1` on a column whose honest value
/// is adjacent to another admissible one reports a live gate as dead. A genuinely ungated column
/// survives both.
///
/// ⚑ **The undetected set is pinned EXACTLY, and it is exactly the two MULTIPLICITY columns.**
/// `CHIP_MULT` and `CHIP_MULT_NARROW` are the counts the served `ir2_p2` / `ir2_p2_narrow` /
/// `ir2_fact` legs ride at, and no gate on any row reads them: their discipline is the LogUp
/// balance of the assembled batch, which is a property of another object and which no single-AIR
/// gate check can decide. Saying that exactly is the point — an instrument that reported
/// "386 of 386 columns gated" would be lying about which mechanism protects what.
#[test]
fn every_gated_chip_cell_is_still_gated_after_the_cutover() {
    let t = chip_table_air();
    let row = honest_node8_row();
    assert!(
        table_air_gates_accept(&t, &[row.clone()]),
        "honest baseline"
    );

    let mut detected: Vec<usize> = Vec::new();
    let mut undetected: Vec<usize> = Vec::new();
    for col in 0..t.width {
        let caught = [1u32, 2u32].iter().any(|&d| {
            let mut mutated = row.clone();
            mutated[col] = mutated[col] + BabyBear::new(d);
            !table_air_gates_accept(&t, &[mutated])
        });
        if caught {
            detected.push(col);
        } else {
            undetected.push(col);
        }
    }

    assert_eq!(
        undetected,
        vec![CHIP_MULT, CHIP_MULT_NARROW],
        "the undetected set is not exactly the two multiplicity columns — either a gate was lost \
         in the Lean re-emission or a gate appeared where the LogUp balance is the mechanism"
    );
    assert_eq!(detected.len(), CHIP_WIDTH - 2);

    println!(
        "MEASURED: {}/{} chip columns are gated by the Lean emission; the undetected {} are \
         exactly the multiplicity columns (bus-bound, by construction)",
        detected.len(),
        CHIP_WIDTH,
        undetected.len()
    );
}

/// ⚑ **THE 352 AUX COLUMNS ARE EVERY ONE OF THEM GATED**, said separately because they are 91% of
/// the table and because they are what the sharing node re-expressed. A `shr` that resolved to the
/// wrong definition would leave some round's block free, and the sweep above would report it inside
/// a 386-column total; here it is named.
#[test]
fn every_permutation_aux_column_is_gated() {
    let t = chip_table_air();
    let row = honest_node8_row();
    for col in CHIP_AUX0..CHIP_AUX0 + 352 {
        let mut mutated = row.clone();
        mutated[col] = mutated[col] + BabyBear::ONE;
        assert!(
            !table_air_gates_accept(&t, &[mutated]),
            "aux column {col} (round block {}, lane {}) is NOT gated — a permutation round lost \
             its binding in the shared re-emission",
            (col - CHIP_AUX0) / 16,
            (col - CHIP_AUX0) % 16
        );
    }
}

/// ⚑ **§2b — THE INVERTED-COMMENT GATE, MEASURED AT THE DEPLOYED EVALUATOR.** The deleted arm's
/// comment said `p7` is nonzero on `{0,2,3,4,11,16}` and zero at 7. If that were true, an
/// arity-7 row with `big` LOW would be ACCEPTED and a pad row would need `big` HIGH. Both are
/// measured here and both come out the other way.
#[test]
fn the_p7_forcing_products_bind_the_opposite_way_to_the_deleted_comment() {
    let t = chip_table_air();

    // The honest arity-7 leaf row has `big` HIGH. Clearing it must be REFUSED — which is only
    // possible if `p7` is NONZERO at arity 7, the opposite of what the comment said.
    let ins: Vec<BabyBear> = (0..7u32).map(|i| BabyBear::new(2 + i)).collect();
    let mut row = chip_honest_row(7, &ins);
    assert_eq!(
        row[CHIP_BIG],
        BabyBear::ONE,
        "the honest arity-7 row sets big"
    );
    assert!(table_air_gates_accept(&t, &[row.clone()]), "honest arity-7");
    row[CHIP_BIG] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &[row]),
        "arity 7 with `big` LOW was accepted — `p7` would have to VANISH at arity 7, which is what \
         the deleted comment claimed"
    );

    // …and the PAD row (arity 0) has `big` LOW and is accepted, so `p7` does NOT force it high
    // there — the reading the comment's own words produce.
    let pad = chip_honest_row(0, &[]);
    assert_eq!(pad[CHIP_BIG], BabyBear::ZERO);
    assert!(
        table_air_gates_accept(&t, &[pad]),
        "the pad row was refused — `p7·(1−big)` would have to force `big` HIGH there, which is \
         what the deleted comment says when read literally"
    );

    // The same shape for `node8` at arity 16.
    let mut n8 = honest_node8_row();
    assert_eq!(n8[CHIP_NODE8], BabyBear::ONE);
    n8[CHIP_NODE8] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &[n8]),
        "arity 16 with `node8` LOW was accepted"
    );
}

// -------------------------------------------------------------------------------------------
// §3 — THE SHARING IS SEMANTICS-PRESERVING, AND IT IS WHAT THE PROVER PAYS.
// -------------------------------------------------------------------------------------------

/// ⚑ **THE DEFINITION LIST IS REAL, ORDERED, AND READ.** A `defs` list that decoded and then went
/// unused would shrink the artifact and change nothing; a list whose gates read it but whose order
/// was wrong would silently resolve shares to `0`. Both are excluded here, on the decoded object.
#[test]
fn the_emitted_chip_carries_an_ordered_definition_list_its_gates_read() {
    for t in [chip_table_air(), chip_state16_table_air()] {
        assert_eq!(t.def_count(), 1078, "{}", t.name);
        // Ordered: `parse_table_air` refuses a forward reference, so decoding at all is the
        // acyclicity check. Assert the shape it guarantees, so a decoder regression is visible.
        for (i, d) in t.defs.iter().enumerate() {
            if let Some(m) = d.max_share() {
                assert!(m < i, "{}: definition {i} reads {m}", t.name);
            }
        }
        // READ: some gate names the LAST definition, so the list is not padded with dead entries.
        let last = t.def_count() - 1;
        assert!(
            t.gates.iter().any(|g| g.body.max_share() == Some(last)),
            "{}: no gate reads the final definition",
            t.name
        );
        // …and the sharing is where the permutation is: the arity/selector/seeding block reads
        // NO definition, which is what lets the Lean sub-table proofs carry back to this object.
        let share_free = t
            .gates
            .iter()
            .filter(|g| g.body.max_share().is_none())
            .count();
        assert_eq!(
            share_free,
            if t.name == "dregg-ir2-chip-v1" {
                39
            } else {
                40
            },
            "{}: the share-free gate count moved — 31 (or 32) selector gates + 8 output bindings",
            t.name
        );
    }
}

/// ⚑ **SHARING CHANGES REPRESENTATION, NOT DEGREE.** A `Shr` treated as a leaf would report the
/// chip's degree-7 S-box as degree 1 and silently under-size the quotient. The emitted table's
/// resolved max degree is 7 — the same number `ir2_degree_budget` freezes, and the same number the
/// deleted arm announced as a hardcoded `Some(7)`.
#[test]
fn the_shared_emission_has_the_same_degree_as_the_deleted_arm() {
    for t in [chip_table_air(), chip_state16_table_air()] {
        assert_eq!(t.max_degree(), 7, "{}", t.name);
        // …and the S-box's four definitions really do climb 2, 3, 4, 7 — so the degree is coming
        // out of the definition pass rather than from some unrelated gate.
        let dd = t.def_degrees();
        assert_eq!(*dd.iter().max().unwrap(), 7, "{}", t.name);
        let mut counts = std::collections::BTreeMap::<usize, usize>::new();
        for d in &dd {
            *counts.entry(*d).or_insert(0) += 1;
        }
        assert!(counts.contains_key(&2) && counts.contains_key(&3) && counts.contains_key(&4));
        println!("{}: definition degrees {counts:?}", t.name);
    }
}

/// ⚑ **THE MEASUREMENT THE SHARING NODE EXISTS FOR** — per-row evaluation through the DEPLOYED
/// evaluator, tree spelling against shared spelling, on the prover's own honest row.
///
/// The tree spelling is 3.1 MB and is NOT checked in; it is rebuilt here from the shared emission's
/// own definitions by INLINING every `Shr`, so the two objects are the same polynomial by
/// construction rather than by two emitters agreeing. That also makes this an agreement check: the
/// inlined table must accept and refuse exactly where the shared one does.
///
/// ⚠ The absolute microseconds are machine-dependent and are printed, not asserted. What is
/// asserted is the RATIO, at a floor far below the measured 24×, so the test says "the sharing is
/// load-bearing" without pinning a number that a faster laptop would break.
#[test]
fn the_shared_emission_evaluates_an_order_of_magnitude_faster_than_the_tree() {
    let shared = chip_table_air();
    let tree = inline_all_shares(&shared);
    assert_eq!(tree.def_count(), 0, "the inlined table shares nothing");
    assert_eq!(tree.gates.len(), shared.gates.len());

    let row = honest_node8_row();
    assert!(table_air_gates_accept(&shared, &[row.clone()]));
    assert!(
        table_air_gates_accept(&tree, &[row.clone()]),
        "the inlined tree must accept the same honest row — otherwise the sharing changed the \
         polynomial rather than its representation"
    );
    // …and REFUSES the same mutations, so the comparison is between two live evaluators.
    for col in [CHIP_OUT, CHIP_AUX0, CHIP_AUX0 + 176, CHIP_IN0] {
        let mut bad = row.clone();
        bad[col] = bad[col] + BabyBear::ONE;
        assert_eq!(
            table_air_gates_accept(&tree, &[bad.clone()]),
            table_air_gates_accept(&shared, &[bad]),
            "the two spellings disagree on a mutation at column {col}"
        );
    }

    let time = |t: &dregg_circuit::table_air::LeanTableAir, n: u32| {
        for _ in 0..2 {
            table_air_gates_accept(t, std::slice::from_ref(&row));
        }
        let st = Instant::now();
        for _ in 0..n {
            std::hint::black_box(table_air_gates_accept(t, std::slice::from_ref(&row)));
        }
        st.elapsed() / n
    };
    let tree_t = time(&tree, 5);
    let shared_t = time(&shared, 50);
    println!("MEASURED per-row evaluation: TREE {tree_t:?}, SHARED {shared_t:?}");
    assert!(
        tree_t.as_nanos() > 5 * shared_t.as_nanos(),
        "the shared emission is not materially faster than the tree ({tree_t:?} vs {shared_t:?}) \
         — either the definition prelude stopped memoising or the emission stopped sharing"
    );
}

/// Inline every `Shr` in a table, producing the TREE spelling of the same polynomials.
fn inline_all_shares(
    t: &dregg_circuit::table_air::LeanTableAir,
) -> dregg_circuit::table_air::LeanTableAir {
    fn go(e: &TableExpr, resolved: &[TableExpr]) -> TableExpr {
        match e {
            TableExpr::Shr(i) => resolved[*i].clone(),
            TableExpr::Add(a, b) => {
                TableExpr::Add(Box::new(go(a, resolved)), Box::new(go(b, resolved)))
            }
            TableExpr::Mul(a, b) => {
                TableExpr::Mul(Box::new(go(a, resolved)), Box::new(go(b, resolved)))
            }
            other => other.clone(),
        }
    }
    let mut resolved: Vec<TableExpr> = Vec::with_capacity(t.defs.len());
    for d in &t.defs {
        let r = go(d, &resolved);
        resolved.push(r);
    }
    dregg_circuit::table_air::LeanTableAir {
        name: t.name.clone(),
        width: t.width,
        defs: Vec::new(),
        gates: t
            .gates
            .iter()
            .map(|g| dregg_circuit::table_air::TableGate {
                sel: g.sel,
                body: go(&g.body, &resolved),
            })
            .collect(),
        interactions: t
            .interactions
            .iter()
            .map(|i| dregg_circuit::table_air::TableInteraction {
                bus: i.bus.clone(),
                op: i.op,
                mult: go(&i.mult, &resolved),
                tuple: i.tuple.iter().map(|e| go(e, &resolved)).collect(),
            })
            .collect(),
    }
}

// -------------------------------------------------------------------------------------------
// §4 — SHAPE AND SIDES.
// -------------------------------------------------------------------------------------------

/// The emitted shape, derived from the layout rather than transcribed from the Lean `#guard`s.
#[test]
fn the_chip_emission_decodes_at_the_deployed_shape() {
    let t = chip_table_air();
    // 2 booleans/membership + 1 fact-arity + 3·3 flag gates + 16 input-zeroing + 3 seeding = 31,
    // then 352 permutation gates, then 8 output bindings.
    assert_eq!(t.gates.len(), 31 + 352 + CHIP_OUT_LANES);
    assert_eq!(t.gates.len(), 391);
    assert_eq!(t.gate_count_sel(RowSel::All), 391, "the chip is ROW-LOCAL");
    assert_eq!(t.gate_count_sel(RowSel::Transition), 0);
    assert_eq!(t.gate_count_sel(RowSel::First), 0);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
    assert!(t.gates.iter().all(|g| !t.gate_reads_next(g)));

    let s = chip_state16_table_air();
    assert_eq!(s.gates.len(), 392, "one more gate: the state16 arity pin");
    assert_eq!(s.width, t.width);
    assert_eq!(s.def_count(), t.def_count());
}

/// ⚑ The chip's absorb legs ride at `mult · (1 − is_fact)` and the fact leg at `mult · is_fact`, so
/// a fact row provides ZERO on the absorb buses and vice versa. That is the field a descriptor
/// `Lookup` could not carry, and a decoder that dropped it would break the LogUp balance rather
/// than a gate — invisible to §2's sweep.
#[test]
fn the_chip_legs_carry_the_fact_split_as_a_multiplicity_expression() {
    let t = chip_table_air();
    for i in &t.interactions {
        assert_eq!(i.op, BusOp::Provide, "leg on {} is not a Provide", i.bus);
        assert!(
            matches!(i.mult, TableExpr::Mul(_, _)),
            "the {} leg's multiplicity is not a product — the fact split is gone: {:?}",
            i.bus,
            i.mult
        );
    }
    let absorb = t.interactions.iter().find(|i| i.bus == "ir2_p2").unwrap();
    assert_eq!(absorb.tuple.len(), 1 + CHIP_RATE + CHIP_OUT_LANES);
    assert_eq!(absorb.tuple.len(), 25);
    assert!(matches!(absorb.tuple[0], TableExpr::Loc(CHIP_ARITY)));
    let narrow = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_p2_narrow")
        .unwrap();
    assert_eq!(narrow.tuple.len(), 1 + CHIP_RATE + 1, "no output lanes");
    let fact = t.interactions.iter().find(|i| i.bus == "ir2_fact").unwrap();
    assert_eq!(fact.tuple.len(), 3, "(l, r, out)");
}

// -------------------------------------------------------------------------------------------
// §5 — ⚠ THE DEAD GUARD, MEASURED.
// -------------------------------------------------------------------------------------------

/// ⚑ **THE `(1 − is_fact)` FACTOR ON THE STATE16 BUS CAN NEVER FIRE**, measured at the deployed
/// evaluator rather than only proved in Lean (`state16_bus_guard_is_dead`).
///
/// The state16 pin forces `arity = 16` on any row with a nonzero state multiplicity, and
/// `is_fact·arity` forces `arity = 0` on any fact row. `16 ≠ 0`, so no satisfying row has both —
/// and the factor therefore equals `mult_state16` on every row where it is consulted. It is not
/// WRONG; it is a factor that can never do anything, which is a thing this repo's doctrine says not
/// to keep. Recorded rather than deleted, because deleting it is a Lean-side emission change and it
/// belongs with whatever else moves that artifact.
#[test]
fn the_state16_fact_guard_is_unsatisfiable_and_therefore_dead() {
    let t = chip_state16_table_air();
    let mut row = honest_node8_row();
    row[CHIP_MULT_NARROW] = BabyBear::new(3); // CHIP_MULT_STATE16 is the same column
    assert!(
        table_air_gates_accept(&t, &[row.clone()]),
        "arity 16 at a nonzero state multiplicity must be accepted"
    );
    // Setting `is_fact` on that row is REFUSED — so `mult_state16 ≢ 0 ∧ is_fact = 1` is UNSAT and
    // the `(1 − is_fact)` factor has no reachable row on which it differs from 1.
    let mut fact = row.clone();
    fact[CHIP_IS_FACT] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &[fact]),
        "a fact row at a nonzero state multiplicity was ACCEPTED — the guard would then be live"
    );

    // …and the extra state16 gate is NOT decoration: an arity-4 absorb at a nonzero state
    // multiplicity is refused, while the same row at ZERO multiplicity is accepted.
    let ins: Vec<BabyBear> = (0..4u32).map(|i| BabyBear::new(1 + i)).collect();
    let mut a4 = chip_honest_row(4, &ins);
    assert!(
        table_air_gates_accept(&t, &[a4.clone()]),
        "arity 4 at ZERO state multiplicity must stay free"
    );
    a4[CHIP_MULT_NARROW] = BabyBear::new(3);
    assert!(
        !table_air_gates_accept(&t, &[a4]),
        "arity 4 at a nonzero state multiplicity was accepted — the fixed length tag could be \
         laundered through a seed-from-zero absorb row"
    );
}

/// ⚠ …and the LEGACY chip does NOT carry that gate, so the two artifacts are not interchangeable.
#[test]
fn the_legacy_chip_lacks_the_state16_pin() {
    let legacy = chip_table_air();
    let ins: Vec<BabyBear> = (0..4u32).map(|i| BabyBear::new(1 + i)).collect();
    let mut a4 = chip_honest_row(4, &ins);
    a4[CHIP_MULT_NARROW] = BabyBear::new(3);
    assert!(
        table_air_gates_accept(&legacy, &[a4]),
        "the legacy chip must NOT pin arity on the narrow multiplicity column — it is the narrow \
         bus count there, not a state multiplicity"
    );
}

/// The checked-in artifacts are the ones the decoder reads, and they decode. A byte-level pin on a
/// 159 KB artifact would be unreadable; the shape pins above plus this are the tripwire.
#[test]
fn the_checked_in_chip_artifacts_decode() {
    for (path, name) in [
        (
            "circuit/descriptors/table-airs/dregg-ir2-chip-v1.json",
            "dregg-ir2-chip-v1",
        ),
        (
            "circuit/descriptors/table-airs/dregg-ir2-chip-state16-v1.json",
            "dregg-ir2-chip-state16-v1",
        ),
    ] {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join(path);
        let src = std::fs::read_to_string(&root).unwrap_or_else(|e| panic!("{path}: {e}"));
        let t = parse_table_air(&src).unwrap_or_else(|e| panic!("{path}: {e}"));
        assert_eq!(t.name, name);
        assert_eq!(t.width, CHIP_WIDTH);
        assert_eq!(t.def_count(), 1078);
    }
}
