//! **THE SHARED LIMB TABLE'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::ByteTable` was a hand-written Rust arm: two `assert_zero` calls under p3 row filters
//! plus a `table_entry` leg. Architectural law #1 says that object is authored in Lean and Rust
//! only interprets. It was not. **That arm is now DELETED**; its author is
//! `metatheory/Dregg2/Circuit/Emit/ByteTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-byte-v1.json`, and `Ir2Air::LeanTable` walks it.
//!
//! ⚑ **WHY THIS TABLE MATTERS OUT OF ALL PROPORTION TO ITS TWO COLUMNS.** Every range check in
//! IR-v2 bottoms out here. `eval_decomp` splits a value into 4-bit limbs and queries each FULL
//! limb on `ir2_byte`; "this felt is 30 bits wide" MEANS "its limbs are rows of this table". So
//! the served key set IS the admissible limb range, for the memory gap bound, the boundary address
//! bound, the canonical key split and every comparator built on them.
//!
//! # The three questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    value and the multiplicity OUT of the prover's own byte trace.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2 — a per-column, per-row
//!    mutation sweep through the REAL deployed evaluator, with the undetected set pinned EXACTLY
//!    rather than bounded.)
//! 3. **Do both poles still hold at the deployed prover?** (§3.)
//!
//! # ⚠ What this cutover did NOT do
//!
//! It did not change the height, the range, or the pin that enforces it. The Lean side proves both
//! halves of the claim `BYTE_TABLE_HEIGHT`'s doc comment makes — `value_is_the_row_index` (the AIR
//! forces the value column to be the index) and `gates_admit_every_height` (the AIR does NOT bound
//! the height, so `verify_vm_descriptor2`'s separate check is what refuses a widened table).
//! `ir2_oversized_byte_table_refuses` is the deployed measurement of the second half and is
//! UNCHANGED by this cutover.

use dregg_circuit::descriptor_ir2::{
    BYTE_TABLE_HEIGHT, CHIP_OUT_LANES, EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness,
    VmConstraint2, WindowExpr, byte_rows_for, prove_vm_descriptor2, table_air_gates_accept,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::fold_bytes32_to_bb;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX};
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::table_air::{BusOp, RowSel, byte_table_air};

/// The deployed layout, transcribed ONCE here so the assertions below can name a column.
const BT_VALUE: usize = 0;
const BT_MULT: usize = 1;
const BT_WIDTH: usize = 2;

// -------------------------------------------------------------------------------------------
// An honest descriptor that USES the byte table. The map-absent gate's canonical decompositions
// are the system's densest byte-bus client, so this is a real consumer, not a synthetic one.
// -------------------------------------------------------------------------------------------

fn nullifier_of_note(nonce: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-note-nullifier-v1");
    h.update(&nonce.to_le_bytes());
    *h.finalize().as_bytes()
}

fn deployed_key(nf: &[u8; 32]) -> BabyBear {
    fold_bytes32_to_bb(nf)
}

fn absent_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "byte-lean-emission-differential".to_string(),
        trace_width: 18,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MapOp(MapOpSpec {
            guard: LeanExpr::Var(17),
            root: (0..CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            key: LeanExpr::Var(8),
            value: LeanExpr::Const(0),
            new_root: (9..9 + CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            op: MapKind::Absent,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

fn absent_trace(heap: &[HeapLeaf], key: BabyBear) -> Vec<Vec<BabyBear>> {
    let tree = CanonicalHeapTree8::new(heap.to_vec(), HEAP_TREE_DEPTH);
    let root = tree.root8();
    let mk = |guard: BabyBear| {
        let mut r = vec![BabyBear::ZERO; 18];
        r[0..CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[8] = key;
        r[9..9 + CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[17] = guard;
        r
    };
    vec![
        mk(BabyBear::ONE),
        mk(BabyBear::ZERO),
        mk(BabyBear::ZERO),
        mk(BabyBear::ZERO),
    ]
}

fn honest_setup() -> (Vec<HeapLeaf>, BabyBear) {
    let spent: Vec<[u8; 32]> = (20_000_000u64..20_000_024).map(nullifier_of_note).collect();
    let heap: Vec<HeapLeaf> = spent
        .iter()
        .map(|nf| HeapLeaf::entry(deployed_key(nf), BabyBear::new(7)))
        .collect();
    let tree = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH);
    let fresh = (30_000_000u64..30_010_000)
        .map(nullifier_of_note)
        .find(|nf| {
            let k = deployed_key(nf);
            tree.position_of(k).is_none()
                && k.as_u32() > 0
                && k.as_u32() < SENTINEL_MAX.as_u32()
                && tree
                    .sorted_leaves()
                    .iter()
                    .any(|l| l.addr.as_u32() < k.as_u32() && l.next_addr.as_u32() > k.as_u32())
        })
        .expect("an honest fresh nullifier exists");
    (heap, deployed_key(&fresh))
}

fn honest_byte_rows() -> Vec<Vec<BabyBear>> {
    let (heap, key) = honest_setup();
    byte_rows_for(&absent_desc(), &absent_trace(&heap, key), &[heap.clone()])
        .expect("the deployed prover assembles a byte table")
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP: the emitted algebra reads the columns the prover writes.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The Lean-emitted table declares width 2, anchors column 0 at
/// zero on the first row, increments it across every transition, and serves column 0 at
/// multiplicity column 1. The prover's OWN trace builder writes those columns. This reads them
/// back out and checks the value column IS the row index and the multiplicity column IS a genuine
/// nonzero histogram — not "the tables differ".
///
/// If the emission had swapped the two columns (a one-character slip that keeps every shape pin
/// green — width 2, two gates, one leg), the honest table would still satisfy nothing in
/// particular and this round-trip is what catches it.
#[test]
fn the_emitted_columns_round_trip_the_value_and_the_multiplicity() {
    let rows = honest_byte_rows();
    let t = byte_table_air();

    assert_eq!(t.width, BT_WIDTH);
    assert_eq!(
        rows.len(),
        BYTE_TABLE_HEIGHT,
        "the deployed byte table is exactly BYTE_TABLE_HEIGHT rows"
    );
    assert!(
        rows.iter().all(|r| r.len() == t.width),
        "the prover's rows are exactly the emitted width"
    );

    // ⚑ THE ROUND-TRIP, half one: the value column IS the row index — which is what makes the
    // served key set `[0, BYTE_TABLE_HEIGHT)` and therefore what a 4-bit limb bound MEANS.
    for (i, r) in rows.iter().enumerate() {
        assert_eq!(
            r[BT_VALUE],
            BabyBear::new(i as u32),
            "row {i}'s value column is not the row index"
        );
    }

    // Half two: the multiplicity column is a REAL histogram of this witness's limb queries, not a
    // constant. A table whose counts were all zero would satisfy every gate here and balance
    // nothing — so "some entry is consumed" is the anti-vacuity claim, and it must hold on a
    // witness whose canonical decompositions genuinely query limbs.
    let total: u64 = rows.iter().map(|r| u64::from(r[BT_MULT].as_u32())).sum();
    assert!(
        total > 0,
        "the honest witness queries no limb at all — the byte table is not exercised"
    );
    assert!(
        rows.iter().any(|r| r[BT_MULT] != BabyBear::ZERO),
        "every multiplicity is zero"
    );

    // The deployed evaluator accepts the honest table.
    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );

    println!(
        "MEASURED: {} byte-table rows, values 0..{}, total limb queries {}",
        rows.len(),
        rows.len() - 1,
        total
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP: no gate was lost, and the undetected set is pinned EXACTLY.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every row and every column, bump the value and ask the REAL deployed
/// evaluator whether the table still accepts.
///
/// The byte table is small enough that the undetected set can be pinned EXACTLY rather than
/// bounded, and the answer is the interesting part:
///
/// * **column 0 (value) is gated on every row** — row 0 by the `.first` anchor, every other row
///   by the `.transition` increment reading the PREVIOUS row's value. Both gates are needed:
///   without the anchor the whole chain could be shifted (every value +k, still incrementing);
///   without the increment the rows after the first are free.
/// * **column 1 (multiplicity) is gated on NO row** — and that is correct, not a hole. Its
///   discipline is the LogUp balance, which is a property of the assembled batch and which no
///   single-AIR gate check can decide. Saying so exactly is the point: an instrument that reported
///   "2 of 2 columns gated" would be lying about which mechanism protects what.
#[test]
fn every_gated_byte_cell_is_still_gated_after_the_cutover() {
    let rows = honest_byte_rows();
    let t = byte_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    let mut detected: Vec<(usize, usize)> = Vec::new();
    let mut undetected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
            // TWO bumps, for the same reason the map-absent sweep uses two: a `+1` on a column
            // whose honest value is adjacent to another admissible one reports a live gate as
            // dead. A genuinely ungated column survives both.
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

    // ⚑ EVERY value cell is gated — not "the first" and not "most".
    for row in 0..rows.len() {
        assert!(
            detected.contains(&(row, BT_VALUE)),
            "row {row}'s value column lost its gate in the Lean re-emission — detected: \
             {detected:?}"
        );
    }

    // ⚑ AND THE OTHER SIDE, said rather than implied. The multiplicity column is bound by the
    // BUS, not by a gate, so it must be undetected on every row — and NOTHING ELSE may be.
    let expected_undetected: Vec<(usize, usize)> = (0..rows.len()).map(|r| (r, BT_MULT)).collect();
    assert_eq!(
        undetected, expected_undetected,
        "the undetected set is not exactly the multiplicity column — either a gate was lost or a \
         gate appeared where the LogUp balance is supposed to be the mechanism"
    );

    println!(
        "MEASURED: {}/{} byte-table cells are gated by the Lean emission; the undetected {} are \
         exactly the multiplicity column (bus-bound, by construction)",
        detected.len(),
        detected.len() + undetected.len(),
        undetected.len()
    );
}

/// ⚑ **THE SELECTOR IS LOAD-BEARING, MEASURED AT THE EVALUATOR.** The increment gate is
/// `.transition`-scoped. Re-scoping it to `.all` would leave the algebra byte-identical and make
/// the honest table UNSAT, because on the last row p3's `next` is the WRAP row (value 0), and
/// `0 = 15 + 1` is false.
///
/// This measures the direction that a body-only differential cannot see. The mutation sweep above
/// fires the deployed selectors; this shows what they are DOING by exhibiting the row the
/// transition gate must NOT bind.
#[test]
fn the_increment_gate_does_not_bind_the_wrap_row() {
    let rows = honest_byte_rows();
    let t = byte_table_air();

    // The honest table wraps: the last row's value is `height - 1`, the first row's is 0, and
    // those two are p3's `local`/`next` on the final row.
    let last = rows.len() - 1;
    assert_eq!(rows[last][BT_VALUE], BabyBear::new(last as u32));
    assert_eq!(rows[0][BT_VALUE], BabyBear::ZERO);
    assert_ne!(
        rows[0][BT_VALUE],
        rows[last][BT_VALUE] + BabyBear::ONE,
        "the wrap step is NOT an increment — so an `.all`-scoped gate would refuse this table"
    );

    // …and the deployed evaluator accepts anyway, which is only possible because the gate is
    // transition-scoped.
    assert!(table_air_gates_accept(&t, &rows));

    // The emission says so too: exactly one transition gate, exactly one first-row gate, and no
    // unfiltered gate at all.
    assert_eq!(t.gate_count_sel(RowSel::Transition), 1);
    assert_eq!(t.gate_count_sel(RowSel::First), 1);
    assert_eq!(t.gate_count_sel(RowSel::All), 0);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** An honest witness whose range checks ride the byte table proves and verifies
/// through the Lean-emitted AIR.
#[test]
fn an_honest_witness_proves_and_verifies_through_the_lean_byte_emission() {
    let (heap, key) = honest_setup();
    let desc = absent_desc();
    let proof = prove_vm_descriptor2(
        &desc,
        &absent_trace(&heap, key),
        &[],
        &MemBoundaryWitness::default(),
        &[heap.clone()],
    )
    .expect("an honest witness must prove through the Lean-emitted byte AIR");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES.** A table that lies about its values is refused,
/// in each of the three ways it can lie. Each forgery keeps the shape (16 rows, 2 columns) and
/// changes only what the table SAYS, so a re-emission that dropped either gate would accept one
/// of these and hand every range check in the system a wider admissible set.
#[test]
fn a_forged_value_column_is_refused_by_the_emitted_gates() {
    let rows = honest_byte_rows();
    let t = byte_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // (a) SHIFT THE WHOLE CHAIN. Every value +1: still a perfect increment chain, so the
    //     `.transition` gate is satisfied on every row — and the table now serves `[1, 16]`,
    //     admitting the out-of-range limb 16. Only the `.first` anchor refuses this.
    let mut shifted = rows.clone();
    for r in shifted.iter_mut() {
        r[BT_VALUE] = r[BT_VALUE] + BabyBear::ONE;
    }
    assert!(
        !table_air_gates_accept(&t, &shifted),
        "the `.first` anchor must refuse a chain that starts at 1 — otherwise the served range \
         slides and a limb of 16 becomes admissible"
    );

    // (b) BREAK ONE STEP. Anchor intact, one interior row duplicated: the table would serve a
    //     value twice and skip one. Only the `.transition` increment refuses this.
    let mut stuck = rows.clone();
    stuck[7][BT_VALUE] = stuck[6][BT_VALUE];
    assert!(
        !table_air_gates_accept(&t, &stuck),
        "the `.transition` increment must refuse a repeated value"
    );

    // (c) SKIP AHEAD. Anchor intact, a jump in the middle — the shape a prover would want in
    //     order to serve a value above the height without growing the table.
    let mut jumped = rows.clone();
    jumped[9][BT_VALUE] = jumped[9][BT_VALUE] + BabyBear::new(64);
    assert!(
        !table_air_gates_accept(&t, &jumped),
        "the `.transition` increment must refuse a jump"
    );
}

/// The emitted leg is the `.provide` SIDE of `ir2_byte`, carrying the value at the multiplicity
/// column. ⚠ This is the half the mutation sweep is structurally blind to: no gate reads the
/// multiplicity, so a `.query`-instead-of-`.provide` slip would leave every gate green and make
/// the bus unsatisfiable in one direction and vacuous in the other. It is checked HERE, on the
/// emitted object, because there is nowhere else it can be checked.
#[test]
fn the_byte_table_serves_the_bus_it_does_not_query_it() {
    let t = byte_table_air();
    assert_eq!(t.interactions.len(), 1);
    assert_eq!(t.bus_count_op("ir2_byte", BusOp::Provide), 1);
    assert_eq!(t.bus_count_op("ir2_byte", BusOp::Query), 0);

    let leg = &t.interactions[0];
    assert_eq!(leg.bus, "ir2_byte");
    assert_eq!(leg.op, BusOp::Provide);
    assert_eq!(leg.tuple.len(), 1, "the served key is one felt: the value");
    assert_eq!(leg.tuple[0], WindowExpr::Loc(BT_VALUE));
    assert_eq!(
        leg.mult,
        WindowExpr::Loc(BT_MULT),
        "the leg rides at the multiplicity COLUMN — a constant here would refuse every honest \
         witness whose limb histogram is not flat"
    );
}
