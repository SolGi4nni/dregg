//! **THE MAP RECONCILIATION TABLE'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::MapOps` was a hand-written Rust arm, and the largest one left: the row guard and op
//! membership, the AAFI selector's three pins, the read discipline, 32 direction booleans across
//! TWO independent paths, the pointer-bracket range block (three canonical splits and two
//! lexicographic comparators) and FIVE `node8` Merkle folds totalling 84 chip lookups.
//! Architectural law #1 says that object is authored in Lean and Rust only interprets. It was not.
//! **That arm is now DELETED** — the enum VARIANT with it; its author is
//! `metatheory/Dregg2/Circuit/Emit/MapOpsTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-map-ops-v1.json`, and `Ir2Air::LeanTable` walks it.
//!
//! # The three questions a re-emission can fail
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    reconciliation OUT of the prover's own map-ops trace.)
//! 2. **Was any gate LOST, and what can this instrument NOT see?** (§2 — a per-cell mutation sweep
//!    through the REAL deployed evaluator, with the undetected set pinned EXACTLY.)
//! 3. **Do both poles still hold at the deployed prover?** (§3.)
//!
//! # ⚑ What the port REFUTED — and why §2's undetected set is ENORMOUS on purpose
//!
//! **Not one of this table's 84 chip legs is a gate.** The Lean file proves
//! `an_aafi_row_with_no_opening_satisfies_every_gate`: a row with `root = new_root = 0`, an honest
//! pointer bracket and an ALL-ZERO opening — no leaf digest, no sibling, no chain node — satisfies
//! every one of the 91 emitted gates. So the entire Merkle content of the table is 70% of its
//! interactions and 0% of its algebra, and a gate-level sweep is *structurally* blind to it
//! (`root_is_read_by_no_gate`, `the_first_sibling_lane_is_read_by_no_gate`).
//!
//! ⚠ That is why §2's `expected` set is stated as a PREDICATE over named column classes rather
//! than as a small list, and why §3 carries the deployed-prover poles: what refuses a forged
//! opening is the `ir2_p2` chip bus, which lives in a different AIR. Naming which mechanism
//! refuses what is the point. A bus refusal quoted as a gate verdict is how an accepting gate
//! hides.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness, VmConstraint2,
    map_ops_rows_for, prove_vm_descriptor2, table_air_gates_accept, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};
use dregg_circuit::table_air::{BusOp, RowSel, map_ops_table_air};

// The deployed layout, transcribed ONCE here so the assertions below can name a column. These are
// the same numbers `MapOpsTableEmit.lean` derives; a drift on either side reds §1.
const MAP_ROOT: usize = 0;
const MAP_KEY: usize = 8;
const MAP_VALUE: usize = 9;
const MAP_OP: usize = 10;
const MAP_NEW_ROOT: usize = 11;
const MAP_IS_REAL: usize = 19;
const MAP_OLD_VALUE: usize = 20;
const MAP_NEXT: usize = 21;
const MAP_SIB0: usize = 22;
const MAP_DIR0: usize = 150;
const MAP_OLD_LEAF: usize = 166;
const MAP_R1: usize = 423;
const MAP_A_DEC0: usize = 833;
const MAP_AAFI_BASE: usize = 422;
const MAP_S: usize = MAP_AAFI_BASE;
const MAP_WIDTH: usize = 898;

const KEY: u32 = 100;
const OLD_VALUE: u32 = 77;
const NEW_VALUE: u32 = 99;

fn heap() -> Vec<HeapLeaf> {
    vec![
        HeapLeaf::entry(BabyBear::new(KEY), BabyBear::new(OLD_VALUE)),
        HeapLeaf::entry(BabyBear::new(200), BabyBear::new(88)),
    ]
}

/// A minimal descriptor with ONE guarded map WRITE — enough to make the map-ops table present.
/// Trace columns: `root8 [0..8)`, `key 8`, `value 9`, `new_root8 [10..18)`, `guard 18`.
fn map_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "map-ops-lean-emission-differential".to_string(),
        trace_width: 19,
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MapOp(MapOpSpec {
            guard: LeanExpr::Var(18),
            root: (0..CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            key: LeanExpr::Var(8),
            value: LeanExpr::Var(9),
            new_root: (10..10 + CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            op: MapKind::Write,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// One honest in-place update at an existing key, then three pad rows.
fn map_trace() -> Vec<Vec<BabyBear>> {
    let tree = CanonicalHeapTree8::new(heap(), HEAP_TREE_DEPTH);
    let root = tree.root8();
    let w = tree
        .update_witness(HeapLeaf::entry(
            BabyBear::new(KEY),
            BabyBear::new(NEW_VALUE),
        ))
        .expect("the key is present");
    let mk = |guard: BabyBear| {
        let mut r = vec![BabyBear::ZERO; 19];
        r[0..CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[8] = BabyBear::new(KEY);
        r[9] = BabyBear::new(NEW_VALUE);
        r[10..10 + CHIP_OUT_LANES].copy_from_slice(&w.new_root);
        r[18] = guard;
        r
    };
    vec![
        mk(BabyBear::ONE),
        mk(BabyBear::ZERO),
        mk(BabyBear::ZERO),
        mk(BabyBear::ZERO),
    ]
}

fn honest_map_rows() -> Vec<Vec<BabyBear>> {
    map_ops_rows_for(&map_desc(), &map_trace(), &[heap()])
        .expect("the deployed prover assembles a map-ops table")
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The emitted table declares width 898 and reads the pre-root
/// at `[0, 8)`, the key at 8, the written value at 9, the op code at 10, the post-root at
/// `[11, 19)`, the guard at 19, the committed old value at 20 and the IMT pointer at 21. The
/// prover's OWN trace builder writes those columns; this reads them back out and checks each
/// against the base trace and the heap witness, recovered independently rather than off the same
/// row.
///
/// If the Lean emission had transcribed one offset wrong, the honest witness would still prove
/// (the gate would read a zero column and vanish) but this round-trip would fail.
#[test]
fn the_emitted_columns_round_trip_the_map_reconciliation() {
    let rows = honest_map_rows();
    let t = map_ops_table_air();
    let base = map_trace();

    assert_eq!(t.width, MAP_WIDTH);
    assert!(rows.iter().all(|r| r.len() == t.width));

    // ⓘ MEASURED, not assumed: one GUARDED op out of four base rows, padded to a power of two
    // floored at `MIN_TABLE_HEIGHT` — so exactly one real row, and the rest are pads. That
    // asymmetry is the whole reason a table AIR needs a per-row multiplicity EXPRESSION.
    let reals = rows
        .iter()
        .filter(|r| r[MAP_IS_REAL] == BabyBear::ONE)
        .count();
    assert_eq!(reals, 1, "one guarded map op");
    assert!(rows.len() >= 8, "padded to the table-height floor");

    let real = &rows[0];
    assert_eq!(real[MAP_IS_REAL], BabyBear::ONE);
    assert_eq!(real[MAP_KEY], BabyBear::new(KEY));
    assert_eq!(real[MAP_VALUE], BabyBear::new(NEW_VALUE));
    // op code 1 = Write. §3 measures that op 2 (`absent`) is UNSAT here.
    assert_eq!(real[MAP_OP], BabyBear::ONE);
    // The COMMITTED prior value, which the read-discipline gate compares on a read row.
    assert_eq!(real[MAP_OLD_VALUE], BabyBear::new(OLD_VALUE));
    // ⚑ The IMT pointer both arity-3 absorbs read, and it is NOT what `HeapLeaf::entry` starts
    // from: `entry` sets `next_addr = SENTINEL_MAX`, and `CanonicalHeapTree8::new` RELINKS the
    // chain, so leaf(100)'s pointer is its successor KEY 200. A value update holds it FIXED — the
    // old and new leaf absorbs read the same column — which is why a write cannot silently
    // re-point the linked list.
    assert_eq!(real[MAP_NEXT], BabyBear::new(200));
    assert_ne!(
        real[MAP_NEXT],
        HeapLeaf::entry(BabyBear::ZERO, BabyBear::ZERO).next_addr
    );
    // Both 8-felt root groups come back lane for lane, out of the prover's own row.
    for i in 0..CHIP_OUT_LANES {
        assert_eq!(real[MAP_ROOT + i], base[0][i], "pre-root lane {i}");
        assert_eq!(
            real[MAP_NEW_ROOT + i],
            base[0][10 + i],
            "post-root lane {i}"
        );
    }
    // ⚑ The AAFI block is byte-disjoint and the selector is OFF on a write row — which is what
    // `s_is_the_op4_indicator` says and what makes the 49 AAFI chip legs vacuous here.
    assert_eq!(real[MAP_S], BabyBear::ZERO);
    assert!(
        real[MAP_AAFI_BASE..].iter().all(|f| *f == BabyBear::ZERO),
        "every AAFI column is zero on an op-1 row"
    );
    // The honest row is accepted by the EMITTED gates.
    assert!(table_air_gates_accept(&t, &rows));
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP, and what it CANNOT see.
// -------------------------------------------------------------------------------------------

/// **⚑ THE SWEEP, WITH THE UNDETECTED SET PINNED EXACTLY.** Every cell of every row gets two
/// deltas (a `+1` on a column that is honestly zero lands on 1, which a boolean gate still
/// accepts, so one delta alone under-reports), and each mutated table is run through the REAL
/// deployed evaluator (`Ir2Air::LeanTable`, the same code path the prover uses). A cell is
/// "detected" iff at least one delta makes some gate fail.
///
/// ⚠ **The undetected set here is most of the row, and that is the FINDING rather than a
/// weakness of the instrument.** The Lean file proves it directly
/// (`root_is_read_by_no_gate`, `new_root_is_read_by_no_gate`,
/// `the_first_sibling_lane_is_read_by_no_gate`): the pre-root, the post-root, both leaf digests,
/// all 256 sibling columns and all 480 chain columns enter this AIR ONLY through `ir2_p2` lookup
/// tuples. What this test pins is that the undetected set is EXACTLY the bus-bound classes plus
/// the pad rows' gated-off payload — so a gate LOST in the re-emission moves a column from
/// detected to undetected and reds here.
#[test]
fn every_gated_map_ops_cell_is_still_gated_after_the_cutover() {
    let t = map_ops_table_air();
    let honest = honest_map_rows();
    assert!(table_air_gates_accept(&t, &honest));

    let reals = honest
        .iter()
        .filter(|r| r[MAP_IS_REAL] == BabyBear::ONE)
        .count();

    let mut undetected: Vec<(usize, usize)> = Vec::new();
    for row in 0..honest.len() {
        for col in 0..t.width {
            let detected = [1u32, 2u32].iter().any(|d| {
                let mut m = honest.clone();
                m[row][col] += BabyBear::new(*d);
                !table_air_gates_accept(&t, &m)
            });
            if !detected {
                undetected.push((row, col));
            }
        }
    }

    // ⚑ THE THREE UNDETECTED CLASSES, each named by the mechanism that DOES bind it. ⓘ Note that
    // none of them is row-dependent: unlike every earlier table in this burn-down, this sweep's
    // blind spot is the same on a real row and on a pad, because what carries the reconciliation
    // is the chip bus and the chip bus does not care which row it is on.
    //
    //  * `digest_bound` — every digest LANE: the two 8-felt roots, the two leaf digests, all 128
    //    sibling columns and all 240 chain columns. Bound by the 84 `ir2_p2` node8 / absorb
    //    lookups. This is 400 of the 898 columns and the Lean file proves it directly
    //    (`root_is_read_by_no_gate`, `the_first_sibling_lane_is_read_by_no_gate`).
    //  * `payload_bound` — the key, the written value, the committed old value and the IMT
    //    pointer. ⚠ On a WRITE row the read-discipline gate is IDENTICALLY VACUOUS (its `(1 − op)`
    //    factor is 0 at `op = 1`), so these are bound by the leaf ABSORB tuple and the
    //    `ir2_map_log` receive — buses again, on the REAL row as much as on a pad.
    //  * `aafi_witness_off` — the AAFI witness block `[MAP_R1, MAP_A_DEC0)`: the intermediate
    //    root, the low leaf, PATH2's siblings and direction bits, and the empty-slot digest. Every
    //    gate over them carries an `s` factor and `s = 0` on an op-1 row, which is
    //    `s_is_the_op4_indicator` working as designed.
    //
    // ⚠ NOT in the set, and worth naming because a reader would guess otherwise: `MAP_S` itself
    // (422) and the whole pointer-bracket range block `[MAP_A_DEC0, MAP_WIDTH)` are DETECTED even
    // at `s = 0`. The canonical-split and comparator recompositions carry no `s` factor in their
    // bodies — only in the `gate` argument — so a forged limb is refused on an op-1 row too. That
    // is the deployed twin of the Lean `a_pad_row_still_owes_a_real_bracket`.
    let digest_bound = |col: usize| {
        (MAP_ROOT..MAP_ROOT + CHIP_OUT_LANES).contains(&col)
            || (MAP_NEW_ROOT..MAP_NEW_ROOT + CHIP_OUT_LANES).contains(&col)
            || (MAP_SIB0..MAP_SIB0 + CHIP_OUT_LANES * HEAP_TREE_DEPTH).contains(&col)
            || (MAP_OLD_LEAF..MAP_AAFI_BASE).contains(&col)
    };
    let payload_bound = |col: usize| matches!(col, MAP_KEY | MAP_VALUE | MAP_OLD_VALUE | MAP_NEXT);
    let aafi_witness_off = |col: usize| (MAP_R1..MAP_A_DEC0).contains(&col);

    let mut expected: Vec<(usize, usize)> = Vec::new();
    for row in 0..honest.len() {
        for col in 0..t.width {
            if digest_bound(col) || payload_bound(col) || aafi_witness_off(col) {
                expected.push((row, col));
            }
        }
    }
    // The classes really are the row's bulk, and the detected remainder is really non-empty.
    assert_eq!(
        expected.len(),
        honest.len() * (400 + 4 + (MAP_A_DEC0 - MAP_R1))
    );
    assert!(undetected.len() < honest.len() * t.width);
    if undetected != expected {
        let only_u: Vec<_> = undetected
            .iter()
            .filter(|c| !expected.contains(c))
            .collect();
        let only_e: Vec<_> = expected
            .iter()
            .filter(|c| !undetected.contains(c))
            .collect();
        panic!("undetected \\ expected = {only_u:?}\nexpected \\ undetected = {only_e:?}");
    }
    assert_eq!(
        undetected, expected,
        "the undetected set is not exactly {{the bus-bound digest lanes}} ∪ {{the AAFI block on a \
         selector-off row}} ∪ {{a pad row's gated-off payload}} — either a gate was lost in the \
         Lean re-emission, or a gate appeared where a bus is supposed to be the mechanism"
    );

    // …and the POSITIVE half, column by column, naming the gate that catches each. Without this
    // the equality above could be satisfied by a table with no gates at all.
    let bite = |row: usize, col: usize, d: u32| {
        let mut m = honest.clone();
        m[row][col] += BabyBear::new(d);
        !table_air_gates_accept(&t, &m)
    };
    assert!(bite(0, MAP_IS_REAL, 1), "the row guard's boolean gate");
    assert!(bite(0, MAP_OP, 1), "the op membership gate (1 -> 2)");
    assert!(bite(0, MAP_S, 1), "the AAFI selector pin `s * (op - 4)`");
    assert!(bite(0, MAP_DIR0, 2), "a PATH1 direction bit's boolean gate");
    assert!(
        bite(0, MAP_A_DEC0, 1),
        "the pointer-bracket canonical split is gate-bound even at `s = 0` — its recomposition \
         carries no selector factor"
    );
    assert!(
        !bite(0, MAP_OLD_VALUE, 1) && !bite(0, MAP_VALUE, 1),
        "the read discipline is IDENTICALLY VACUOUS on a WRITE row (its `(1 - op)` factor is 0 at \
         op = 1), so the payload is bus-bound here — if a gate caught it the emission grew one"
    );
    // ⚑ A pad row's op code is NOT free — the membership gate is unconditional.
    assert!(
        bite(reals, MAP_OP, 2),
        "a pad row's op code must still be an ADMITTED op: the membership gate carries no \
         `is_real` factor"
    );
}

/// ⚑ **THE INSTRUMENT'S OWN BLIND SPOT, MEASURED RATHER THAN INFERRED.** Zeroing the ENTIRE
/// opening — both roots, both leaves, every sibling, every chain node — leaves every emitted gate
/// green. This is the deployed twin of the Lean `an_aafi_row_with_no_opening_satisfies_every_gate`,
/// and it is what a soundness story about this table must not read past: the 84 `ir2_p2` legs are
/// the mechanism, and `TableAir.Holds` does not speak about them.
#[test]
fn an_opening_free_row_is_accepted_by_every_emitted_gate() {
    let t = map_ops_table_air();
    let mut rows = honest_map_rows();
    assert!(table_air_gates_accept(&t, &rows));
    for row in &mut rows {
        for col in 0..MAP_WIDTH {
            let digest_lane = (MAP_ROOT..MAP_ROOT + CHIP_OUT_LANES).contains(&col)
                || (MAP_NEW_ROOT..MAP_NEW_ROOT + CHIP_OUT_LANES).contains(&col)
                || (MAP_SIB0..MAP_SIB0 + CHIP_OUT_LANES * HEAP_TREE_DEPTH).contains(&col)
                || (MAP_OLD_LEAF..MAP_AAFI_BASE).contains(&col);
            if digest_lane {
                row[col] = BabyBear::ZERO;
            }
        }
    }
    assert!(
        rows[0][MAP_ROOT] == BabyBear::ZERO && rows[0][MAP_OLD_LEAF] == BabyBear::ZERO,
        "the opening really is gone"
    );
    assert!(
        table_air_gates_accept(&t, &rows),
        "every gate is green on a reconciliation that opens NOTHING — the Merkle content of this \
         table is 84 bus legs and zero gates"
    );
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** The honest reconciliation proves and verifies through the deployed batch
/// prover against the Lean-authored table AIR.
#[test]
fn an_honest_map_write_proves_and_verifies_through_the_lean_emission() {
    let desc = map_desc();
    let proof = prove_vm_descriptor2(
        &desc,
        &map_trace(),
        &[],
        &MemBoundaryWitness::default(),
        &[heap()],
    )
    .expect("an honest map write must prove");
    assert_eq!(
        proof.degree_bits.len(),
        3,
        "a map-only descriptor commits main + chip + map-ops (the chains ride the chip bus)"
    );
    verify_vm_descriptor2(&desc, &proof, &[]).expect("the honest map write must verify");
}

/// **SOUNDNESS, the pole the sweep cannot reach.** A post-root that is not the genuine sorted
/// write is refused all the way through the deployed prover. ⚠ This is refused by the `ir2_p2`
/// chip bus — the node8 fold has no matching chip row for a forged terminal — NOT by a gate, and
/// saying so is the point: `assert_violated_constraint_not_bus` is deliberately NOT applied here,
/// because it would be false, and quoting a gate verdict for a bus refusal is exactly how an
/// accepting gate hides.
#[test]
fn a_forged_post_root_is_refused_at_the_deployed_prover() {
    let desc = map_desc();
    let mut rows = map_trace();
    rows[0][10] += BabyBear::ONE;
    must_refuse_or_unsat_panic("a post-root that is not the genuine sorted write", || {
        prove_vm_descriptor2(&desc, &rows, &[], &MemBoundaryWitness::default(), &[heap()])
            .map(|_| ())
    });
}

/// ⚑ **THE READ-DISCIPLINE GATE IS UNREACHABLE FROM THE PROVER ENTRY POINT — measured, and it
/// is the honest version of a test that would otherwise read as a gate verdict.**
///
/// `is_real·(1 − op)·(op − 3)·(old_value − value)` is the one gate of this table whose subject is
/// PAYLOAD rather than a digest. But `build_traces` writes `MAP_OLD_VALUE` from the heap itself,
/// so no `(descriptor, trace, heap)` input can make the two columns disagree: the ASSEMBLER
/// refuses first, with `"map op 0: read at key 100 opens to 77, row claims 99"`.
///
/// ⚠ That refusal is a COMPLETENESS-OF-REFUSAL fact about `build_traces`, **not** a gate verdict,
/// and `assert_violated_constraint_not_bus` is deliberately NOT applied to it — it would fail, and
/// quoting an assembler refusal as a constraint verdict is exactly how an accepting gate hides.
/// The gate's own verdict is measured below, at the evaluator, on a MUTATED assembled row.
#[test]
fn a_lying_read_is_refused_by_the_assembler_and_the_gate_is_reached_only_by_mutation() {
    let tree = CanonicalHeapTree8::new(heap(), HEAP_TREE_DEPTH);
    let root = tree.root8();
    let desc = EffectVmDescriptor2 {
        name: "map-ops-lying-read".to_string(),
        trace_width: 19,
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MapOp(MapOpSpec {
            guard: LeanExpr::Var(18),
            root: (0..CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            key: LeanExpr::Var(8),
            value: LeanExpr::Var(9),
            new_root: (10..10 + CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            op: MapKind::Read,
        })],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mk = |guard: BabyBear, value: u32| {
        let mut r = vec![BabyBear::ZERO; 19];
        r[0..CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[8] = BabyBear::new(KEY);
        r[9] = BabyBear::new(value);
        // A read leaves the root unchanged.
        r[10..10 + CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[18] = guard;
        r
    };
    let honest_trace = vec![
        mk(BabyBear::ONE, OLD_VALUE),
        mk(BabyBear::ZERO, 0),
        mk(BabyBear::ZERO, 0),
        mk(BabyBear::ZERO, 0),
    ];
    // COMPLETENESS first — otherwise the refusal below proves nothing.
    prove_vm_descriptor2(
        &desc,
        &honest_trace,
        &[],
        &MemBoundaryWitness::default(),
        &[heap()],
    )
    .expect("the honest read must prove");

    let lying = vec![
        mk(BabyBear::ONE, NEW_VALUE),
        mk(BabyBear::ZERO, 0),
        mk(BabyBear::ZERO, 0),
        mk(BabyBear::ZERO, 0),
    ];
    let refused =
        must_refuse_or_unsat_panic("a read that does not return the committed value", || {
            prove_vm_descriptor2(
                &desc,
                &lying,
                &[],
                &MemBoundaryWitness::default(),
                &[heap()],
            )
            .map(|_| ())
        });
    let reason = refused.reason();
    assert!(
        reason.contains("opens to"),
        "the ASSEMBLER is what refuses a lying read, and its message is what should be quoted: \
         {reason}"
    );

    // …and now the GATE'S OWN VERDICT, on a genuinely assembled read row whose committed prior
    // value has been moved out from under it. `op = 0` here, so `(1 − op)·(op − 3) = −3` and the
    // read discipline BITES — the only column class of this table that a gate, rather than a bus,
    // is the mechanism for.
    let t = map_ops_table_air();
    let rows = map_ops_rows_for(&desc, &honest_trace, &[heap()])
        .expect("the deployed prover assembles the read row");
    assert_eq!(rows[0][MAP_OP], BabyBear::ZERO, "op 0 = Read");
    assert!(table_air_gates_accept(&t, &rows));
    let mut mutated = rows.clone();
    mutated[0][MAP_OLD_VALUE] += BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &mutated),
        "the read-discipline GATE refuses a returned value that is not the committed one"
    );
    // …and the CONTRAST that shows the gate is the op-selected one and not a blanket equality:
    // the same mutation on the WRITE row of `map_desc()` is accepted, because `(1 − op) = 0`.
    let mut write_rows = honest_map_rows();
    write_rows[0][MAP_OLD_VALUE] += BabyBear::ONE;
    assert!(
        table_air_gates_accept(&map_ops_table_air(), &write_rows),
        "the read discipline is inactive at op = 1 — a write is not required to return the old \
         value, and that asymmetry is the `(1 - op)` factor"
    );
}

/// ⚑ **THE BUS SIDES AND THE SELECTOR SCOPES — the half the sweep is blind to, pinned.** The
/// sweep can only see gates. These counts are what a dropped bus leg or a re-scoped gate moves,
/// and they are asserted against the DECODED emission rather than against the Lean `#guard`.
#[test]
fn the_map_ops_table_queries_everything_and_serves_nothing() {
    let t = map_ops_table_air();
    // FIVE node8 folds of DEPTH levels, plus four arity-3 leaf absorbs.
    assert_eq!(
        t.bus_count_op("ir2_p2", BusOp::Query),
        4 + 5 * HEAP_TREE_DEPTH
    );
    assert_eq!(t.bus_count_op("ir2_p2", BusOp::Provide), 0);
    assert_eq!(t.bus_count_op("ir2_byte", BusOp::Query), 35);
    assert_eq!(t.bus_count_op("ir2_byte", BusOp::Provide), 0);
    assert_eq!(t.bus_count_op("ir2_map_log", BusOp::Receive), 1);
    assert_eq!(t.bus_count_op("ir2_map_log", BusOp::Send), 0);
    // Purely row-local: the log ORDER lives in the multiset, not in an adjacency gate.
    assert_eq!(t.gate_count_sel(RowSel::All), t.gates.len());
    assert_eq!(t.gate_count_sel(RowSel::Transition), 0);
    // ⚠ The refusal in `a_forged_post_root_is_refused_at_the_deployed_prover` is one of these 84
    // legs, not one of these 91 gates. Stated as an assertion so the two counts stay visible
    // beside each other.
    assert_eq!(t.gates.len(), 91);
    assert_eq!(t.interactions.len(), 120);
}
