//! **THE LIVE DOUBLE-SPEND GATE'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::MapAbsent` was ~120 lines of hand-written Rust algebra (`builder.assert_zero(..)` +
//! `bus.lookup_key(..)`) implementing the in-circuit non-membership gate a note spend rides
//! through `noteSpendVmDescriptor2R24`'s `nullifierFreshOp`. Architectural law #1 says that object
//! is authored in Lean and Rust only interprets. It was not. **That arm is now DELETED**; its
//! author is `metatheory/Dregg2/Circuit/Emit/MapAbsentTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-map-absent-v1.json`, and `Ir2Air::LeanTable` walks it.
//!
//! This file is the gate on that cutover. It asks the three questions a re-emission can fail:
//!
//! 1. **Does the emitted algebra read the columns the prover writes?** (§1 — a ROUND-TRIP of the
//!    key, the low address and the IMT pointer OUT of the honest table row, not "the digests
//!    differ".)
//! 2. **Was any gate LOST?** (§2 — a per-column MUTATION SWEEP over all 358 columns through the
//!    REAL deployed evaluator. A shape count cannot answer this: a re-emission can keep 70 gates
//!    and change one. Lean names the direction as `TableAir.rowHolds_of_sublist` — dropping gates
//!    accepts strictly more.)
//! 3. **Do both poles still hold at the deployed prover?** (§3.)
//!
//! # ⚠ WHAT THIS CUTOVER DID NOT DO, said plainly
//!
//! **The key was not widened.** `MA_KEY`, `MA_LO_ADDR` and `MA_LO_NEXT` are still one felt each —
//! the 2^15.45-collision sort key `mapabsent_key_width_tooth.rs` measures. So the tripwires in
//! that file are NOT flipped by this change and MUST NOT BE: they pin the WIDTH wound, this change
//! is the AUTHORSHIP fix, and they are different wounds. §4 asserts that the half-widened state —
//! the strictly-worse intermediate where the key widens and the pointer does not — was not entered,
//! by pinning the two invariants whose loss defines it.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness, VmConstraint2,
    WindowExpr, map_absent_rows_for, prove_vm_descriptor2, table_air_gates_accept,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::fold_bytes32_to_bb;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    CanonicalHeapTree8, HEAP_LEAF_ARITY, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX,
};
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::must_refuse_or_unsat_panic;
use dregg_circuit::table_air::{BusOp, map_absent_table_air};

// The deployed layout, transcribed ONCE here so the assertions below can name a column. These are
// the same numbers `MapAbsentTableEmit.lean` derives; a drift on either side reds §1.
const MA_KEY: usize = 8;
const MA_IS_REAL: usize = 17;
const MA_LO_ADDR: usize = 18;
const MA_LO_VALUE: usize = 19;
const MA_LO_NEXT: usize = 20;
const MA_WIDTH: usize = 358;

/// A nullifier as the protocol makes one.
fn nullifier_of_note(nonce: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-note-nullifier-v1");
    h.update(&nonce.to_le_bytes());
    *h.finalize().as_bytes()
}

fn deployed_key(nf: &[u8; 32]) -> BabyBear {
    fold_bytes32_to_bb(nf)
}

/// The `.absent` descriptor `nullifierFreshOp` realizes at its minimal width — byte-for-byte the
/// shape `descriptor_ir2.rs`'s own `absent_desc()` uses, so this is the deployed gate.
fn absent_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "mapabsent-lean-emission-differential".to_string(),
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

/// An honest spent set at genuine deployed keys, plus a genuinely fresh, genuinely bracketed key.
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

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP: the emitted algebra reads the columns the prover writes.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The Lean-emitted table declares width 358 and reads the key
/// at column 8, the low address at 18 and the IMT pointer at 20. The prover's OWN trace builder
/// (`map_absent_rows_for` returns `build_traces`' output, not a re-derivation) writes those
/// columns. This reads the three values back OUT of the honest row and checks they are the
/// deployed key and the genuine bracketing leaf — not that "the digests differ".
///
/// If the Lean emission had transcribed one offset wrong, the honest witness would still prove
/// (the gate would read a zero column and vanish) but this round-trip would fail. That is the
/// failure mode a shape count cannot see.
#[test]
fn the_emitted_columns_round_trip_the_key_and_the_pointer() {
    let (heap, key) = honest_setup();
    let rows = map_absent_rows_for(&absent_desc(), &absent_trace(&heap, key), &[heap.clone()])
        .expect("the deployed prover assembles a map-absent table");

    let t = map_absent_table_air();
    assert_eq!(t.width, MA_WIDTH);
    assert!(!rows.is_empty());
    assert!(
        rows.iter().all(|r| r.len() == t.width),
        "the prover's rows are exactly the emitted width"
    );

    // The ONE real row (the rest are pads).
    let real: Vec<&Vec<BabyBear>> = rows
        .iter()
        .filter(|r| r[MA_IS_REAL] == BabyBear::ONE)
        .collect();
    assert_eq!(real.len(), 1, "exactly one real absent row");
    let row = real[0];

    // ⚑ THE ROUND-TRIP. The key column carries the deployed key…
    assert_eq!(
        row[MA_KEY], key,
        "the emitted key column IS the deployed key"
    );

    // …and the two pointer columns carry the genuine bracketing leaf, recovered independently
    // from the tree rather than read off the same row.
    let tree = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH);
    let leaves = tree.sorted_leaves();
    let expected = leaves
        .iter()
        .find(|l| l.addr.as_u32() < key.as_u32() && l.next_addr.as_u32() > key.as_u32())
        .expect("a genuine bracketing low leaf exists");
    assert_eq!(
        row[MA_LO_ADDR], expected.addr,
        "the low address round-trips"
    );
    assert_eq!(
        row[MA_LO_VALUE], expected.value,
        "the low value round-trips"
    );
    assert_eq!(
        row[MA_LO_NEXT], expected.next_addr,
        "the IMT pointer round-trips"
    );

    // …and the bracket the emitted comparators check is a REAL strict bracket.
    assert!(row[MA_LO_ADDR].as_u32() < row[MA_KEY].as_u32());
    assert!(row[MA_KEY].as_u32() < row[MA_LO_NEXT].as_u32());

    // The deployed evaluator accepts the honest table.
    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP: no gate was lost in the re-emission.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For each of the 358 columns, bump the real row's value by one and ask
/// the REAL deployed evaluator whether the table still accepts. A column whose mutation is
/// DETECTED is a column the emitted row-local algebra genuinely constrains.
///
/// This is the check a shape count cannot make. `mapAbsentTable.gates.length == 70` is pinned in
/// Lean and re-derived in `table_air.rs`, but a re-emission could keep 70 gates and change what
/// one of them says; only firing them tells you.
///
/// **What the sweep can and cannot see, stated rather than implied.** Row-local gates are
/// decided here; BUS legs are swallowed (the LogUp balance is the batch's job — the same
/// faithfulness split `ir2_eval_accepts` documents). So the sibling and chain digest columns,
/// which are bound ONLY by chip lookups, are expected to be UNDETECTED here and are covered by
/// §3's prover-level refusals instead. The assertion below is therefore a FLOOR on the detected
/// set plus an exact pin on the columns that must be in it.
#[test]
fn every_gated_column_is_still_gated_after_the_cutover() {
    let (heap, key) = honest_setup();
    let rows = map_absent_rows_for(&absent_desc(), &absent_trace(&heap, key), &[heap.clone()])
        .expect("the deployed prover assembles a map-absent table");
    let t = map_absent_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    let real_ix = rows
        .iter()
        .position(|r| r[MA_IS_REAL] == BabyBear::ONE)
        .expect("one real row");

    // TWO bumps, not one. A `+1` on a boolean column that is honestly ZERO lands on 1, which the
    // boolean gate still accepts — so a single-bump sweep reports a live gate as dead. (Measured:
    // it did, on `MA_LO_DIR0`, whose level-0 direction bit is honestly 0 on this path.) `+2`
    // leaves both boolean polarities out of range, and a column genuinely ungated survives both.
    let mut detected: Vec<usize> = Vec::new();
    let mut undetected: Vec<usize> = Vec::new();
    for col in 0..t.width {
        let caught = [1u32, 2u32].iter().any(|&d| {
            let mut mutated = rows.clone();
            mutated[real_ix][col] = mutated[real_ix][col] + BabyBear::new(d);
            !table_air_gates_accept(&t, &mutated)
        });
        if caught {
            detected.push(col);
        } else {
            undetected.push(col);
        }
    }

    // ⚑ The columns that MUST be caught by row-local algebra. Each names the gate that catches it.
    //   8  MA_KEY        — its canonical decomposition no longer recomposes
    //  17  MA_IS_REAL    — the boolean gate (1 → 2)
    //  18  MA_LO_ADDR    — its canonical decomposition
    //  20  MA_LO_NEXT    — its canonical decomposition
    // 157  MA_LO_DIR0    — the direction bit's boolean gate
    // 293  MA_A_DEC0     — the low address's `hi4` nibble, feeding both the split and `is15`
    // 306  MA_K_DEC0     — the key's `hi4`
    // 319  MA_B_DEC0     — the pointer's `hi4`
    // 332  MA_CMP_LO0    — the `lo_addr < key` comparator's selector `s`
    // 345  MA_CMP_HI0    — the `key < lo_next` comparator's selector `s`
    for must in [8usize, 17, 18, 20, 157, 293, 306, 319, 332, 345] {
        assert!(
            detected.contains(&must),
            "column {must} lost its row-local gate in the Lean re-emission — detected set: {detected:?}"
        );
    }

    // The root-preservation gates: every one of the eight post-root lanes is pinned to its
    // pre-root lane, so a bump on ANY of them is caught. A re-emission that emitted the gate for
    // lane 0 only would pass a spot check and fail this.
    for lane in 0..CHIP_OUT_LANES {
        assert!(
            detected.contains(&(9 + lane)),
            "post-root lane {lane} (column {}) is not root-preserved — the re-emission dropped a \
             lane",
            9 + lane
        );
    }

    // …and all sixteen direction bits, not just the first.
    for lvl in 0..HEAP_TREE_DEPTH {
        assert!(
            detected.contains(&(157 + lvl)),
            "direction bit at level {lvl} (column {}) lost its boolean gate",
            157 + lvl
        );
    }

    // ⚑ AND THE OTHER SIDE, said rather than implied: which columns this instrument CANNOT
    // decide. Every undetected column must be one the row-local algebra genuinely does not
    // constrain — the digest columns bound only by chip lookups (`MA_LO_LEAF` and the sibling /
    // chain groups, 21..293) and `MA_LO_VALUE` (19), which appears only inside the leaf absorb
    // tuple. If a column OUTSIDE that window ever lands here, a gate was lost.
    for &u in &undetected {
        assert!(
            u == MA_LO_VALUE || (21..293).contains(&u),
            "column {u} is not row-locally gated and is not one of the bus-bound digest columns \
             — the Lean re-emission lost a gate. undetected: {undetected:?}"
        );
    }

    // A FLOOR, so a wholesale collapse of the gate list cannot pass.
    assert!(
        detected.len() >= 90,
        "only {} of {} columns are row-locally gated — the re-emission lost algebra. detected: \
         {detected:?}",
        detected.len(),
        t.width
    );

    println!(
        "MEASURED: {} of {} map-absent columns are row-locally gated by the Lean emission; the \
         {} undetected are the chip-lookup-bound digest columns (leaf/siblings/chain) plus the \
         stored low value",
        detected.len(),
        t.width,
        undetected.len()
    );
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** An honest note spend proves and verifies through the Lean-emitted AIR.
#[test]
fn an_honest_note_spend_proves_and_verifies_through_the_lean_emission() {
    let (heap, key) = honest_setup();
    let desc = absent_desc();
    let proof = prove_vm_descriptor2(
        &desc,
        &absent_trace(&heap, key),
        &[],
        &MemBoundaryWitness::default(),
        &[heap.clone()],
    )
    .expect("an honest freshness witness must prove through the Lean-emitted AIR");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES, not at the assembler.**
///
/// ⚠ A present key does not reach the constraint evaluator at all: `build_traces` refuses to
/// assemble a witness for it ("absent key … IS present in the heap — no bracketing witness
/// exists"), which is honest prover behaviour but says nothing about the AIR. That distinction is
/// exactly what this test exists to keep straight, so it does BOTH halves separately.
///
/// The half that measures the emitted algebra: take the prover's OWN honest rows and forge the
/// bracket in place — move the IMT pointer below the key, so the `key < low_next` comparator's
/// premise is false while every digest column still holds a genuine opening. The Lean-emitted
/// gates must refuse. If the re-emission had dropped the upper comparator, this forged row would
/// be accepted and the gate would admit a key the chain PRESENTS.
#[test]
fn a_forged_bracket_is_refused_by_the_emitted_gates() {
    let (heap, key) = honest_setup();
    let t = map_absent_table_air();
    let rows = map_absent_rows_for(&absent_desc(), &absent_trace(&heap, key), &[heap.clone()])
        .expect("the deployed prover assembles a map-absent table");
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    let real_ix = rows
        .iter()
        .position(|r| r[MA_IS_REAL] == BabyBear::ONE)
        .expect("one real row");

    // Forge the UPPER bracket: pull the pointer down to the key itself, so `key < low_next` is
    // false. Nothing else changes — the low address still brackets from below, the digests are
    // still the genuine ones.
    let mut forged = rows.clone();
    forged[real_ix][MA_LO_NEXT] = forged[real_ix][MA_KEY];
    assert!(
        !table_air_gates_accept(&t, &forged),
        "the emitted `key < low_next` comparator must refuse a pointer that does not exceed the key"
    );

    // …and the LOWER bracket, the other direction.
    let mut forged_lo = rows.clone();
    forged_lo[real_ix][MA_LO_ADDR] = forged_lo[real_ix][MA_KEY];
    assert!(
        !table_air_gates_accept(&t, &forged_lo),
        "the emitted `low_addr < key` comparator must refuse a low address equal to the key"
    );

    // …and root preservation: a non-membership read may not move the root.
    let mut forged_root = rows.clone();
    forged_root[real_ix][9] = forged_root[real_ix][9] + BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &forged_root),
        "the emitted root-preservation gate must refuse a moved post-root"
    );
}

/// The prover-level pole, stated at ITS OWN resolution: a genuinely spent nullifier claiming
/// freshness is refused. ⚠ The refusal is the ASSEMBLER's — there is no bracketing witness to
/// build — so this is a completeness-of-refusal fact, not a constraint verdict. The constraint
/// verdict is the test above. Naming which is which is the point: a bus-or-assembler refusal
/// quoted as a gate verdict is how an accepting gate hides.
#[test]
fn a_present_key_is_refused_by_the_deployed_prover() {
    let spent: Vec<[u8; 32]> = (20_000_000u64..20_000_024).map(nullifier_of_note).collect();
    let heap: Vec<HeapLeaf> = spent
        .iter()
        .map(|nf| HeapLeaf::entry(deployed_key(nf), BabyBear::new(7)))
        .collect();
    let desc = absent_desc();
    let present = deployed_key(&spent[3]);

    let refused =
        must_refuse_or_unsat_panic("an already-spent nullifier claiming freshness", || {
            prove_vm_descriptor2(
                &desc,
                &absent_trace(&heap, present),
                &[],
                &MemBoundaryWitness::default(),
                &[heap.clone()],
            )
            .map(|_| ())
        });
    assert!(
        refused.reason().contains("IS present in the heap"),
        "the refusal must name the reason: {}",
        refused.reason()
    );
}

// -------------------------------------------------------------------------------------------
// §4 — THE HALF-WIDENED STATE WAS NOT ENTERED.
// -------------------------------------------------------------------------------------------

/// ⚑ **THE FAILURE MODE THIS CUTOVER COULD HAVE PRODUCED, AND DID NOT.**
///
/// Widening the sort key while leaving the IMT pointer at one lane makes the honest low leaf and
/// a fabricated one ONE preimage — for every hash, with no collision-resistance hypothesis —
/// while the fabricated pointer brackets a PRESENT address. That is a non-membership FORGERY, and
/// it is strictly worse than today's narrow gate, which is merely incomplete
/// (`MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present`; the arithmetic is exhibited in
/// `mapabsent_key_width_tooth::half_widening_conflates_the_pointer_and_forges_absence`).
///
/// This cutover changed the AUTHOR of the constraints, not their WIDTH, so it cannot have entered
/// that state. This test is the check rather than the claim: the two invariants whose loss
/// defines half-widening are pinned against the LEAN EMISSION itself.
#[test]
fn the_cutover_did_not_half_widen_the_key() {
    let t = map_absent_table_air();

    // (a) The leaf absorb is still arity THREE — `[3, addr, value, next, 0×13, out8]`. A
    //     half-widened schema is arity 10 (`addr8 ‖ value ‖ proj0 next`); a fully widened one is
    //     17 or (correctly, at nine lanes) 19. Reading the arity tag out of the EMITTED tuple is
    //     what makes this a measurement of the deployed object.
    let chip: Vec<_> = t
        .interactions
        .iter()
        .filter(|i| i.bus == "ir2_p2" && i.op == BusOp::Query)
        .collect();
    assert_eq!(
        chip.len(),
        1 + HEAP_TREE_DEPTH,
        "one leaf absorb + the folds"
    );
    let leaf = chip[0];
    assert_eq!(
        leaf.tuple[0],
        WindowExpr::Const(HEAP_LEAF_ARITY as i64),
        "the emitted leaf absorb is arity {HEAP_LEAF_ARITY} — the deployed narrow schema"
    );
    assert_eq!(HEAP_LEAF_ARITY, 3);

    // (b) The address and the pointer are ONE column each, and — the half-widening tell — they
    //     are adjacent single columns inside the SAME arity-3 preimage. If the address had been
    //     widened while the pointer had not, the tuple would read eight address lanes and one
    //     pointer lane; it reads one and one.
    assert_eq!(leaf.tuple[1], WindowExpr::Loc(MA_LO_ADDR));
    assert_eq!(leaf.tuple[2], WindowExpr::Loc(MA_LO_VALUE));
    assert_eq!(leaf.tuple[3], WindowExpr::Loc(MA_LO_NEXT));
    assert_eq!(
        MA_LO_NEXT - MA_LO_ADDR,
        2,
        "address and pointer are one column each — the arithmetic proof that neither widened"
    );

    // (c) The pointer is INSIDE the committed digest's preimage. That is the property whose loss
    //     IS the forgery: a pointer outside the absorbed leaf could be chosen freely per proof.
    assert!(
        leaf.tuple[1..4]
            .iter()
            .any(|e| *e == WindowExpr::Loc(MA_LO_NEXT)),
        "the IMT pointer must ride inside the leaf digest's preimage"
    );

    // (d) And the comparators still compare ONE felt each, not a lane vector: two comparator
    //     blocks, 13 columns apiece.
    assert_eq!(t.width, MA_WIDTH);
}
