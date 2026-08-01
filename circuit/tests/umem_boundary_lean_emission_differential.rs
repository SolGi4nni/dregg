//! **THE GENERAL UNIVERSAL BOUNDARY'S CONSTRAINTS NOW COME FROM LEAN — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::UMemBoundary` was a hand-written Rust arm: four booleans, the real-row prefix, two
//! canonical-`none` legs, the canonical `(hi4, lo27)` split of a full-felt key, the domain-gap
//! nibble with its `same_dom` inverse witness, the DOMAIN-MAJOR lexicographic strict-increase
//! comparator against the SUCCESSOR row, both `ir2_umem_check` Blum legs and the served
//! `ir2_umem_addrs` closure entry. Architectural law #1 says that object is authored in Lean and
//! Rust only interprets. It was not. **That arm is now DELETED**; its author is
//! `metatheory/Dregg2/Circuit/Emit/UMemBoundaryTableEmit.lean`, its emission is
//! `circuit/descriptors/table-airs/dregg-ir2-umem-boundary-v1.json`, and `Ir2Air::LeanTable` walks
//! it.
//!
//! # ⚑ What the port PROVED and what it REFUTED
//!
//! The arm asserted: *"DOMAIN-MAJOR LEXICOGRAPHIC strict increase ⇒ the declared addresses are
//! Nodup — the hypothesis `memcheck_sound` stands on … same_dom is FORCED to the dgap-zero
//! indicator."* `Nodup` is the hypothesis the whole universal-memory soundness result rests on.
//!
//! The Lean file proves the FORCING in both directions (`same_dom_forces_zero_gap`,
//! `zero_gap_forces_same_dom`) — and then exhibits
//! `the_gates_alone_admit_a_duplicate_declared_address`: a three-row trace with domains
//! `1 → 0 → 1` where every GATE holds and rows 0 and 2 declare THE SAME `(domain, key)`. The
//! domain-major half of the order is carried by the `ir2_byte` nibble LOOKUP on the gap column — a
//! BUS leg — so the gates alone do not give `Nodup`. §3 measures that same witness through the
//! REAL deployed evaluator.
//!
//! ⚠ Direction: the deployed AIR HAS the lookup, so the prover does not admit the witness. What is
//! being said is which mechanism refuses it, because a soundness story that read the 28 gates as
//! establishing `Nodup` would be resting on a leg this table does not have.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, UMemBoundaryWitness, UMemOpSpec,
    VmConstraint2, WindowExpr, prove_vm_descriptor2_umem, table_air_gates_accept,
    umem_boundary_rows_for, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::must_refuse_or_unsat_panic;
use dregg_circuit::table_air::{
    BusOp, RowSel, umem_boundary_cohort_table_air, umem_boundary_table_air,
};

// The deployed layout, transcribed ONCE here. These are the same numbers
// `UMemBoundaryTableEmit.lean` derives; a drift on either side reds §1.
const UB_DOMAIN: usize = 0;
const UB_KEY: usize = 1;
const UB_INIT_PRESENT: usize = 2;
const UB_INIT_VALUE: usize = 3;
const UB_FIN_PRESENT: usize = 4;
const UB_FIN_VALUE: usize = 5;
const UB_FIN_SERIAL: usize = 6;
const UB_IS_REAL: usize = 7;
const UB_ADDR_MULT: usize = 8;
const UB_KEY_HI4: usize = 9;
const UB_KEY_IS15: usize = 20;
const UB_KEY_INV15: usize = 21;
const UB_DGAP: usize = 22;
const UB_SAME_DOM: usize = 23;
const UB_SAMEDOM_INV: usize = 24;
const UB_KCMP_S: usize = 25;
const UB_KCMP_DHI: usize = 26;
const UB_KCMP_DLO: usize = 27;
const UB_WIDTH: usize = 38;

/// The nullifier domain (`NULLIFIER_DOMAIN`), which the deployed insert-only tooth keys off.
const NULLIFIER_DOMAIN: u32 = 3;
/// A FULL-FELT key at the TOP of the canonical range: `p − 1 = 15 · 2^27`, the ONE value whose
/// canonical `hi4` is 15. ⓘ MEASURED, not assumed — `p − 2` has `hi4 = 14`, because `15 · 2^27` is
/// `p − 1` exactly. Choosing `p − 1` is what exercises the `is15 · lo27 = 0` uniqueness tooth on a
/// REAL row: it is the only key for which the tooth is not vacuous, and it is precisely the alias
/// the tooth exists to make unrepresentable twice.
const BIG_KEY: u32 = 2013265921 - 1;

/// A THREE-address, TWO-domain descriptor — enough to make the general (non-cohort) boundary
/// present and its comparator load-bearing at every step.
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
        name: "umem-boundary-lean-emission-differential".to_string(),
        trace_width: 5,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![
            // A nullifier INSERT (serial 1).
            op(
                NULLIFIER_DOMAIN,
                LeanExpr::Var(0),
                LeanExpr::Const(1),
                LeanExpr::Const(1),
                MemKind::Write,
            ),
            // THE FRESHNESS READ (serial 2) at a full-felt key: present = 0, i.e. `none`.
            op(
                NULLIFIER_DOMAIN,
                LeanExpr::Var(1),
                LeanExpr::Const(0),
                LeanExpr::Const(0),
                MemKind::Read,
            ),
            // A register write (serial 3) in a SECOND domain — what makes the DOMAIN-major half of
            // the comparator fire at all.
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
        BabyBear::new(7),       // inserted nullifier
        BabyBear::new(BIG_KEY), // fresh-checked nullifier (full-felt key)
        BabyBear::new(0),       // register key
        BabyBear::new(42),      // register value
        BabyBear::ZERO,         // guard (row 0 only)
    ];
    let mut rows = vec![row; 4];
    rows[0][4] = BabyBear::ONE;
    rows
}

/// The declared list, DOMAIN-MAJOR increasing: domain 0 first, then the two nullifier-domain keys
/// in ascending key order. ⚑ The second→third step is the SAME-domain one, so the key comparator
/// is genuinely switched on at least once here rather than being gated off throughout.
fn umem_boundary() -> UMemBoundaryWitness {
    UMemBoundaryWitness {
        addrs: vec![
            (0, BabyBear::new(0)),
            (NULLIFIER_DOMAIN, BabyBear::new(7)),
            (NULLIFIER_DOMAIN, BabyBear::new(BIG_KEY)),
        ],
        init_vals: vec![None, None, None],
    }
}

fn honest_rows() -> Vec<Vec<BabyBear>> {
    umem_boundary_rows_for(&umem_desc(), &umem_trace(), &umem_boundary())
        .expect("the deployed prover assembles a general universal boundary")
}

// -------------------------------------------------------------------------------------------
// §1 — THE ROUND-TRIP.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY, THE ROUND-TRIP.** The emitted table declares width 38, and this reads the
/// declared `(domain, key)` list, the canonical split, the domain gap and the `same_dom` indicator
/// back out of the prover's OWN trace, checking each against the witness rather than against the
/// same row.
#[test]
fn the_emitted_columns_round_trip_the_declared_address_list() {
    let rows = honest_rows();
    let t = umem_boundary_table_air();
    let w = umem_boundary();

    assert_eq!(t.width, UB_WIDTH);
    assert!(rows.iter().all(|r| r.len() == t.width));
    // ⓘ MEASURED: three declared addresses, height floored at `MIN_TABLE_HEIGHT = 8`.
    assert_eq!(rows.len(), 8);

    for (i, (d, key)) in w.addrs.iter().enumerate() {
        assert_eq!(rows[i][UB_DOMAIN], BabyBear::new(*d), "declared domain {i}");
        assert_eq!(rows[i][UB_KEY], *key, "declared key {i}");
        assert_eq!(rows[i][UB_IS_REAL], BabyBear::ONE);
        // Every declared init image is `none`, canonically: present 0 AND payload 0.
        assert_eq!(rows[i][UB_INIT_PRESENT], BabyBear::ZERO);
        assert_eq!(rows[i][UB_INIT_VALUE], BabyBear::ZERO);
        // The canonical split really is `key = hi4·2^27 + lo27`, recovered from the key.
        let hi4 = key.as_u32() >> 27;
        assert_eq!(rows[i][UB_KEY_HI4], BabyBear::new(hi4), "hi4 of key {i}");
    }
    // ⚑ The full-felt key sits at the TOP nibble, so the `is15` tooth fires on a real row — the
    // one case where the canonical split is not merely bookkeeping.
    assert_eq!(
        rows[2][UB_KEY],
        BabyBear::ZERO - BabyBear::ONE,
        "the key is p − 1"
    );
    assert_eq!(rows[2][UB_KEY_HI4], BabyBear::new(15));
    assert_eq!(rows[2][UB_KEY_IS15], BabyBear::ONE, "the is15 tooth fires");
    assert_eq!(rows[2][UB_KEY_INV15], BabyBear::ZERO);
    // …and on the two small keys it does not, so the inverse witness is the nonzero branch.
    assert_eq!(rows[0][UB_KEY_IS15], BabyBear::ZERO);
    assert_ne!(rows[0][UB_KEY_INV15], BabyBear::ZERO);

    // The DOMAIN GAP: 0 → 3 is a jump of 3; 3 → 3 is 0 (same domain); the last real→pad step is 0.
    assert_eq!(rows[0][UB_DGAP], BabyBear::new(3));
    assert_eq!(rows[1][UB_DGAP], BabyBear::ZERO);
    assert_eq!(rows[2][UB_DGAP], BabyBear::ZERO);
    // …and `same_dom` is its zero-indicator against next-real, exactly as the Lean §4a forcing
    // says: 0 on the cross-domain step, 1 on the same-domain one, 0 at the end of the list.
    assert_eq!(rows[0][UB_SAME_DOM], BabyBear::ZERO);
    assert_eq!(
        rows[1][UB_SAME_DOM],
        BabyBear::ONE,
        "keys are compared here"
    );
    assert_eq!(
        rows[2][UB_SAME_DOM],
        BabyBear::ZERO,
        "no successor to order"
    );
    // The inverse witness is nonzero exactly where the gap is.
    assert_ne!(rows[0][UB_SAMEDOM_INV], BabyBear::ZERO);
    assert_eq!(rows[1][UB_SAMEDOM_INV], BabyBear::ZERO);

    // ⚑ THE COMPARATOR, on the one step where it fires: 7 → p−2 crosses the top nibble, so the
    // `s = 1` branch is taken and `dhi` witnesses the nibble jump.
    assert_eq!(rows[1][UB_KCMP_S], BabyBear::ONE, "the hi-nibble branch");
    assert_eq!(rows[1][UB_KCMP_DHI], BabyBear::new(15 - 0 - 1));
    assert_eq!(rows[1][UB_KCMP_DLO], BabyBear::ZERO);
    // …and it is OFF everywhere else.
    assert_eq!(rows[0][UB_KCMP_S], BabyBear::ZERO);
    assert_eq!(rows[0][UB_KCMP_DHI], BabyBear::ZERO);

    assert!(
        table_air_gates_accept(&t, &rows),
        "the REAL `Ir2Air::LeanTable` evaluator must accept the prover's own honest rows"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — THE MUTATION SWEEP.
// -------------------------------------------------------------------------------------------

/// **⚑ WAS A GATE LOST?** For every row and every one of the 38 columns, bump the value and ask
/// the REAL deployed evaluator whether the table still accepts. The undetected set is pinned
/// EXACTLY and printed with its mechanism, rather than bounded.
#[test]
fn every_gated_boundary_cell_is_still_gated_after_the_cutover() {
    let rows = honest_rows();
    let t = umem_boundary_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    let mut detected: Vec<(usize, usize)> = Vec::new();
    let mut undetected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        for col in 0..t.width {
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

    // ⚑ The columns that MUST be caught on EVERY row, named with the gate that catches them.
    for row in 0..rows.len() {
        assert!(
            detected.contains(&(row, UB_IS_REAL)),
            "row {row}: the row guard"
        );
        assert!(
            detected.contains(&(row, UB_INIT_PRESENT)),
            "row {row}: the init presence boolean"
        );
        assert!(
            detected.contains(&(row, UB_FIN_PRESENT)),
            "row {row}: the final presence boolean"
        );
        assert!(
            detected.contains(&(row, UB_SAME_DOM)),
            "row {row}: the same-domain boolean + the `dgap·same_dom` forcing leg"
        );
        assert!(
            detected.contains(&(row, UB_KEY_HI4)),
            "row {row}: the canonical split's hi4"
        );
        assert!(
            detected.contains(&(row, UB_KEY_IS15)),
            "row {row}: the is15 uniqueness tooth"
        );
        assert!(
            detected.contains(&(row, UB_KCMP_S)),
            "row {row}: the comparator's branch selector"
        );
        // every limb of the key's 27-bit low word, and of the comparator's `dlo`.
        for col in 10..20 {
            assert!(detected.contains(&(row, col)), "row {row}: key limb {col}");
        }
        for col in 28..38 {
            assert!(detected.contains(&(row, col)), "row {row}: dlo limb {col}");
        }
    }

    // ⚠ THE UNDETECTED SET, EXACTLY — every member named with what binds it instead.
    //
    // * `UB_DOMAIN` — bound by the `ir2_byte` NIBBLE LOOKUP and the `ir2_umem_check` multiset.
    //   ⚑ NOT by a gate: this is the column `the_gates_alone_admit_a_duplicate_declared_address`
    //   turns on.
    // * `UB_ADDR_MULT`, `UB_FIN_SERIAL` — the LogUp / multiset counts.
    // * `(pad row, …)` — a pad's payload columns, gated off by `is_real`.
    //
    // Anything else here means the re-emission lost a gate.
    // ⚑ DERIVED FROM THE HONEST ROWS BY A PER-COLUMN RULE, each naming its mechanism, rather than
    // written out as a table of indices — a table would be a transcription of the answer, and this
    // is a statement of WHY each cell is free.
    let last = rows.len() - 1;
    let mut expected: Vec<(usize, usize)> = Vec::new();
    for row in 0..rows.len() {
        let real = rows[row][UB_IS_REAL] == BabyBear::ONE;
        for col in 0..t.width {
            let free = match col {
                // The multiset / LogUp counts, on every row. No gate reads either.
                UB_FIN_SERIAL | UB_ADDR_MULT => true,
                // ⚑ THE DOMAIN. On a REAL row it is bound only by the PREVIOUS row's dgap
                // definition (`dgap = next.is_real·(next.domain − domain)`), which a pad
                // predecessor zeroes out — so on a pad it is free. Its RANGE is the `ir2_byte`
                // nibble lookup and never a gate, which is exactly the hole
                // `the_gates_alone_admit_a_duplicate_declared_address` turns on.
                UB_DOMAIN => !real,
                // The canonical-`none` legs ride at `is_real·(1 − present)`: a payload is bound
                // exactly when its row is real AND its cell is ABSENT. ⓘ Here the three declared
                // INIT images are all `none` (so all three are gated) while only the freshness
                // read leaves its FINAL image absent — the asymmetry is read off the rows, not
                // asserted.
                UB_INIT_VALUE => !(real && rows[row][UB_INIT_PRESENT] == BabyBear::ZERO),
                UB_FIN_VALUE => !(real && rows[row][UB_FIN_PRESENT] == BabyBear::ZERO),
                // The `same_dom` inverse witness is pinned only where the gap is NONZERO:
                // `dgap·inv = next_real − same_dom` degenerates to `0 = 0` at a zero gap.
                UB_SAMEDOM_INV => rows[row][UB_DGAP] == BabyBear::ZERO,
                // ⚑ …and the SAME degeneracy in the canonical split, at the one key that reaches
                // the top nibble. `is15`'s inverse witness rides `(hi4 − 15)·inv15 = gate − is15`,
                // so at `hi4 = 15` the left side is 0·inv15 and `inv15` is bound by NOTHING. That
                // is harmless — `is15` is already forced to 1 by the same equation, and the
                // `is15 · lo27 = 0` tooth then pins `lo27` — but it is a free column and this
                // measures it rather than assuming the block is fully gated everywhere.
                UB_KEY_INV15 => rows[row][UB_KEY_HI4] == BabyBear::new(15),
                // ⚠ On the LAST row every `.transition` gate is vacuous, so the gap column and the
                // comparator's `dhi` witness are bound by their byte lookups alone.
                UB_DGAP | UB_KCMP_DHI => row == last,
                _ => false,
            };
            if free {
                expected.push((row, col));
            }
        }
    }
    assert_eq!(
        undetected, expected,
        "the undetected set is not exactly {{the nibble-, multiset- and LogUp-bound columns}} ∪ \
         {{the is_real-gated payloads}} — either a gate was lost in the Lean re-emission, or a \
         gate appeared where a bus is supposed to be the mechanism. undetected: {undetected:?}"
    );

    println!(
        "MEASURED: {}/{} boundary cells are gated by the Lean emission; the undetected {} are the \
         nibble-, multiset- and LogUp-bound columns plus the is_real-gated payloads",
        detected.len(),
        detected.len() + undetected.len(),
        undetected.len()
    );
}

// -------------------------------------------------------------------------------------------
// §3 — BOTH POLES AT THE DEPLOYED PROVER.
// -------------------------------------------------------------------------------------------

/// **COMPLETENESS.** An honest three-address, two-domain universal-memory witness proves and
/// verifies through the Lean-emitted AIR — with NO chip table committed, which is the measured
/// point of the universal-memory argument (it hashes nothing).
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
    .expect("an honest umem witness must prove through the Lean-emitted boundary AIR");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must verify");
}

/// **SOUNDNESS, the forged pole — at the GATES.**
#[test]
fn a_forged_declaration_is_refused_by_the_emitted_gates() {
    let rows = honest_rows();
    let t = umem_boundary_table_air();
    assert!(table_air_gates_accept(&t, &rows), "honest baseline");

    // (a) ⚑ SWITCH THE KEY COMPARATOR OFF on the same-domain step, by claiming the domains differ.
    //     Refused by the inverse-witness gate — `dgap·inv = next_real − same_dom` becomes
    //     `0 = 1 − 0` — which is exactly `zero_gap_forces_same_dom`, firing.
    let mut lie_diff = rows.clone();
    lie_diff[1][UB_SAME_DOM] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &lie_diff),
        "the emitted forcing must refuse `same_dom = 0` on a zero-gap step into a real row"
    );

    // (b) ⚑ SWITCH IT ON where the domains differ. Refused by the `dgap·same_dom = 0` gate —
    //     `same_dom_forces_zero_gap`, firing.
    let mut lie_same = rows.clone();
    lie_same[0][UB_SAME_DOM] = BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &lie_same),
        "the emitted forcing must refuse `same_dom = 1` against a nonzero domain gap"
    );

    // (c) ⚑ BREAK THE KEY ORDER within a domain: swap the comparator's branch selector so the
    //     nibble jump is claimed on the low-word branch. Refused by the branch equations.
    let mut bad_branch = rows.clone();
    bad_branch[1][UB_KCMP_S] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &bad_branch),
        "the emitted comparator must refuse a mis-selected branch"
    );

    // (d) ⚑ A NON-CANONICAL SPLIT: move `hi4` without its low word. Refused by the whole-value
    //     recomposition — this is what makes the comparator integer-faithful rather than
    //     representative-dependent (`MapAbsentTableEmit.canonSplit_unique`).
    let mut bad_split = rows.clone();
    bad_split[0][UB_KEY_HI4] = bad_split[0][UB_KEY_HI4] + BabyBear::ONE;
    assert!(
        !table_air_gates_accept(&t, &bad_split),
        "the emitted canonical split must refuse an unwitnessed hi4"
    );

    // (e) ⚑ BREAK THE PREFIX: make row 0 a pad while row 1 stays real.
    let mut broken = rows.clone();
    broken[0][UB_IS_REAL] = BabyBear::ZERO;
    assert!(
        !table_air_gates_accept(&t, &broken),
        "the emitted prefix gate must refuse a real row hiding behind a pad"
    );
}

/// ⚑ **THE REFUTED CLAIM, MEASURED AT THE DEPLOYED EVALUATOR.**
///
/// `UMemBoundaryTableEmit.the_gates_alone_admit_a_duplicate_declared_address` proves in Lean that
/// a three-row trace with domains `1 → 0 → 1` satisfies every emitted gate while rows 0 and 2
/// declare the same `(domain, key)`. This runs the SAME witness through the REAL
/// `Ir2Air::LeanTable` evaluator, so the Lean theorem and the deployed constraint system agree
/// about where the bound lives.
///
/// ⚠ Read the direction. The deployed AIR HAS the `ir2_byte` nibble lookup on `UB_DGAP`, and row
/// 0's gap here is `p − 1`, so the prover cannot use this. What it shows is that the domain-major
/// half of the ordering argument is a BUS leg — invisible to `TableAir.Holds`, and therefore to
/// every single-table theorem — so "the 28 gates establish `Nodup`" is false as stated.
#[test]
fn the_gates_alone_admit_a_duplicate_declared_address() {
    let t = umem_boundary_table_air();

    // Row `i`: a real declared cell at `(domain, p − 1)`, split at the top nibble (hi4 = 15,
    // lo27 = 0, is15 = 1, inv15 = 0 — the one split needing no inverse witness), comparator off.
    let row = |domain: u32, dgap: BabyBear, sdinv: BabyBear| {
        let mut r = vec![BabyBear::ZERO; UB_WIDTH];
        r[UB_DOMAIN] = BabyBear::new(domain);
        r[UB_KEY] = BabyBear::ZERO - BabyBear::ONE; // p − 1
        r[UB_IS_REAL] = BabyBear::ONE;
        r[UB_ADDR_MULT] = BabyBear::ONE;
        r[UB_KEY_HI4] = BabyBear::new(15);
        r[UB_KEY_IS15] = BabyBear::ONE;
        r[UB_DGAP] = dgap;
        r[UB_SAMEDOM_INV] = sdinv;
        r
    };
    let minus_one = BabyBear::ZERO - BabyBear::ONE;
    let wrap = vec![
        // 1 → 0: the gap is −1 ≡ p−1, whose inverse is itself.
        row(1, minus_one, minus_one),
        // 0 → 1: an HONEST nibble gap of 1, inverse 1.
        row(0, BabyBear::ONE, BabyBear::ONE),
        // the last row: no successor, so the transition gates are vacuous.
        row(1, BabyBear::ZERO, BabyBear::ZERO),
    ];

    assert!(
        table_air_gates_accept(&t, &wrap),
        "MEASURED: the emitted gates ACCEPT a domain sequence 1 → 0 → 1 — the domain-major half of \
         the order is the `ir2_byte` nibble LOOKUP on the gap column, not a gate \
         (UMemBoundaryTableEmit §4b)"
    );
    // …and rows 0 and 2 really do declare THE SAME address, which is `Nodup` failing.
    assert_eq!(wrap[0][UB_DOMAIN], wrap[2][UB_DOMAIN]);
    assert_eq!(wrap[0][UB_KEY], wrap[2][UB_KEY]);
    assert_eq!(wrap[0][UB_IS_REAL], BabyBear::ONE);
    assert_eq!(wrap[2][UB_IS_REAL], BabyBear::ONE);
    // ⚑ …and exactly ONE of the two gaps is out of nibble range. The other is honest, which is
    // what makes this a hole in the GATES rather than a trace nothing would look at twice.
    assert!(wrap[0][UB_DGAP].as_u32() >= 16, "the wrapped gap");
    assert!(wrap[1][UB_DGAP].as_u32() < 16, "…and the honest one");
}

/// The prover-level pole, stated at ITS OWN resolution: the ASSEMBLER refuses a non-increasing
/// declared list. ⚠ A completeness-of-refusal fact about `build_traces`, NOT a gate verdict — and
/// the test above is exactly why the distinction is worth drawing here.
#[test]
fn a_non_increasing_declaration_is_refused_by_the_deployed_assembler() {
    let desc = umem_desc();
    let refused = must_refuse_or_unsat_panic("a domain-decreasing declared list", || {
        prove_vm_descriptor2_umem(
            &desc,
            &umem_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness {
                addrs: vec![
                    (NULLIFIER_DOMAIN, BabyBear::new(7)),
                    (0, BabyBear::new(0)),
                    (NULLIFIER_DOMAIN, BabyBear::new(BIG_KEY)),
                ],
                init_vals: vec![None, None, None],
            },
        )
        .map(|_| ())
    });
    println!("MEASURED refusal: {}", refused.reason());
}

/// The emitted bus legs are the SIDES the universal-memory argument needs, and the two boundary
/// forms agree on the ones they share. ⚠ The half the mutation sweep is structurally blind to.
#[test]
fn the_boundary_serves_the_closure_table_and_agrees_with_the_cohort() {
    let t = umem_boundary_table_air();

    assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Provide), 1);
    assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Query), 0);
    let serve = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_addrs")
        .expect("one served entry");
    assert_eq!(
        serve.tuple,
        vec![WindowExpr::Loc(UB_DOMAIN), WindowExpr::Loc(UB_KEY)]
    );
    assert_eq!(serve.mult, WindowExpr::Loc(UB_ADDR_MULT));

    let send = t
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Send)
        .expect("one init publish");
    assert_eq!(
        send.tuple,
        vec![
            WindowExpr::Loc(UB_DOMAIN),
            WindowExpr::Loc(UB_KEY),
            WindowExpr::Loc(UB_INIT_PRESENT),
            WindowExpr::Loc(UB_INIT_VALUE),
            WindowExpr::Const(0)
        ],
        "the INIT cell is published at serial ZERO"
    );
    assert_eq!(send.mult, WindowExpr::Loc(UB_IS_REAL));

    // ⚑ THE TWO FORMS AGREE ON THE SHARED PREFIX. `build_traces` writes ONE nine-column prefix for
    // both tables (`THE_COHORT_IS_THE_GENERAL_PREFIX` pins the offsets); this checks the two
    // EMISSIONS read it the same way, which the Rust-side constant assertion cannot see.
    let c = umem_boundary_cohort_table_air();
    let cserve = c
        .interactions
        .iter()
        .find(|i| i.bus == "ir2_umem_addrs")
        .expect("one cohort served entry");
    assert_eq!(serve.tuple, cserve.tuple);
    assert_eq!(serve.mult, cserve.mult);

    // Six transition-scoped gates: prefix, dgap definition, inverse witness, three branches.
    assert_eq!(t.gate_count_sel(RowSel::Transition), 6);
    assert_eq!(t.gate_count_sel(RowSel::All), 22);
    assert_eq!(t.gate_count_sel(RowSel::First), 0);
    assert_eq!(t.gate_count_sel(RowSel::Last), 0);
}
