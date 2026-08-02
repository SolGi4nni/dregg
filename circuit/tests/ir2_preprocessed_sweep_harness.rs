//! **⚑ THE SWEEP HARNESS COULD NOT SEE A PREPROCESSED COLUMN. NOW IT CAN, AND IT REFUSES RATHER
//! THAN GUESSING.**
//!
//! Every mutation sweep in the table-AIR cutover runs through one row-local builder in
//! `descriptor_ir2.rs`, and that builder used to hand every AIR
//! `p3_air::RowWindow::from_two_rows(&[], &[])` — an EMPTY preprocessed window — with the comment
//! *"the IR-v2 Main AIR carries no preprocessed columns"*. The comment was true of the two arms the
//! builder then served. It was **false of the batch**: `Ir2Air::ExactPublicTable` reads nothing BUT
//! preprocessed columns. Its whole algebra is
//!
//! ```text
//! entry    := prep_row[..arity]                 // the manifest tuple the bus is served
//! pinned   := prep_row[mult_col]                // the multiplicity the descriptor DECLARES
//! assert_zero(committed_multiplicity − pinned)  // the ONE gate
//! ```
//!
//! so an oracle that hands it an empty window is not measuring a weakened version of that arm — it
//! is measuring nothing at all, and `TableAirIR` §7 item 4 named this as the thing that must land
//! **before** the first preprocessed-reading table AIR is emitted, not after.
//!
//! # What this file measures
//!
//! 1. the arm is now REACHABLE by a sweep at all — the honest instance accepts, and a mutation of
//!    the one committed column is CAUGHT (§1);
//! 2. ⚑ the oracle **REFUSES** a shape mismatch instead of substituting zeros (§2). That is the
//!    difference between a fixed instrument and a differently-broken one: a harness that silently
//!    zero-filled would report a clean undetected set for exactly the columns the arm is about.
//!    This is the repo's own doctrine — *a gate that cannot go red is not a gate* — applied to the
//!    instrument rather than to the circuit;
//! 3. the SIX Lean-authored table AIRs genuinely declare no preprocessed columns, so the empty
//!    matrix `table_air_gates_accept` passes is a CHECKED shape and not an assumed one (§3).
//!
//! ⚠ What this does NOT do: it does not port `Ir2Air::ExactPublicTable` to Lean. That arm is priced
//! in `TableAirIR` §7 and needs a `prep` expression leaf, a declared preprocessed width on the wire,
//! and a parameterized schema. This is item 4 of that list, landed on its own because the other
//! three cannot be measured honestly until it is.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, LookupSpec, TableDef2, TableSem, VmConstraint2, exact_public_instance_for,
    ir2_air_gates_accept, table_air_gates_accept,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::table_air::{
    byte_table_air, map_absent_table_air, mem_boundary_table_air, memory_table_air,
    umem_boundary_cohort_table_air, umem_boundary_table_air, umemory_table_air,
};

/// The exact-public table id used throughout (any non-reserved id works; the bus name is derived
/// from it, and nothing else in this file depends on the number).
const TID: usize = 9;

/// A descriptor declaring ONE exact-public manifest with a DUPLICATE row, so the pinned
/// multiplicity is genuinely `2` on one entry rather than `1` everywhere. A manifest of distinct
/// rows would make the pin gate look like `committed − 1`, and a sweep against that could not tell a
/// pinned column from a constant one.
fn manifest_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "ir2-preprocessed-sweep-harness".to_string(),
        trace_width: 2,
        public_input_count: 0,
        tables: vec![TableDef2 {
            id: TID,
            name: "manifest".to_string(),
            arity: 2,
            sem: TableSem::ExactPublicRows {
                rows: vec![vec![3, 4], vec![5, 6], vec![3, 4]],
            },
        }],
        constraints: vec![VmConstraint2::Lookup(LookupSpec {
            table: TID,
            tuple: vec![LeanExpr::Var(0), LeanExpr::Var(1)],
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

// -------------------------------------------------------------------------------------------
// §1 — THE ARM IS REACHABLE, AND ITS ONE GATE BITES.
// -------------------------------------------------------------------------------------------

/// **ANTI-VACUITY.** The honest instance — the committed multiplicity column the prover writes and
/// the preprocessed manifest the VERIFIER recomputes — is accepted by the real evaluator, and the
/// preprocessed matrix really does carry the declared tuple and its multiplicity.
#[test]
fn the_exact_public_instance_is_reachable_by_the_row_local_oracle() {
    let (air, main_rows, prep_rows) =
        exact_public_instance_for(&manifest_desc(), TID).expect("the descriptor declares it");

    // Two DISTINCT rows out of three declared, so the committed height is `next_pow2(2) = 2`.
    assert_eq!(main_rows.len(), 2);
    assert_eq!(prep_rows.len(), main_rows.len());
    assert!(
        main_rows.iter().all(|r| r.len() == 1),
        "one committed column"
    );
    assert!(
        prep_rows.iter().all(|r| r.len() == 3),
        "arity 2 + the pinned multiplicity"
    );

    // ⚑ THE ROUND-TRIP: the preprocessed rows ARE the declared manifest, deduplicated, with the
    // duplicate's multiplicity folded into the pin — and the committed column MIRRORS the pin.
    assert_eq!(prep_rows[0][0], BabyBear::new(3));
    assert_eq!(prep_rows[0][1], BabyBear::new(4));
    assert_eq!(prep_rows[0][2], BabyBear::new(2), "declared TWICE");
    assert_eq!(prep_rows[1][2], BabyBear::ONE);
    assert_eq!(main_rows[0][0], prep_rows[0][2]);
    assert_eq!(main_rows[1][0], prep_rows[1][2]);

    assert!(
        ir2_air_gates_accept(&air, &main_rows, &prep_rows),
        "the deployed evaluator must accept the prover's own committed column against the \
         verifier's own preprocessed manifest"
    );
}

/// **⚑ THE MEASUREMENT THE OLD HARNESS COULD NOT MAKE.** A sweep over the committed multiplicity
/// column: every cell is CAUGHT by the pin gate. With the empty preprocessed window this arm was
/// unreachable by any sweep in the repo — the undetected set would have been "all of it", reported
/// as clean.
///
/// ⓘ Free capacity here would demote the exact-public permutation to a CONTAINMENT (see
/// `ExactPublicManifest`), so "the committed column is pinned" is a soundness claim and not
/// bookkeeping. This is the first test that measures it at the evaluator rather than reading it off
/// the arm.
#[test]
fn every_committed_multiplicity_cell_is_pinned_to_the_preprocessed_manifest() {
    let (air, main_rows, prep_rows) =
        exact_public_instance_for(&manifest_desc(), TID).expect("the descriptor declares it");
    assert!(
        ir2_air_gates_accept(&air, &main_rows, &prep_rows),
        "honest baseline"
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
        "the exact-public pin gate left rows {undetected:?} free — a free capacity column demotes \
         the manifest permutation to a containment"
    );

    // …and symmetrically, a MANIFEST the prover altered is caught too. (In deployment the verifier
    // recomputes the preprocessed matrix from the descriptor, so this cannot happen on the wire —
    // it is asserted here to show the gate reads BOTH sides rather than only the committed one.)
    let mut forged_prep = prep_rows.clone();
    forged_prep[0][2] = forged_prep[0][2] + BabyBear::ONE;
    assert!(
        !ir2_air_gates_accept(&air, &main_rows, &forged_prep),
        "the pin gate must refuse a preprocessed multiplicity that disagrees with the committed one"
    );
}

// -------------------------------------------------------------------------------------------
// §2 — ⚑ IT REFUSES; IT DOES NOT SUBSTITUTE.
// -------------------------------------------------------------------------------------------

/// **⚑ THE FIX IS THE REFUSAL, NOT THE PLUMBING.** Handing a preprocessed-reading AIR NO
/// preprocessed rows — the exact shape the old harness hard-coded for every call — must be REFUSED,
/// not zero-filled.
///
/// This is the test that would have gone red on the old harness, and it is the reason the shape
/// contract is asked of `BaseAir::preprocessed_width` rather than written as a list of arms: a
/// future Lean-authored table that declares a preprocessed matrix inherits the refusal without
/// anyone remembering to add it.
///
/// ⚠ Note what a zero-filled window would have DONE here rather than what it would have failed to
/// do: the manifest's first entry is pinned at multiplicity 2, so against an all-zero prep row the
/// gate reads `2 − 0 ≠ 0` and the honest instance would have been reported UNSAT. Substituting a
/// witness does not merely blind an instrument in one direction; it makes both verdicts meaningless.
#[test]
fn an_absent_preprocessed_matrix_is_refused_not_zero_filled() {
    let (air, main_rows, prep_rows) =
        exact_public_instance_for(&manifest_desc(), TID).expect("the descriptor declares it");
    assert!(
        ir2_air_gates_accept(&air, &main_rows, &prep_rows),
        "honest baseline"
    );

    assert!(
        !ir2_air_gates_accept(&air, &main_rows, &[]),
        "an AIR that declares preprocessed columns must be REFUSED when handed none — a silently \
         zero-filled window is the instrument certifying the wound (TableAirIR §7 item 4)"
    );
    // The wrong HEIGHT and the wrong WIDTH are refused too, not truncated or padded.
    assert!(!ir2_air_gates_accept(&air, &main_rows, &prep_rows[..1]));
    let narrowed: Vec<Vec<BabyBear>> = prep_rows.iter().map(|r| r[..2].to_vec()).collect();
    assert!(!ir2_air_gates_accept(&air, &main_rows, &narrowed));
}

/// …and the OTHER direction: an AIR that declares NO preprocessed columns must be refused a
/// preprocessed matrix. A caller supplying one has confused two instances, and letting that pass
/// would mean the shape contract only bites in the direction someone happened to think of.
#[test]
fn a_preprocessed_matrix_supplied_to_a_prep_free_air_is_refused() {
    let t = umemory_table_air();
    let rows = vec![vec![BabyBear::ZERO; t.width]; 8];
    // The all-zero table is not the point (it may or may not satisfy the gates); the point is that
    // the two calls must DISAGREE, and the disagreeing one must be the one carrying a matrix the
    // AIR cannot read.
    let air = |prep: &[Vec<BabyBear>]| {
        ir2_air_gates_accept(
            &dregg_circuit::descriptor_ir2::Ir2Air::LeanTable(std::sync::Arc::new(t.clone())),
            &rows,
            prep,
        )
    };
    let stray = vec![vec![BabyBear::ONE; 3]; rows.len()];
    assert!(
        !air(&stray),
        "a table AIR with no preprocessed columns must refuse a supplied preprocessed matrix"
    );
}

// -------------------------------------------------------------------------------------------
// §3 — THE EMPTY WINDOW `table_air_gates_accept` PASSES IS A CHECKED SHAPE.
// -------------------------------------------------------------------------------------------

/// Every Lean-authored table AIR on the batch declares ZERO preprocessed columns today, so the
/// empty matrix `table_air_gates_accept` passes through is what the shape contract DEMANDS rather
/// than what the harness assumes. ⓘ This is the fact that makes the six existing differentials'
/// sweeps sound; it is asserted rather than described, so the day it stops being true this reds
/// instead of the sweeps quietly going blind.
#[test]
fn every_lean_table_air_declares_no_preprocessed_columns() {
    use p3_air::BaseAir;
    for t in [
        map_absent_table_air(),
        byte_table_air(),
        mem_boundary_table_air(),
        memory_table_air(),
        umemory_table_air(),
        umem_boundary_cohort_table_air(),
        umem_boundary_table_air(),
    ] {
        let name = t.name.clone();
        let air = dregg_circuit::descriptor_ir2::Ir2Air::LeanTable(std::sync::Arc::new(t));
        let pw = <dregg_circuit::descriptor_ir2::Ir2Air as BaseAir<
            p3_baby_bear::BabyBear,
        >>::preprocessed_width(&air);
        assert_eq!(
            pw, 0,
            "{name} declares {pw} preprocessed columns — every sweep that runs through \
             `table_air_gates_accept` now REFUSES it rather than sweeping it against zeros, and \
             the table IR needs the `prep` leaf priced in TableAirIR §7 before it can be emitted"
        );
    }
}

/// The width contract on the MAIN rows is unchanged and still fail-closed: a row of the wrong width
/// is refused rather than padded. Asserted so the refactor into `ir2_air_gates_accept` is measured
/// to have kept it.
#[test]
fn a_main_row_of_the_wrong_width_is_still_refused() {
    let t = umemory_table_air();
    assert!(!table_air_gates_accept(&t, &[]), "no rows");
    assert!(!table_air_gates_accept(
        &t,
        &[vec![BabyBear::ZERO; t.width - 1]]
    ));
    assert!(!table_air_gates_accept(
        &t,
        &[vec![BabyBear::ZERO; t.width + 1]]
    ));
}
