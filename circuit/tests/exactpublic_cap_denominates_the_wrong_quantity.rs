//! # ⚑ `MAX_EXACT_PUBLIC_CELLS` BOUNDS A QUANTITY NOTHING ALLOCATES — measured, not asserted.
//!
//! ## What this file is the detection for
//!
//! `check_descriptor2` refuses an exact-public table when `rows.len() * arity` exceeds
//! `MAX_EXACT_PUBLIC_CELLS = 2^25`. `rows` is the DECLARED manifest with duplicates kept. The only
//! matrix any code path materialises is `ExactPublicManifest`'s preprocessed table, whose shape is
//! `max(next_pow2(|distinct rows|), 2) * (arity + 2)`. For a manifest that carries multiplicity —
//! and an MSM generator table is nothing but multiplicity — those are different numbers.
//!
//! `Dregg2.Circuit.Emit.PastaMsmBucketed` §6c prices the deployed SRS manifest against the second
//! quantity. **This file is what stops that price from being a transcription.** Every figure below
//! is produced by the deployed `ExactPublicManifest::committed_shape` and the deployed
//! `MAX_EXACT_PUBLIC_CELLS`, and compared against the literals the Lean file `decide`s. If either
//! side moves, this goes red.
//!
//! ## ⚑ The defect this file was written to make detectable
//!
//! Before 2026-08-06, §6c modelled the committed height as `n = 2^16` — "already a power of two" —
//! and concluded the cap over-counts by **21×**. That is wrong by 2×. `srsManifest` emits
//! `termRows = 20 * 65,536 = 1,310,720` real rows and then pads to `bucketedRows = 1,474,800` with
//! copies of the all-zero `SRS_TUP`-tuple. A real row begins with `i + 1 >= 1`; the pad begins with
//! `0`; so the pad is a **65,537th distinct row** and `next_pow2` rounds to `2^17`, not `2^16`. The
//! true factor is **10×**, and `the_pad_row_pushes_the_height_up_a_rung` below is the pole that
//! would have caught it: it shows the two heights the two readings give, side by side.
//!
//! ## What this file does NOT claim
//!
//! It does not claim the cap should be raised, lowered, or removed — that is a live design question
//! and `srs_cells_exceed_the_deployed_cap` remains a true statement about the deployed refusal. It
//! claims only that the refused number and the allocated number are different numbers, and pins
//! both.

use dregg_circuit::descriptor_ir2::{ExactPublicManifest, MAX_EXACT_PUBLIC_CELLS};

// ---------------------------------------------------------------------------------------------
// The real object's parameters, as `PastaMsmBucketed` names them. Every one is a Lean `def` whose
// value that file `decide`s; they are restated here so a drift on either side is visible.
// ---------------------------------------------------------------------------------------------

/// `PastaMsmBucketed.STEP_SRS` — the Step/Tick SRS width (`accumulator_check.rs`'s `2^16` Vesta
/// bases).
const STEP_SRS: usize = 65536;
/// `PastaMsmBucketed.SRS_TUP` = `1 + PTLIMBS` — the declared tuple arity of the generator table.
const SRS_TUP: usize = 28;
/// `PastaMsmBucketed.windowsOf FULL_BITS BEST_C` = `(255 + 13 - 1) / 13`.
const WINDOWS: usize = 20;
/// `PastaMsmBucketed.termRows STEP_SRS FULL_BITS BEST_C` — one row per generator per window.
const TERM_ROWS: usize = WINDOWS * STEP_SRS;
/// `PastaMsmBucketed.bucketedRows STEP_SRS FULL_BITS BEST_C` = `fusedAdds` = `20 * 73_740`.
const BUCKETED_ROWS: usize = 1_474_800;

/// ⚑ `PastaMsmBucketed.the_srs_manifest_really_pads` — the declared manifest is strictly longer
/// than its real content, which is the whole premise of the over-count this file measures. Both
/// operands are constants, so it is a build obligation and not something one `#[test]` discovers.
const THE_SRS_MANIFEST_REALLY_PADS: () = assert!(
    TERM_ROWS < BUCKETED_ROWS,
    "the SRS manifest no longer pads: its declared row count is not above its real content, so \
     there is no over-count for this file to bracket"
);
const _: () = THE_SRS_MANIFEST_REALLY_PADS;

/// The distinct rows of the SRS manifest, in first-declaration order: one per generator, then the
/// all-zero pad. A generator row is `[i + 1, limbs..]`; the pad is `[0; SRS_TUP]`.
///
/// Height depends only on the DISTINCT count, so feeding the deduplicated list computes the same
/// height the full 1,474,800-row declared list would — at 7 MB instead of 165 MB.
/// `dedup_is_what_makes_the_short_list_legitimate` is the control for that step.
fn srs_distinct_rows(include_pad: bool) -> Vec<Vec<u32>> {
    let mut rows: Vec<Vec<u32>> = Vec::with_capacity(STEP_SRS + 1);
    for i in 0..STEP_SRS {
        let mut row = vec![0u32; SRS_TUP];
        row[0] = (i + 1) as u32;
        rows.push(row);
    }
    if include_pad {
        rows.push(vec![0u32; SRS_TUP]);
    }
    rows
}

/// ⚑ The declared manifest really is over the cap, so `srs_cells_exceed_the_deployed_cap` is a true
/// statement about the deployed refusal and not a Lean-side modelling artifact.
#[test]
fn the_declared_manifest_is_refused_by_the_deployed_cap() {
    let declared_cells = BUCKETED_ROWS * SRS_TUP;
    assert_eq!(
        declared_cells, 41_294_400,
        "PastaMsmBucketed.srsCells STEP_SRS FULL_BITS BEST_C"
    );
    assert!(
        declared_cells > MAX_EXACT_PUBLIC_CELLS,
        "the declared multiset ({declared_cells}) must exceed the deployed cap \
         ({MAX_EXACT_PUBLIC_CELLS}) -- this is what check_descriptor2 compares"
    );
}

/// ⚑⚑ **THE COMMITTED SHAPE, FROM THE DEPLOYED ALLOCATOR.** `2^17 x 30 = 3,932,160` cells — the
/// figure `PastaMsmBucketed.srsCommittedCells` `decide`s, produced here by the function that
/// actually builds the matrix.
#[test]
fn the_committed_shape_is_what_the_deployed_allocator_computes() {
    let rows = srs_distinct_rows(true);
    assert_eq!(rows.len(), 65_537, "PastaMsmBucketed.srsDistinctRows");

    let (height, prep_width) = ExactPublicManifest::committed_shape(&rows, SRS_TUP);

    assert_eq!(
        height, 131_072,
        "PastaMsmBucketed.srsCommittedHeight -- next_pow2(65_537) is 2^17"
    );
    assert_eq!(height, 1 << 17, "and it is the seventeenth power of two");
    assert_eq!(
        prep_width,
        SRS_TUP + 2,
        "PastaMsmBucketed.prepWidthOf SRS_TUP -- id column, values, pinned multiplicity"
    );
    assert_eq!(
        height * prep_width,
        3_932_160,
        "PastaMsmBucketed.srsCommittedCells"
    );
}

/// ⚑⚑ **THE POLE THAT WOULD HAVE CAUGHT THE 2× ERROR.** Drop the pad row and the distinct count is
/// `2^16` exactly, so `next_pow2` is the identity and the committed matrix is HALF the real one.
/// That is precisely the reading §6c shipped, and the two heights sit here side by side so the
/// difference is a test result rather than a paragraph.
#[test]
fn the_pad_row_pushes_the_height_up_a_rung() {
    let with_pad = srs_distinct_rows(true);
    let without_pad = srs_distinct_rows(false);

    let (h_with, _) = ExactPublicManifest::committed_shape(&with_pad, SRS_TUP);
    let (h_without, _) = ExactPublicManifest::committed_shape(&without_pad, SRS_TUP);

    assert_eq!(
        h_without, 65_536,
        "the old, wrong reading: n is already 2^16"
    );
    assert_eq!(
        h_with, 131_072,
        "the real one: n + 1 distinct rows round up"
    );
    assert_eq!(
        h_with,
        2 * h_without,
        "so the pre-2026-08-06 figure was low by exactly 2x"
    );

    // …and the pad really is emitted: the manifest is longer than its real content. Two
    // constants, so this is a build obligation — see `THE_SRS_MANIFEST_REALLY_PADS` below the
    // constants' definitions.
}

/// ⚑ **THE OVER-COUNT, BRACKETED.** `PastaMsmBucketed.srs_declared_overcounts_committed_by_10x`
/// states `10 * committed <= declared < 11 * committed`; both bounds are checked here against the
/// allocator's own output, so neither side can drift alone.
#[test]
fn the_cap_over_counts_the_srs_manifest_by_ten_times() {
    let rows = srs_distinct_rows(true);
    let (height, prep_width) = ExactPublicManifest::committed_shape(&rows, SRS_TUP);
    let committed = height * prep_width;
    let declared = BUCKETED_ROWS * SRS_TUP;

    assert!(
        10 * committed <= declared,
        "10 * {committed} must not exceed {declared}"
    );
    assert!(
        declared < 11 * committed,
        "{declared} must be under 11 * {committed} -- the factor is 10, not the 21 §6c claimed"
    );

    // The refused descriptor costs the verifier 11.7% of the cap it is refused by.
    assert!(
        100 * committed < 12 * MAX_EXACT_PUBLIC_CELLS,
        "PastaMsmBucketed.srs_committed_cells_fit"
    );
    assert!(
        committed < MAX_EXACT_PUBLIC_CELLS,
        "the allocated matrix is under the cap that refuses the declaration"
    );
}

/// The control for the short-list shortcut above: `committed_shape` genuinely deduplicates, so
/// passing the distinct rows computes the same height the full declared list would. Without this,
/// `the_committed_shape_is_what_the_deployed_allocator_computes` would be measuring a manifest the
/// emitter never produces.
#[test]
fn dedup_is_what_makes_the_short_list_legitimate() {
    // Three distinct rows declared with multiplicity 4, 1, 1 -- five declared, three distinct.
    let a = vec![1u32, 7, 7];
    let b = vec![2u32, 8, 8];
    let c = vec![0u32, 0, 0];
    let declared = vec![
        a.clone(),
        a.clone(),
        b.clone(),
        a.clone(),
        a.clone(),
        c.clone(),
    ];
    let distinct = vec![a, b, c];

    let (h_declared, w_declared) = ExactPublicManifest::committed_shape(&declared, 3);
    let (h_distinct, w_distinct) = ExactPublicManifest::committed_shape(&distinct, 3);

    assert_eq!(
        (h_declared, w_declared),
        (h_distinct, w_distinct),
        "six declared rows over three distinct commit the same matrix as the three"
    );
    assert_eq!(h_declared, 4, "next_pow2(3) = 4");
    assert_eq!(w_declared, 5, "arity 3 + id + multiplicity");

    // …and the cap would have counted six rows, not three: the two quantities differ at any scale.
    assert_eq!(declared.len() * 3, 18);
    assert_eq!(h_declared * w_declared, 20);
}

/// The floor: a one-row manifest still commits two rows (`MIN_EXACT_PUBLIC_HEIGHT`), so the
/// `max(_, 2)` in the shape law is not decoration.
#[test]
fn a_one_row_manifest_still_commits_two_rows() {
    let rows = vec![vec![1u32, 2]];
    let (height, prep_width) = ExactPublicManifest::committed_shape(&rows, 2);
    assert_eq!(height, 2, "MIN_EXACT_PUBLIC_HEIGHT floors next_pow2(1) = 1");
    assert_eq!(prep_width, 4);
}
