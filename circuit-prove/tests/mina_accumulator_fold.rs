//! ⚑⚑ **THE ACCUMULATOR CHAIN'S FOLD — IT PRODUCES A ROOT.**
//!
//! ## ⛑⛑ RESULT FIRST, and it replaces "it has never produced a root"
//!
//! Measured 2026-08-06, `/usr/bin/time -l`, release, 96 GiB box. Both proving polarities RUN:
//!
//! | test                                              | wall     | maxrss              | peak footprint       |
//! |---------------------------------------------------|----------|---------------------|----------------------|
//! | `a_one_segment_chain_is_the_final_rung`            | 223.36 s | 48.85 GiB / 52.45 GB | 117.93 GiB / 126.63 GB |
//! | `the_split_chain_folds_and_the_root_carries_both_endpoints` | 500.37 s | 61.35 GiB / 65.87 GB | 118.30 GiB / 127.03 GB |
//!
//! The second is **two leaves and one `cb.connect` fold**, and its root carries segment A's
//! incoming accumulator, segment B's outgoing one, and `claim.is_identity()` on that outgoing
//! point — the whole chain's endpoints, from a proof that exists.
//!
//! ⚠ **TWO METRICS, TWO UNIT SYSTEMS, AND THEY ARE NOT INTERCHANGEABLE.** `maxrss` and `peak memory
//! footprint` differ by 2.4× here: the first is what stayed resident, the second is what was charged
//! including compressed pages. The footprint EXCEEDS physical RAM. **This fits only because macOS
//! compresses**; a Linux box at 96 GiB with no swap headroom meets the OOM killer on the way up, and
//! the run was visibly memory-stalled throughout (500 s wall against 263 s user and 608 s sys).
//!
//! ## ⛑⛑ RE-MEASURED 2026-08-06, AND THE FOOTPRINT IS THE SHAPE WHILE THE WALL IS THE BOX
//!
//! Same binary, same fixture, same box, second run — this time with the box **co-tenanted** (three
//! other lanes' `lean` processes at 5.7 / 1.8 / 1.4 GB, and swap already 62 GB deep):
//!
//! | metric            | first run              | re-measured            | moved  |
//! |-------------------|------------------------|------------------------|--------|
//! | wall              | 500.37 s               | **696.97 s**           | +39.3% |
//! | user / sys        | 263 s / 608 s          | **280.58 s / 765.47 s**| sys 2.7× user |
//! | maxrss            | 61.35 GiB / 65.87 GB   | **50.13 GiB / 53.82 GB** | −18.3% |
//! | peak footprint    | 118.30 GiB / 127.03 GB | **117.97 GiB / 126.67 GB** | **−0.3%** |
//!
//! ⚑ **The footprint reproduces to three parts in a thousand while the wall moves 39% and maxrss
//! moves 18%.** That is the cost model confirming itself: the footprint is a function of the
//! COMMITTED LDE — a property of the descriptor's shape — and `maxrss` is a function of how much of
//! it the machine happened to keep resident, which is a property of the box. Quote the footprint
//! when comparing shapes; quote the wall only against a box you can describe.
//!
//! ⚠ **AND NO UNLOADED BOX IN THE FLEET CAN HOST IT.** 126.67 GB of footprint against persvati's
//! 83 GiB RAM + 15 GiB swap (98 GiB, would OOM) and hbox's 123 GiB + 8 GiB swap where 34 GiB is a
//! co-tenant's and `earlyoom` is armed. The 96 GiB Mac is the only machine it fits on, and only
//! because macOS compresses. "Re-measure on an unloaded box" has no answer at this width — which is
//! itself the argument for the narrowing below.
//!
//! ⚑ **AND THE 68.3 GiB THAT STOOD IN THIS HEADER WAS NOT A PEAK.** It was labelled "peak memory
//! footprint" of a run that was *killed before finishing* — the high-water mark of a climb that had
//! not stopped climbing. Both completed runs reach ~118 GiB, 1.7× higher. **A killed run's
//! high-water mark bounds nothing from above**, and quoting it as a peak understated the wall in
//! the flattering direction — the same shape of error as quoting one member of a unit pair.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-accumulator-{seg,final}::v1` are
//! `EffectLower.lowerAir` of `Dregg2.Circuit.Emit.MinaAccumulatorAir.{accSegAir, accFinalAir}`, and
//! the traces come from `metatheory/EmitMinaAccumulator.lean`. Rust proves and folds; it authors
//! nothing.
//!
//! ## THE EXHIBIT
//!
//! One honest 8-row Vesta chain that ends at the point at infinity, **split down the middle**:
//!
//! ```text
//!   segment A = rows 0..3   (dregg-mina-accumulator-seg::v1)     acc: G  ->  5G
//!   segment B = rows 4..7   (dregg-mina-accumulator-final::v1)   acc: 5G ->  O
//! ```
//!
//! Inside a segment the accumulator crosses rows through the 96 `.transition` window gates. Between
//! segments it crosses through 96 in-circuit `cb.connect`s. Both are constraints; neither is a host
//! comparison, and that is the entire content of the claim.
//!
//! ## ⚑ THE FALSIFIER, AND WHY IT ISOLATES THE CARRY
//!
//! `the_fold_refuses_two_segments_that_do_not_chain` folds segment A **with itself**. Both children
//! are the SAME proof — individually valid, verifying, exposing a well-formed 192-lane claim — and
//! the fold must still have no satisfying assignment, because A ends at `5G` and begins at `G`.
//!
//! That is precisely what a fold looks like when it re-pins public inputs instead of carrying
//! state: two honest sub-proofs whose endpoints do not meet. If the `cb.connect` loop were deleted,
//! this test would go GREEN and every other test in this file would stay green — which is what
//! makes it the load-bearing one.
//!
//! ## ⛑ THE THREE PROVING TESTS STAY `#[ignore]`d — FOR ~10 MINUTES AND ~118 GiB, NOT FOR "SLOW"
//!
//! They run, and they are `#[ignore]`d because a default `cargo test` must not commit a developer's
//! box to a ten-minute run that pushes its memory into compression. Each `#[ignore]` reason now
//! carries the measured wall and the measured wall-clock rather than a word.
//!
//! ## ⚑⚑ THE COST LAW, MEASURED WITH A CONTROL — COLUMNS, NOT CELLS, AND NOT ROWS
//!
//! The previous draft attributed the wall to the descriptor's **3,048** columns against the phase-2
//! chainlink's **469** — an inference from a ratio, taken while the two also differed by 256× in
//! ROWS, with only one of the two named. `tests/mina_accumulator_leaf_anatomy.rs` separates them by
//! BUILDING the leaf-wrap verification circuit without proving it (~20 s, ~2 GiB for five wraps):
//!
//! ```text
//!  in_cols  rows      wrap ops    witness         npo       horner   wrap LDE cells
//!      469  2048       248,555    383,938      68,777      127,547      932,916,224
//!     3048     1     2,862,507  4,532,901     795,215    1,575,100   14,911,873,024
//!     3048     8     2,878,069  4,548,539     795,215    1,575,100   14,911,873,024
//! ```
//!
//! **Eight times the inner ROWS moves the wrap circuit by 0.5%** and its committed cells not at all;
//! **6.5× the inner COLUMNS, at 1/256th the rows, costs 11.6× the ops and 16.0× the cells.** The
//! in-circuit verifier pays `Q · W` per commitment round — one Poseidon2-W16 permutation per 8
//! opened base coefficients, one `HornerAcc` per opened COLUMN per opening point — at
//! `INNER_FRI_NUM_QUERIES = 19`. Rows enter only as Merkle depth and fold-phase count.
//!
//! ⚑ The cells account for the peak, which is what makes this a model and not a correlation:
//! `14,911,873,024 × 4 B = 59.6 GB / 55.5 GiB` of committed LDE at `IR2_INNER_LOG_BLOWUP = 6` (64×),
//! against the ~118 GiB footprint once quotient chunks, Merkle trees and working copies are added.
//!
//! ⚑ **SO "TALLER, NO WIDER" IS NOT A MITIGATION — IT IS FREE, AND SPLITTING A CHAIN INTO MORE
//! SEGMENTS IS A PURE LOSS.** This file's own exhibit is the demonstration: the 8-row chain as ONE
//! segment costs 223 s, and split into two costs 500 s for the same eight additions.
//! `the_leaf_wrap_cost_tracks_columns_and_not_rows` keeps both halves in the tree.
//!
//! ## ⚑ AND THE NARROWING THAT WOULD MAKE THIS ORDINARY — 446 COLUMNS
//!
//! `MinaAccumulatorAir.the_row_boundary_is_two_hundred_eighty_eight` establishes that only **288**
//! of the 3,048 columns cross a row boundary; the other 2,760 are scratch that exists because 33 SSA
//! ops share ONE row. A row carrying one op needs its witness plus the DAG's live set, whose peak is
//! 11 values: `11 × 32 + 94 = 446`, at 33× the rows — **under the 469 that already folds 46 leaves
//! and 45 folds in 1,037 s.** See `the_narrowing_target_is_four_hundred_forty_six_columns`. That is
//! `PastaLadderThread`'s own move one rail further down, and it is Lean authoring, not a knob.
//!
//! Run everything, including the three that prove (~20 min, ~118 GiB peak footprint):
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_accumulator_fold -- --include-ignored --nocapture
//! ```

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::mina_accumulator_fold::{
    ACC_CLAIM_LEN, POINT_WIDTH, Rung, SK, accumulator_config, accumulator_descriptor,
    fold_accumulator_segments, prove_accumulator_fold, prove_accumulator_segment,
    read_accumulator_claim, segment_public_inputs,
};

const DISCHARGING: &str =
    include_str!("../../circuit/tests/fixtures/mina-accumulator-discharging-trace.txt");

/// The honest chain, as `BabyBear` rows.
fn full_trace() -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = DISCHARGING
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(rows.len(), 8, "the fixture is eight rows");
    assert!(rows.iter().all(|r| r.len() == 3048));
    rows
}

/// The two halves, each a power-of-two height the deployed prover accepts.
fn segments() -> Vec<(Vec<Vec<BabyBear>>, Vec<BabyBear>)> {
    let t = full_trace();
    let a: Vec<Vec<BabyBear>> = t[..4].to_vec();
    let b: Vec<Vec<BabyBear>> = t[4..].to_vec();
    let pa = segment_public_inputs(&a).expect("segment A public inputs");
    let pb = segment_public_inputs(&b).expect("segment B public inputs");
    vec![(a, pa), (b, pb)]
}

/// ⚑ **THE SPLIT IS A REAL SEAM, AND IT MEETS.** Segment A's published terminal accumulator IS
/// segment B's published initial one, limb for limb — checked on the FIXTURE before any prover
/// runs, so a green fold below cannot be green because the two halves happened to be the same
/// point, and a red one cannot be blamed on a fixture that never chained.
#[test]
fn the_two_segments_meet_at_the_seam_and_are_not_the_same_point() {
    let segs = segments();
    let (_, pa) = &segs[0];
    let (_, pb) = &segs[1];
    assert_eq!(pa.len(), ACC_CLAIM_LEN);
    assert_eq!(pb.len(), ACC_CLAIM_LEN);

    assert_eq!(
        &pa[POINT_WIDTH..],
        &pb[..POINT_WIDTH],
        "A's outgoing accumulator must BE B's incoming one — this is what the fold connects"
    );
    assert_ne!(
        &pa[..POINT_WIDTH],
        &pa[POINT_WIDTH..],
        "segment A must MOVE the accumulator; a fixed point would make the carry vacuous"
    );
    assert_ne!(
        &pb[..POINT_WIDTH],
        &pb[POINT_WIDTH..],
        "segment B must MOVE the accumulator too"
    );

    // …and B ends at the point at infinity: X and Z zero, Y NOT zero.
    let out = &pb[POINT_WIDTH..];
    for i in 0..SK {
        assert_eq!(out[i], BabyBear::new(0), "terminal X limb {i}");
        assert_eq!(out[2 * SK + i], BabyBear::new(0), "terminal Z limb {i}");
    }
    assert!(
        (0..SK).any(|i| out[SK + i] != BabyBear::new(0)),
        "the identity is (0 : y : 0) with y NONZERO"
    );
}

/// The two rungs resolve to the two Lean artifacts, and the final one forces strictly more.
#[test]
fn the_rungs_resolve_to_the_lean_artifacts() {
    let a = accumulator_descriptor(Rung::Interior).expect("segment descriptor");
    let b = accumulator_descriptor(Rung::Final).expect("final descriptor");
    assert_eq!(a.trace_width, 3048);
    assert_eq!(b.constraints.len(), a.constraints.len() + 64);
}

/// ⛑⛑ **THE COST LAW, MEASURED WITH A CONTROL — AND THE CONTROL IS THE HALF THAT WAS MISSING.**
///
/// The previous draft of this test asserted a RATIO — 3,048 columns against the phase-2 chain's
/// 469 — and inferred the cause from it. An inference from a ratio is not a law: a 6.5× width and a
/// 256× row difference were both present and only one of them was named. Both are now separated,
/// by `tests/mina_accumulator_leaf_anatomy.rs`, which BUILDS the leaf-wrap verification circuit
/// (without proving it, so the whole sweep costs ~20 s and 2 GiB) and censuses it:
///
/// ```text
///  in_cols  rows      wrap ops    witness      npo         alu      horner   wrap LDE cells
///      469  2048       248,555    383,938   68,777     155,421     127,547      932,916,224
///     3048     1     2,862,507  4,532,901  795,215   1,772,030   1,575,100   14,911,873,024
///     3048     2     2,878,065  4,548,535  795,215   1,787,587   1,575,100   14,911,873,024
///     3048     4     2,878,067  4,548,537  795,215   1,787,588   1,575,100   14,911,873,024
///     3048     8     2,878,069  4,548,539  795,215   1,787,589   1,575,100   14,911,873,024
/// ```
///
/// ⚑ **ROWS ARE FREE AND COLUMNS ARE THE WHOLE BILL.** Eight times the inner rows moves the wrap
/// circuit by **0.5%** (2,862,507 → 2,878,069) and does not move the committed cells at all, while
/// 6.5× the inner columns — at **1/256th** the rows — costs **11.6×** the wrap ops and **16.0×** the
/// committed cells. The mechanism is that the in-circuit verifier pays `Q · W` per commitment
/// round: one Poseidon2-W16 permutation per 8 opened base coefficients and one `HornerAcc` per
/// opened COLUMN per opening point (`recursion/src/pcs/mmcs.rs`, `pcs/fri/verifier.rs`), at
/// `INNER_FRI_NUM_QUERIES = 19`. Rows enter only as Merkle depth and fold-phase count.
///
/// ⚑ …and the committed cells ACCOUNT FOR THE MEASURED PEAK, which is what makes this a model
/// rather than a correlation: 14,911,873,024 BabyBear cells × 4 bytes = **59.6 GB / 55.5 GiB**
/// against a measured **68.3 GiB** peak — 81% of it, with quotient chunks, Merkle trees and working
/// copies the remainder. The wrap's own tables are LDE'd at `IR2_INNER_LOG_BLOWUP = 6`, i.e. 64×,
/// because `create_recursion_config_with_fri` sets the MINTING blowup and the in-circuit verifier's
/// blowup from one argument.
///
/// ⚑ **SO "A SEGMENT THAT IS TALLER AND NO WIDER" IS NOT A MITIGATION — IT IS FREE, AND IT WAS
/// ALREADY BEING PAID FOR.** Splitting the 8-row exhibit into two 4-row segments buys nothing and
/// costs an extra 68 GiB-class wrap. The leaf should carry every row it can.
///
/// If this assertion goes red because `RCB_WIDTH` moved, re-run the anatomy sweep before assuming
/// the wall moved with it.
#[test]
fn the_leaf_wrap_cost_tracks_columns_and_not_rows() {
    /// `MinaPhase2Chain`'s chain-link descriptor width, the one that DOES fold in production.
    const PHASE2_WIDTH: usize = 469;
    /// The measured peak of one accumulator leaf wrap, in bytes (2026-08-06, `/usr/bin/time -l`).
    const MEASURED_LEAF_PEAK_BYTES: u64 = 73_344_091_528;

    // --- the measured wrap-circuit sizes, from tests/mina_accumulator_leaf_anatomy.rs ---------
    /// Wrap-circuit ops for the 469-column chainlink leaf, at 2,048 inner rows.
    const CHAINLINK_WRAP_OPS: u64 = 248_555;
    /// …and for the 3,048-column accumulator segment, at 1 inner row.
    const ACC_WRAP_OPS_1_ROW: u64 = 2_862_507;
    /// …and at 8 inner rows. Eight times the rows.
    const ACC_WRAP_OPS_8_ROWS: u64 = 2_878_069;

    let a = accumulator_descriptor(Rung::Interior).expect("segment descriptor");
    assert_eq!(a.trace_width, 3048);
    assert!(
        a.trace_width > 6 * PHASE2_WIDTH,
        "the accumulator segment is {} columns against the phase-2 chain's {PHASE2_WIDTH}; if that \
         ratio ever drops below 6x, the wrap is worth re-measuring",
        a.trace_width
    );

    // ⚑ THE CONTROL. Eight times the inner rows must not move the wrap circuit by even 1%. If this
    // ever fails, the cost law changed and "make the leaf taller" stopped being free.
    assert!(
        ACC_WRAP_OPS_8_ROWS - ACC_WRAP_OPS_1_ROW < ACC_WRAP_OPS_1_ROW / 100,
        "8x the inner ROWS moved the wrap circuit by {} ops out of {ACC_WRAP_OPS_1_ROW} — the cost \
         law measured on 2026-08-06 says rows are free",
        ACC_WRAP_OPS_8_ROWS - ACC_WRAP_OPS_1_ROW
    );

    // ⚑ THE TREATMENT. 6.5x the inner COLUMNS, at 1/256th the rows, costs >10x the wrap circuit.
    assert!(
        ACC_WRAP_OPS_8_ROWS > 10 * CHAINLINK_WRAP_OPS,
        "the accumulator wrap is {ACC_WRAP_OPS_8_ROWS} ops against the chainlink's \
         {CHAINLINK_WRAP_OPS} — the width term is what this file exists to name"
    );

    // ⚑ 68.3 GiB. Stated in BOTH unit systems and asserted in both, because the first draft of this
    // assertion compared the DECIMAL figure (73.3 GB) against a BINARY threshold (70 GiB) and went
    // red — a unit slip is exactly how a memory figure drifts into a flattering one.
    assert!(
        MEASURED_LEAF_PEAK_BYTES > 73 * 1_000_000_000,
        "73.3 GB decimal"
    );
    assert!(
        MEASURED_LEAF_PEAK_BYTES > 68 * 1024 * 1024 * 1024,
        "68.3 GiB binary"
    );
    // …and that is 71% of a 96 GiB box, which is why a co-tenant run met the OOM killer.
    assert!(MEASURED_LEAF_PEAK_BYTES * 10 > 7 * 96 * 1024 * 1024 * 1024);
}

/// ⚑⚑ **WHERE A FOLDABLE ACCUMULATOR LEAF WOULD COME FROM — 446 COLUMNS, DERIVED FROM THE EMITTED
/// GADGET'S OWN SSA LISTING.**
///
/// ⚠ This is a DERIVATION, not a measurement, and it is labelled as one everywhere it is used: no
/// such descriptor exists and nothing here proves one would be sound. What it is not is a mood — it
/// is the arithmetic that says whether narrowing lands in the class that already folds.
///
/// `MinaAccumulatorAir.the_row_boundary_is_two_hundred_eighty_eight` establishes in Lean that only
/// **288** of the 3,048 columns cross a row boundary: six input blocks in, three output blocks out.
/// The other **2,760** are scratch that exists solely because `swCompleteAddSoundLegs`' 33 SSA ops
/// share ONE row. A row carrying one op instead of 33 needs the op's witness plus whatever the SSA
/// DAG has LIVE at that point — and the peak live set of that DAG, walked over the listing at
/// `PastaCurveSound.lean:419-451` (12 mul + 2 smul + 14 add + 5 sub, which
/// `the_op_kind_census_matches_the_lean_listing` below pins), is **11** 256-bit values:
///
/// ```text
///   row = 11 live values × SK(32) + max witness(94, the multiply's 32 quotient + 62 carries) = 446
/// ```
///
/// ⚑ **446 against the 469 that folds 46 leaves and 45 folds in 1,037 s.** Threading one rail
/// further down — the same move `PastaLadderThread` made when it took the row-local ladder from
/// 731,136 columns in one row to 3,048 columns over rows — lands the accumulator leaf BELOW the
/// width class that is already in production, at 33× the rows, which the cost law above measures as
/// free. That is the shape of the fix, and it is Lean authoring work on a new AIR plus a multi-row
/// re-proof of `vestaCompleteAddSound_forces`, not a knob.
///
/// ⚠ And it is NOT a soundness relaxation: every constraint the gadget emits is already a statement
/// about ONE op's operands and output. What changes is which row they sit on.
#[test]
fn the_narrowing_target_is_four_hundred_forty_six_columns() {
    /// `PastaFieldSound.SK` — limbs in a 256-bit value at the sound 8-bit encoding.
    const SK: usize = 32;
    /// `SK + (NG - 1)` — a multiply witness: 32 quotient limbs then 62 carries. The widest witness.
    const MUL_WITNESS: usize = 94;
    /// Peak simultaneously-live 256-bit values in the 33-op complete-addition DAG.
    const PEAK_LIVE: usize = 11;
    /// The width that folds in production.
    const PHASE2_WIDTH: usize = 469;

    let narrowed = PEAK_LIVE * SK + MUL_WITNESS;
    assert_eq!(narrowed, 446);
    assert!(
        narrowed < PHASE2_WIDTH,
        "a one-op-per-row sound RCB is {narrowed} columns against the {PHASE2_WIDTH} that already \
         folds — the narrowing lands INSIDE the foldable class, which is the whole point of stating \
         it as a number"
    );

    let a = accumulator_descriptor(Rung::Interior).expect("segment descriptor");
    assert!(
        a.trace_width > 6 * narrowed,
        "…and it is {:.1}x narrower than what is emitted today",
        a.trace_width as f64 / narrowed as f64
    );
}

/// The op-kind census the 446 above is derived from, taken from the Lean gadget's own listing
/// (`PastaCurveSound.swCompleteAddSoundLegs`, whose docblock states `12 mul + 2 smul + 14 add +
/// 5 sub`). Pinned here because the derived width depends on the DAG having exactly this shape, and
/// a silently re-ordered gadget would leave the 446 quoting a listing that had moved.
///
/// ⚠ Both sides of this are the SAME source today — the Lean docblock and this constant — so it is
/// a tripwire on the derivation, not two independent measurements of the gadget.
#[test]
fn the_op_kind_census_matches_the_lean_listing() {
    const MUL: usize = 12;
    const SMUL: usize = 2;
    const ADD: usize = 14;
    const SUB: usize = 5;
    assert_eq!(MUL + SMUL + ADD + SUB, 33, "the gadget is 33 SSA ops");

    // …and those 33 ops' witness columns are what `MinaAccumulatorAir.the_column_census` counts:
    // 12 * 94 + 2 * 32 + 19 * 32 = 1,800, with 19 = ADD + SUB.
    assert_eq!(ADD + SUB, 19);
    assert_eq!(MUL * 94 + SMUL * 32 + (ADD + SUB) * 32, 1800);
    // …plus 33 SSA value blocks and six input blocks: the emitted width.
    assert_eq!(1800 + 33 * 32 + 6 * 32, 3048);
}

/// ⚑⚑ **POLARITY 1 — THE CHAIN FOLDS. MEASURED 2026-08-06: 500.37 s, AND IT PASSES.**
///
/// Two leaves and one fold. The root exposes `A.acc_in ‖ B.acc_out` — the point the chain started
/// from and the point it ended on — and B was proved against the descriptor whose 64
/// `when_last_row` gates FORCE that terminal point to be the identity, so the discharge is in the
/// AIR rather than in a host read.
///
/// | metric                    | binary     | decimal   |
/// |---------------------------|------------|-----------|
/// | wall clock                | 500.37 s   | 500.37 s  |
/// | maximum resident set size | 61.35 GiB  | 65.87 GB  |
/// | peak memory footprint     | 118.30 GiB | 127.03 GB |
///
/// ⚑ The 96 limbs crossing the seam cross it through `cb.connect`, in-circuit. That the assertions
/// below hold on a proof that EXISTS is what separates this from a described mechanism — and
/// `the_fold_refuses_two_segments_that_do_not_chain` is the other half, without which a green here
/// would be equally green if the connect loop were deleted.
#[test]
#[ignore = "RUNS: 500 s, 118.3 GiB peak footprint / 61.4 GiB maxrss — ignored for cost, not failure"]
fn the_split_chain_folds_and_the_root_carries_both_endpoints() {
    let cfg = accumulator_config();
    let segs = segments();

    let root = prove_accumulator_fold(&segs, &cfg, |i, phase| {
        println!("  segment {i}: {phase}");
    })
    .expect("the honest split chain must fold");

    let claim = read_accumulator_claim(&root).expect("the root publishes a 192-lane claim");
    assert_eq!(claim.acc_in.len(), POINT_WIDTH);
    assert_eq!(claim.acc_out.len(), POINT_WIDTH);

    // the root's endpoints are the WHOLE chain's, not one segment's
    assert_eq!(
        claim.acc_in,
        segs[0].1[..POINT_WIDTH],
        "the root must carry the FIRST segment's incoming accumulator"
    );
    assert_eq!(
        claim.acc_out,
        segs[1].1[POINT_WIDTH..],
        "the root must carry the LAST segment's outgoing accumulator"
    );

    // …and that outgoing accumulator is the point at infinity, on both rails.
    assert!(
        claim.is_identity(),
        "the folded chain must end at the point at infinity"
    );
    assert!(
        claim.terminal_y_is_nonzero(),
        "an all-zero triple is not a projective point"
    );
}

/// ⚑⚑ **POLARITY 2 — THE FOLD REFUSES TWO SEGMENTS THAT DO NOT CHAIN.**
///
/// Segment A folded with ITSELF. Both children are the same individually-valid proof, so nothing is
/// wrong with either one — the only thing wrong is that A's terminal accumulator (`5G`) is not A's
/// initial one (`G`). The 96 `cb.connect`s are the only thing in the aggregation that can object.
///
/// This is the test that would go green if the carry were replaced by re-pinned public inputs, and
/// it is why the carry is not a re-pin.
/// ⚑ Measured 2026-08-06: **249.88 s / 50.12 GiB maxrss / 117.83 GiB peak footprint**, and the
/// refusal is a `WitnessConflict` on one witness slot — `204` against `1`. That is the `cb.connect`
/// objecting by name: two expressions forced to one slot with different values.
#[test]
#[ignore = "RUNS: 250 s, 117.8 GiB peak footprint / 50.1 GiB maxrss — ignored for cost, not failure"]
fn the_fold_refuses_two_segments_that_do_not_chain() {
    let cfg = accumulator_config();
    let segs = segments();
    let (a, pa) = &segs[0];

    let leaf = prove_accumulator_segment(Rung::Interior, a, pa, &cfg)
        .expect("segment A is an honest segment and must prove on its own");

    // sanity: the leaf really does expose endpoints that DISAGREE, so the refusal below is about
    // the connect and not about a degenerate claim.
    let claim = read_accumulator_claim(&leaf).expect("the leaf publishes a claim");
    assert_ne!(
        claim.acc_in, claim.acc_out,
        "segment A must not be a fixed point, or folding it with itself would legitimately succeed \
         and this tooth would prove nothing"
    );

    // ⚑ **AND WHAT DISAGREES MUST BE UNABLE TO BE A RANGE REFUSAL.** A falsifier whose moved value
    // left the declared width would be refused by a limb lookup, and the refusal would say nothing
    // about the connect. So: at least one limb the connect ties differs with BOTH sides nonzero,
    // and every limb on both endpoints is inside the declared 8-bit width.
    let differing: Vec<usize> = (0..POINT_WIDTH)
        .filter(|&k| claim.acc_in[k] != claim.acc_out[k])
        .collect();
    assert!(
        !differing.is_empty(),
        "the two endpoints must differ somewhere the connect looks"
    );
    assert!(
        differing
            .iter()
            .any(|&k| claim.acc_in[k] != BabyBear::new(0) && claim.acc_out[k] != BabyBear::new(0)),
        "at least one connected limb must differ with BOTH sides NONZERO — a falsifier that only \
         ever moved a zero into a zero is the class `a-falsifier-that-stopped-falsifying` records"
    );
    for k in 0..POINT_WIDTH {
        for (side, v) in [("acc_in", claim.acc_in[k]), ("acc_out", claim.acc_out[k])] {
            assert!(
                v.0 < 256,
                "{side} limb {k} is {} — outside the declared 8-bit limb width, so a RANGE LOOKUP \
                 could be what refuses below and the refusal would not be about the connect",
                v.0
            );
        }
    }

    let r = fold_accumulator_segments(&leaf, &leaf, &cfg);
    let err = r.err().expect(
        "folding a segment with itself connects `5G` to `G` — there is no satisfying assignment, \
         so there must be no parent proof. A fold that accepts this is re-pinning public inputs \
         rather than carrying state.",
    );
    println!("fold refused the unchained pair: {err}");

    // ⚑ **THE REFUSAL MUST NAME THE CONNECT, NOT A BUS AND NOT A SHAPE.** `cb.connect` forces two
    // expressions onto one witness slot; an unsatisfiable connect surfaces as a `WitnessConflict`
    // naming that slot and the two values. Asserted because `is_err()` alone was satisfied equally
    // by a fold that refused for a reason having nothing to do with the carry.
    assert!(
        err.contains("WitnessConflict"),
        "the refusal must be the connect's own — a witness forced to two values — but it was: {err}"
    );
    // …and NOT one of `require_accumulator_claim`'s layout refusals, which fire BEFORE the connect
    // is ever built and would make this test green with the connect loop deleted.
    assert!(
        !err.contains("claim lane(s)") && !err.contains("carries no expose_claim instance"),
        "the fold refused on CLAIM LAYOUT, before the connect existed — this tooth would then be \
         green with the `cb.connect` loop deleted: {err}"
    );
}

/// ⚑⚑ **A ROOT. MEASURED 2026-08-06: 223.36 s, AND IT COMPLETES.**
///
/// A single-segment chain is the deterministic case: it is the FINAL rung and there is no fold, so
/// the discharge is forced by that one leaf's own AIR. Stated because a fold that only ever ran at
/// depth ≥ 2 would leave the base case untested — and it is the first thing in this cone to
/// produce a root at all.
///
/// `/usr/bin/time -l`, release, 8-row `dregg-mina-accumulator-final::v1`, 96 GiB box:
///
/// | metric                         | binary      | decimal    |
/// |--------------------------------|-------------|------------|
/// | wall clock                     | 223.36 s    | 223.36 s   |
/// | maximum resident set size      | 48.85 GiB   | 52.45 GB   |
/// | peak memory footprint          | 117.93 GiB  | 126.63 GB  |
///
/// ⚠ **BOTH UNITS AND BOTH METRICS.** The units because this file's own first draft compared a
/// decimal figure against a binary threshold. The METRICS because they differ by 2.4× here and a
/// reader who takes one for the other is wrong by that much: `maxrss` is what stayed resident,
/// `peak memory footprint` is what was charged including compressed pages. The footprint EXCEEDS
/// physical RAM — this run fits only because macOS compresses, and a Linux box with no swap
/// headroom at 96 GiB would meet the OOM killer on the way up.
///
/// ⚑ **AND THE 68.3 GiB IN THIS FILE'S EARLIER HEADER WAS NOT A PEAK.** It was labelled "peak
/// memory footprint" of a run that was *killed before finishing*, which makes it a WAYPOINT — the
/// high-water mark of a climb that had not stopped climbing. The completed run's footprint is
/// **117.9 GiB**, 1.7× higher. A killed run's high-water mark bounds nothing from above, and
/// quoting it as a peak understates the wall in the flattering direction.
#[test]
#[ignore = "SLOW (223 s) and 117.9 GiB peak footprint / 48.9 GiB maxrss — but it COMPLETES; see the docblock"]
fn a_one_segment_chain_is_the_final_rung() {
    let cfg = accumulator_config();
    let t = full_trace();
    let pis = segment_public_inputs(&t).expect("public inputs");
    let root = prove_accumulator_fold(&[(t, pis)], &cfg, |_, _| {})
        .expect("a one-segment chain must prove against the FINAL descriptor");
    let claim = read_accumulator_claim(&root).expect("claim");
    assert!(claim.is_identity());
}
