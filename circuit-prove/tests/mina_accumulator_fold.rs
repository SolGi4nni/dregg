//! ⚑⚑ **THE ACCUMULATOR CHAIN'S FOLD — WRITTEN, AND BLOCKED BY A MEASURED WIDTH WALL.**
//!
//! ⛑ Read the "THE THREE PROVING TESTS DO NOT RUN" section below before citing this file for
//! anything. The fold is built and its non-proving teeth pass; **it has never produced a root.**
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
//! ## ⛑⛑ THE THREE PROVING TESTS DO NOT RUN, AND "SLOW" IS THE FLATTERING HALF
//!
//! Measured 2026-08-06, `/usr/bin/time -l` on the release binary: ONE recursion leaf wrap of ONE
//! 8-row segment reached a **peak memory footprint of 68.3 GiB** — `73,344,091,528` bytes, **71% of
//! a 96 GiB box** — and was killed before finishing; an earlier run under normal co-tenant load was
//! SIGKILLed by the OOM killer. So these three are `#[ignore]`d for a **measured memory wall**, not
//! for being slow, and calling them slow would be the flattering member of a pair.
//!
//! ⚠ That figure is `73.3 GB` in DECIMAL units and both are written down, because the first draft of
//! `the_leaf_wrap_width_is_the_measured_wall` compared the decimal number against a binary threshold
//! and went red. Quoting one member of a unit pair is the same shape of error as quoting the
//! flattering member of a bound pair.
//!
//! ⚑ **AND THE CAUSE IS THE WIDTH, WHICH IS THE SAME WALL ONE RAIL UP.**
//! `PastaLadderThread` cured the ROW-LOCAL wall — a sound ladder was `731,136` columns in one row —
//! by making depth into rows at a flat `RCB_WIDTH = 3,048`. The recursion wrap now hits that 3,048:
//! `mina_phase2_chain_leaf` folds **46 leaves + 45 folds in 1,037 s** over a **469**-column
//! descriptor, and this one is **6.5×** wider, with the in-circuit verifier's cost scaling in the
//! inner trace's width. `the_leaf_wrap_width_is_the_measured_wall` keeps that ratio in the tree so
//! it moves when the width does.
//!
//! ⚠ **So the accumulator chain is NOT folded end to end today.** The fold is written, its layout
//! and rung teeth pass, and the mechanism it uses is the one `mina_phase2_chain_leaf` already runs
//! in production — but nothing here has produced a root, and no sentence in this repo should say it
//! has. What IS demonstrated is the single-instance AIR: `circuit/tests/mina_accumulator_air_proves.rs`,
//! 9/9 in release, both polarities, refusing gates named by index.
//!
//! Run the two that do work with:
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_accumulator_fold -- --nocapture
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

/// ⛑⛑ **THE MEASURED WALL, KEPT IN THE TREE SO IT MOVES WHEN THE WIDTH DOES.**
///
/// The three proving tests above are `#[ignore]`d because ONE recursion leaf wrap of ONE 8-row
/// segment reached a **68.3 GiB peak memory footprint** — 71% of a 96 GiB box (2026-08-06,
/// `/usr/bin/time -l`). The cause is the descriptor's WIDTH, and this is that ratio as an assertion:
/// the phase-2 chain — which folds 46 leaves and 45 folds in 1,037 s in production — runs over a
/// **469**-column descriptor, and the accumulator segment is **3,048**.
///
/// ⚑ This is the SAME wall `PastaLadderThread` cured one rail down, arriving one rail up. The
/// row-local sound ladder was `731,136` columns in a single row; threading made the depth into rows
/// at a flat `RCB_WIDTH = 3,048`. The recursion wrap builds an in-circuit verifier whose cost scales
/// in the inner trace's width, so 3,048 is now the number that binds.
///
/// The ways out are all real work and none is a tuning knob: a NARROWER sound encoding (the 8-bit
/// limb choice is what makes a Pasta coordinate 32 columns), a two-stage wrap that shrinks the
/// segment before the recursion sees it, or a segment whose trace is taller and no wider so the
/// fixed per-wrap cost amortises. Naming them is not doing them.
///
/// If this assertion ever goes red because `RCB_WIDTH` moved, re-measure the wrap before assuming
/// the wall moved with it.
#[test]
fn the_leaf_wrap_width_is_the_measured_wall() {
    /// `MinaPhase2Chain`'s chain-link descriptor width, the one that DOES fold in production.
    const PHASE2_WIDTH: usize = 469;
    /// The measured peak of one accumulator leaf wrap, in bytes.
    const MEASURED_LEAF_PEAK_BYTES: u64 = 73_344_091_528;

    let a = accumulator_descriptor(Rung::Interior).expect("segment descriptor");
    assert_eq!(a.trace_width, 3048);
    assert!(
        a.trace_width > 6 * PHASE2_WIDTH,
        "the accumulator segment is {} columns against the phase-2 chain's {PHASE2_WIDTH}; if that \
         ratio ever drops below 6x, the wrap is worth re-measuring",
        a.trace_width
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

/// ⚑ **POLARITY 1 — THE CHAIN FOLDS, AND THE ROOT'S CLAIM IS THE WHOLE CHAIN'S.**
///
/// Two leaves and one fold. The root exposes `A.acc_in ‖ B.acc_out` — the point the chain started
/// from and the point it ended on — and B was proved against the descriptor whose 64
/// `when_last_row` gates FORCE that terminal point to be the identity, so the discharge is in the
/// AIR rather than in a host read.
#[test]
#[ignore = "MEASURED WALL, not slowness: one leaf wrap peaked at 68.3 GiB (see the header)"]
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
#[test]
#[ignore = "MEASURED WALL, not slowness: one leaf wrap peaked at 68.3 GiB (see the header)"]
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

    let r = fold_accumulator_segments(&leaf, &leaf, &cfg);
    assert!(
        r.is_err(),
        "folding a segment with itself connects `5G` to `G` — there is no satisfying assignment, \
         so there must be no parent proof. A fold that accepts this is re-pinning public inputs \
         rather than carrying state."
    );
    println!("fold refused the unchained pair: {:?}", r.err());
}

/// A single-segment chain is the deterministic case: it is the FINAL rung and there is no fold, so
/// the discharge is forced by that one leaf's own AIR. Stated because a fold that only ever ran at
/// depth ≥ 2 would leave the base case untested.
#[test]
#[ignore = "MEASURED WALL, not slowness: this exact test peaked at 68.3 GiB (see the header)"]
fn a_one_segment_chain_is_the_final_rung() {
    let cfg = accumulator_config();
    let t = full_trace();
    let pis = segment_public_inputs(&t).expect("public inputs");
    let root = prove_accumulator_fold(&[(t, pis)], &cfg, |_, _| {})
        .expect("a one-segment chain must prove against the FINAL descriptor");
    let claim = read_accumulator_claim(&root).expect("claim");
    assert!(claim.is_identity());
}
