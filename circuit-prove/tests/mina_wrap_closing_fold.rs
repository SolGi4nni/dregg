//! # The IPA closing chain, folded — `recursion_layer_over` at every rung, `cb.connect` for the
//! carry.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-wrap-closing-{seg,final}::v1` are
//! `EffectLower.lowerAir` of `Dregg2.Circuit.Emit.MinaWrapClosingAir.{closingSegAir,
//! closingFinalAir}`, and the trace is `PastaCurveSound.rcbSoundRow` rendered by
//! `metatheory/EmitMinaWrapClosing.lean`. Nothing here authors a constraint.
//!
//! ## What is folded, and why the split matters
//!
//! The eight-row closing chain is cut into two four-row segments. The FIRST is
//! `dregg-mina-wrap-closing-seg::v1` — it publishes its endpoints and says nothing about
//! vanishing, which is what an interior segment must do. The SECOND is
//! `dregg-mina-wrap-closing-final::v1`, whose own AIR forces the terminal accumulator to be the
//! point at infinity. So the discharge is a consequence of the LAST leaf's constraints and the
//! chain's continuity is a consequence of the fold's `cb.connect`, not of a host assertion.
//!
//! ⚑ **THE ENGINE IS DERIVED.** `prove_closing_segment` takes the child's engine and derives its
//! own wrap engine with `recursion_layer_over`; `prove_closing_fold` applies it twice. No config
//! constant is named here. At the accumulator's identically-shaped leaf that rule measured
//! `298.08 s / 117.79 GiB / LDE 2^26` → `21.63 s / 23.23 GiB / LDE 2^23`.
//!
//! ⚠ `#[ignore]`d: a 3 049-column leaf wrap is minutes and tens of GiB, and the default profile is
//! the fast gauntlet.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test mina_wrap_closing_fold -- --ignored --nocapture`

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::mina_wrap_closing_fold::{
    CLOSING_WIDTH, ClosingRung, closing_descriptor, closing_inner_config, prove_closing_fold,
};

const SEG_JSON: &str = include_str!("../../circuit/tests/fixtures/mina-wrap-closing-seg.json");
const FINAL_JSON: &str = include_str!("../../circuit/tests/fixtures/mina-wrap-closing-final.json");
const BOUND_TRACE: &str =
    include_str!("../../circuit/tests/fixtures/mina-wrap-closing-bound-trace.txt");

const SK: usize = 32;
const ACC: [usize; 3] = [0, SK, 2 * SK];
const OUT: [usize; 3] = [1024, 1120, 1216];
const ROWS: usize = 8;

fn full_trace() -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = BOUND_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let row: Vec<BabyBear> = l
                .split_whitespace()
                .map(|c| {
                    BabyBear::new(
                        u32::try_from(c.parse::<u64>().expect("decimal cell"))
                            .expect("cell inside BabyBear"),
                    )
                })
                .collect();
            assert_eq!(row.len(), CLOSING_WIDTH);
            row
        })
        .collect();
    assert_eq!(t.len(), ROWS);
    t
}

/// Public inputs are READ OFF the segment's own pinned columns: its first row's `ACC` blocks and
/// its last row's `OUT` blocks. Never authored, so a PI the host invented cannot be what makes a
/// fold close.
fn segment_public_inputs(seg: &[Vec<BabyBear>]) -> Vec<BabyBear> {
    let last = seg.len() - 1;
    let mut pis = Vec::with_capacity(192);
    for base in ACC {
        for i in 0..SK {
            pis.push(seg[0][base + i]);
        }
    }
    for base in OUT {
        for i in 0..SK {
            pis.push(seg[last][base + i]);
        }
    }
    pis
}

/// ⚑ The two segments really do chain: the first's outgoing accumulator IS the second's incoming
/// one, limb for limb, in the FIXTURE. If they did not, `cb.connect` would refuse and the fold's
/// green would be about the wrong thing.
#[test]
fn the_two_segments_chain_in_the_fixture() {
    let t = full_trace();
    let (l, r) = (&t[..4], &t[4..]);
    let (lp, rp) = (segment_public_inputs(l), segment_public_inputs(r));
    assert_eq!(lp[96..], rp[..96], "left's acc_out IS right's acc_in");

    // …and the descriptors resolve to the rungs this file names.
    assert!(closing_descriptor(ClosingRung::Interior, SEG_JSON).is_ok());
    assert!(closing_descriptor(ClosingRung::Final, FINAL_JSON).is_ok());
}

/// ⚑⚑ The chain folds and the root carries both endpoints: the FIRST segment's incoming
/// accumulator (`c·Q`) and the LAST segment's outgoing one (the point at infinity, forced by the
/// final leaf's own discharge gates).
#[test]
#[ignore = "a 3 049-column leaf wrap is minutes and tens of GiB"]
fn the_closing_chain_folds() {
    let t = full_trace();
    let left: Vec<Vec<BabyBear>> = t[..4].to_vec();
    let right: Vec<Vec<BabyBear>> = t[4..].to_vec();
    let lp = segment_public_inputs(&left);
    let rp = segment_public_inputs(&right);

    let segments = vec![
        (ClosingRung::Interior, SEG_JSON, left, lp.clone()),
        (ClosingRung::Final, FINAL_JSON, right, rp.clone()),
    ];

    let started = std::time::Instant::now();
    let root = prove_closing_fold(&segments, &closing_inner_config(), |i, what| {
        println!(
            "[{:>6.1}s] segment {i}: {what}",
            started.elapsed().as_secs_f64()
        );
    })
    .expect("the closing chain folds");

    let lanes = root
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map_or(0, |e| e.public_values.len());
    println!(
        "closing fold root in {:.1}s; claim lanes {lanes}",
        started.elapsed().as_secs_f64()
    );
    assert_eq!(lanes, 192, "the root republishes `acc_in ‖ acc_out`");

    // The terminal accumulator the last leaf was forced to vanish really is all zero.
    assert!(
        rp[96..].iter().all(|v| *v == BabyBear::new(0)),
        "the chain's terminal accumulator is the canonical point at infinity"
    );
}
