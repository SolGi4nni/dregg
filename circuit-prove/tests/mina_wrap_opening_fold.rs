//! # The IPA opening leaf, folded into the recursion tower — `recursion_layer_over` at the wrap,
//! never a named config.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-mina-wrap-opening-sched::v1` is `EffectLower.lowerTiedAir`
//! of `Dregg2.Circuit.Emit.MinaWrapOpeningSched.openingSchedAir`, and the trace is rendered by
//! `metatheory/MinaWrapOpeningSchedEmit.lean`. Nothing here authors a constraint.
//!
//! ## What is folded
//!
//! ONE leaf — the whole 35-addend opening chain fits a single 2^11-row instance — wrapped at the
//! engine derived from its child's mint knobs (`recursion_layer_over(config)`). The wrap exposes
//! the leaf's own FRI-bound 256 PI lanes (`acc_in ‖ acc_out ‖ sg.x ‖ sg.y`) as its claim, so a
//! consumer above reads a REAL `G` — block 539508's own `opening.sg` — off the recursion
//! boundary, not off a host label. The first 192 lanes are the accumulator adapter unchanged, so
//! a future multi-segment split folds with `mina_wrap_closing_fold`'s own `cb.connect` shape.
//!
//! ⚠ `#[ignore]`d: a leaf wrap is minutes and tens of GiB; the default profile is the fast
//! gauntlet.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test mina_wrap_opening_fold -- --ignored --nocapture`

use std::path::PathBuf;

use dregg_circuit::field::BabyBear;
use p3_field::PrimeField32;

use dregg_circuit_prove::mina_wrap_opening_fold::{
    OPENING_PI_COUNT, OPENING_WIDTH, opening_descriptor, opening_inner_config, prove_opening_leaf,
};

const ROWS: usize = 2048;
const SK: usize = 32;

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../circuit/tests/fixtures")
}

fn read_fixture(name: &str) -> String {
    let path = fixture_dir().join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "fixture {} missing ({e}).\nEmit the opening-sched artifacts first (COMPILED):\n  \
             cd metatheory && lake build mina_wrap_opening_sched_emit \\\n    \
             && ./.lake/build/bin/mina_wrap_opening_sched_emit ../circuit/tests/fixtures",
            path.display()
        )
    })
}

fn full_trace() -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = read_fixture("mina-wrap-opening-sched-trace.txt")
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let row: Vec<BabyBear> = l
                .split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("decimal cell")))
                .collect();
            assert_eq!(row.len(), OPENING_WIDTH);
            row
        })
        .collect();
    assert_eq!(t.len(), ROWS);
    t
}

fn public_inputs() -> Vec<BabyBear> {
    let p: Vec<BabyBear> = read_fixture("mina-wrap-opening-sched-pis.txt")
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI limb")))
        .collect();
    assert_eq!(p.len(), OPENING_PI_COUNT);
    p
}

/// The descriptor resolves to this rung, and the fixture's claim has the right endpoint shape,
/// BEFORE any expensive proving is attempted.
#[test]
fn the_descriptor_and_claim_have_the_opening_shape() {
    let json = read_fixture("mina-wrap-opening-sched.json");
    let d = opening_descriptor(&json).expect("the opening descriptor resolves");
    assert_eq!(d.trace_width, OPENING_WIDTH);
    let p = public_inputs();
    // acc_in = (0 : 1 : 0), acc_out = (0 : y : 0) with y nonzero — the identity, as the
    // discharge forces it (X and Z, never Y).
    assert!((0..SK).all(|i| p[i] == BabyBear::new(0)));
    assert_eq!(p[SK].as_u32(), 1);
    for i in 0..SK {
        assert_eq!(p[3 * SK + i], BabyBear::new(0), "acc_out.X limb {i}");
        assert_eq!(p[5 * SK + i], BabyBear::new(0), "acc_out.Z limb {i}");
    }
    assert!(
        (0..SK).any(|i| p[4 * SK + i] != BabyBear::new(0)),
        "the identity is (0 : y : 0) with y NONZERO"
    );
}

/// ⚑⚑ The opening leaf proves and wraps at the DERIVED engine, and the wrap's exposed claim is
/// the leaf's own 256 PI lanes — a real `G` on the recursion boundary.
#[test]
#[ignore = "a 581-column leaf wrap is minutes and GiBs"]
fn the_opening_leaf_folds_into_the_tower() {
    let json = read_fixture("mina-wrap-opening-sched.json");
    let t = full_trace();
    let p = public_inputs();

    let started = std::time::Instant::now();
    let root = prove_opening_leaf(&json, &t, &p, &opening_inner_config())
        .expect("the opening leaf proves and wraps");
    println!(
        "opening leaf + wrap in {:.1}s",
        started.elapsed().as_secs_f64()
    );

    let claim = root
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .expect("the wrap exposes a claim");
    assert_eq!(
        claim.public_values.len(),
        OPENING_PI_COUNT,
        "the wrap republishes `acc_in ‖ acc_out ‖ sg.x ‖ sg.y`"
    );
    // The exposed lanes ARE the leaf's PI vector — the claim is FRI-bound, not a host label.
    for (k, v) in claim.public_values.iter().enumerate() {
        assert_eq!(
            v.as_canonical_u32(),
            p[k].as_u32(),
            "claim lane {k} must be the leaf's own PI"
        );
    }
    println!(
        "claim lanes {} — sg on the boundary.",
        claim.public_values.len()
    );
}
