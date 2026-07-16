//! **THE BUDGET CENSUS.** Program width, LOWERED-LEAF width, degree, PIs, and Poseidon2
//! sites at each shape, measured against the deployed caps (`MAX_TRACE_WIDTH = 1024`,
//! `MAX_CONSTRAINT_DEGREE = 8`, `MAX_PUBLIC_INPUTS = 64`) — the automatafl lesson taken up
//! front rather than discovered.
//!
//! # Two widths, and why BOTH are measured
//!
//! `prog` is the AIR's own column count (`descriptor.trace_width`). `leaf` is the width the
//! FOLDED leaf actually carries: the custom-leaf lowering (`cellprogram_to_descriptor2`)
//! allocates extra `lane` columns per single-output Poseidon2 site (7 per `Hash4to1` /
//! `Hash2to1` / `Hash3Cap`), so the leaf a prover mints is `prog + lane`. A census that
//! reports only `prog` UNDER-COUNTS the leaf — which is exactly the trap this AIR used to
//! sit in (the 8-chain digest paid 368 hash sites × 7 = 2576 lane columns the earlier
//! report never counted, so a "999-column" realistic shape folded a 3575-column leaf).
//!
//! The digest is now `MerkleHash8` (`node8`), whose 8 outputs are PROGRAM-OWNED, so it
//! allocates ZERO lane columns and `leaf == prog`. This test measures both and ASSERTS the
//! shapes it claims fit actually fit at the LEAF width — a gate that can go red, not a print.
//!
//! Run:
//!   cargo test -p dregg-param-compose --test size -- --nocapture

use dregg_circuit::custom_leaf_lowering::cellprogram_to_descriptor2;
use dregg_circuit::field::BabyBear;
use dregg_param_compose::air::build;
use dregg_param_compose::field::fb;
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::{
    ComposeShape, MAX_CONSTRAINT_DEGREE, MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH,
};

fn old8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(1000 + i as i128))
}
fn new8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(2000 + i as i128))
}

/// A DENSE composition that saturates every one of the shape's bounds — so the census
/// measures the worst case a VK of this shape must carry, not a lucky sparse one.
fn saturating(shape: &ComposeShape) -> Composition {
    let roles: Vec<u64> = (0..shape.max_subjects).map(|i| 100 + i as u64).collect();
    let subjects = (0..shape.max_subjects)
        .map(|i| Subject {
            identity: 10 + 7 * i as u64,
            role: roles[i],
            params: (0..shape.max_params).map(|p| (i + p + 1) as i64).collect(),
        })
        .collect();
    let linear = (0..shape.max_linear)
        .map(|t| LinearTerm {
            role: roles[t % shape.max_subjects],
            param: t % shape.max_params,
            coeff: (t as i64 + 1) * 3,
        })
        .collect();
    let knots = (0..shape.max_knots)
        .map(|k| Knot {
            role_a: roles[k % shape.max_subjects],
            param_a: k % shape.max_params,
            role_b: roles[(k + 1) % shape.max_subjects],
            param_b: (k + 1) % shape.max_params,
            coeff: -(k as i64 + 1),
        })
        .collect();
    Composition {
        subjects,
        ruleset: Ruleset {
            id: 42,
            version: 1,
            linear,
            knots,
        },
        param_count: shape.max_params,
    }
}

/// A measured census row: `(program_width, lane_columns, leaf_width, degree, pis)`.
struct Row {
    prog: usize,
    lane: usize,
    leaf: usize,
    deg: usize,
    pis: usize,
}

fn report(tag: &str, shape: &ComposeShape) -> Row {
    let comp = saturating(shape);
    let air = build(shape, &comp, &old8(), &new8()).expect("saturating composition builds");
    assert!(
        air.builder.air_accepts(),
        "{tag}: the honest saturating witness must self-accept"
    );
    let d = air.builder.descriptor();
    let prog = d.trace_width;

    // Lower to the IR-v2 leaf the FOLD actually proves — the lane columns the lowering
    // allocates past the base width are the leaf's real cost (zero for node8 sites).
    let program = air.builder.cellprogram();
    let lowered = cellprogram_to_descriptor2(&program).unwrap_or_else(|e| {
        panic!("{tag}: the composition AIR must lower to a foldable leaf: {e}")
    });
    let leaf = lowered.trace_width;
    let lane = leaf - prog;

    let fits = if leaf <= MAX_TRACE_WIDTH {
        "FITS"
    } else {
        "EXCEEDS -> SEGMENT"
    };
    eprintln!(
        "{tag:<26} prog={:<5} lane={:<5} leaf={:<5} deg={:<2} pis={:<3} app_pis={:<3} sites={:<4} \
         constraints={:<6} [{fits}]",
        prog,
        lane,
        leaf,
        d.max_degree,
        d.public_input_count,
        d.public_input_count - pi::APP_BASE,
        air.builder.hash_site_count(),
        d.constraints.len(),
    );
    assert!(
        d.max_degree <= MAX_CONSTRAINT_DEGREE,
        "{tag}: degree {} exceeds the deployed cap {MAX_CONSTRAINT_DEGREE}",
        d.max_degree
    );
    assert!(
        d.public_input_count <= MAX_PUBLIC_INPUTS,
        "{tag}: {} PIs exceed the deployed cap {MAX_PUBLIC_INPUTS}",
        d.public_input_count
    );
    Row {
        prog,
        lane,
        leaf,
        deg: d.max_degree,
        pis: d.public_input_count,
    }
}

/// **THE HEADLINE MEASUREMENT + GATE.** The realistic HOARDLIGHT-scale composition the task
/// names: ~8 params x ~4 subjects + ~6 knots, at the DEFAULT 28-bit identity namespace.
///
/// Unlike the old census this does not merely print a verdict — it ASSERTS the LEAF width
/// (program + lowering lane columns) fits the deployed cap. With the `node8` digest the
/// realistic shape fits at its default identity namespace, with headroom, so this is a real
/// gate: if a change reintroduced the lane-column cost (a single-output digest), it goes RED
/// here rather than silently printing EXCEEDS while 3.5x over the leaf budget.
#[test]
fn realistic_shape_fits_as_one_leaf() {
    eprintln!("\n=== REALISTIC SHAPE: ~8 params x ~4 subjects + ~6 knots (default 28-bit ids) ===");
    let realistic = ComposeShape::new(4, 8, 8, 6);
    let r = report("realistic (id=28)", &realistic);

    assert_eq!(
        r.lane, 0,
        "the digest is node8 (program-owned outputs), so the lowered leaf must allocate ZERO \
         lane columns; a nonzero count means a single-output hash site crept back in"
    );
    assert!(
        r.leaf <= MAX_TRACE_WIDTH,
        "the realistic shape must fold as ONE leaf at the DEFAULT identity namespace: leaf \
         {} > cap {MAX_TRACE_WIDTH}",
        r.leaf
    );
    eprintln!(
        "  VERDICT: realistic shape folds a {}-column leaf (0 lane columns) — {} under the \
         {MAX_TRACE_WIDTH} cap, at the DEFAULT 28-bit namespace. ONE leaf, no segmentation, no \
         identity narrowing.",
        r.leaf,
        MAX_TRACE_WIDTH - r.leaf
    );
    eprintln!(
        "  PI budget: {}/{MAX_PUBLIC_INPUTS} total, {}/48 app — CONSTANT in the subject count.",
        r.pis,
        r.pis - pi::APP_BASE
    );
    let _ = r.deg;
    let _ = r.prog;
}

/// **THE IDENTITY-WIDTH LEVER.** The ordering tooth's range gadgets are the AIR's single
/// biggest column cost: a `b`-bit identity namespace spends `b` range columns per subject
/// plus `b+1` per ordering comparison. With the digest no longer the dominant cost, this is
/// the lever that decides how far past the realistic shape a single leaf reaches.
#[test]
fn identity_width_sweep() {
    eprintln!("\n=== IDENTITY-WIDTH SWEEP (realistic shape) ===");
    let realistic = ComposeShape::new(4, 8, 8, 6);
    for bits in [12usize, 16, 20, 24, 28] {
        let sh = realistic.with_identity_bits(bits);
        let r = report(
            &format!(
                "identity_bits={bits} ({:>3}M ids)",
                (1u64 << bits) / 1_000_000
            ),
            &sh,
        );
        assert!(
            sh.identity_bits_sound(),
            "the ordering tooth must stay non-vacuous"
        );
        assert!(
            r.leaf <= MAX_TRACE_WIDTH,
            "the realistic shape must fit at every sound identity width: id={bits} leaf {} > {MAX_TRACE_WIDTH}",
            r.leaf
        );
    }
}

/// A shape whose identity width would make the ordering comparison VACUOUS is REFUSED,
/// not silently built. A 31-bit namespace lets both comparison bits satisfy the range
/// gadget, so the "canonical order + duplicate rejection" tooth would look present and
/// enforce nothing — exactly the failure this check exists to make impossible.
#[test]
fn an_identity_width_that_would_go_vacuous_is_refused() {
    let sh = ComposeShape::new(4, 8, 8, 6).with_identity_bits(31);
    assert!(!sh.identity_bits_sound());
    let comp = saturating(&ComposeShape::new(4, 8, 8, 6));
    assert!(
        build(&sh, &comp, &old8(), &new8()).is_err(),
        "a shape whose ordering comparison would be VACUOUS must be refused, never built"
    );
}

/// The census across shapes: where the 1024-column LEAF wall actually is. The shapes
/// documented to fit are ASSERTED (a real gate); the larger shapes that still segment are
/// printed as honest scope — node8 shrinks their leaf dramatically but does not make them
/// fit.
#[test]
fn staged_leaf_width_census() {
    eprintln!("\n=== SHAPE CENSUS (leaf = program + lowering lane columns) ===");

    // Documented-to-fit shapes: ASSERT the leaf fits (these gates can go red).
    for (tag, sh) in [
        ("n2 p2 l1 k1", ComposeShape::new(2, 2, 1, 1)),
        ("n3 p4 l3 k2 (leaf test)", ComposeShape::new(3, 4, 3, 2)),
        ("n4 p8 l8 k6 (realistic)", ComposeShape::new(4, 8, 8, 6)),
    ] {
        let r = report(tag, &sh);
        assert_eq!(r.lane, 0, "{tag}: node8 digest must cost zero lane columns");
        assert!(
            r.leaf <= MAX_TRACE_WIDTH,
            "{tag}: documented to FIT, but leaf {} > {MAX_TRACE_WIDTH}",
            r.leaf
        );
    }

    // Larger shapes: these EXCEED the single-leaf cap and segment. Measured (not asserted
    // to fit) — honest scope. node8 still costs zero lane columns.
    for (tag, sh) in [
        ("n6 p8 l12 k10", ComposeShape::new(6, 8, 12, 10)),
        ("n8 p16 l16 k16", ComposeShape::new(8, 16, 16, 16)),
    ] {
        let r = report(tag, &sh);
        assert_eq!(r.lane, 0, "{tag}: node8 digest must cost zero lane columns");
        assert!(
            r.leaf > MAX_TRACE_WIDTH,
            "{tag}: documented to SEGMENT — if it now fits, update the crate's budget scope \
             (leaf {})",
            r.leaf
        );
    }
}

/// The PI layout is CONSTANT in the number of subjects — the §9.3 property. Growing the
/// scene from 2 to 8 subjects must not move a single public input slot.
#[test]
fn the_pi_layout_does_not_encode_the_subject_count() {
    let counts: Vec<usize> = (2..=8)
        .map(|n| ComposeShape::new(n, 8, 8, 6).public_input_count())
        .collect();
    assert!(
        counts.windows(2).all(|w| w[0] == w[1]),
        "the PI count must not track the subject count (that is the cul-de-sac \
         HOARDLIGHT §9.3 names): {counts:?}"
    );
    assert_eq!(counts[0], 53, "layout: 16 door + 5 scalars + 4 roots x 8");
    assert!(counts[0] <= MAX_PUBLIC_INPUTS);
    assert_eq!(
        counts[0] - pi::APP_BASE,
        37,
        "37 app PIs, inside the door's 48-PI app budget"
    );
}
