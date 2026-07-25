//! **THE BUDGET CENSUS**, measured on the LEAN-EMITTED object. Leaf width, degree, PIs and
//! Poseidon2 sites at each shape, against the deployed caps (`MAX_TRACE_WIDTH = 1024`,
//! `MAX_CONSTRAINT_DEGREE = 8`, `MAX_PUBLIC_INPUTS = 64`) — the automatafl lesson taken up front
//! rather than discovered.
//!
//! **Say the substrate out loud:** nothing here authors or lowers a constraint. Every number is
//! read off `paramComposeDesc` as byte-pinned by
//! `metatheory/Dregg2/Circuit/Emit/{ParamComposeEmit,ParamComposeGolden,ParamComposeGoldenShapes,
//! ParamComposeGoldenCensus}.lean` and decoded by the production IR-v2 decoder.
//!
//! # ONE width, not two — and where the missing measurement went
//!
//! The pre-migration census reported TWO widths: `prog` (a Rust-authored `CircuitDescriptor`'s
//! own columns) and `leaf` (`prog` + the `lane` columns `cellprogram_to_descriptor2` allocates
//! per single-output Poseidon2 site). The `lane == 0` assertion was the gate that no
//! single-output hash site had crept back in and re-inflated the folded leaf.
//!
//! **That measurement does not exist on this route, and is not faked here.** The Lean family
//! emits IR-v2 DIRECTLY: there is no `CellProgram`, no custom-leaf lowering step, and hence no
//! lane-column term — `leaf == trace_width` by construction, and the fold proves exactly this
//! object. The CONTENT the `lane == 0` assertion carried (every digest site is a WIDE 25-tuple
//! `node8` whose 8 outputs are program-owned, so no site can allocate lanes) is a Lean `#guard`
//! at the emitter, `ParamComposeEmit.lean` §14:
//!
//! ```text
//!   #guard ((paramComposeDesc pcMin).constraints.filterMap
//!             (fun c => match c with | .lookup l => some l.tuple.length | _ => none)).all
//!           (· == 1 + CHIP_RATE + CHIP_OUT_LANES)
//! ```
//!
//! It fires at `lake build`, over the emitted object, before any Rust sees it. That is where the
//! tooth lives now; no Rust stand-in is invented for it.
//!
//! Run:
//!   cargo test -p dregg-param-compose --test size -- --nocapture

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_param_compose::field::fb;
use dregg_param_compose::lean_descriptor::lean_descriptor_for;
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::{
    ComposeShape, MAX_CONSTRAINT_DEGREE, MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH,
};
use dregg_param_compose::witness::{compose_trace_accepts, compose_witness};

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

/// Total degree of an emitted expression. A pure MEASUREMENT of the decoded object — it decides
/// nothing and constrains nothing; `Const` is 0, `Var` is 1, `Add` takes the max and `Mul` adds.
fn expr_degree(e: &LeanExpr) -> usize {
    match e {
        LeanExpr::Const(_) => 0,
        LeanExpr::Var(_) => 1,
        LeanExpr::Add(a, b) => expr_degree(a).max(expr_degree(b)),
        LeanExpr::Mul(a, b) => expr_degree(a) + expr_degree(b),
    }
}

/// The largest constraint degree the emitted descriptor carries.
fn emitted_max_degree(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .map(|c| match c {
            VmConstraint2::Base(VmConstraint::Gate(e)) => expr_degree(e),
            VmConstraint2::Base(VmConstraint::Boundary { body, .. }) => expr_degree(body),
            VmConstraint2::Base(_) => 1,
            VmConstraint2::Lookup(l) => l.tuple.iter().map(expr_degree).max().unwrap_or(0),
            _ => 1,
        })
        .max()
        .unwrap_or(0)
}

/// Wide `node8` chip lookups the emitted descriptor carries — the Poseidon2 site count.
fn emitted_site_count(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
        .count()
}

/// A measured census row, read off the EMITTED object.
struct Row {
    /// The IR-v2 leaf width the fold actually proves (there is no lowering step, so this IS the
    /// leaf).
    leaf: usize,
    deg: usize,
    pis: usize,
    sites: usize,
}

fn report(tag: &str, shape: &ComposeShape) -> Row {
    let desc = lean_descriptor_for(shape)
        .unwrap_or_else(|| panic!("{tag}: Lean must carry a byte-pinned instance at {shape:?}"));

    // The saturating composition must actually fill this shape's layout and satisfy the emitted
    // object — a census over a descriptor nothing can witness would be measuring a ghost.
    let comp = saturating(shape);
    let w = compose_witness(shape, &comp, &old8(), &new8()).unwrap_or_else(|e| {
        panic!("{tag}: the saturating composition must produce a witness: {e}")
    });
    assert!(
        compose_trace_accepts(&desc, &w),
        "{tag}: the honest saturating witness must satisfy the EMITTED descriptor"
    );

    let leaf = desc.trace_width;
    let deg = emitted_max_degree(&desc);
    let sites = emitted_site_count(&desc);
    let fits = if leaf <= MAX_TRACE_WIDTH {
        "FITS"
    } else {
        "EXCEEDS -> SEGMENT"
    };
    eprintln!(
        "{tag:<26} leaf={:<5} deg={:<2} pis={:<3} app_pis={:<3} sites={:<4} constraints={:<6} \
         [{fits}]  {}",
        leaf,
        deg,
        desc.public_input_count,
        desc.public_input_count - pi::APP_BASE,
        sites,
        desc.constraints.len(),
        desc.name,
    );
    assert!(
        deg <= MAX_CONSTRAINT_DEGREE,
        "{tag}: emitted degree {deg} exceeds the deployed cap {MAX_CONSTRAINT_DEGREE}"
    );
    assert!(
        desc.public_input_count <= MAX_PUBLIC_INPUTS,
        "{tag}: {} PIs exceed the deployed cap {MAX_PUBLIC_INPUTS}",
        desc.public_input_count
    );
    assert_eq!(
        sites,
        shape.hash_sites(),
        "{tag}: the shape's published fuel bound must be the emitted site count"
    );
    Row {
        leaf,
        deg,
        pis: desc.public_input_count,
        sites,
    }
}

/// **THE HEADLINE MEASUREMENT + GATE.** The realistic HOARDLIGHT-scale composition the task
/// names: ~8 params x ~4 subjects + ~6 knots, at the DEFAULT 28-bit identity namespace — Lean's
/// `pcRealistic`, the shape `entity-compose` deploys.
///
/// This does not merely print a verdict — it ASSERTS the leaf the fold proves fits the deployed
/// cap, and that the saturated witness satisfies it.
#[test]
fn realistic_shape_fits_as_one_leaf() {
    eprintln!("\n=== REALISTIC SHAPE: ~8 params x ~4 subjects + ~6 knots (default 28-bit ids) ===");
    let realistic = ComposeShape::new(4, 8, 8, 6);
    let r = report("realistic (id=28)", &realistic);

    assert!(
        r.leaf <= MAX_TRACE_WIDTH,
        "the realistic shape must fold as ONE leaf at the DEFAULT identity namespace: leaf \
         {} > cap {MAX_TRACE_WIDTH}",
        r.leaf
    );
    eprintln!(
        "  VERDICT: realistic shape folds a {}-column leaf — {} under the {MAX_TRACE_WIDTH} cap, \
         at the DEFAULT 28-bit namespace. ONE leaf, no segmentation, no identity narrowing.",
        r.leaf,
        MAX_TRACE_WIDTH - r.leaf
    );
    eprintln!(
        "  PI budget: {}/{MAX_PUBLIC_INPUTS} total, {}/48 app — CONSTANT in the subject count.",
        r.pis,
        r.pis - pi::APP_BASE
    );
    let _ = (r.deg, r.sites);
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
///
/// It is refused at BOTH poles, and the shape is deliberately NOT byte-pinned in Lean: pinning
/// it would pin an object that must not exist.
#[test]
fn an_identity_width_that_would_go_vacuous_is_refused() {
    let sh = ComposeShape::new(4, 8, 8, 6).with_identity_bits(31);
    assert!(!sh.identity_bits_sound());
    assert!(
        lean_descriptor_for(&sh).is_none(),
        "an unsound identity width must have NO emitted descriptor — blocked, not faked"
    );
    let comp = saturating(&ComposeShape::new(4, 8, 8, 6));
    assert!(
        compose_witness(&sh, &comp, &old8(), &new8()).is_err(),
        "a shape whose ordering comparison would be VACUOUS must be refused, never witnessed"
    );
}

/// The census across shapes: where the 1024-column LEAF wall actually is. The shapes
/// documented to fit are ASSERTED (a real gate); the larger shapes that still segment are
/// asserted to still EXCEED, so "it segments" cannot silently become false.
#[test]
fn staged_leaf_width_census() {
    eprintln!("\n=== SHAPE CENSUS (leaf = the emitted IR-v2 trace width; no lowering step) ===");

    // Documented-to-fit shapes: ASSERT the leaf fits (these gates can go red).
    for (tag, sh) in [
        ("n2 p2 l1 k1", ComposeShape::new(2, 2, 1, 1)),
        ("n3 p4 l3 k2 (leaf test)", ComposeShape::new(3, 4, 3, 2)),
        ("n4 p8 l8 k6 (realistic)", ComposeShape::new(4, 8, 8, 6)),
    ] {
        let r = report(tag, &sh);
        assert!(
            r.leaf <= MAX_TRACE_WIDTH,
            "{tag}: documented to FIT, but leaf {} > {MAX_TRACE_WIDTH}",
            r.leaf
        );
    }

    // Larger shapes: these EXCEED the single-leaf cap and segment. Lean pins them precisely so
    // the segmentation boundary is a MEASURED number rather than an estimate.
    for (tag, sh) in [
        ("n6 p8 l12 k10", ComposeShape::new(6, 8, 12, 10)),
        ("n8 p16 l16 k16", ComposeShape::new(8, 16, 16, 16)),
    ] {
        let r = report(tag, &sh);
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
    // ...and the EMITTED object agrees at every pinned shape it is checked against.
    for n in [2usize, 4, 6, 8] {
        let sh = match n {
            2 => ComposeShape::new(2, 4, 1, 1),
            4 => ComposeShape::new(4, 8, 8, 6),
            6 => ComposeShape::new(6, 8, 12, 10),
            _ => ComposeShape::new(8, 16, 16, 16),
        };
        assert_eq!(
            lean_descriptor_for(&sh).expect("pinned").public_input_count,
            counts[0],
            "the emitted PI count must be constant across shapes ({sh:?})"
        );
    }
}
