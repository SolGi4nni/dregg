//! **THE LEAN-AUTHORED DESCRIPTOR, REACHED FROM RUST.**
//!
//! The parameter-composition AIR is authored in Lean
//! (`metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean`, a shape-parametric
//! `paramComposeDesc` family byte-pinned by an `emitVmJson2` `#guard`). This module resolves that
//! emitted object for a [`ComposeShape`] and hands it to the production IR-v2 decoder.
//!
//! **Say the substrate out loud:** nothing here authors a constraint. The goldens are
//! `include_str!`d STRAIGHT OUT OF THE LEAN SOURCE and split on the raw-string delimiter, so no
//! hand-transcription hop can open between the Lean author and this consumer — the same posture as
//! `circuit/tests/param_compose_descriptor.rs` and `pq_identity_authority_descriptor.rs`.
//!
//! ## Which shapes are reachable
//!
//! Only the shapes Lean has byte-pinned — but that is now the WHOLE shape census this crate's
//! tests exercise, not just the deployed pair:
//!
//! | shape | Lean name | columns | Lean leaf |
//! |---|---|---|---|
//! | `n2 p2 l1 k1 i2`   | `pcMin`           |  108 | `ParamComposeEmit`         |
//! | `n4 p8 l8 k6 i28`  | `pcRealistic`     |  770 | `ParamComposeGolden`       |
//! | `n3 p4 l3 k2 i28`  | `pcLeaf`          |  346 | `ParamComposeGoldenShapes` |
//! | `n2 p4 l1 k1 i28`  | `pcN2P4L1K1`      |  198 | `ParamComposeGoldenShapes` |
//! | `n5 p6 l4 k3 i28`  | `pcN5P6L4K3`      |  619 | `ParamComposeGoldenShapes` |
//! | `n2 p4 l1 k1 i16`  | `pcN2P4L1K1I16`   |  162 | `ParamComposeGoldenShapes` |
//! | `n4 p4 l3 k2 i28`  | `pcN4P4L3K2`      |  436 | `ParamComposeGoldenShapes` |
//! | `n3 p5 l3 k2 i28`  | `pcN3P5L3K2`      |  365 | `ParamComposeGoldenShapes` |
//! | `n3 p4 l4 k2 i28`  | `pcN3P4L4K2`      |  359 | `ParamComposeGoldenShapes` |
//! | `n3 p4 l3 k3 i28`  | `pcN3P4L3K3`      |  377 | `ParamComposeGoldenShapes` |
//! | `n3 p4 l3 k2 i24`  | `pcLeafI24`       |  326 | `ParamComposeGoldenShapes` |
//! | `n2 p2 l1 k1 i28`  | `pcN2P2L1K1`      |  186 | `ParamComposeGoldenShapes` |
//! | `n4 p8 l8 k6 i12`  | `pcRealisticI12`  |  658 | `ParamComposeGoldenShapes` |
//! | `n4 p8 l8 k6 i16`  | `pcRealisticI16`  |  686 | `ParamComposeGoldenShapes` |
//! | `n4 p8 l8 k6 i20`  | `pcRealisticI20`  |  714 | `ParamComposeGoldenShapes` |
//! | `n4 p8 l8 k6 i24`  | `pcRealisticI24`  |  742 | `ParamComposeGoldenShapes` |
//! | `n6 p8 l12 k10 i28`| `pcSegN6`         | 1277 | `ParamComposeGoldenCensus` |
//! | `n8 p16 l16 k16 i28`| `pcSegN8`        | 2462 | `ParamComposeGoldenCensus` |
//!
//! `pcRealistic` is the shape `entity-compose` deploys; the last two EXCEED the deployed
//! 1024-column single-leaf cap and are pinned so the segmentation boundary is a measured number.
//!
//! A shape with no pin is still NOT reachable from Rust and [`lean_descriptor_for`] returns `None`
//! — a fail-closed answer, never a Rust-side re-emission of the family (that would re-author the
//! AIR in Rust, which the Lean-authored-AIR law forbids). Widening the reachable set stays a LEAN
//! change and only a Lean change: the resolver below derives the golden's `def` name from the shape
//! (`PARAM_COMPOSE_GOLDEN_N<n>P<p>L<l>K<k>I<ib>`) and searches the pinned sources for it, so adding
//! a `#guard`-pinned instance in either golden leaf makes that shape reachable with no edit here.
//! The two ORIGINAL pins keep their pre-scheme names (`PARAM_COMPOSE_MIN_GOLDEN`,
//! `PARAM_COMPOSE_REALISTIC_GOLDEN`) because `circuit/tests/param_compose_descriptor.rs` reads them
//! by those names; they are the two explicit aliases below.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};

use crate::shape::ComposeShape;

/// The Lean emit module — carries `PARAM_COMPOSE_MIN_GOLDEN` (`pcMin`).
const EMIT_LEAN: &str = include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean");
/// The deployed-size leaf — carries `PARAM_COMPOSE_REALISTIC_GOLDEN` (`pcRealistic`).
const GOLDEN_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeGolden.lean");
/// The single-leaf test-corpus shapes (fourteen), pinned under the mechanical name scheme.
const SHAPES_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeGoldenShapes.lean");
/// The two shapes that EXCEED the single-leaf cap, pinned so the segmentation boundary is measured.
const CENSUS_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeGoldenCensus.lean");

/// The Lean sources searched for a shape's pin, in the order a lookup tries them.
const PINNED_SOURCES: [&str; 2] = [SHAPES_LEAN, CENSUS_LEAN];

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module.
fn lean_raw_golden(source: &'static str, name: &str) -> &'static str {
    try_lean_raw_golden(source, name)
        .unwrap_or_else(|| panic!("the Lean module still exposes {name}"))
}

/// The same split, but `None` when this module does not carry that `def` — the form the
/// shape-derived lookup needs, since a given shape lives in exactly one of the golden leaves.
fn try_lean_raw_golden(source: &'static str, name: &str) -> Option<&'static str> {
    let open = format!("def {name} : String := r#\"");
    let (_, after) = source.split_once(open.as_str())?;
    let (json, _) = after
        .split_once("\"#")
        .unwrap_or_else(|| panic!("{name} remains a raw string"));
    Some(json)
}

/// The `def` name Lean pins a shape's wire under, in the mechanical scheme the golden leaves use.
/// A pure function of the SHAPE, exactly as [`lean_descriptor_name`] is — so a new Lean pin is
/// reachable from Rust with no edit here.
fn lean_golden_def_name(shape: &ComposeShape) -> String {
    format!(
        "PARAM_COMPOSE_GOLDEN_N{}P{}L{}K{}I{}",
        shape.max_subjects,
        shape.max_params,
        shape.max_linear,
        shape.max_knots,
        shape.identity_bits
    )
}

/// The Lean shape `pcMin` (`ParamComposeEmit.lean` §14): the smallest shape exercising every gate
/// family.
pub fn pc_min() -> ComposeShape {
    ComposeShape::new(2, 2, 1, 1).with_identity_bits(2)
}

/// The Lean shape `pcRealistic` — the DEPLOYED shape `entity-compose` builds.
pub fn pc_realistic() -> ComposeShape {
    ComposeShape::new(4, 8, 8, 6)
}

/// **EVERY shape Lean has byte-pinned**, with the Lean `def` name it is pinned under.
///
/// This is a MIRROR of the Lean source and is checked against it, not trusted: every entry must
/// resolve through [`lean_descriptor_json`] (which reads the Lean text), and the descriptor it
/// decodes to must carry [`lean_descriptor_name`] for that shape. `lean_pin_census` in
/// `tests/lean_witness.rs` is that gate — so a shape listed here but dropped from the Lean tree
/// goes RED rather than silently vanishing from the reachable set.
///
/// It exists so the test corpus can iterate the reachable set instead of naming shapes one at a
/// time, and so "which shapes can Rust reach" is one readable answer.
pub fn pinned_shapes() -> Vec<(&'static str, ComposeShape)> {
    vec![
        ("pcMin", pc_min()),
        ("pcRealistic", pc_realistic()),
        ("pcLeaf", ComposeShape::new(3, 4, 3, 2)),
        ("pcN2P4L1K1", ComposeShape::new(2, 4, 1, 1)),
        ("pcN5P6L4K3", ComposeShape::new(5, 6, 4, 3)),
        (
            "pcN2P4L1K1I16",
            ComposeShape::new(2, 4, 1, 1).with_identity_bits(16),
        ),
        ("pcN4P4L3K2", ComposeShape::new(4, 4, 3, 2)),
        ("pcN3P5L3K2", ComposeShape::new(3, 5, 3, 2)),
        ("pcN3P4L4K2", ComposeShape::new(3, 4, 4, 2)),
        ("pcN3P4L3K3", ComposeShape::new(3, 4, 3, 3)),
        (
            "pcLeafI24",
            ComposeShape::new(3, 4, 3, 2).with_identity_bits(24),
        ),
        ("pcN2P2L1K1", ComposeShape::new(2, 2, 1, 1)),
        ("pcRealisticI12", pc_realistic().with_identity_bits(12)),
        ("pcRealisticI16", pc_realistic().with_identity_bits(16)),
        ("pcRealisticI20", pc_realistic().with_identity_bits(20)),
        ("pcRealisticI24", pc_realistic().with_identity_bits(24)),
        ("pcSegN6", ComposeShape::new(6, 8, 12, 10)),
        ("pcSegN8", ComposeShape::new(8, 16, 16, 16)),
    ]
}

/// The descriptor NAME Lean emits for a shape (`paramComposeName`). A function of the SHAPE alone,
/// never of the ruleset or the content — two unrelated rulesets share one VK.
pub fn lean_descriptor_name(shape: &ComposeShape) -> String {
    format!(
        "dregg-param-compose-v1-n{}p{}l{}k{}i{}::poseidon2-node8",
        shape.max_subjects,
        shape.max_params,
        shape.max_linear,
        shape.max_knots,
        shape.identity_bits
    )
}

/// The raw wire JSON Lean pinned for `shape`, or `None` when Lean has no pinned instance at that
/// shape.
///
/// The two ORIGINAL pins are named explicitly (their `def` names predate the mechanical scheme and
/// are read by name elsewhere); every other shape is found by deriving
/// [`lean_golden_def_name`] and searching the pinned golden leaves, so a new Lean pin needs no edit
/// here.
pub fn lean_descriptor_json(shape: &ComposeShape) -> Option<&'static str> {
    if *shape == pc_min() {
        return Some(lean_raw_golden(EMIT_LEAN, "PARAM_COMPOSE_MIN_GOLDEN"));
    }
    if *shape == pc_realistic() {
        return Some(lean_raw_golden(
            GOLDEN_LEAN,
            "PARAM_COMPOSE_REALISTIC_GOLDEN",
        ));
    }
    let def = lean_golden_def_name(shape);
    PINNED_SOURCES
        .iter()
        .find_map(|src| try_lean_raw_golden(src, &def))
}

/// **The Lean-authored parameter-composition descriptor at `shape`**, decoded by the production
/// IR-v2 decoder. `None` when Lean has no byte-pinned instance at that shape.
pub fn lean_descriptor_for(shape: &ComposeShape) -> Option<EffectVmDescriptor2> {
    let json = lean_descriptor_json(shape)?;
    let desc = parse_vm_descriptor2(json)
        .expect("a Lean-emitted param-compose golden decodes as IR2 (the wire canary pins this)");
    debug_assert_eq!(
        desc.name,
        lean_descriptor_name(shape),
        "the decoded golden must be the descriptor this shape names"
    );
    Some(desc)
}
