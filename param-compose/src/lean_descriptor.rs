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
//! Only the shapes Lean has byte-pinned. Today that is two:
//!
//! | shape | Lean name | columns |
//! |---|---|---|
//! | `n2 p2 l1 k1 i2`  | `pcMin`        | 108 |
//! | `n4 p8 l8 k6 i28` | `pcRealistic`  | 770 |
//!
//! `pcRealistic` is the shape `entity-compose` deploys. A shape with no pin is NOT reachable from
//! Rust and [`lean_descriptor_for`] returns `None` — a fail-closed answer, never a Rust-side
//! re-emission of the family (that would re-author the AIR in Rust, which the Lean-authored-AIR law
//! forbids). Widening the reachable set is a Lean change: add a `#guard`-pinned instance.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};

use crate::shape::ComposeShape;

/// The Lean emit module — carries `PARAM_COMPOSE_MIN_GOLDEN` (`pcMin`).
const EMIT_LEAN: &str = include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean");
/// The deployed-size leaf — carries `PARAM_COMPOSE_REALISTIC_GOLDEN` (`pcRealistic`).
const GOLDEN_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeGolden.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module.
fn lean_raw_golden(source: &'static str, name: &str) -> &'static str {
    let open = format!("def {name} : String := r#\"");
    let (_, after) = source
        .split_once(open.as_str())
        .unwrap_or_else(|| panic!("the Lean module still exposes {name}"));
    let (json, _) = after
        .split_once("\"#")
        .unwrap_or_else(|| panic!("{name} remains a raw string"));
    json
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
pub fn lean_descriptor_json(shape: &ComposeShape) -> Option<&'static str> {
    if *shape == pc_min() {
        Some(lean_raw_golden(EMIT_LEAN, "PARAM_COMPOSE_MIN_GOLDEN"))
    } else if *shape == pc_realistic() {
        Some(lean_raw_golden(
            GOLDEN_LEAN,
            "PARAM_COMPOSE_REALISTIC_GOLDEN",
        ))
    } else {
        None
    }
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
