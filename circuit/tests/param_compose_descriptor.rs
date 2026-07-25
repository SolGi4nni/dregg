//! **Lean→Rust wire canary for the parameter-composition AIR.**
//!
//! The constraints are AUTHORED IN LEAN (`metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean`,
//! byte-pinned there by an `emitVmJson2` `#guard`, with the SAT ⟹ SEM bridge in
//! `ParamComposeRefine.lean`). This test takes the byte-pinned goldens STRAIGHT OUT OF THE LEAN
//! SOURCE and hands them to the production IR2 decoder, so no hand-transcription hop can open
//! between the Lean author and the Rust consumer — the same posture as
//! `pq_identity_authority_descriptor.rs`.
//!
//! ## What this establishes, and what it does NOT
//!
//! ESTABLISHES: the Lean-emitted object is wire-compatible with `parse_vm_descriptor2`, decodes to
//! the exact shape the Lean `#guard`s pin, and carries the constraint census the emit module
//! documents (the wide `node8` chip lookups at their 25-wide `chip_lookup_sound_N` tuple width, and
//! all 37 app PI bindings of `param-compose/src/pi.rs`).
//!
//! DOES NOT: prove anything semantic. Semantic faithfulness is
//! `ParamComposeRefine.paramCompose_refines_law` / `fetch_resolves` / `role_key_of_sat` /
//! `knot_neuter_rejected` in Lean, over the ACTUAL emitted object. A Rust assertion about a
//! decoded descriptor is a shape check; it is not refinement, not translation validation, and not
//! verification.
//!
//! ## Why it exists (the crate it replaces)
//!
//! `param-compose/src/air.rs` + `src/builder.rs` hand-write this AIR in Rust — constraints, gadgets
//! and an `air_accepts` predicate, the three things the Lean-authored-AIR law names — and
//! `entity-compose/src/lib.rs` rides it on the deployed `Effect::Custom` door. The Lean family here
//! is the replacement route; this test is the evidence the route REACHES Rust.
//!
//! ## The remaining rewiring (NOT done here, stated precisely)
//!
//! `entity-compose::LandedComposition::fold_leaf_inputs` currently calls
//! `dregg_param_compose::air::build(..)` and reads `air.builder.cellprogram()` /
//! `trace_witness()` / `pis`. The replacement is:
//!
//!   1. `parse_vm_descriptor2(PARAM_COMPOSE_REALISTIC_GOLDEN)` for the descriptor (or resolve it by
//!      name once the by-name install is provenance-stamped);
//!   2. a WITNESS PRODUCER that fills the Lean column layout (`ComposeShape.sBase`/`lBase`/`kBase`/
//!      `digBase`, §2 of the emit module) rather than the Rust `Builder::alloc` order — the two
//!      layouts differ by exactly the 33 constant-pinned columns the Lean family drops;
//!   3. `prove_vm_descriptor2(&desc, &base_trace, &pis, &mem_boundary, &[])` — `trace_with_chip_lanes`
//!      fills the Poseidon2 lane columns, so the producer supplies only the main trace.
//!
//! Only step 2 is real work, and it is the piece that must land before `param-compose` is deleted.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::lean_descriptor_air::VmConstraint;

const EMIT_LEAN: &str = include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean");
const GOLDEN_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/ParamComposeGolden.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module.
fn lean_raw_golden(source: &'static str, name: &str) -> &'static str {
    let open = format!("def {name} : String := r#\"");
    let (_, after) = source
        .split_once(open.as_str())
        .unwrap_or_else(|| panic!("Lean module still exposes {name}"));
    let (json, _) = after
        .split_once("\"#")
        .unwrap_or_else(|| panic!("{name} remains a raw string"));
    json
}

fn lookup_tuple_widths(desc: &EffectVmDescriptor2) -> Vec<usize> {
    desc.constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Lookup(l) => Some(l.tuple.len()),
            _ => None,
        })
        .collect()
}

fn pi_binding_count(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count()
}

#[test]
fn lean_param_compose_min_golden_parses_with_exact_shape() {
    let desc = parse_vm_descriptor2(lean_raw_golden(EMIT_LEAN, "PARAM_COMPOSE_MIN_GOLDEN"))
        .expect("Lean-emitted param-compose (pcMin) descriptor parses as IR2");

    assert_eq!(
        desc.name,
        "dregg-param-compose-v1-n2p2l1k1i2::poseidon2-node8"
    );
    assert_eq!(desc.trace_width, 108);
    assert_eq!(desc.public_input_count, 53);
    assert_eq!(desc.constraints.len(), 129);
    assert!(desc.tables.is_empty());
    assert!(desc.hash_sites.is_empty());
    assert!(desc.ranges.is_empty());

    // The four `cap_node8` Merkle-Damgard chains: subjects (1 block) + ruleset (2) + outcome (1)
    // + explanation (1) at this shape, plus the extra subjects block = 6 sites total, each a WIDE
    // arity-16 tuple (`1 + CHIP_RATE + CHIP_OUT_LANES = 25`) so `chip_lookup_sound_N` applies.
    let widths = lookup_tuple_widths(&desc);
    assert_eq!(widths.len(), 6, "one node8 site per 8-felt stream block");
    assert!(
        widths.iter().all(|w| *w == 25),
        "wide node8 tuples: {widths:?}"
    );

    // The PI layout of `param-compose/src/pi.rs`: 16 raw door PIs (bound by the EXECUTOR, not here)
    // + 5 scalars + 4 roots x 8 lanes.
    assert_eq!(pi_binding_count(&desc), 37);
}

#[test]
fn lean_param_compose_deployed_golden_parses_with_exact_shape() {
    let desc = parse_vm_descriptor2(lean_raw_golden(
        GOLDEN_LEAN,
        "PARAM_COMPOSE_REALISTIC_GOLDEN",
    ))
    .expect("Lean-emitted param-compose (deployed n4 p8 l8 k6 i28) descriptor parses as IR2");

    assert_eq!(
        desc.name,
        "dregg-param-compose-v1-n4p8l8k6i28::poseidon2-node8"
    );
    assert_eq!(desc.trace_width, 770);
    assert_eq!(desc.public_input_count, 53);
    assert_eq!(desc.constraints.len(), 863);
    assert_eq!(pi_binding_count(&desc), 37);

    // `ComposeShape::hash_sites` at the realistic shape is 18; the emitted lookups must agree,
    // because the fuel meter a host prices a composition by is only honest if it counts the sites
    // the descriptor actually carries.
    let widths = lookup_tuple_widths(&desc);
    assert_eq!(widths.len(), 18);
    assert!(widths.iter().all(|w| *w == 25));

    // The deployed program-validation caps this AIR is measured against.
    assert!(
        desc.trace_width <= dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH,
        "the deployed 1024-column cap"
    );
    assert!(
        desc.public_input_count <= dregg_circuit::dsl::circuit::MAX_PUBLIC_INPUTS,
        "the deployed 64-PI cap"
    );
}

/// The Lean column census is 33 below the hand-written Rust AIR's own published budget table at
/// EVERY shape (`param-compose/src/lib.rs`: 219 / 379 / 803 for n2p2l1k1 / n3p4l3k2 / n4p8l8k6).
/// 33 = the shared `zero` column + the four 8-felt domain-IV column groups, which the Lean family
/// replaces with literal constants in the chip tuple. A constant cannot be tampered, so this is a
/// strengthening; the constant delta across independent shapes is the structural evidence that
/// nothing ELSE moved.
#[test]
fn lean_column_census_is_the_rust_census_minus_the_constant_pins() {
    let min = parse_vm_descriptor2(lean_raw_golden(EMIT_LEAN, "PARAM_COMPOSE_MIN_GOLDEN")).unwrap();
    let real = parse_vm_descriptor2(lean_raw_golden(
        GOLDEN_LEAN,
        "PARAM_COMPOSE_REALISTIC_GOLDEN",
    ))
    .unwrap();
    // pcMin runs at identity_bits = 2 rather than the default 28, so it is not directly comparable
    // to the Rust n2p2l1k1 row (which is 28-bit); the DEPLOYED row is.
    assert_eq!(real.trace_width + 33, 803, "Rust realistic prog columns");
    assert!(min.trace_width < real.trace_width);
}
