//! **THE BUDGET — the entity's composition rides the LEAN-AUTHORED 770-column leaf.**
//!
//! A realistic HOARDLIGHT-scale entity composition (4 subjects x 8 params + 6 knots, the DEPLOYED
//! shape `pcRealistic`) is built through THIS crate's substrate (a deployed entity + partners) and
//! measured against the IR-v2 leaf the fold actually proves — the object
//! `metatheory/Dregg2/Circuit/Emit/ParamComposeGolden.lean` byte-pins. The test ASSERTS the leaf
//! fits the deployed `MAX_TRACE_WIDTH = 1024` cap and that the produced witness satisfies it: a
//! gate that can go red, not a print.
//!
//! There is no lowering step and hence no lane-column term: the Lean family emits IR-v2 directly,
//! and its wide `node8` digest sites are program-owned.
//!
//! Run: cargo test -p dregg-entity-compose --test budget -- --nocapture

use dregg_circuit::dsl::circuit::{MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH};
use dregg_entity_compose::{compose_onto, deploy_entity, entity_key};
use dregg_param_compose::lean_descriptor::lean_descriptor_for;
use dregg_param_compose::model::{Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;
use dregg_param_compose::witness::ComposeLayout;

/// The realistic (DEPLOYED) shape: 4 subjects, 8 params each, 8 linear terms, 6 knots (saturated).
fn realistic_shape() -> ComposeShape {
    ComposeShape::new(4, 8, 8, 6)
}

fn roles() -> Vec<u64> {
    (0..4).map(|i| 100 + i as u64).collect()
}

/// The primary entity's projection (subject 0), saturated to 8 params.
fn actor() -> Subject {
    Subject {
        identity: 10,
        role: roles()[0],
        params: (0..8).map(|p| (p + 1) as i64).collect(),
    }
}

/// The three partner/context subjects (1..4), saturated to 8 params.
fn partners() -> Vec<Subject> {
    (1..4)
        .map(|i| Subject {
            identity: 10 + 7 * i as u64,
            role: roles()[i],
            params: (0..8).map(|p| (i + p + 1) as i64).collect(),
        })
        .collect()
}

/// A dense law saturating the shape's linear + knot bounds.
fn ruleset() -> Ruleset {
    let r = roles();
    Ruleset {
        id: 42,
        version: 1,
        linear: (0..8)
            .map(|t| LinearTerm {
                role: r[t % 4],
                param: t % 8,
                coeff: (t as i64 + 1) * 3,
            })
            .collect(),
        knots: (0..6)
            .map(|k| Knot {
                role_a: r[k % 4],
                param_a: k % 8,
                role_b: r[(k + 1) % 4],
                param_b: (k + 1) % 8,
                coeff: -(k as i64 + 1),
            })
            .collect(),
    }
}

#[test]
fn the_realistic_entity_composition_rides_the_lean_770_column_leaf() {
    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed =
        compose_onto(&entity, &partners(), ruleset(), realistic_shape(), 8).expect("composes");

    // The LEAN-EMITTED descriptor for this shape — the object the fold proves.
    let desc = lean_descriptor_for(&landed.shape)
        .expect("the deployed shape has a byte-pinned Lean descriptor");
    assert_eq!(
        desc.name,
        "dregg-param-compose-v1-n4p8l8k6i28::poseidon2-node8"
    );
    assert_eq!(desc.trace_width, 770);
    assert_eq!(
        ComposeLayout::new(&landed.shape).width,
        desc.trace_width,
        "the witness producer's layout must be the emitted width"
    );

    // The produced witness satisfies it (the deployed IR-v2 row-local evaluator's verdict).
    assert!(
        landed.lean_descriptor_accepts(),
        "the saturated realistic composition's witness must satisfy the emitted descriptor"
    );

    let sites = desc
        .constraints
        .iter()
        .filter(|c| matches!(c, dregg_circuit::descriptor_ir2::VmConstraint2::Lookup(_)))
        .count();
    eprintln!(
        "REALISTIC ENTITY COMPOSITION (n4 p8 l8 k6, LEAN-AUTHORED): leaf={}/{MAX_TRACE_WIDTH} \
         constraints={} pis={} sites={sites} — outcome={}",
        desc.trace_width,
        desc.constraints.len(),
        landed.pis.len(),
        landed.outcome,
    );

    assert!(
        desc.trace_width <= MAX_TRACE_WIDTH,
        "the realistic entity composition must fold as ONE leaf: {} > {MAX_TRACE_WIDTH}",
        desc.trace_width
    );
    // The public-input budget: constant in the subject count, inside the door's 64-PI cap.
    assert_eq!(landed.pis.len(), desc.public_input_count);
    assert!(
        landed.pis.len() <= MAX_PUBLIC_INPUTS,
        "the composition PIs must fit the deployed cap"
    );
    // The fuel meter the shape publishes is the number of sites the descriptor actually carries.
    assert_eq!(sites, landed.shape.hash_sites());
}
