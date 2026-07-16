//! **THE BUDGET — the entity's composition rides `dregg-param-compose`'s 803-column leaf.**
//!
//! A realistic HOARDLIGHT-scale entity composition (4 subjects x 8 params + 6 knots, the shape
//! `dregg-param-compose` measures at an 803-column leaf) is built through THIS crate's substrate
//! (a deployed entity + partners) and LOWERED to the IR-v2 leaf the fold actually proves. The
//! test ASSERTS the leaf fits the deployed `MAX_TRACE_WIDTH = 1024` cap at ZERO lowering lane
//! columns (the node8 digest is program-owned) — a gate that can go red, not a print.
//!
//! Run: cargo test -p dregg-entity-compose --test budget -- --nocapture

use dregg_circuit::custom_leaf_lowering::cellprogram_to_descriptor2;
use dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH;
use dregg_circuit::field::BabyBear;
use dregg_entity_compose::{compose_onto, deploy_entity, door_felt8};
use dregg_param_compose::air::build;
use dregg_param_compose::model::{Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;

/// The realistic shape: 4 subjects, 8 params each, 8 linear terms, 6 knots (saturated).
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
fn the_realistic_entity_composition_rides_the_803_column_leaf() {
    let entity = deploy_entity(1, 1_000, actor());
    let landed =
        compose_onto(&entity, &partners(), ruleset(), realistic_shape(), 8).expect("composes");

    // Rebuild the AIR bound to the entity's REAL commitments and lower it to the fold leaf.
    let old8 = door_felt8(&landed.old_commitment);
    let new8 = door_felt8(&landed.new_commitment);
    let air = build(&landed.shape, &landed.composition, &old8, &new8).expect("builds");
    assert!(
        air.builder.air_accepts(),
        "the saturated realistic composition must self-accept"
    );

    let program = air.builder.cellprogram();
    let prog = program.descriptor.trace_width;
    let lowered = cellprogram_to_descriptor2(&program).expect("lowers to a foldable leaf");
    let leaf = lowered.trace_width;
    let lane = leaf - prog;

    eprintln!(
        "REALISTIC ENTITY COMPOSITION (n4 p8 l8 k6): prog={prog} lane={lane} leaf={leaf}/{MAX_TRACE_WIDTH} \
         pis={} sites={} — outcome={}",
        air.builder.pis.len(),
        air.builder.hash_site_count(),
        landed.outcome,
    );

    assert_eq!(
        lane, 0,
        "the node8 digest is program-owned, so the lowered leaf must allocate ZERO lane columns"
    );
    assert!(
        leaf <= MAX_TRACE_WIDTH,
        "the realistic entity composition must fold as ONE leaf: {leaf} > {MAX_TRACE_WIDTH}"
    );
    // The public-input budget: constant in the subject count, inside the door's 64-PI cap.
    assert!(
        air.builder.pis.len() <= dregg_param_compose::shape::MAX_PUBLIC_INPUTS,
        "the composition PIs must fit the deployed cap"
    );
    let _ = BabyBear::ZERO; // (keep the field import meaningful if the asserts change)
}
