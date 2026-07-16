//! **THE COMPOSITION REALLY PROVES — bound to the ENTITY's real state.** The entity's
//! composition mints a commitment-exposing foldable leaf whose in-circuit PI commitment
//! byte-matches the host `WideHash` binding an `Effect::Custom` row carries, over the entity's
//! REAL v9 `old8`/`new8`. This is the HARD gate that the substrate is reachable from the Door
//! rather than merely self-consistent — and that a composition the ruleset does not license
//! cannot mint a leaf.
//!
//! Custom-leaf proving is minutes+; every test here is `#[ignore]`. It needs the `prove`
//! feature (which pulls the plonky3 recursion prover). Run on persvati:
//!   cargo test -p dregg-entity-compose --features prove --test leaf_prove -- --ignored --nocapture
#![cfg(feature = "prove")]

use dregg_entity_compose::{compose_onto, deploy_entity, door_felt8};
use dregg_param_compose::air::{Forgery, build, build_forged};
use dregg_param_compose::model::{Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;

const ROLE_ACTOR: u64 = 101;
const ROLE_PARTNER: u64 = 202;

fn shape() -> ComposeShape {
    ComposeShape::new(3, 4, 3, 2)
}

fn actor() -> Subject {
    Subject {
        identity: 7,
        role: ROLE_ACTOR,
        params: vec![2, 5, 0, 0],
    }
}

fn partner() -> Subject {
    Subject {
        identity: 9,
        role: ROLE_PARTNER,
        params: vec![3, 4, 0, 0],
    }
}

fn ruleset() -> Ruleset {
    Ruleset {
        id: 0xAB,
        version: 1,
        linear: vec![LinearTerm {
            role: ROLE_ACTOR,
            param: 0,
            coeff: 10,
        }],
        knots: vec![Knot {
            role_a: ROLE_ACTOR,
            param_a: 1,
            role_b: ROLE_PARTNER,
            param_b: 1,
            coeff: -2,
        }],
    }
}

/// **THE LEAF GATE, ENTITY-BOUND.** The honest composition of a real deployed entity's params
/// mints a foldable leaf, and the commitment the leaf computes IN-CIRCUIT from its public inputs
/// (which open with the entity's REAL `old8`/`new8`) equals the host binding the `Effect::Custom`
/// row carries. That equality is what the deployed fold `connect`s lane-by-lane.
#[test]
#[ignore = "SLOW: real leaf prove of the entity's param-composition + in-circuit commitment expose"]
fn entity_composition_leaf_proves_and_binds_its_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let entity = deploy_entity(1, 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    let old8 = door_felt8(&landed.old_commitment);
    let new8 = door_felt8(&landed.new_commitment);
    let air = build(&landed.shape, &landed.composition, &old8, &new8).expect("builds");
    assert!(
        air.builder.air_accepts(),
        "sanity: the honest entity composition must self-accept before proving"
    );

    let program = air.builder.cellprogram();
    let rows = 2usize;
    let w = air.builder.trace_witness(rows);
    let pis = air.builder.pis.clone();
    let config = ir2_leaf_wrap_config();

    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        .expect("the entity's composition must prove as a commitment-exposing foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "the in-circuit commitment must byte-match the host WideHash binding the Effect::Custom \
         row carries — the entity's real transition is what the fold connects"
    );
    eprintln!(
        "ENTITY COMPOSITION LEAF: w={} cols, {} constraints, {} node8 sites, {} PIs — PROVED as a \
         foldable leaf bound to the entity's real old8/new8; outcome={}.",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        air.builder.hash_site_count(),
        pis.len(),
        landed.outcome,
    );
}

/// **NON-VACUITY AT THE REAL PROVER.** A composition the ruleset does not license (a forged
/// outcome over the same entity) has no satisfying witness — so it cannot mint a leaf, even
/// though everything else in the witness is self-consistent.
#[test]
#[ignore = "SLOW: real leaf prove attempt on an outcome the ruleset does not license"]
fn a_wrong_entity_outcome_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let entity = deploy_entity(1, 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");
    let old8 = door_felt8(&landed.old_commitment);
    let new8 = door_felt8(&landed.new_commitment);

    let air = build_forged(
        &landed.shape,
        &landed.composition,
        &old8,
        &new8,
        &Forgery {
            claimed_outcome: Some(landed.outcome + 1),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !air.builder.air_accepts(),
        "sanity: the forged outcome must self-reject"
    );

    let program = air.builder.cellprogram();
    let rows = 2usize;
    let w = air.builder.trace_witness(rows);
    let pis = air.builder.pis.clone();
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!(
                "ENTITY COMPOSITION LEAF REJECT: an unlicensed outcome had no satisfying leaf."
            );
        }
        Ok(Ok(_)) => panic!("a FORGED entity outcome minted a foldable leaf — soundness OPEN"),
    }
}
