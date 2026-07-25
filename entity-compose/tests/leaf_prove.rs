//! **THE COMPOSITION REALLY PROVES — bound to the ENTITY's real state, through the LEAN AIR.**
//! The entity's composition mints a commitment-exposing foldable leaf whose in-circuit PI
//! commitment byte-matches the host `WideHash` binding an `Effect::Custom` row carries, over the
//! entity's REAL v9 `old8`/`new8`. This is the HARD gate that the substrate is reachable from the
//! Door rather than merely self-consistent — and that a composition the ruleset does not license
//! cannot mint a leaf.
//!
//! **Say the substrate out loud:** the leaf proves the **LEAN-AUTHORED descriptor** directly
//! (`prove_custom_leaf_descriptor_with_state_commitment` over `paramComposeDesc pcRealistic`,
//! byte-pinned in `metatheory/Dregg2/Circuit/Emit/ParamComposeGolden.lean`). No Rust `CellProgram`
//! is lowered, so the relation has exactly one semantics; Rust supplies only the trace fill
//! (`dregg_param_compose::witness`).
//!
//! Custom-leaf proving is minutes+; every test here is `#[ignore]`. It needs the `prove`
//! feature (which pulls the plonky3 recursion prover). Run on persvati:
//!   cargo test -p dregg-entity-compose --features prove --test leaf_prove -- --ignored --nocapture
#![cfg(feature = "prove")]

use dregg_entity_compose::{compose_onto, deploy_entity, door_felt8, entity_key};
use dregg_param_compose::field::fb;
use dregg_param_compose::model::{Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;
use dregg_param_compose::witness::compose_trace_accepts;

const ROLE_ACTOR: u64 = 101;
const ROLE_PARTNER: u64 = 202;

/// The DEPLOYED shape — Lean's `pcRealistic`, the one whose descriptor is byte-pinned. A shape is a
/// BOUND, so this two-subject composition rides it unchanged.
fn shape() -> ComposeShape {
    ComposeShape::new(4, 8, 8, 6)
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
        prove_custom_leaf_descriptor_with_state_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    let old8 = door_felt8(&landed.old_commitment);
    let new8 = door_felt8(&landed.new_commitment);
    let rows = 2usize;
    let (desc, base_trace, pis) = landed
        .direct_ir2_leaf_inputs(&old8, &new8, rows)
        .expect("the deployed shape resolves the Lean descriptor and the witness satisfies it");
    let config = ir2_leaf_wrap_config();

    let out = prove_custom_leaf_descriptor_with_state_commitment(&desc, &base_trace, &pis, &config)
        .expect("the entity's composition must prove as a commitment-exposing foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "the in-circuit commitment must byte-match the host WideHash binding the Effect::Custom \
         row carries — the entity's real transition is what the fold connects"
    );
    eprintln!(
        "ENTITY COMPOSITION LEAF (LEAN-AUTHORED {}): w={} cols, {} constraints, {} PIs — PROVED as \
         a foldable leaf bound to the entity's real old8/new8; outcome={}.",
        desc.name,
        desc.trace_width,
        desc.constraints.len(),
        pis.len(),
        landed.outcome,
    );
}

/// **NON-VACUITY AT THE REAL PROVER.** A composition the ruleset does not license (a forged
/// outcome over the same entity, re-committed honestly so the chains and PIs bind the lie) has no
/// satisfying witness — so it cannot mint a leaf.
#[test]
#[ignore = "SLOW: real leaf prove attempt on an outcome the ruleset does not license"]
fn a_wrong_entity_outcome_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_descriptor_with_state_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_param_compose::lean_descriptor::lean_descriptor_for;

    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");
    let desc = lean_descriptor_for(&landed.shape).expect("the deployed shape is Lean-pinned");

    let mut forged = landed.witness.clone();
    forged.row[forged.layout.out_col] = fb(landed.outcome + 1);
    forged.fill_chains();
    forged.fill_pis();
    assert!(
        !compose_trace_accepts(&desc, &forged),
        "sanity: the emitted LAW gate must already refuse the forged outcome"
    );

    let rows = 2usize;
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_descriptor_with_state_commitment(
            &desc,
            &forged.base_trace(rows),
            &forged.pis,
            &config,
        )
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
