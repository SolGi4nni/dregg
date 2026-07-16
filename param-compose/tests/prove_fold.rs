//! SLOW: the composition AIR PROVES as a real recursion-foldable custom leaf, and its
//! in-circuit PI commitment byte-matches the host binding the `Effect::Custom` row
//! carries — the HARD GATE that this AIR is reachable from the door rather than merely
//! self-consistent in the DSL evaluator.
//!
//! Custom-leaf proving is minutes+; every test here is `#[ignore]`. Run on persvati:
//!   cargo test -p dregg-param-compose --test prove_fold -- --ignored --nocapture

use dregg_circuit::field::BabyBear;
use dregg_param_compose::air::{Forgery, build, build_forged};
use dregg_param_compose::field::fb;
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;

const ROLE_P: u64 = 101;
const ROLE_Q: u64 = 202;

/// The shape driven here: small enough to prove in a test, with every mechanism live
/// (multiple subjects, a linear term, a KNOT, the 8-felt node8 binding width).
fn shape() -> ComposeShape {
    ComposeShape::new(3, 4, 3, 2)
}

fn old8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(1000 + i as i128))
}
fn new8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(2000 + i as i128))
}

fn composition() -> Composition {
    Composition {
        subjects: vec![
            Subject {
                identity: 7,
                role: ROLE_P,
                params: vec![2, 5, 0, 0],
            },
            Subject {
                identity: 9,
                role: ROLE_Q,
                params: vec![3, 4, 0, 0],
            },
        ],
        ruleset: Ruleset {
            id: 0xAB,
            version: 1,
            linear: vec![LinearTerm {
                role: ROLE_P,
                param: 0,
                coeff: 10,
            }],
            knots: vec![Knot {
                role_a: ROLE_P,
                param_a: 1,
                role_b: ROLE_Q,
                param_b: 1,
                coeff: -2,
            }],
        },
        param_count: 4,
    }
}

/// **THE LEAF GATE.** The honest composition mints a commitment-exposing foldable leaf,
/// and the commitment the leaf computes IN-CIRCUIT from its real public inputs equals the
/// host `WideHash` binding that an `Effect::Custom` row carries. That equality is what the
/// deployed fold `connect`s lane-by-lane, so a claimed commitment no verifying sub-proof
/// backs is UNSAT.
#[test]
#[ignore = "SLOW: real leaf prove of the param-composition AIR + in-circuit commitment expose"]
fn composition_leaf_proves_and_binds_its_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = shape();
    let air = build(&sh, &composition(), &old8(), &new8()).expect("builds");
    assert!(
        air.builder.air_accepts(),
        "sanity: the honest composition must self-accept before proving"
    );

    let program = air.builder.cellprogram();
    let rows = 2usize;
    let w = air.builder.trace_witness(rows);
    let pis = air.builder.pis.clone();
    let config = ir2_leaf_wrap_config();

    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config).expect(
        "the honest parameter-composition AIR must prove as a commitment-exposing foldable leaf",
    );
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "the in-circuit commitment must byte-match the host WideHash binding the \
         Effect::Custom row carries"
    );
    eprintln!(
        "COMPOSITION LEAF: w={} cols, {} constraints, {} Poseidon2 sites, {} PIs — PROVED as a \
         foldable leaf; in-circuit commitment == host binding.",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        air.builder.hash_site_count(),
        pis.len(),
    );
}

/// **THE REALISTIC SHAPE PROVES AS ONE LEAF.** The HOARDLIGHT-scale composition the task
/// names — ~8 params x ~4 subjects + ~6 knots, saturated (every bound full), at the 8-felt
/// node8 binding width — over the DEFAULT 28-bit identity namespace (268M identities).
///
/// `tests/size.rs` measures this shape at an 803-column leaf (program == leaf: the node8
/// digest allocates ZERO lowering lane columns). That is a fact about the DESCRIPTOR; this
/// test is the fact about the PROVER: it really does mint one foldable leaf, so the
/// realistic shape needs NO segmentation and NO identity narrowing. (The old 8-chain
/// digest folded a 3575-column leaf here — 999 program + 2576 lane columns — and this shape
/// only "fit" because the report never counted the lane columns.)
#[test]
#[ignore = "SLOW: real leaf prove of the realistic (saturated n4 p8 l8 k6) composition"]
fn the_realistic_shape_proves_as_a_single_leaf() {
    use dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH;
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = ComposeShape::new(4, 8, 8, 6);

    // A composition saturating every one of the shape's bounds — the worst case a VK of
    // this shape must carry, not a lucky sparse one.
    let roles: Vec<u64> = (0..4).map(|i| 100 + i as u64).collect();
    let comp = Composition {
        subjects: (0..4)
            .map(|i| Subject {
                identity: 10 + 7 * i as u64,
                role: roles[i],
                params: (0..8).map(|p| (i + p + 1) as i64).collect(),
            })
            .collect(),
        ruleset: Ruleset {
            id: 42,
            version: 1,
            linear: (0..8)
                .map(|t| LinearTerm {
                    role: roles[t % 4],
                    param: t % 8,
                    coeff: (t as i64 + 1) * 3,
                })
                .collect(),
            knots: (0..6)
                .map(|k| Knot {
                    role_a: roles[k % 4],
                    param_a: k % 8,
                    role_b: roles[(k + 1) % 4],
                    param_b: (k + 1) % 8,
                    coeff: -(k as i64 + 1),
                })
                .collect(),
        },
        param_count: 8,
    };

    let air = build(&sh, &comp, &old8(), &new8()).expect("builds");
    assert!(
        air.builder.air_accepts(),
        "sanity: the saturated witness must self-accept"
    );
    let program = air.builder.cellprogram();
    assert!(
        program.descriptor.trace_width <= MAX_TRACE_WIDTH,
        "the realistic shape must fit the deployed width cap: {} > {MAX_TRACE_WIDTH}",
        program.descriptor.trace_width
    );

    let rows = 2usize;
    let w = air.builder.trace_witness(rows);
    let pis = air.builder.pis.clone();
    let out = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &ir2_leaf_wrap_config())
        .expect("the realistic saturated composition must prove as ONE foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    assert_eq!(
        exposed,
        custom_proof_pi_commitment(&pis),
        "in-circuit commitment must byte-match the host binding"
    );
    eprintln!(
        "REALISTIC LEAF (n4 p8 l8 k6, node8 8-felt digest, identity_bits=28): \
         w={}/{MAX_TRACE_WIDTH} cols (0 lowering lane columns), {} \
         constraints, {} node8 sites, {} PIs — PROVED as a SINGLE foldable leaf. \
         NO SEGMENTATION, NO IDENTITY NARROWING at the realistic shape.",
        program.descriptor.trace_width,
        program.descriptor.constraints.len(),
        air.builder.hash_site_count(),
        pis.len(),
    );
}

/// **NON-VACUITY AT THE REAL PROVER.** A composition the ruleset does not license has no
/// satisfying witness — so it cannot mint a leaf. The `air_accepts` shadow says this in
/// milliseconds; this says it against the actual STARK quotient/FRI.
#[test]
#[ignore = "SLOW: real leaf prove attempt on an outcome the ruleset does not license"]
fn a_wrong_outcome_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = shape();
    let c = composition();
    let truth = c.compose().unwrap().outcome;
    let air = build_forged(
        &sh,
        &c,
        &old8(),
        &new8(),
        &Forgery {
            claimed_outcome: Some(truth + 1),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !air.builder.air_accepts(),
        "sanity: the forgery must self-reject"
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
            eprintln!("COMPOSITION LEAF REJECT: an unlicensed outcome had no satisfying leaf.");
        }
        Ok(Ok(_)) => panic!("a FORGED composition minted a foldable leaf — soundness OPEN"),
    }
}

/// **THE DUPLICATE, AT THE REAL PROVER.** The same entity in two seats cannot mint a leaf:
/// the in-circuit strict identity ordering has no satisfying witness for it.
#[test]
#[ignore = "SLOW: real leaf prove attempt on a duplicated subject identity"]
fn a_duplicated_subject_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = shape();
    let dup = vec![
        Subject {
            identity: 7,
            role: ROLE_P,
            params: vec![2, 5, 0, 0],
        },
        Subject {
            identity: 7, // the double-count
            role: ROLE_Q,
            params: vec![3, 4, 0, 0],
        },
    ];
    let air = build_forged(
        &sh,
        &composition(),
        &old8(),
        &new8(),
        &Forgery {
            raw_subject_order: Some(dup),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !air.builder.air_accepts(),
        "sanity: the duplicate must self-reject"
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
            eprintln!("COMPOSITION LEAF REJECT: a duplicated subject identity had no leaf.");
        }
        Ok(Ok(_)) => panic!("a DUPLICATED subject minted a foldable leaf — soundness OPEN"),
    }
}
