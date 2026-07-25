//! SLOW: the LEAN-AUTHORED composition descriptor PROVES as a real recursion-foldable custom
//! leaf, and its in-circuit PI commitment byte-matches the host binding the `Effect::Custom` row
//! carries — the HARD GATE that this AIR is reachable from the door rather than merely
//! satisfying a row-local evaluator.
//!
//! **Say the substrate out loud:** the leaf proves the object
//! `metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean` emits and the golden leaves byte-pin,
//! handed to `prove_custom_leaf_descriptor_with_state_commitment` DIRECTLY. No Rust
//! `CellProgram` is built and no custom-leaf lowering runs, so the relation has exactly one
//! semantics; Rust supplies only the trace fill (`dregg_param_compose::witness`).
//!
//! Custom-leaf proving is minutes+; every test here is `#[ignore]`. Run on persvati:
//!   cargo test -p dregg-param-compose --test prove_fold -- --ignored --nocapture

use dregg_circuit::field::BabyBear;
use dregg_param_compose::field::fb;
use dregg_param_compose::lean_descriptor::lean_descriptor_for;
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;
use dregg_param_compose::witness::{compose_trace_accepts, compose_witness, compose_witness_over};

const ROLE_P: u64 = 101;
const ROLE_Q: u64 = 202;

/// The shape driven here: small enough to prove in a test, with every mechanism live
/// (multiple subjects, a linear term, a KNOT, the 8-felt node8 binding width). Lean's `pcLeaf`.
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

/// **THE LEAF GATE.** The honest composition mints a commitment-exposing foldable leaf over the
/// LEAN-EMITTED descriptor, and the commitment the leaf computes IN-CIRCUIT from its real public
/// inputs equals the host `WideHash` binding that an `Effect::Custom` row carries. That equality
/// is what the deployed fold `connect`s lane-by-lane, so a claimed commitment no verifying
/// sub-proof backs is UNSAT.
#[test]
#[ignore = "SLOW: real leaf prove of the Lean-authored param-composition descriptor + in-circuit commitment expose"]
fn composition_leaf_proves_and_binds_its_commitment() {
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_descriptor_with_state_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = shape();
    let desc = lean_descriptor_for(&sh).expect("a Lean-pinned shape");
    let w = compose_witness(&sh, &composition(), &old8(), &new8()).expect("produces");
    assert!(
        compose_trace_accepts(&desc, &w),
        "sanity: the emitted descriptor must accept the honest row before proving"
    );

    let rows = 2usize;
    let trace = w.base_trace(rows);
    let config = ir2_leaf_wrap_config();

    let out = prove_custom_leaf_descriptor_with_state_commitment(&desc, &trace, &w.pis, &config)
        .expect(
            "the honest parameter-composition witness must prove the Lean-authored descriptor as \
             a commitment-exposing foldable leaf",
        );
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    let host = custom_proof_pi_commitment(&w.pis);
    assert_eq!(
        exposed, host,
        "the in-circuit commitment must byte-match the host WideHash binding the \
         Effect::Custom row carries"
    );
    eprintln!(
        "COMPOSITION LEAF (LEAN-AUTHORED {}): w={} cols, {} constraints, {} PIs — PROVED as a \
         foldable leaf; in-circuit commitment == host binding.",
        desc.name,
        desc.trace_width,
        desc.constraints.len(),
        w.pis.len(),
    );
}

/// **THE REALISTIC SHAPE PROVES AS ONE LEAF.** The HOARDLIGHT-scale composition the task
/// names — ~8 params x ~4 subjects + ~6 knots, saturated (every bound full), at the 8-felt
/// node8 binding width — over the DEFAULT 28-bit identity namespace (268M identities).
///
/// `tests/size.rs` measures this shape at a 770-column emitted leaf. That is a fact about the
/// DESCRIPTOR; this test is the fact about the PROVER: it really does mint one foldable leaf, so
/// the realistic shape needs NO segmentation and NO identity narrowing.
#[test]
#[ignore = "SLOW: real leaf prove of the realistic (saturated n4 p8 l8 k6) composition"]
fn the_realistic_shape_proves_as_a_single_leaf() {
    use dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH;
    use dregg_circuit_prove::custom_leaf_adapter::{
        prove_custom_leaf_descriptor_with_state_commitment, read_exposed_pi_commitment,
    };
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = ComposeShape::new(4, 8, 8, 6);
    let desc = lean_descriptor_for(&sh).expect("the DEPLOYED shape is Lean-pinned");
    assert!(
        desc.trace_width <= MAX_TRACE_WIDTH,
        "the realistic shape must fit the deployed width cap: {} > {MAX_TRACE_WIDTH}",
        desc.trace_width
    );

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

    let w = compose_witness(&sh, &comp, &old8(), &new8()).expect("produces");
    assert!(
        compose_trace_accepts(&desc, &w),
        "sanity: the saturated witness must satisfy the emitted descriptor"
    );

    let rows = 2usize;
    let out = prove_custom_leaf_descriptor_with_state_commitment(
        &desc,
        &w.base_trace(rows),
        &w.pis,
        &ir2_leaf_wrap_config(),
    )
    .expect("the realistic saturated composition must prove as ONE foldable leaf");
    let exposed = read_exposed_pi_commitment(&out).expect("leaf exposes an 8-felt commitment");
    assert_eq!(
        exposed,
        custom_proof_pi_commitment(&w.pis),
        "in-circuit commitment must byte-match the host binding"
    );
    eprintln!(
        "REALISTIC LEAF (LEAN-AUTHORED {}, node8 8-felt digest, identity_bits=28): \
         w={}/{MAX_TRACE_WIDTH} cols, {} constraints, {} PIs — PROVED as a SINGLE foldable leaf. \
         NO SEGMENTATION, NO IDENTITY NARROWING at the realistic shape.",
        desc.name,
        desc.trace_width,
        desc.constraints.len(),
        w.pis.len(),
    );
}

/// **NON-VACUITY AT THE REAL PROVER.** A composition the ruleset does not license has no
/// satisfying witness — so it cannot mint a leaf. The row-local evaluator says this in
/// milliseconds; this says it against the actual STARK quotient/FRI.
#[test]
#[ignore = "SLOW: real leaf prove attempt on an outcome the ruleset does not license"]
fn a_wrong_outcome_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_descriptor_with_state_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = shape();
    let desc = lean_descriptor_for(&sh).expect("a Lean-pinned shape");
    let c = composition();
    let truth = c.compose().unwrap().outcome;
    let mut w = compose_witness(&sh, &c, &old8(), &new8()).expect("produces");
    // Claim a different outcome and RE-COMMIT to it honestly, so the chains and the PIs bind the
    // lie and the only thing that can refuse it is the composition law itself.
    w.row[w.layout.out_col] = fb(truth + 1);
    w.fill_chains();
    w.fill_pis();
    assert!(
        !compose_trace_accepts(&desc, &w),
        "sanity: the emitted LAW gate must already refuse the forgery"
    );

    let rows = 2usize;
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_descriptor_with_state_commitment(
            &desc,
            &w.base_trace(rows),
            &w.pis,
            &config,
        )
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
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_descriptor_with_state_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

    let sh = shape();
    let desc = lean_descriptor_for(&sh).expect("a Lean-pinned shape");
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
    let w = compose_witness_over(&sh, &composition(), &dup, &old8(), &new8())
        .expect("the producer lays the list AS GIVEN — the emitted AIR is the judge");
    assert!(
        !compose_trace_accepts(&desc, &w),
        "sanity: the duplicate must already be refused row-locally"
    );

    let rows = 2usize;
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_descriptor_with_state_commitment(
            &desc,
            &w.base_trace(rows),
            &w.pis,
            &config,
        )
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!("COMPOSITION LEAF REJECT: a duplicated subject identity had no leaf.");
        }
        Ok(Ok(_)) => panic!("a DUPLICATED subject minted a foldable leaf — soundness OPEN"),
    }
}

/// **THE NODE8 SITE CANARY, AT THE REAL PROVER.** A `MerkleHash8` (`node8`) chip lookup binds
/// its 16 inputs to its 8 outputs via the genuine `cap_node8` permutation. Tamper ONE digest
/// output lane and re-publish the PIs to match, and every ROW-LOCAL gate still holds — the PI
/// bindings bind the tampered value, and no composition gate reads a digest column. The ONLY
/// thing that can refuse it is the chip-bus arm the batch prover runs.
///
/// This is why it is here and not in the fast gauntlet: `ir2_eval_accepts_i64` is deliberately
/// silent on cross-table bus arms, so the digest site's tooth is unobservable until the real
/// multi-table STARK is assembled.
///
/// (This replaces a pre-migration canary that built a standalone one-site chip through the Rust
/// DSL `Builder` and toggled the constraint on and off. That form is gone with the Rust AIR: it
/// hand-authored a mini-circuit, and on this route there is no constraint to omit.)
#[test]
#[ignore = "SLOW: real leaf prove attempt on a tampered node8 digest lane"]
fn a_tampered_node8_digest_lane_does_not_prove() {
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_descriptor_with_state_commitment;
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_param_compose::witness::CHAIN_RULESET;

    let sh = shape();
    let desc = lean_descriptor_for(&sh).expect("a Lean-pinned shape");
    let mut w = compose_witness(&sh, &composition(), &old8(), &new8()).expect("produces");

    // Tamper one lane of the ruleset chain's ROOT, then re-publish the PIs from the row so the
    // `PiBinding` constraints are satisfied by the tampered value.
    let lane = w.layout.root_cols(CHAIN_RULESET);
    w.row[lane] += BabyBear::new(1);
    w.fill_pis();
    assert!(
        compose_trace_accepts(&desc, &w),
        "the ROW-LOCAL evaluator must be silent here — that silence is what this test exists to \
         cover with the real prover"
    );

    let rows = 2usize;
    let config = ir2_leaf_wrap_config();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_custom_leaf_descriptor_with_state_commitment(
            &desc,
            &w.base_trace(rows),
            &w.pis,
            &config,
        )
    }));
    match res {
        Err(_) | Ok(Err(_)) => {
            eprintln!("COMPOSITION LEAF REJECT: a tampered node8 digest lane had no leaf.");
        }
        Ok(Ok(_)) => panic!(
            "a TAMPERED node8 digest lane minted a foldable leaf — the chip-bus \
                             arm is not binding the digest"
        ),
    }
}
