//! Byte pin and adversarial real-prover gate for deployed sorted-tree non-revocation.
//!
//! Constraint authorship is exclusively Lean's
//! `Dregg2/Circuit/Emit/NonRevocationAdjacencyEmit.lean`. This gate pins the exact emitted bytes,
//! checks production dispatch, proves a genuine depth-4 / 16-leaf witness, and requires the real
//! descriptor prover/verifier to refute every security-relevant forgery.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::revocation::{
    DslRevocationTree, NonMembershipWitnessDsl, TREE_DEPTH, prove_non_revocation_p3,
    verify_non_revocation_p3,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::non_revocation_adjacency_witness::{
    NON_REVOCATION_ADJACENCY_NAME, NONREV_ADJ_PI_COUNT, NONREV_ADJ_WIDTH, PI_QUERIED_ITEM, PI_ROOT,
    non_revocation_adjacency_witness,
};
use dregg_circuit::refusal::{Outcome, classify};

/// Exact `DescriptorIR2.emitVmJson2 nonRevocationAdjacencyDesc` bytes emitted by
/// `metatheory/EmitNonRevocationAdjacency.lean`.
const GOLDEN_JSON: &str = r#"{"name":"dregg-non-revocation-adjacency::poseidon2-fact-v1","ir":2,"trace_width":37,"public_input_count":2,"tables":[{"id":2,"name":"range","arity":1,"sem":"range","bits":30}],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":3},{"t":"var","v":4},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":5},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23},{"t":"var","v":24}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":16}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":10}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":11},{"t":"var","v":12},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":13},{"t":"var","v":25},{"t":"var","v":26},{"t":"var","v":27},{"t":"var","v":28},{"t":"var","v":29},{"t":"var","v":30},{"t":"var","v":31}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":14}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":16}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":13}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":15}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":17},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":16}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":17}}}},{"t":"pi_binding","row":"last","col":5,"pi_index":0},{"t":"pi_binding","row":"last","col":13,"pi_index":0},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}},{"t":"boundary","row":"first","body":{"t":"var","v":6}},{"t":"boundary","row":"first","body":{"t":"var","v":14}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":7}},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":10}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":16}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":14}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":16}}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":33},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}}},"r":{"t":"var","v":0}},"r":{"t":"const","v":1}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":34},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":32}},"r":{"t":"const","v":1}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":35},"r":{"t":"var","v":33}},"r":{"t":"const","v":-1006632959}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":36},"r":{"t":"var","v":34}},"r":{"t":"const","v":-1006632959}}},{"t":"lookup","table":2,"tuple":[{"t":"var","v":35}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":36}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":33}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":34}]},{"t":"pi_binding","row":"first","col":32,"pi_index":1}],"hash_sites":[],"ranges":[]}"#;

fn tree() -> DslRevocationTree {
    DslRevocationTree::new(
        [100u32, 300, 500, 700, 900]
            .into_iter()
            .map(BabyBear::new)
            .collect(),
        TREE_DEPTH,
    )
}

fn honest_fixture() -> (DslRevocationTree, NonMembershipWitnessDsl) {
    let tree = tree();
    let witness = tree
        .prove_non_membership(&BabyBear::new(400))
        .expect("400 is bracketed by the adjacent deployed leaves 300 and 500");
    (tree, witness)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("non-revocation adjacency rejection", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) | Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

#[test]
fn lean_bytes_parse_dispatch_and_pin_the_composition_shape() {
    let checked_in =
        include_str!("../../circuit/descriptors/by-name/non-revocation-adjacency.json");
    assert_eq!(
        GOLDEN_JSON,
        checked_in
            .strip_suffix('\n')
            .expect("the checked-in JSON is one newline-terminated emitted record"),
        "checked-in artifact must equal the Lean emitter's pinned bytes"
    );
    let parsed = parse_vm_descriptor2(GOLDEN_JSON).expect("Lean bytes parse as IR-v2");
    let dispatched = descriptor_by_name(NON_REVOCATION_ADJACENCY_NAME)
        .expect("production registry dispatches the composed descriptor");
    assert_eq!(
        parsed, dispatched,
        "dispatch must serve the pinned artifact"
    );
    assert_eq!(parsed.trace_width, NONREV_ADJ_WIDTH);
    assert_eq!(parsed.public_input_count, NONREV_ADJ_PI_COUNT);
    assert_eq!(parsed.constraints.len(), 39);

    let fact_node_lookups = parsed
        .constraints
        .iter()
        .filter(|constraint| {
            matches!(
                constraint,
                VmConstraint2::Lookup(lookup)
                    if matches!(lookup.tuple.first(), Some(LeanExpr::Const(7)))
            )
        })
        .count();
    assert_eq!(
        fact_node_lookups, 2,
        "two parallel fact-domain membership paths"
    );
    let root_pins = parsed
        .constraints
        .iter()
        .filter(|constraint| {
            matches!(
                constraint,
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::Last,
                    pi_index: PI_ROOT,
                    ..
                })
            )
        })
        .count();
    assert_eq!(
        root_pins, 2,
        "both private paths must reach the same public root"
    );
}

#[test]
fn deployed_depth_four_honest_proof_uses_four_genuine_path_rows() {
    assert_eq!(
        TREE_DEPTH, 4,
        "the deployed tree remains depth 4 / 16 leaves"
    );
    let (tree, witness) = honest_fixture();
    let (trace, pis) = non_revocation_adjacency_witness(&witness, tree.root())
        .expect("depth-4 production witness builds");
    assert_eq!(trace.len(), TREE_DEPTH, "one row per real tree level");
    assert!(
        trace.windows(2).all(|rows| rows[0] != rows[1]),
        "the path rows are folds, not clones"
    );
    assert_eq!(pis[PI_ROOT], tree.root());
    assert_eq!(pis[PI_QUERIED_ITEM], BabyBear::new(400));

    let proof = prove_non_revocation_p3(&tree, BabyBear::new(400))
        .expect("the deployed depth-4 witness proves through the Lean descriptor");
    verify_non_revocation_p3(&proof, tree.root(), BabyBear::new(400))
        .expect("the Lean-emitted descriptor proof re-verifies");
}

#[test]
fn forged_brackets_nonadjacency_and_merkle_data_are_all_refuted() {
    let desc = descriptor_by_name(NON_REVOCATION_ADJACENCY_NAME).expect("dispatch");
    let (tree, honest) = honest_fixture();
    let (honest_trace, honest_pis) =
        non_revocation_adjacency_witness(&honest, tree.root()).expect("honest witness");
    assert!(
        !rejects(&desc, &honest_trace, &honest_pis),
        "honest control must accept"
    );

    let mut at_lower = honest.clone();
    at_lower.ancestor_hash = at_lower.left_neighbor;
    let (trace, pis) =
        non_revocation_adjacency_witness(&at_lower, tree.root()).expect("mechanical witness");
    assert!(
        rejects(&desc, &trace, &pis),
        "x <= L must be REJECTED by the direct diff range tooth"
    );

    let mut at_upper = honest.clone();
    at_upper.ancestor_hash = at_upper.right_neighbor;
    let (trace, pis) =
        non_revocation_adjacency_witness(&at_upper, tree.root()).expect("mechanical witness");
    assert!(
        rejects(&desc, &trace, &pis),
        "x >= R must be REJECTED by the direct diff range tooth"
    );

    // Both leaves are genuine members under the same root, but positions 2 and 4 are not adjacent.
    let (left_siblings, left_directions) = tree.prove_membership(2).expect("member 2");
    let (right_siblings, right_directions) = tree.prove_membership(4).expect("member 4");
    let wide = NonMembershipWitnessDsl {
        ancestor_hash: BabyBear::new(400),
        left_neighbor: BabyBear::new(300),
        right_neighbor: BabyBear::new(700),
        left_siblings,
        left_directions,
        right_siblings,
        right_directions,
        left_tree_position: 2,
        right_tree_position: 4,
    };
    let (trace, pis) = non_revocation_adjacency_witness(&wide, tree.root()).expect("wide witness");
    assert!(
        rejects(&desc, &trace, &pis),
        "two real but non-adjacent members must be REJECTED"
    );

    let mut forged_leaf = honest.clone();
    forged_leaf.left_neighbor += BabyBear::ONE;
    let (trace, pis) =
        non_revocation_adjacency_witness(&forged_leaf, tree.root()).expect("forged leaf trace");
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged leaf not under the root must be REJECTED"
    );

    let mut forged_sibling = honest.clone();
    forged_sibling.left_siblings[0] += BabyBear::ONE;
    let (trace, pis) = non_revocation_adjacency_witness(&forged_sibling, tree.root())
        .expect("forged sibling trace");
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged co-path sibling must be REJECTED"
    );

    let mut forged_root = honest_pis.clone();
    forged_root[PI_ROOT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &honest_trace, &forged_root),
        "a forged public root must be REJECTED"
    );
}
