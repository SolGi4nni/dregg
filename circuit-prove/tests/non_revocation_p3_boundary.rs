//! Public-API boundary gate for deployed Lean-emitted non-revocation.
//!
//! Raw adversarial traces are covered by `non_revocation_adjacency_emit_gate`.
//! This sibling keeps the externally callable producer/verifier contract honest:
//! a genuine depth-4 non-member accepts, committed members cannot acquire a
//! witness, and both public inputs remain load-bearing.

use dregg_circuit::dsl::revocation::{
    DslRevocationTree, TREE_DEPTH, prove_non_revocation_p3, verify_non_revocation_p3,
};
use dregg_circuit::field::BabyBear;

fn tree() -> DslRevocationTree {
    DslRevocationTree::new(
        [100u32, 300, 500, 700]
            .into_iter()
            .map(BabyBear::new)
            .collect(),
        TREE_DEPTH,
    )
}

#[test]
fn honest_depth_four_non_member_accepts() {
    assert_eq!(TREE_DEPTH, 4, "the deployed revocation tree stays depth 4");
    let tree = tree();
    let queried = BabyBear::new(400);
    let proof = prove_non_revocation_p3(&tree, queried)
        .expect("an honestly bracketed non-member must prove");
    verify_non_revocation_p3(&proof, tree.root(), queried)
        .expect("the emitted descriptor must accept the honest proof");
}

#[test]
fn public_root_and_queried_item_are_load_bearing() {
    let tree = tree();
    let queried = BabyBear::new(400);
    let proof = prove_non_revocation_p3(&tree, queried).expect("honest proof");

    assert!(
        verify_non_revocation_p3(&proof, tree.root() + BabyBear::ONE, queried).is_err(),
        "a forged public root must be rejected"
    );
    assert!(
        verify_non_revocation_p3(&proof, tree.root(), queried + BabyBear::ONE).is_err(),
        "a forged queried item must be rejected"
    );
}

#[test]
fn api_refuses_committed_members() {
    let tree = tree();
    for member in [100u32, 300, 500, 700].map(BabyBear::new) {
        assert!(
            prove_non_revocation_p3(&tree, member).is_err(),
            "the deployed API must refuse a freshness proof for committed member {member:?}"
        );
    }
}
