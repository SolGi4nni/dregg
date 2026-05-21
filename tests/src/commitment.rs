//! Merkle tree and commitment scheme attack tests.
//!
//! These tests verify the integrity of the Merkle commitment layer against:
//! - Second preimage attacks
//! - Path forgery
//! - Non-membership proof forgery
//! - State collision attacks

use pyana_commit::{
    Fact, FactSet, FieldElement, FoldDelta, FoldDeltaBuilder, FoldVerification, MerkleProof,
    MerkleTree, NonMembershipProof, StateCommitment, SurvivalWitness, TokenState, hash_leaf,
    hash_node, verify_fold_chain,
};

// =============================================================================
// 1. Second preimage resistance
// =============================================================================

#[test]
fn distinct_facts_produce_distinct_leaf_hashes() {
    // Generate many pairs of distinct facts and verify their hashes never collide
    for i in 0u64..1000 {
        let fact_a = Fact::unary(
            FieldElement::from_symbol("pred_a"),
            FieldElement::from_u64(i),
        );
        let fact_b = Fact::unary(
            FieldElement::from_symbol("pred_b"),
            FieldElement::from_u64(i),
        );
        let hash_a = hash_leaf(&fact_a.to_bytes());
        let hash_b = hash_leaf(&fact_b.to_bytes());
        assert_ne!(
            hash_a, hash_b,
            "Facts with different predicates at i={i} must have different hashes"
        );
    }
}

#[test]
fn same_predicate_different_terms_no_collision() {
    for i in 0u64..1000 {
        let fact_a = Fact::binary(
            FieldElement::from_symbol("edge"),
            FieldElement::from_u64(i),
            FieldElement::from_u64(i + 1),
        );
        let fact_b = Fact::binary(
            FieldElement::from_symbol("edge"),
            FieldElement::from_u64(i + 1),
            FieldElement::from_u64(i),
        );
        let hash_a = hash_leaf(&fact_a.to_bytes());
        let hash_b = hash_leaf(&fact_b.to_bytes());
        assert_ne!(
            hash_a, hash_b,
            "Facts with swapped terms at i={i} must have different hashes"
        );
    }
}

#[test]
fn collision_resistance_random_facts() {
    // Generate 10000 random facts and verify no hash collisions
    let mut hashes = std::collections::HashSet::new();
    let mut buf = [0u8; 16];
    for i in 0u64..10000 {
        let fact = Fact::binary(
            FieldElement::from_u64(i),
            FieldElement::from_u64(i * 7 + 3),
            FieldElement::from_u64(i * 13 + 7),
        );
        let h = hash_leaf(&fact.to_bytes());
        assert!(
            hashes.insert(h),
            "Hash collision found at i={i} (astronomically unlikely with BLAKE3)"
        );
    }
}

#[test]
fn node_hash_is_order_dependent() {
    // Verify that hash_node is not commutative (child order matters)
    let child_a = [1u8; 32];
    let child_b = [2u8; 32];
    let child_c = [3u8; 32];
    let child_d = [4u8; 32];

    let h1 = hash_node(&[child_a, child_b, child_c, child_d]);
    let h2 = hash_node(&[child_b, child_a, child_c, child_d]);
    let h3 = hash_node(&[child_d, child_c, child_b, child_a]);

    assert_ne!(h1, h2, "Swapping children 0,1 must change hash");
    assert_ne!(h1, h3, "Reversing child order must change hash");
    assert_ne!(h2, h3, "Different orderings must produce different hashes");
}

// =============================================================================
// 2. Path forgery attacks
// =============================================================================

#[test]
fn forged_membership_proof_rejected() {
    let mut fs = FactSet::new();
    let fact = Fact::from_symbols("owns", &["alice", "file"]);
    fs.insert(fact);
    let root = fs.root();

    // Get a real proof
    let real_proof = fs.membership_proof(&fact).unwrap();

    // Forge a proof with wrong siblings
    let mut forged = real_proof.clone();
    if let Some(sibs) = forged.siblings.first_mut() {
        sibs[0] = [0xDE; 32]; // tamper with first sibling
    }

    assert!(
        !FactSet::verify_membership(&root, &fact, &forged),
        "Forged membership proof must be rejected"
    );
}

#[test]
fn proof_for_wrong_fact_rejected() {
    let mut fs = FactSet::new();
    let fact_a = Fact::from_symbols("owns", &["alice", "file1"]);
    let fact_b = Fact::from_symbols("owns", &["alice", "file2"]);
    fs.insert(fact_a);
    fs.insert(fact_b);
    let root = fs.root();

    // Get proof for fact_a
    let proof_a = fs.membership_proof(&fact_a).unwrap();

    // Try to use proof_a to verify fact_b -> must fail
    assert!(
        !FactSet::verify_membership(&root, &fact_b, &proof_a),
        "Proof for fact_a must not verify fact_b"
    );
}

#[test]
fn proof_against_wrong_root_rejected() {
    let mut fs = FactSet::new();
    let fact = Fact::from_symbols("access", &["resource"]);
    fs.insert(fact);
    let real_root = fs.root();
    let proof = fs.membership_proof(&fact).unwrap();

    // Verify against wrong root
    let fake_root = [0xFF; 32];
    assert_ne!(real_root, fake_root);
    assert!(
        !FactSet::verify_membership(&fake_root, &fact, &proof),
        "Proof must not verify against wrong root"
    );
}

#[test]
fn empty_path_proof_rejected() {
    let mut fs = FactSet::new();
    let fact = Fact::from_symbols("test", &["value"]);
    fs.insert(fact);
    let root = fs.root();

    // Construct a bogus proof with empty path
    let fake_proof = pyana_commit::MerkleProof {
        leaf_hash: hash_leaf(&fact.to_bytes()),
        path_indices: vec![],
        siblings: vec![],
    };

    assert!(
        !FactSet::verify_membership(&root, &fact, &fake_proof),
        "Proof with empty path must be rejected"
    );
}

#[test]
fn proof_with_invalid_path_indices_rejected() {
    let mut fs = FactSet::new();
    let fact = Fact::from_symbols("data", &["x"]);
    fs.insert(fact);
    let root = fs.root();

    let real_proof = fs.membership_proof(&fact).unwrap();

    // Tamper: set a path index to 4 (valid range is 0-3 for 4-ary tree)
    let mut bad_proof = real_proof.clone();
    if let Some(idx) = bad_proof.path_indices.first_mut() {
        *idx = 4; // invalid!
    }

    assert!(
        !FactSet::verify_membership(&root, &fact, &bad_proof),
        "Proof with out-of-range path index must be rejected"
    );
}

// =============================================================================
// 3. Non-membership forgery
// =============================================================================

#[test]
fn forged_non_membership_for_present_fact() {
    let mut fs = FactSet::new();
    let fact = Fact::from_symbols("revoked", &["token-123"]);
    fs.insert(fact);
    let root = fs.root();

    // The fact IS present, so we cannot get a legitimate non-membership proof
    assert!(
        fs.non_membership_proof(&fact).is_none(),
        "Cannot prove non-membership for a present fact"
    );
}

#[test]
fn non_membership_proof_invalid_after_insertion() {
    let mut fs = FactSet::new();
    let fact_a = Fact::from_symbols("item", &["a"]);
    let fact_b = Fact::from_symbols("item", &["b"]);
    fs.insert(fact_a);

    let root_before = fs.root();
    let nm_proof = fs.non_membership_proof(&fact_b).unwrap();

    // The proof verifies against the current root
    assert!(FactSet::verify_non_membership(
        &root_before,
        &fact_b,
        &nm_proof
    ));

    // Now insert fact_b
    fs.insert(fact_b);
    let root_after = fs.root();

    // The old non-membership proof should NOT verify against the new root
    assert_ne!(root_before, root_after);
    assert!(
        !FactSet::verify_non_membership(&root_after, &fact_b, &nm_proof),
        "Old non-membership proof must fail after the fact is inserted"
    );
}

#[test]
fn non_membership_proof_with_tampered_neighbors() {
    let mut fs = FactSet::new();
    fs.insert(Fact::from_symbols("x", &["1"]));
    fs.insert(Fact::from_symbols("x", &["3"]));
    let root = fs.root();

    let absent = Fact::from_symbols("x", &["2"]);
    let nm_proof = fs.non_membership_proof(&absent).unwrap();

    // Verify legitimate proof works
    assert!(FactSet::verify_non_membership(&root, &absent, &nm_proof));

    // Tamper with a neighbor's proof
    let mut tampered = nm_proof.clone();
    if let Some((_, _, ref mut proof)) = tampered.left_neighbor {
        if let Some(sibs) = proof.siblings.first_mut() {
            sibs[0] = [0xBB; 32];
        }
    }

    assert!(
        !FactSet::verify_non_membership(&root, &absent, &tampered),
        "Tampered non-membership proof must be rejected"
    );
}

#[test]
fn non_membership_claim_for_revoked_token_fails() {
    // Simulate: a revoked token trying to claim it's not revoked
    let mut fs = FactSet::new();
    let revoked_fact = Fact::from_symbols("revoked", &["evil-token"]);
    fs.insert(revoked_fact);

    // Attacker cannot produce a non-membership proof
    assert!(fs.non_membership_proof(&revoked_fact).is_none());
}

// =============================================================================
// 4. State collision attacks
// =============================================================================

#[test]
fn different_fact_sets_different_roots() {
    // Two token states with different facts must have different roots
    let mut state1 = TokenState::new();
    state1.add_fact(Fact::from_symbols("can_read", &["alice", "secret"]));

    let mut state2 = TokenState::new();
    state2.add_fact(Fact::from_symbols("can_write", &["alice", "secret"]));

    assert_ne!(
        state1.root(),
        state2.root(),
        "Different fact sets must have different roots"
    );
}

#[test]
fn random_state_collision_sampling() {
    // Generate 1000 distinct token states and verify all roots are unique
    let mut roots = std::collections::HashSet::new();
    for i in 0u64..1000 {
        let mut state = TokenState::new();
        state.add_fact(Fact::unary(
            FieldElement::from_u64(i),
            FieldElement::from_u64(i * 31 + 7),
        ));
        state.add_fact(Fact::binary(
            FieldElement::from_u64(i + 1000),
            FieldElement::from_u64(i * 17),
            FieldElement::from_u64(i * 23),
        ));
        let r = state.root();
        assert!(
            roots.insert(r),
            "State collision at i={i} (should be astronomically unlikely)"
        );
    }
}

#[test]
fn insertion_order_independence() {
    // Same facts inserted in different orders produce the same root
    let facts = vec![
        Fact::from_symbols("a", &["1"]),
        Fact::from_symbols("b", &["2"]),
        Fact::from_symbols("c", &["3"]),
        Fact::from_symbols("d", &["4"]),
        Fact::from_symbols("e", &["5"]),
    ];

    let mut state_fwd = TokenState::new();
    for f in &facts {
        state_fwd.add_fact(*f);
    }

    let mut state_rev = TokenState::new();
    for f in facts.iter().rev() {
        state_rev.add_fact(*f);
    }

    assert_eq!(
        state_fwd.root(),
        state_rev.root(),
        "Insertion order must not affect the root"
    );
}

// =============================================================================
// 5. Fold delta attacks
// =============================================================================

#[test]
fn fold_delta_with_tampered_removal_proof() {
    let mut state = TokenState::new();
    state.add_fact(Fact::from_symbols("owns", &["alice", "file1"]));
    state.add_fact(Fact::from_symbols("owns", &["alice", "file2"]));

    let to_remove = Fact::from_symbols("owns", &["alice", "file1"]);
    let mut delta = FoldDeltaBuilder::new(state)
        .remove_fact(to_remove)
        .build()
        .unwrap();

    // Tamper with the removal proof
    delta.removed[0].1.leaf_hash = [0xEE; 32];

    assert_eq!(
        delta.verify(),
        FoldVerification::InvalidRemovalProof { index: 0 },
        "Tampered removal proof must be detected"
    );
}

#[test]
fn fold_delta_removing_nonexistent_fact() {
    let mut state = TokenState::new();
    state.add_fact(Fact::from_symbols("owns", &["alice", "file1"]));

    let nonexistent = Fact::from_symbols("owns", &["bob", "file2"]);
    let result = FoldDeltaBuilder::new(state)
        .remove_fact(nonexistent)
        .build();

    assert!(
        result.is_none(),
        "Cannot build delta removing a nonexistent fact"
    );
}

#[test]
fn fold_chain_broken_by_reordering() {
    let mut state0 = TokenState::new();
    state0.add_fact(Fact::from_symbols("a", &["1"]));
    state0.add_fact(Fact::from_symbols("b", &["2"]));
    state0.add_fact(Fact::from_symbols("c", &["3"]));

    let delta1 = FoldDeltaBuilder::new(state0.clone())
        .remove_fact(Fact::from_symbols("c", &["3"]))
        .build()
        .unwrap();

    let state1 = delta1.reconstruct_new_state(&state0).unwrap();

    let delta2 = FoldDeltaBuilder::new(state1)
        .remove_fact(Fact::from_symbols("b", &["2"]))
        .build()
        .unwrap();

    // Correct order verifies
    assert!(verify_fold_chain(&[delta1.clone(), delta2.clone()]));

    // Reversed order fails (delta2's old_root != delta1's new_root)
    assert!(
        !verify_fold_chain(&[delta2, delta1]),
        "Reversed fold chain must fail verification"
    );
}

#[test]
fn fold_delta_with_tampered_old_root() {
    let mut state = TokenState::new();
    state.add_fact(Fact::from_symbols("x", &["1"]));
    state.add_fact(Fact::from_symbols("y", &["2"]));

    let mut delta = FoldDeltaBuilder::new(state)
        .remove_fact(Fact::from_symbols("x", &["1"]))
        .build()
        .unwrap();

    // Tamper with old_root
    delta.old_root = [0xAA; 32];

    assert!(
        !delta.apply_and_verify(),
        "Delta with tampered old_root must fail"
    );
}

#[test]
fn fold_delta_with_tampered_new_root() {
    let mut state = TokenState::new();
    state.add_fact(Fact::from_symbols("x", &["1"]));
    state.add_fact(Fact::from_symbols("y", &["2"]));

    let mut delta = FoldDeltaBuilder::new(state)
        .remove_fact(Fact::from_symbols("x", &["1"]))
        .build()
        .unwrap();

    // Tamper with new_root
    delta.new_root = [0xBB; 32];

    assert!(
        !delta.apply_and_verify(),
        "Delta with tampered new_root must fail"
    );
}

#[test]
fn fold_delta_adding_capability_without_check() {
    // Verify that you cannot ADD a fact via fold (only remove or add checks)
    let mut state = TokenState::new();
    state.add_fact(Fact::from_symbols("can_read", &["alice", "public"]));

    // You can only narrow - the FoldDeltaBuilder only supports remove_fact and add_check
    // There is no "add_fact" method, which is the enforcement mechanism.
    // We test the verify() path by constructing a malformed delta manually
    let delta = FoldDelta {
        old_root: state.root(),
        new_root: [0x42; 32], // fake root that would include extra facts
        removed: vec![],
        added_checks: vec![], // no changes at all
        surviving_proof: SurvivalWitness {
            old_root: state.root(),
            new_root: [0x42; 32],
            unchanged_subtrees: vec![],
        },
    };

    assert_eq!(
        delta.verify(),
        FoldVerification::EmptyDelta,
        "Empty delta (no narrowing) must be rejected"
    );
}
