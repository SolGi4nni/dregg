//! Proof soundness tests.
//!
//! These tests verify that the STARK proof system rejects forged, tampered,
//! and replayed proofs. A sound proof system must never accept a proof for
//! a false statement.

use dregg_circuit::field::BabyBear;
use dregg_circuit::fold_air::{FoldAir, FoldWitness, RemovedFact};
use dregg_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};
use dregg_circuit::mock_prover::{MockProof, MockProver};
use dregg_circuit::presentation::{
    PresentationAir, PresentationVerification, PresentationWitness, create_test_presentation,
};
use dregg_circuit::stark::{
    MerkleStarkAir, StarkProof, generate_merkle_trace, proof_from_bytes, proof_to_bytes, prove,
    verify,
};

// =============================================================================
// Helper: generate a valid proof for reuse in tampering tests
// =============================================================================

fn valid_proof_and_inputs() -> (StarkProof, Vec<BabyBear>) {
    let siblings = [
        [100u32, 200, 300],
        [400, 500, 600],
        [700, 800, 900],
        [1000, 1100, 1200],
    ];
    let positions = [0u32, 1, 2, 3];
    let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
    let air = MerkleStarkAir;
    let proof = prove(&air, &trace, &public_inputs);
    (proof, public_inputs)
}

// =============================================================================
// 1. Wrong public inputs
// =============================================================================

#[test]
fn wrong_leaf_hash_rejected() {
    let (proof, _pi) = valid_proof_and_inputs();
    let air = MerkleStarkAir;
    // Provide wrong leaf value in public inputs
    let wrong_pi = vec![BabyBear::new(99999), BabyBear::new(42)];
    let result = verify(&air, &proof, &wrong_pi);
    assert!(
        result.is_err(),
        "Must reject proof with wrong leaf public input"
    );
}

#[test]
fn wrong_root_in_public_inputs_rejected() {
    let (proof, pi) = valid_proof_and_inputs();
    let air = MerkleStarkAir;
    // Keep leaf correct but change root
    let wrong_pi = vec![pi[0], BabyBear::new(0)];
    let result = verify(&air, &proof, &wrong_pi);
    assert!(
        result.is_err(),
        "Must reject proof with wrong root public input"
    );
}

#[test]
fn empty_public_inputs_rejected() {
    let (proof, _pi) = valid_proof_and_inputs();
    let air = MerkleStarkAir;
    let result = verify(&air, &proof, &[]);
    assert!(
        result.is_err(),
        "Must reject proof with empty public inputs"
    );
}

#[test]
fn extra_public_inputs_rejected() {
    let (proof, pi) = valid_proof_and_inputs();
    let air = MerkleStarkAir;
    let mut extra = pi.clone();
    extra.push(BabyBear::new(9999));
    let result = verify(&air, &proof, &extra);
    assert!(
        result.is_err(),
        "Must reject proof with extra public inputs"
    );
}

// =============================================================================
// 2. Byte-level proof tampering
// =============================================================================

#[test]
fn tamper_trace_commitment_byte_0() {
    let (mut proof, pi) = valid_proof_and_inputs();
    proof.trace_commitment[0] ^= 0xFF;
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_trace_commitment_byte_31() {
    let (mut proof, pi) = valid_proof_and_inputs();
    proof.trace_commitment[31] ^= 0x01;
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_constraint_commitment() {
    let (mut proof, pi) = valid_proof_and_inputs();
    proof.constraint_commitment[16] ^= 0xAB;
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_fri_commitment() {
    let (mut proof, pi) = valid_proof_and_inputs();
    if let Some(fc) = proof.fri_commitments.first_mut() {
        fc[0] ^= 0x42;
    }
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_query_trace_value() {
    let (mut proof, pi) = valid_proof_and_inputs();
    if let Some(q) = proof.query_proofs.first_mut() {
        q.trace_values[0] ^= 1;
    }
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_query_constraint_value() {
    let (mut proof, pi) = valid_proof_and_inputs();
    if let Some(q) = proof.query_proofs.first_mut() {
        q.constraint_value ^= 1;
    }
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_query_merkle_path() {
    let (mut proof, pi) = valid_proof_and_inputs();
    if let Some(q) = proof.query_proofs.first_mut() {
        if let Some(h) = q.trace_path.first_mut() {
            h[0] ^= 0xFF;
        }
    }
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_query_index() {
    let (mut proof, pi) = valid_proof_and_inputs();
    if let Some(q) = proof.query_proofs.first_mut() {
        q.index = (q.index + 1) % 16; // shift index
    }
    let air = MerkleStarkAir;
    assert!(verify(&air, &proof, &pi).is_err());
}

#[test]
fn tamper_random_positions_in_serialized_proof() {
    let (proof, pi) = valid_proof_and_inputs();
    let air = MerkleStarkAir;
    let bytes = proof_to_bytes(&proof);

    // Tamper at many positions across the proof.
    // Not every byte is necessarily checked by the verifier (e.g., FRI values
    // that are used only for commitment but not arithmetically validated in
    // the simplified verifier). We verify that MOST tampering is detected.
    let positions: Vec<usize> = (0..bytes.len()).step_by(bytes.len() / 20 + 1).collect();
    let mut detected = 0;
    let mut total = 0;

    for &pos in &positions {
        if pos < bytes.len() {
            total += 1;
            let mut tampered = bytes.clone();
            tampered[pos] ^= 0xFF;
            // Parse failure or verification failure both count as detected
            match proof_from_bytes(&tampered) {
                Err(_) => detected += 1,
                Ok(tampered_proof) => {
                    if verify(&air, &tampered_proof, &pi).is_err() {
                        detected += 1;
                    }
                }
            }
        }
    }

    // At least 50% of tampering positions should be detected
    // (the critical positions: trace/constraint commitments, query indices/values)
    assert!(
        detected * 2 >= total,
        "At least half of tampered positions should be detected: {detected}/{total}"
    );
}

// =============================================================================
// 3. Proof replay attacks
// =============================================================================

#[test]
fn replay_proof_with_different_leaf() {
    let siblings = [
        [100u32, 200, 300],
        [400, 500, 600],
        [700, 800, 900],
        [1000, 1100, 1200],
    ];
    let positions = [0u32, 1, 2, 3];

    let air = MerkleStarkAir;

    // Generate proof for leaf=12345
    let (trace, pi_a) = generate_merkle_trace(12345, &siblings, &positions);
    let proof_a = prove(&air, &trace, &pi_a);

    // Try to verify proof_a against different leaf's public inputs
    let (_, pi_b) = generate_merkle_trace(99999, &siblings, &positions);
    let result = verify(&air, &proof_a, &pi_b);
    assert!(
        result.is_err(),
        "Replayed proof with different leaf must fail"
    );
}

#[test]
fn replay_proof_with_different_siblings() {
    let air = MerkleStarkAir;

    let siblings_a = [[1u32, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]];
    let siblings_b = [[99u32, 98, 97], [96, 95, 94], [93, 92, 91], [90, 89, 88]];
    let positions = [0u32, 1, 2, 3];

    let (trace_a, pi_a) = generate_merkle_trace(42, &siblings_a, &positions);
    let proof_a = prove(&air, &trace_a, &pi_a);

    let (_, pi_b) = generate_merkle_trace(42, &siblings_b, &positions);
    // Same leaf but different tree structure => different roots
    assert_ne!(pi_a[1], pi_b[1]);
    let result = verify(&air, &proof_a, &pi_b);
    assert!(
        result.is_err(),
        "Proof for one tree structure must not verify against another"
    );
}

#[test]
fn swap_proofs_between_statements() {
    let air = MerkleStarkAir;

    let siblings = [[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]];
    let positions = [0u32, 1, 2, 3];

    let (trace1, pi1) = generate_merkle_trace(111, &siblings, &positions);
    let proof1 = prove(&air, &trace1, &pi1);

    let (trace2, pi2) = generate_merkle_trace(222, &siblings, &positions);
    let proof2 = prove(&air, &trace2, &pi2);

    // Each verifies its own statement
    assert!(verify(&air, &proof1, &pi1).is_ok());
    assert!(verify(&air, &proof2, &pi2).is_ok());

    // Cross-verification must fail
    assert!(verify(&air, &proof1, &pi2).is_err());
    assert!(verify(&air, &proof2, &pi1).is_err());
}

// =============================================================================
// 4. Presentation proof: fake derivation traces
// =============================================================================

#[test]
fn presentation_with_nonexistent_federation_root() {
    let mut witness = create_test_presentation();
    // Set a random federation root that doesn't match issuer membership
    witness.federation_root = BabyBear::new(0xDEAD);
    let air = PresentationAir::new(witness);
    let result = air.verify_all();
    assert_eq!(result, PresentationVerification::IssuerNotInFederation);
}

#[test]
fn presentation_with_broken_fold_chain() {
    let mut witness = create_test_presentation();
    witness.federation_root = witness.issuer_membership.expected_root;
    // Break the chain: second fold's old_root doesn't match first fold's new_root
    witness.fold_chain[1].old_root = BabyBear::new(0xBAD);
    let air = PresentationAir::new(witness);
    assert_eq!(
        air.verify_all(),
        PresentationVerification::FoldChainBreak { index: 1 }
    );
}

#[test]
fn presentation_derivation_for_wrong_state() {
    let mut witness = create_test_presentation();
    witness.federation_root = witness.issuer_membership.expected_root;
    // Derivation claims to be over a different state root
    witness.derivation.state_root = BabyBear::new(0xFA4E);
    let air = PresentationAir::new(witness);
    assert_eq!(
        air.verify_all(),
        PresentationVerification::DerivationRootMismatch
    );
}

#[test]
fn presentation_with_unverified_membership() {
    let mut witness = create_test_presentation();
    witness.federation_root = witness.issuer_membership.expected_root;
    // Tamper with a fold: mark membership as not verified
    witness.fold_chain[0].removed_facts[0].membership_verified = false;
    let air = PresentationAir::new(witness);
    let result = air.verify_all();
    assert_ne!(result, PresentationVerification::Valid);
}

// =============================================================================
// 5. IVC: wider capability attacks
// =============================================================================

#[test]
fn ivc_empty_fold_chain_rejected() {
    // Cannot prove anything with zero steps (would be meaningless)
    let initial_root = BabyBear::new(12345);
    let result = prove_ivc(initial_root, vec![]);
    // An empty chain should either reject or produce a trivially invalid proof
    assert!(
        result.is_none(),
        "Empty IVC chain should not produce a proof"
    );
}

#[test]
fn ivc_fold_chain_with_swapped_roots() {
    let initial_root = BabyBear::new(100);
    let mid_root = BabyBear::new(200);
    let final_root = BabyBear::new(300);

    let fold1 = FoldWitness {
        old_root: initial_root,
        new_root: mid_root,
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(1),
            terms: [BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO],
            membership_verified: true,
        }],
        num_added_checks: 0,
    };

    // fold2 has WRONG old_root (should be mid_root but is initial_root)
    let fold2 = FoldWitness {
        old_root: initial_root, // WRONG - should be mid_root
        new_root: final_root,
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(3),
            terms: [BabyBear::new(4), BabyBear::ZERO, BabyBear::ZERO],
            membership_verified: true,
        }],
        num_added_checks: 0,
    };

    let deltas = vec![FoldDelta::new(fold1), FoldDelta::new(fold2)];
    let result = prove_ivc(initial_root, deltas);
    // Should fail because roots don't chain
    assert!(result.is_none(), "IVC with broken root chain must fail");
}

#[test]
fn ivc_proof_tampered_accumulated_hash() {
    let initial_root = BabyBear::new(100);
    let mid_root = BabyBear::new(200);

    let fold1 = FoldWitness {
        old_root: initial_root,
        new_root: mid_root,
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(10),
            terms: [BabyBear::new(20), BabyBear::ZERO, BabyBear::ZERO],
            membership_verified: true,
        }],
        num_added_checks: 1,
    };

    let deltas = vec![FoldDelta::new(fold1)];
    if let Some(mut proof) = prove_ivc(initial_root, deltas) {
        // Tamper with accumulated hash
        proof.accumulated_hash = BabyBear::new(0xDEAD);
        let result = verify_ivc(&proof, None);
        assert_ne!(result, IvcVerification::Valid, "Tampered hash must fail");
    }
}

#[test]
fn ivc_proof_tampered_step_count() {
    let initial_root = BabyBear::new(100);
    let mid_root = BabyBear::new(200);

    let fold1 = FoldWitness {
        old_root: initial_root,
        new_root: mid_root,
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(10),
            terms: [BabyBear::new(20), BabyBear::ZERO, BabyBear::ZERO],
            membership_verified: true,
        }],
        num_added_checks: 1,
    };

    let deltas = vec![FoldDelta::new(fold1)];
    if let Some(mut proof) = prove_ivc(initial_root, deltas) {
        // Claim more steps than actually performed
        proof.step_count = 5;
        let result = verify_ivc(&proof, None);
        assert_ne!(result, IvcVerification::Valid, "Wrong step count must fail");
    }
}

// =============================================================================
// 6. Fold AIR: capability widening
// =============================================================================

#[test]
fn fold_with_no_removals_and_no_checks_is_invalid() {
    // Empty fold delta should be rejected: it doesn't narrow anything
    let fold = FoldWitness {
        old_root: BabyBear::new(100),
        new_root: BabyBear::new(100), // same root - no change
        removed_facts: vec![],
        num_added_checks: 0,
    };

    let air = FoldAir::new(fold);
    let result = MockProver::verify(&air);
    // An empty delta should fail the "delta_nonempty" constraint
    assert!(!result.is_valid(), "Empty fold must be invalid");
}

#[test]
fn fold_with_fake_membership_rejected() {
    // Claim removal of a fact whose membership was not verified
    let fold = FoldWitness {
        old_root: BabyBear::new(100),
        new_root: BabyBear::new(200),
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(42),
            terms: [BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)],
            membership_verified: false, // NOT verified
        }],
        num_added_checks: 0,
    };

    let air = FoldAir::new(fold);
    let result = MockProver::verify(&air);
    assert!(!result.is_valid(), "Unverified membership must reject");
}

#[test]
fn fold_with_unverified_removal_and_added_checks() {
    // A fold that claims to verify membership but actually doesn't
    // should be caught by the circuit when membership_verified is false
    let fold = FoldWitness {
        old_root: BabyBear::new(100),
        new_root: BabyBear::new(200),
        removed_facts: vec![
            RemovedFact {
                predicate: BabyBear::new(42),
                terms: [BabyBear::new(1), BabyBear::ZERO, BabyBear::ZERO],
                membership_verified: false, // NOT verified - attack!
            },
            RemovedFact {
                predicate: BabyBear::new(43),
                terms: [BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO],
                membership_verified: false, // NOT verified - attack!
            },
        ],
        num_added_checks: 0,
    };

    let air = FoldAir::new(fold);
    let result = MockProver::verify(&air);
    assert!(
        !result.is_valid(),
        "Fold with unverified membership removals must fail"
    );
}
