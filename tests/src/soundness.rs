//! Proof soundness tests.
//!
//! These tests verify that the circuit proof system rejects forged, tampered,
//! and inconsistent witnesses. A sound proof system must never accept a proof
//! for a false statement.
//!
//! The low-level hand-STARK Merkle-membership soundness tests that used to live
//! here were retired together with the legacy hand-STARK engine;
//! their coverage now lives in the descriptor-prover emit-gate tests. The
//! IVC / fold / presentation soundness checks below exercise the higher-level
//! circuit witnesses directly.

use dregg_circuit::field::BabyBear;
use dregg_circuit::fold_air::{FoldAir, FoldWitness, RemovedFact};
use dregg_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};
use dregg_circuit::mock_prover::MockProver;
use dregg_circuit::presentation::{
    PresentationAir, PresentationVerification, create_test_presentation,
};

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
