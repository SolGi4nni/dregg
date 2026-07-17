//! Proof soundness tests.
//!
//! ⚠ **SCOPE CORRECTION (mock-proof purge, 2026-07-16) — the four `ivc_*` tests that used to live
//! here did NOT test soundness, and were RETIRED with the simulated engine later the same day
//! (`ivc_empty_fold_chain_rejected`, `ivc_fold_chain_with_swapped_roots`,
//! `ivc_proof_tampered_accumulated_hash`, `ivc_proof_tampered_step_count`).**
//! They exercised `dregg_circuit::ivc::{prove_ivc, verify_ivc}` — the **SIMULATED** IVC, whose
//! `verify_ivc` only recomputes a BLAKE3 digest over the proof's OWN public data. Their assertions
//! ("Tampered hash must fail", "broken root chain must fail") pass TRIVIALLY: mutating a stored field
//! breaks the digest match. That is self-consistency, not soundness. **The attack a real prover must
//! withstand is not tampering an existing proof — it is MINTING a consistent fake, and anyone who can call
//! `prove_ivc` can do exactly that for any root walk** (`circuit/src/constraint_prover.rs:5-8` says it of
//! itself: "nothing here is sound against a prover that lies"). So those four tests certified a mock and
//! were never IVC soundness evidence.
//!
//! **The REAL whole-chain soundness teeth live at `circuit-prove/tests/ivc_turn_chain_rotated.rs`**
//! (`k_fold_turn_chain_proves_and_verifies`, `whole_chain_proof_bytes_roundtrip_and_tamper`): a genuine
//! recursive fold over real `FinalizedTurn`s, with forged-digest / forged-count / broken-order /
//! root / descriptor / public / VK / version / truncation all REJECTED — 5/5 passing, byte-pinned to
//! `Emit/EffectVmEmitTurnChainBinding.lean`. The `ivc_*` tests here are now retired WITH the simulated
//! engine (deleted from `circuit/src/ivc.rs` 2026-07-16 — see
//! `circuit-prove/tests/mock_proof_purge_gate.rs`).
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

use dregg_circuit::dsl::fold::{FoldAir, FoldWitness, RemovedFact};
use dregg_circuit::field::BabyBear;
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
