//! Privacy unlinkability integration test: multiple presentations of the same token
//! must not be correlatable by a colluding set of verifiers.
//!
//! The privacy model requires:
//! 1. presentation_tag differs per presentation (fresh randomness each time).
//! 2. fact_commitments differ when blinding is used.
//! 3. The issuer membership proof uses blinded ring mode (different blinded_leaf each time).
//! 4. No fixed identifier leaks through public inputs.

use dregg_bridge::present::{Predicate, prove_predicate_for_fact, verify_predicate_proof};
use dregg_circuit::BabyBear;
use dregg_circuit::dsl::predicates::{compute_blinded_fact_commitment, compute_fact_commitment};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding};
use dregg_sdk::AuthRequest;
use dregg_teasting::agent::{SimAgent, shared_root_key};

/// Same token, same request, two presentations: presentation tags must differ.
#[test]
fn test_presentation_tags_differ_across_presentations() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("privacy-svc");
    let root_token = alice.mint_token_with_key(&root_key, "privacy");

    let request = AuthRequest {
        service: Some("privacy".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    let proof1 = alice.prove_authorization(&root_token, &request).unwrap();
    let proof2 = alice.prove_authorization(&root_token, &request).unwrap();

    // Both proofs should be valid.
    assert!(proof1.is_valid());
    assert!(proof2.is_valid());

    // The presentation tags (public output) MUST differ between presentations.
    // This is what prevents verifiers from correlating "same token presented twice."
    let tag1 = proof1.circuit_proof.public_inputs.presentation_tag;
    let tag2 = proof2.circuit_proof.public_inputs.presentation_tag;
    assert_ne!(
        tag1, tag2,
        "Presentation tags must differ between independent presentations of the same token"
    );
}

/// Blinded fact commitments: same fact, different blinding → different (unlinkable) commitments.
///
/// 2026-07-16: the "…and both blinded proofs still verify" coda this test lost to the `*_air` shim
/// cleanup (8cc7ef821) is RESTORED below as `blinded_predicate_proofs_verify_and_are_unlinkable` —
/// blinded predicate PROVING is no longer dead code. `prove_predicate_for_fact` now takes a
/// `Blinding`, and the descriptor family's weld leg 2 is an arity-4 chip lookup over
/// `[fact_hash, state_root, blinding, 0]`, so the blinding factor is CONSTRAINED in-circuit rather
/// than applied out-of-band. This test keeps the pure-commitment half of the property; the coda
/// drives the real prover/verifier.
#[test]
fn test_blinded_fact_commitments_unlinkable() {
    let value = 100u32;

    // The raw fact_hash and state_root for one fact.
    let fh = hash_fact(
        BabyBear::new(42),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    let sr = BabyBear::new(99999);

    // Without blinding: a deterministic commitment (correlatable across presentations).
    let fc_unblinded = compute_fact_commitment(fh, sr);

    // The SAME fact, committed under two different blinding factors.
    let fc_blinded1 = compute_blinded_fact_commitment(fh, sr, BabyBear::new(12345));
    let fc_blinded2 = compute_blinded_fact_commitment(fh, sr, BabyBear::new(67890));

    // Unlinkability: blinded commitments of the same fact must differ from each other, and
    // from the unblinded one — otherwise colluding verifiers can correlate presentations.
    assert_ne!(
        fc_blinded1, fc_blinded2,
        "Different blinding → different commitments"
    );
    assert_ne!(
        fc_blinded1, fc_unblinded,
        "Blinded must differ from unblinded"
    );
    assert_ne!(
        fc_blinded2, fc_unblinded,
        "Blinded must differ from unblinded"
    );
}

// NOTE: removed 2 empty #[ignore] placeholder tests (delegation unlinkability,
// timing side-channel) that provided zero runtime value.

/// **THE RESTORED CODA — blinded predicate proofs VERIFY, and two showings are UNLINKABLE.**
///
/// This is the half the retraction said had "no live implementation to assert against". It does now.
/// Both showings are about the SAME fact and the SAME value, differing only in the blinding factor:
/// each must independently prove AND verify (soundness is not paid for privacy), and their public
/// fact commitments must differ (privacy is not paid for soundness).
#[test]
fn blinded_predicate_proofs_verify_and_are_unlinkable() {
    let value = 100u32;
    let fact = FactBinding {
        predicate_sym: BabyBear::new(42),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: BabyBear::new(99999),
    };
    let predicate = Predicate::Gte(40);

    // Two showings of the same fact under DIFFERENT blinding factors.
    let b1 = Blinding(BabyBear::new(12345));
    let b2 = Blinding(BabyBear::new(67890));

    let proof1 = prove_predicate_for_fact(value, fact, b1, &predicate).expect("showing 1 proves");
    let proof2 = prove_predicate_for_fact(value, fact, b2, &predicate).expect("showing 2 proves");

    // SOUNDNESS half — each verifies against the commitment IT presents.
    let c1 = fact.commitment_of(BabyBear::from_u64(value as u64), b1);
    let c2 = fact.commitment_of(BabyBear::from_u64(value as u64), b2);
    assert!(
        verify_predicate_proof(&proof1, c1),
        "a blinded predicate proof must verify against its own blinded commitment"
    );
    assert!(
        verify_predicate_proof(&proof2, c2),
        "a blinded predicate proof must verify against its own blinded commitment"
    );

    // PRIVACY half — the two public commitments differ, so the showings cannot be correlated.
    assert_ne!(
        c1, c2,
        "UNLINKABILITY LOST — two showings of the same fact emitted the same public commitment"
    );

    // ...and a proof does NOT verify against the OTHER showing's commitment: the blinding is bound
    // in-circuit, not a free relabeling a verifier would accept either way.
    assert!(
        !verify_predicate_proof(&proof1, c2),
        "showing 1 must not verify against showing 2's commitment — the blinding is CONSTRAINED \
         (leg 2 is an arity-4 lookup over [fact_hash, state_root, blinding, 0]), so a proof is tied \
         to the exact commitment it presents"
    );
}

/// **THE LIMIT OF THIS RUNG, DRIVEN — a decommitted proof is brute-forceable.**
///
/// `BridgePredicateProof` carries its `blinding` so that `verify_predicate_proof`'s equality-pinned
/// `expected_fact_commitment` has a sound feed at all (see that field's doc). This test is the
/// falsifier for the comfortable reading of that decision — "publishing the blinding costs privacy
/// nothing because deriving needs the value". Deriving needs the value; GUESSING does not.
///
/// A proof-holder who knows only the fact's SHAPE (predicate symbol, terms, state root) recovers the
/// private value by trying candidates. Predicate values are low-entropy by nature — an age, a tier —
/// so the domain is tiny.
///
/// This is NOT a regression the blinded weld introduced: the unblinded commitment was a
/// deterministic hash of the same low-entropy value and was equally brute-forceable. It is the
/// HONEST boundary of what this lane closed — the commitment is unlinkable to those who see only
/// commitments; a decommitted proof is not private. The fix is an opening/membership check at the
/// verifier instead of equality-pinning (HORIZONLOG).
///
/// It is a TEST rather than a comment so the claim cannot rot into folklore: if a future rung makes
/// the value genuinely hidden from a proof-holder, this goes red and must be rewritten deliberately.
#[test]
fn a_decommitted_proof_leaks_a_low_entropy_value_to_brute_force() {
    let secret_age = 37u32;
    let fact = FactBinding {
        predicate_sym: BabyBear::new(42),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: BabyBear::new(99999),
    };
    let blinding = Blinding(BabyBear::new(0xB11D1));

    // What the verifier receives: the commitment + the decommitment. NOT the value.
    let commitment = fact.commitment_of(BabyBear::from_u64(secret_age as u64), blinding);

    // THE ATTACK: sweep the plausible domain. No knowledge of the value is needed — only its shape.
    let recovered = (0u32..130)
        .find(|v| fact.commitment_of(BabyBear::from_u64(*v as u64), blinding) == commitment);

    assert_eq!(
        recovered,
        Some(secret_age),
        "the brute force must succeed — this test documents the LIMIT of the current rung. If it \
         fails, the verifier side changed and this boundary must be re-described, not deleted."
    );
}
