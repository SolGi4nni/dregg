//! Predicate soundness integration test: forge attempts MUST fail.
//!
//! MIGRATED 2026-07-16 to the bridge-layer predicate API
//! (`dregg_bridge::present::{prove_predicate_for_fact, verify_predicate_proof, Predicate}`)
//! after the circuit-level API this suite used (`dregg_circuit::dsl::predicates::{prove_predicate,
//! verify_predicate, PredicateProof, ...}`) was deleted in 8cc7ef821. The comprehensive per-operator
//! coverage lives in `bridge::present::comparison_predicates_prove_and_verify_end_to_end`; this file
//! keeps the adversarial poles as an integration smoke-test on the live API:
//!   1. honest (true) statements prove AND verify,
//!   2. false statements are rejected (fail to prove, or their proof fails to verify),
//!   3. a forged public input (wrong fact commitment) is rejected.
//! All three poles are non-vacuous.

use dregg_bridge::present::{Predicate, prove_predicate_for_fact, verify_predicate_proof};
use dregg_circuit::BabyBear;

/// (fact_hash, state_root, fact_commitment) for a test fact.
fn fixture() -> (BabyBear, BabyBear, BabyBear) {
    let fact_hash = BabyBear::new(0xABCD);
    let state_root = BabyBear::new(0x1234);
    let fc = dregg_circuit::compute_fact_commitment(fact_hash, state_root);
    (fact_hash, state_root, fc)
}

#[test]
fn honest_statements_prove_and_verify() {
    let (fh, sr, fc) = fixture();
    let cases: &[(u32, Predicate)] = &[
        (100, Predicate::Gte(40)),
        (40, Predicate::Lte(100)),
        (41, Predicate::Neq(40)),
    ];
    for (value, predicate) in cases {
        let proof = prove_predicate_for_fact(*value, fh, sr, predicate)
            .unwrap_or_else(|| panic!("true statement {value} {predicate:?} must PROVE"));
        assert!(
            verify_predicate_proof(&proof, fc),
            "true statement {value} {predicate:?} must VERIFY"
        );
    }
}

#[test]
fn false_statements_are_rejected() {
    let (fh, sr, fc) = fixture();
    let cases: &[(u32, Predicate)] = &[
        (30, Predicate::Gte(40)),
        (110, Predicate::Lte(100)),
        (40, Predicate::Neq(40)),
    ];
    for (value, predicate) in cases {
        let rejected = match prove_predicate_for_fact(*value, fh, sr, predicate) {
            None => true,
            Some(p) => !verify_predicate_proof(&p, fc),
        };
        assert!(
            rejected,
            "false statement {value} {predicate:?} must be REJECTED"
        );
    }
}

#[test]
fn forged_fact_commitment_is_rejected() {
    let (fh, sr, fc) = fixture();
    let proof =
        prove_predicate_for_fact(100, fh, sr, &Predicate::Gte(40)).expect("100 >= 40 must prove");
    assert!(
        verify_predicate_proof(&proof, fc),
        "honest proof must verify"
    );
    // Non-vacuity: the same proof against a FORGED fact commitment must reject.
    assert!(
        !verify_predicate_proof(&proof, BabyBear::new(0xDEAD)),
        "a forged fact commitment must REJECT"
    );
}
