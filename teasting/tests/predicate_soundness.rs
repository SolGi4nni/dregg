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
//!
//! Every pole runs under a REAL, non-zero [`Blinding`] — the deployed (unlinkable) posture. The
//! commitment is therefore not a function of the fact alone, so the verifier's expected commitment
//! is DERIVED the way a real verifier derives it: from the value it trusts, plus the blinding the
//! presentation discloses (`proof.blinding`). See [`expected_commitment`].

use dregg_bridge::present::{Predicate, prove_predicate_for_fact, verify_predicate_proof};
use dregg_circuit::BabyBear;
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding};
use dregg_circuit::refusal::{Outcome, classify};

/// The identity of the test fact — its TERMS plus the state root it lives under. The value is NOT
/// here: it is `terms[0]`, passed to the prover alongside, which is why a value and a commitment
/// covering a different value cannot be paired through this API.
fn fact() -> FactBinding {
    FactBinding {
        predicate_sym: BabyBear::new(0xABCD),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: BabyBear::new(0x1234),
    }
}

/// The per-presentation blinding these poles are driven under — REAL and non-zero, so the suite
/// exercises the deployed posture rather than the degenerate `Blinding::NONE`.
fn test_blinding() -> Blinding {
    Blinding(BabyBear::new(0xB11D1))
}

/// What a verifier holding TRUSTED token state derives as the expected commitment for `value`,
/// under the blinding the presentation disclosed.
///
/// This is the sound feed for [`verify_predicate_proof`]'s parameter: the VALUE comes from state
/// the verifier trusts (never from the prover), the blinding is merely the opening. Feeding the
/// proof's own `fact_commitment` back in would be the `x == x` gate that accepts everything.
fn expected_commitment(value: u32, blinding: BabyBear) -> BabyBear {
    fact().commitment_of(BabyBear::from_u64(value as u64), Blinding(blinding))
}

/// The disclosed opening, or a LOUD failure.
///
/// `BridgePredicateProof::blinding` became `Option<BabyBear>` in 6a852f2766: `Some(b)` is the
/// trusted-state shape (the presentation discloses its decommitment), `None` is the third-party
/// ATTESTED shape, which deliberately carries none. Every pole here drives
/// `prove_predicate_for_fact`, whose contract is the `Some` shape, so `None` is not a case to
/// tolerate — it would mean the opening stopped being emitted, and a test that quietly substituted
/// [`test_blinding`] there would keep verifying while the disclosure it is checking had vanished.
/// This is unwrapped, not defaulted, for that reason.
fn opening(proof: &dregg_bridge::present::BridgePredicateProof) -> BabyBear {
    proof
        .blinding
        .expect("the trusted-state predicate shape MUST disclose its opening")
}

#[test]
fn honest_statements_prove_and_verify() {
    let cases: &[(u32, Predicate)] = &[
        (100, Predicate::Gte(40)),
        (40, Predicate::Lte(100)),
        (41, Predicate::Neq(40)),
    ];
    for (value, predicate) in cases {
        let proof = prove_predicate_for_fact(*value, fact(), test_blinding(), predicate)
            .unwrap_or_else(|| panic!("true statement {value} {predicate:?} must PROVE"));
        assert!(
            verify_predicate_proof(&proof, expected_commitment(*value, opening(&proof))),
            "true statement {value} {predicate:?} must VERIFY"
        );
    }
}

/// A false statement is REFUSED three ways, and all three count:
///   * `prove_predicate_for_fact` returns `None` (the bridge's fail-closed path — e.g. the range
///     tooth's assembler refusal, which surfaces as a typed `Err` the bridge maps to `None`);
///   * it PANICS with the p3 debug prover's DOCUMENTED unsat verdict. `Predicate::Neq(40)` on a
///     value of 40 breaks the degree-2 nonzero gate `diff · diff_inv = 1` — a BASE GATE, which
///     `p3_batch_stark::prove_batch`'s `#[cfg(debug_assertions)]` `check_constraints` reports by
///     PANICKING rather than returning. The bridge does not `catch_unwind`, so under `cargo test`
///     the panic reaches here. [`classify`] is what makes that verdict legible — and it REDS on any
///     OTHER panic, so a stray unwrap can never launder itself as a refusal;
///   * the proof verifies FALSE against the commitment a trusted-state verifier derives.
fn refuses(value: u32, predicate: &Predicate) -> bool {
    let outcome = classify("false-statement", || {
        match prove_predicate_for_fact(value, fact(), test_blinding(), predicate) {
            None => Err("the prover refused the false statement".to_string()),
            Some(p) => {
                if verify_predicate_proof(&p, expected_commitment(value, opening(&p))) {
                    Ok(())
                } else {
                    Err("the proof failed to verify".to_string())
                }
            }
        }
    });
    matches!(outcome, Outcome::Err(_) | Outcome::UnsatPanic(_))
}

#[test]
fn false_statements_are_rejected() {
    let cases: &[(u32, Predicate)] = &[
        (30, Predicate::Gte(40)),
        (110, Predicate::Lte(100)),
        (40, Predicate::Neq(40)),
    ];
    for (value, predicate) in cases {
        assert!(
            refuses(*value, predicate),
            "false statement {value} {predicate:?} must be REJECTED"
        );
    }
}

#[test]
fn forged_fact_commitment_is_rejected() {
    let proof = prove_predicate_for_fact(100, fact(), test_blinding(), &Predicate::Gte(40))
        .expect("100 >= 40 must prove");
    // Non-vacuity: against the commitment a trusted-state verifier derives, the proof verifies.
    assert!(
        verify_predicate_proof(&proof, expected_commitment(100, opening(&proof))),
        "honest proof must verify"
    );
    assert!(
        !verify_predicate_proof(&proof, BabyBear::new(0xDEAD)),
        "a forged fact commitment must REJECT"
    );
}
