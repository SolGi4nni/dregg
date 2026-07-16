//! THE PREDICATE-GATE FORGERY CANARY — the falsifier for the SDK verifier's fact-commitment gate.
//!
//! ## The statement under test
//!
//! `dregg_bridge::verify_predicate_proof(proof, expected_fact_commitment)` proves:
//!
//! > "the value covered by `expected_fact_commitment` satisfies the predicate."
//!
//! The descriptor's value↔fact weld (`circuit/tests/predicate_arith_fact_weld_canary.rs`) supplies
//! half of that: the compared value is forced to be the one the PRESENTED commitment covers. The
//! other half is the verifier's: `expected_fact_commitment` must come from token state the verifier
//! trusts. The SDK used to feed that parameter `pred_proof.fact_commitment` — the proof's OWN
//! commitment — collapsing the gate to `x != x`. Always false. Never rejects. The weld then binds
//! the value to a fact the PROVER chose, and the forgery just moves up one level: pick a fact you
//! like, prove a true statement about it, present it as a statement about token state.
//!
//! ## The falsifier
//!
//! [`forged_commitment_is_accepted_by_the_self_fed_gate_and_refused_by_the_derived_one`] builds a
//! genuine, internally-consistent proof about a fact the prover INVENTED (`score = 999`) while the
//! verifier's trusted state says `score = 300`. It drives BOTH feeds over that one proof:
//!
//! * the `x != x` self-feed (the exact expression that was at `sdk/src/verify.rs:379`) → ACCEPTED;
//! * the derived feed (`AgentCipherclerk::derive_fact_commitment` from trusted state) → REFUSED.
//!
//! Both poles in one test, so neither can pass vacuously: the canary IS the restore-the-old-feed
//! experiment, run on every test invocation rather than by hand.
//!
//! [`honest_predicate_proof_verifies_against_derived_commitment`] pins the completeness pole (the
//! derived feed must still ACCEPT the honest proof), and
//! [`the_four_term_kinds_round_trip_or_fail_loud`] pins the unified reduction that makes the honest
//! pole reachable at all.

use dregg_circuit::field::BabyBear;
use dregg_sdk::AgentCipherclerk;
use dregg_trace::{Fact as TraceFact, Term};

/// The predicate symbol shared by every fact here.
fn pred_sym() -> [u8; 32] {
    *blake3::hash(b"has-credit-score").as_bytes()
}

/// The token-state root the commitments are taken against. A verifier of a real presentation gets
/// this from the trusted token (`AgentCipherclerk::fact_commitment_state_root`); this test stands in
/// for that with a fixed root, since what is under test is the DERIVATION, not the token decode.
fn state_root() -> BabyBear {
    BabyBear::new(0x57A7E)
}

/// A single-`Int`-term fact — the shape the arithmetic predicate path proves about.
fn score_fact(score: i64) -> TraceFact {
    TraceFact {
        predicate: pred_sym(),
        terms: vec![Term::Int(score)],
    }
}

/// The value token state ACTUALLY covers. The prover cannot prove `>= 900` about it honestly.
const TRUE_SCORE: i64 = 300;
/// The value the prover INVENTS: it satisfies the predicate, but trusted state says nothing about it.
const FORGED_SCORE: i64 = 999;
/// The bound. `TRUE_SCORE` fails it; `FORGED_SCORE` passes it — that gap is the forgery's payload.
const THRESHOLD: u32 = 900;

/// Build a genuine predicate proof about `fact` — exactly the construction
/// `AgentCipherclerk::authorize_selective_with_predicates` uses (shared binding, one reduction).
fn prove_about(
    fact: &TraceFact,
    predicate: &dregg_bridge::Predicate,
) -> dregg_bridge::BridgePredicateProof {
    let value = AgentCipherclerk::extract_fact_value(fact).expect("value");
    let binding = AgentCipherclerk::fact_binding(fact, state_root());
    let blinding = dregg_bridge::fresh_predicate_blinding();
    dregg_bridge::prove_predicate_for_fact(value, binding, blinding, predicate)
        .expect("a TRUE statement must prove")
}

/// The verifier's derivation for a TRUSTED fact, opened with the blinding the PROOF carries.
fn derive_expected(trusted: &TraceFact, proof: &dregg_bridge::BridgePredicateProof) -> BabyBear {
    AgentCipherclerk::derive_fact_commitment(
        trusted,
        state_root(),
        dregg_circuit::predicate_arith_witness::Blinding(proof.blinding),
    )
    .expect("a trusted fact must have a canonically derivable commitment")
}

/// ⚑ THE FALSIFIER + ITS OWN CANARY.
///
/// One forged proof, two feeds. The `x != x` feed ACCEPTS it; the derived feed REFUSES it.
#[test]
fn forged_commitment_is_accepted_by_the_self_fed_gate_and_refused_by_the_derived_one() {
    let trusted_fact = score_fact(TRUE_SCORE);
    let forged_fact = score_fact(FORGED_SCORE);
    let predicate = dregg_bridge::Predicate::Gte(THRESHOLD);

    // The prover proves `999 >= 900` about a fact IT invented, and presents that fact's commitment.
    // The proof is internally honest: the weld holds, the comparison is true. Its only lie is about
    // WHICH fact it is about — and the weld cannot catch that, because the weld's job is to bind the
    // value to the presented commitment, not the presented commitment to token state.
    let forged_proof = prove_about(&forged_fact, &predicate);

    // --- POLE 1: the OLD feed (`sdk/src/verify.rs:379`, verbatim) — `x != x`.
    let self_fed =
        dregg_bridge::verify_predicate_proof(&forged_proof, forged_proof.fact_commitment);
    println!("SELF-FED (x != x) gate on the FORGED proof: accepted = {self_fed}");
    assert!(
        self_fed,
        "CANARY BROKEN: the self-fed gate is supposed to accept the forgery — if it does not, this \
         test is no longer demonstrating the hole it exists to close, and the REFUSED pole below \
         proves nothing."
    );

    // --- POLE 2: the NEW feed — the commitment DERIVED from trusted state.
    let expected = derive_expected(&trusted_fact, &forged_proof);
    let derived_fed = dregg_bridge::verify_predicate_proof(&forged_proof, expected);
    println!("DERIVED gate on the FORGED proof:          accepted = {derived_fed}");
    assert!(
        !derived_fed,
        "THE HOLE IS OPEN: a proof presenting a fact_commitment that does not match the trusted \
         token state's derived commitment was ACCEPTED."
    );

    // The two feeds disagree because the commitments differ — the derivation is doing real work,
    // not accidentally agreeing.
    assert_ne!(
        forged_proof.fact_commitment, expected,
        "the forged and derived commitments must differ, or the test is vacuous"
    );
}

/// COMPLETENESS: the honest proof still verifies under the FIXED gate. Without this, refusing
/// everything would score as a pass.
#[test]
fn honest_predicate_proof_verifies_against_derived_commitment() {
    let fact = score_fact(TRUE_SCORE);
    // A bound the TRUE value actually satisfies.
    let predicate = dregg_bridge::Predicate::Gte(100);
    let honest_proof = prove_about(&fact, &predicate);

    let expected = derive_expected(&fact, &honest_proof);
    assert_eq!(
        honest_proof.fact_commitment, expected,
        "the honest prover's commitment MUST equal the verifier's derivation — if these drift, \
         honest proofs get rejected by a correct verifier (the latent completeness break the \
         vacuous gate was hiding)"
    );
    assert!(
        dregg_bridge::verify_predicate_proof(&honest_proof, expected),
        "an honest proof about trusted state must VERIFY under the derived gate"
    );

    // Non-vacuity: the same honest proof against a DIFFERENT trusted fact is refused.
    let other = derive_expected(&score_fact(301), &honest_proof);
    assert!(
        !dregg_bridge::verify_predicate_proof(&honest_proof, other),
        "a proof about score=300 must not verify as a proof about score=301"
    );
}

/// THE UNIFIED REDUCTION, driven over all four term kinds: each either ROUND-TRIPS
/// (`value == terms[0]`, so prover and verifier derive the same commitment) or FAILS LOUD.
/// Silently mis-comparing is not an option for any kind.
#[test]
fn the_four_term_kinds_round_trip_or_fail_loud() {
    let sym: [u8; 32] = *blake3::hash(b"credit-score").as_bytes();
    let cases: &[(&str, TraceFact)] = &[
        (
            "Const",
            TraceFact {
                predicate: pred_sym(),
                terms: vec![Term::Const(sym)],
            },
        ),
        ("Int>=0", score_fact(720)),
        ("Int<0", score_fact(-5)),
        (
            "Int out-of-range",
            score_fact(dregg_circuit::field::BABYBEAR_P as i64),
        ),
        (
            "Var",
            TraceFact {
                predicate: pred_sym(),
                terms: vec![Term::Var(0)],
            },
        ),
    ];

    for (name, fact) in cases {
        let extracted = AgentCipherclerk::extract_fact_value(fact);
        let terms = AgentCipherclerk::trace_fact_terms_bb(fact);
        match extracted {
            Ok(v) => {
                println!(
                    "{name}: extract = {v} | terms[0] = {} | ROUND-TRIP",
                    terms[0].as_u32()
                );
                assert_eq!(
                    BabyBear::new(v),
                    terms[0],
                    "{name}: an accepted value MUST be terms[0] — the commitment the prover welds \
                     and the one the verifier derives are the same element or they are nothing"
                );
                // And the derivation succeeds for exactly these kinds.
                assert!(
                    AgentCipherclerk::derive_fact_commitment(
                        fact,
                        state_root(),
                        dregg_circuit::predicate_arith_witness::Blinding::NONE
                    )
                    .is_ok(),
                    "{name}: a round-tripping kind must derive a commitment"
                );
            }
            Err(e) => {
                println!("{name}: FAILS LOUD — {e}");
                // Fail-loud must be total: the derivation refuses the same kinds the extraction does,
                // so no caller can route around it.
                assert!(
                    AgentCipherclerk::derive_fact_commitment(
                        fact,
                        state_root(),
                        dregg_circuit::predicate_arith_witness::Blinding::NONE
                    )
                    .is_err(),
                    "{name}: a kind with no canonical value must not yield a commitment"
                );
            }
        }
    }

    // The kinds with no meaningful compared value are REFUSED, not silently reduced. `Const` is the
    // one that regressed: the old code returned a raw first-limb read of the symbol, which made
    // `poseidon2-hash >= threshold` *succeed* as if it meant something.
    for (name, fact) in cases.iter().filter(|(n, _)| *n != "Int>=0") {
        assert!(
            AgentCipherclerk::extract_fact_value(fact).is_err(),
            "{name}: must fail loud, never silently mis-compare"
        );
    }
    // The one kind the arithmetic path is actually about round-trips.
    assert_eq!(
        AgentCipherclerk::extract_fact_value(&score_fact(720)).expect("Int>=0 round-trips"),
        720
    );
}

/// THE BLINDING IS A DECOMMITMENT, NOT A LOCKOUT.
///
/// The per-presentation blinding makes two showings of the SAME fact carry different
/// `fact_commitment`s — that is the unlinkability it exists for. But a blinding drawn fresh and then
/// DISCARDED would make the commitment unreproducible by anyone, which does not hide the fact from a
/// verifier so much as remove the verifier: `expected_fact_commitment` would have no sound source at
/// all, leaving the `x != x` self-feed as the only thing that "works". Carrying the blinding in the
/// proof keeps both properties. This pins all three:
///
/// 1. UNLINKABLE — two proofs of the same fact carry different commitments;
/// 2. DERIVABLE — each still opens against trusted state, using the blinding it carries;
/// 3. STILL SOUND — the prover's freedom over the blinding cannot move which fact is named: a
///    forged-value proof is refused under EVERY blinding, including its own.
#[test]
fn blinding_is_unlinkable_yet_derivable_and_still_sound() {
    let fact = score_fact(TRUE_SCORE);
    let predicate = dregg_bridge::Predicate::Gte(100);

    let first = prove_about(&fact, &predicate);
    let second = prove_about(&fact, &predicate);

    // 1. UNLINKABLE: same fact, same predicate, different commitments.
    println!(
        "UNLINKABLE: two showings of score={TRUE_SCORE} -> commitments {} vs {}",
        first.fact_commitment.as_u32(),
        second.fact_commitment.as_u32()
    );
    assert_ne!(
        first.fact_commitment, second.fact_commitment,
        "two showings of the same fact must not be correlatable by commitment"
    );
    assert_ne!(
        first.blinding, second.blinding,
        "each showing draws a fresh blinding"
    );

    // 2. DERIVABLE: each opens against the SAME trusted state, with its own carried blinding.
    for (name, proof) in [("first", &first), ("second", &second)] {
        let expected = derive_expected(&fact, proof);
        assert_eq!(
            proof.fact_commitment, expected,
            "{name}: the carried blinding must open the commitment against trusted state"
        );
        assert!(
            dregg_bridge::verify_predicate_proof(proof, expected),
            "{name}: must verify under the derived gate"
        );
    }

    // Cross-opening fails: `first`'s blinding does not open `second`'s commitment. The blinding is
    // bound to its showing, so it is not a reusable correlation handle.
    assert!(
        !dregg_bridge::verify_predicate_proof(&second, derive_expected(&fact, &first)),
        "one showing's blinding must not open another's commitment"
    );

    // 3. STILL SOUND: a forged-value proof is refused no matter which blinding is used to derive.
    // The prover chooses the blinding freely; what it cannot choose is the VALUE trusted state holds.
    let forged = prove_about(
        &score_fact(FORGED_SCORE),
        &dregg_bridge::Predicate::Gte(THRESHOLD),
    );
    for b in [
        dregg_circuit::predicate_arith_witness::Blinding(forged.blinding),
        dregg_circuit::predicate_arith_witness::Blinding(first.blinding),
        dregg_circuit::predicate_arith_witness::Blinding::NONE,
    ] {
        let expected = AgentCipherclerk::derive_fact_commitment(&fact, state_root(), b)
            .expect("derive commitment");
        assert!(
            !dregg_bridge::verify_predicate_proof(&forged, expected),
            "a forged-value proof must be refused under EVERY blinding — blinding rerandomizes \
             which commitment names a fact, it cannot change which fact is named"
        );
    }
    println!("SOUND: the forged-value proof is refused under every blinding (own, foreign, NONE)");
}
