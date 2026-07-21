//! ADVERSARIAL FORGE PROBE for the value↔fact weld in the committed-threshold
//! predicate disclosure (`circuit/src/dsl/committed_threshold.rs`, welded twin).
//!
//! THE HOLE (now closed): the plain committed-threshold circuit proves
//! `private_value ≥ threshold` and PI-pins `fact_commitment`, but `private_value`
//! (the value the range gadget proves about) was a FREE witness — never tied to the
//! committed fact. A prover could therefore prove "value ≥ threshold" about a value
//! they do NOT hold, against a `fact_commitment` naming a DIFFERENT real fact.
//!
//! The fix opens the fact IN-CIRCUIT (welded descriptor):
//!   fact_hash        == hash_fact(predicate_sym, [private_value, term1, term2])   (C6, `Hash`)
//!   fact_commitment  == Poseidon2(fact_hash, state_root)                          (C7, `Hash2to1`)
//! The SAME `private_value` column feeds BOTH the range gadget AND the fact-hash
//! preimage, so a satisfying assignment forces `private_value` to equal the value
//! inside the committed fact (Poseidon2 collision resistance).
//!
//! Driven through the DEPLOYED, AUDITED Plonky3 prover `prove_dsl_p3`/`verify_dsl_p3`
//! (real Poseidon2 aux blocks for the `Hash`/`Hash2to1` gates). No hand-written
//! descriptor: the descriptor is the production welded one; only the adversarial
//! TRACE is hand-built.

use std::panic::AssertUnwindSafe;

use dregg_circuit::dsl::committed_threshold::{
    CommittedThresholdFactWitness, committed_threshold_welded_circuit,
    generate_committed_threshold_welded_trace, welded_col,
};
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_2_to_1, hash_fact};
use dregg_circuit::refusal::{Outcome, classify};

/// The fact's predicate symbol (arbitrary distinct felt, e.g. a "credit_score" tag).
const PRED: u32 = 100;
/// The token state root the fact commitment is taken over.
const STATE_ROOT: u32 = 88_888;
/// The verifier's secret threshold and threshold-commitment blinding.
const THRESHOLD: u32 = 700;
const BLINDING: u32 = 12_345;

/// Run the real prover+verifier on a (possibly adversarial) trace; `true` = REJECTED.
fn rejects(trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let circuit = committed_threshold_welded_circuit();
    match classify("rejects", || {
        let proof = prove_dsl_p3(&circuit, trace, pis)?;
        verify_dsl_p3(&circuit, &proof, pis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// The real fact for `value`: `fact_hash = hash_fact(PRED,[value,0,0])`, committed
/// over `STATE_ROOT`.
fn fact_of(value: u32) -> (BabyBear, BabyBear) {
    let fh = hash_fact(
        BabyBear::new(PRED),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    let fc = hash_2_to_1(fh, BabyBear::new(STATE_ROOT));
    (fh, fc)
}

/// COMPLETENESS: an honest disclosure — the prover genuinely holds a fact whose
/// value (750) satisfies `≥ 700` — proves+verifies through the deployed prover.
#[test]
fn honest_disclosure_accepts() {
    let witness = CommittedThresholdFactWitness {
        private_value: BabyBear::new(750),
        threshold: BabyBear::new(THRESHOLD),
        blinding: BabyBear::new(BLINDING),
        predicate_sym: BabyBear::new(PRED),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: BabyBear::new(STATE_ROOT),
    };
    let (trace, pis) = generate_committed_threshold_welded_trace(&witness);
    // Sanity: PI fact_commitment IS the genuine commitment of the value-750 fact.
    let (_, fc750) = fact_of(750);
    assert_eq!(
        pis[1], fc750,
        "honest PI must commit the value it proves about"
    );
    assert!(!rejects(&trace, &pis), "honest disclosure MUST verify");
}

/// THE CENTRAL FORGE — prove `value ≥ 700` about a value the prover does NOT hold.
/// The prover holds a fact committing `value = 300` (which FAILS `≥ 700`), yet sets
/// `private_value = 700` in the range gadget while pinning the real value-300
/// `fact_commitment`. The in-circuit fact-open (C6) recomputes
/// `hash_fact(PRED,[700,0,0])` from the range-gadget value and compares it to the
/// pinned value-300 `fact_hash` → `hash(700) == hash(300)` is UNSAT → REJECT.
#[test]
fn value_not_the_fact_forge_rejected() {
    use welded_col as w;

    // The fact the forger actually holds: value 300, which does NOT satisfy ≥ 700.
    let (fact_hash_300, fc_300) = fact_of(300);
    let threshold = BabyBear::new(THRESHOLD);
    let blinding = BabyBear::new(BLINDING);
    let tc = hash_2_to_1(threshold, blinding);
    let sr = BabyBear::new(STATE_ROOT);

    // The forged control row: range gadget claims 700 (passes ≥ 700, diff = 0), but
    // the fact columns carry the REAL value-300 fact/commitment.
    let mut row = vec![BabyBear::ZERO; w::WELDED_WIDTH];
    row[w::PRIVATE_VALUE] = BabyBear::new(700); // the LIE — range gadget value
    row[w::THRESHOLD] = threshold;
    row[w::BLINDING] = blinding;
    row[w::DIFF] = BabyBear::ZERO; // 700 - 700
    // all diff bits 0 (diff = 0), high bit 0 → range gadget accepts 700 ≥ 700
    row[w::POSEIDON2_RESULT] = tc;
    row[w::THRESHOLD_COMMITMENT] = tc;
    row[w::PREDICATE_SYM] = BabyBear::new(PRED);
    row[w::TERM1] = BabyBear::ZERO;
    row[w::TERM2] = BabyBear::ZERO;
    row[w::STATE_ROOT] = sr;
    row[w::FACT_HASH] = fact_hash_300; // the real fact hash (of value 300)
    row[w::FACT_COMMITMENT] = fc_300; // pins the real value-300 commitment
    let trace = vec![row.clone(), row];
    let pis = vec![tc, fc_300];

    // Precondition: the range gadget alone WOULD accept (700 ≥ 700). The rejection
    // is due to the fact-open weld (C6 recomputes hash_fact of the range-gadget value
    // 700 and compares to the pinned value-300 fact_hash), not the range check.
    assert_ne!(
        fact_hash_300,
        hash_fact(
            BabyBear::new(PRED),
            &[BabyBear::new(700), BabyBear::ZERO, BabyBear::ZERO]
        ),
        "the value-300 fact hash differs from the value-700 fact hash (the weld's teeth)"
    );

    assert!(
        rejects(&trace, &pis),
        "SOUNDNESS: proving ≥700 about a value the prover does not hold (fact commits 300) MUST be REJECTED by the in-circuit fact-open weld"
    );
}

/// FORGE VARIANT — satisfy C6 by setting `fact_hash = hash_fact(PRED,[700,..])`, but
/// then C7 forces `fact_commitment = Poseidon2(hash_fact(700), state_root)`, which is
/// NOT the real value-300 commitment the verifier expects. The trace is internally
/// consistent (self-verifies), but its PI `fact_commitment` names a value-700 fact
/// the prover does not hold — caught by the verifier-side trusted-state binding
/// (`fact_commitment` recomputed from the real credential). We assert the emitted PI
/// commitment does NOT equal the honestly-held value-300 commitment.
#[test]
fn internally_consistent_forge_emits_wrong_commitment() {
    // Forger builds a fully honest trace for a value-700 fact (which they do NOT hold).
    let witness = CommittedThresholdFactWitness {
        private_value: BabyBear::new(700),
        threshold: BabyBear::new(THRESHOLD),
        blinding: BabyBear::new(BLINDING),
        predicate_sym: BabyBear::new(PRED),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: BabyBear::new(STATE_ROOT),
    };
    let (trace, pis) = generate_committed_threshold_welded_trace(&witness);
    // The circuit accepts (it is a genuine proof about a value-700 fact)...
    assert!(
        !rejects(&trace, &pis),
        "a genuine value-700 proof self-verifies"
    );
    // ...but its PI fact_commitment is the value-700 commitment, NOT the value-300
    // commitment the prover actually holds. The verifier's trusted-state binding
    // (recompute fact_commitment from the real credential) rejects this mismatch.
    let (_, fc_300) = fact_of(300);
    assert_ne!(
        pis[1], fc_300,
        "the forged proof's fact_commitment cannot equal the held value-300 commitment"
    );
}
