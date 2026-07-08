//! Adversarial forge audit for the committed-threshold disclosure primitive.
//!
//! THE HOLE (hand-written `CommittedThresholdAir`, now un-dispatched): the AIR
//! asserted `POSEIDON2_RESULT == THRESHOLD_COMMITMENT` but NO in-circuit constraint
//! bound `POSEIDON2_RESULT` to `Poseidon2(threshold, blinding)`. `BLINDING` was read
//! by zero constraints. So an attacker who knows only the public commitment `C`
//! (but NOT the secret threshold or blinding) could set
//! `POSEIDON2_RESULT = THRESHOLD_COMMITMENT = C`, `threshold = 0`, `blinding = 0`,
//! `value = 0` and prove "value >= the committed threshold C" — a total break.
//!
//! THE FIX: the deployed `prove/verify_committed_threshold` now route through the
//! DSL circuit (`committed_threshold_dsl_circuit`), whose `Hash2to1` gadget makes
//! `POSEIDON2_RESULT == Poseidon2(threshold, blinding)` a genuine in-circuit
//! constraint. The forge trace above violates it (`Poseidon2(0,0) != C`), so the
//! prover refuses (and the verifier would reject).
//!
//! This test drives the ACTUAL circuits at the trace level (like
//! `non_revocation_p3_boundary.rs`), bypassing the API's honest-trace builder, so
//! it exercises the constraint system itself — the real seat of soundness.

#![allow(deprecated)]

use dregg_circuit::committed_threshold::{
    COMMITTED_DIFF_BITS, COMMITTED_THRESHOLD_AIR_WIDTH, CommittedThresholdAir,
    CommittedThresholdWitness, col,
};
use dregg_circuit::dsl::committed_threshold::committed_threshold_dsl_circuit;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_2_to_1;
use dregg_circuit::stark;

/// Build the adversarial forge trace: claim `value = 0` satisfies the committed
/// threshold `C = Poseidon2(secret_threshold, secret_blinding)` without knowing
/// either secret, by pinning `POSEIDON2_RESULT = THRESHOLD_COMMITMENT = C` and
/// zeroing threshold/blinding/value/diff/bits.
fn forge_trace(c: BabyBear, fact_commitment: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut row = vec![BabyBear::ZERO; COMMITTED_THRESHOLD_AIR_WIDTH];
    row[col::PRIVATE_VALUE] = BabyBear::ZERO; // the forged "value"
    row[col::THRESHOLD] = BabyBear::ZERO; // attacker does NOT know the real threshold
    row[col::BLINDING] = BabyBear::ZERO; // attacker does NOT know the real blinding
    row[col::DIFF] = BabyBear::ZERO; // value - threshold = 0
    for i in 0..COMMITTED_DIFF_BITS {
        row[col::diff_bit(i)] = BabyBear::ZERO; // diff = 0, all bits 0 (high bit 0 => "value >= threshold")
    }
    row[col::THRESHOLD_COMMITMENT] = c; // public commitment (known to the attacker)
    row[col::FACT_COMMITMENT] = fact_commitment; // public
    row[col::POSEIDON2_RESULT] = c; // FORGE: pin result == commitment, skipping the real hash

    let public_inputs = vec![c, fact_commitment];
    // STARK needs >= 2 rows, power of two. Duplicate the (identical) row.
    (vec![row.clone(), row], public_inputs)
}

/// CONFIRM THE HOLE: the deprecated hand-written AIR accepts the forge. This proves
/// the vulnerability was real (and stays as a regression tripwire should anything
/// ever re-dispatch the broken AIR).
#[test]
fn hand_air_accepts_forge_documents_the_hole() {
    let secret_threshold = BabyBear::new(680);
    let secret_blinding = BabyBear::new(0xABCDEF);
    let c = hash_2_to_1(secret_threshold, secret_blinding);
    let fact_commitment = BabyBear::new(0x1234_5678);

    let (trace, public_inputs) = forge_trace(c, fact_commitment);

    // Dummy witness: eval/verify read the trace, not the witness.
    let air = CommittedThresholdAir::new(CommittedThresholdWitness {
        private_value: BabyBear::ZERO,
        threshold: BabyBear::ZERO,
        blinding: BabyBear::ZERO,
        fact_commitment,
    });

    let proof = stark::try_prove(&air, &trace, &public_inputs)
        .expect("hand AIR (broken) accepts the forge trace");
    assert!(
        stark::verify(&air, &proof, &public_inputs).is_ok(),
        "the hole: hand AIR verifies a forged 'value >= C' proof with threshold=blinding=0"
    );
}

/// CONFIRM THE FIX: the DSL circuit's in-circuit `Poseidon2(threshold, blinding)`
/// gadget refuses the forge. `Poseidon2(0, 0) != C`, so the Hash2to1 constraint is
/// violated at the trace row and the prover cannot produce a proof.
#[test]
fn dsl_circuit_rejects_forge() {
    let secret_threshold = BabyBear::new(680);
    let secret_blinding = BabyBear::new(0xABCDEF);
    let c = hash_2_to_1(secret_threshold, secret_blinding);
    let fact_commitment = BabyBear::new(0x1234_5678);

    // Sanity: the pinned result C is NOT the honest hash of the forged inputs.
    assert_ne!(
        c,
        hash_2_to_1(BabyBear::ZERO, BabyBear::ZERO),
        "forge relies on C != Poseidon2(0,0)"
    );

    let (trace, public_inputs) = forge_trace(c, fact_commitment);
    let circuit = committed_threshold_dsl_circuit();

    let result = stark::try_prove(&circuit, &trace, &public_inputs);
    assert!(
        result.is_err(),
        "FORGE MUST BE REJECTED: DSL Hash2to1 gadget must refuse a trace where \
         POSEIDON2_RESULT != Poseidon2(threshold, blinding)"
    );
}

/// HONEST: a genuine `value=700 >= threshold=680` with the real blinding proves and
/// verifies through the SAME DSL circuit the deployed API now uses.
#[test]
fn dsl_circuit_accepts_honest() {
    use dregg_circuit::dsl::committed_threshold::{
        generate_committed_threshold_trace, prove_committed_threshold_dsl,
        verify_committed_threshold_dsl,
    };

    let value = BabyBear::new(700);
    let threshold = BabyBear::new(680);
    let blinding = BabyBear::new(0xABCDEF);
    let fact_commitment = BabyBear::new(0x1234_5678);

    let witness = CommittedThresholdWitness {
        private_value: value,
        threshold,
        blinding,
        fact_commitment,
    };

    // Trace-level honest proof through the DSL circuit.
    let (trace, public_inputs) = generate_committed_threshold_trace(&witness);
    let circuit = committed_threshold_dsl_circuit();
    let proof = stark::try_prove(&circuit, &trace, &public_inputs)
        .expect("honest witness must produce a proof");
    assert!(
        stark::verify(&circuit, &proof, &public_inputs).is_ok(),
        "honest value >= threshold must verify"
    );

    // And through the high-level DSL API.
    let threshold_commitment = witness.compute_threshold_commitment();
    let proof = prove_committed_threshold_dsl(&witness).expect("honest API proof");
    assert!(
        verify_committed_threshold_dsl(&proof, threshold_commitment, fact_commitment),
        "honest API proof must verify"
    );
}

/// CONFIRM THE FIX at the DEPLOYED API boundary: the public
/// `dregg_circuit::prove_committed_threshold` / `verify_committed_threshold`
/// (post-repoint) reject an attacker who supplies threshold=0/blinding=0 hoping to
/// pass off a proof against the real commitment C. The honest-trace builder computes
/// C' = Poseidon2(0,0) != C, so the produced proof binds to C', and verification
/// against the real C fails.
#[test]
fn deployed_api_rejects_wrong_secret_against_committed_c() {
    use dregg_circuit::{prove_committed_threshold, verify_committed_threshold};

    let secret_threshold = BabyBear::new(680);
    let secret_blinding = BabyBear::new(0xABCDEF);
    let real_c = hash_2_to_1(secret_threshold, secret_blinding);
    let fact_commitment = BabyBear::new(0x1234_5678);

    // Attacker knows real_c and fact_commitment, but not the secrets. They try
    // value=big with threshold=0/blinding=0 (the old forge inputs).
    let attacker_witness = CommittedThresholdWitness {
        private_value: BabyBear::new(1_000_000),
        threshold: BabyBear::ZERO,
        blinding: BabyBear::ZERO,
        fact_commitment,
    };
    let proof =
        prove_committed_threshold(attacker_witness).expect("prover builds an honest-shaped proof");

    // The proof commits to C' = Poseidon2(0,0), NOT the real C. Verifying against the
    // real committed threshold C must FAIL.
    assert!(
        !verify_committed_threshold(&proof, real_c, fact_commitment),
        "attacker's proof must NOT verify against the real committed threshold C"
    );

    // Honest end-to-end still accepts.
    let honest = CommittedThresholdWitness {
        private_value: BabyBear::new(700),
        threshold: secret_threshold,
        blinding: secret_blinding,
        fact_commitment,
    };
    let honest_c = honest.compute_threshold_commitment();
    let honest_proof = prove_committed_threshold(honest).expect("honest proof");
    assert!(
        verify_committed_threshold(&honest_proof, honest_c, fact_commitment),
        "honest proof must verify"
    );
}
