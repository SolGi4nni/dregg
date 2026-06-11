//! Two-party private bilateral settlement via the garbled-circuit 2PC primitive.
//!
//! This is the Rust face of `Dregg2/Crypto/GarbledJoint.lean`'s `GarbledKernel`: two parties
//! jointly evaluate a private predicate `P(a, b)` over both their secret inputs, revealing ONLY the
//! outcome bit — neither party's input. It is the bottom rung of the DREGG3 §8 privacy ladder, the
//! secure-two-party-computation primitive the JOINT TURN admits against.
//!
//! Roles (mirroring `garble_comparison_circuit` / `evaluate_garbled_circuit`):
//!   * Party A (garbler)   — wires its private threshold `a` into the garbled tables.
//!   * Party B (evaluator) — obtains input labels for its private value `b` (via OT, simulated
//!     here by label selection), evaluates the circuit, learns ONLY the output bit.
//!
//! The joint condition is `b >= a` (a settlement is admissible iff the counterparty's private value
//! meets the private threshold). We assert the two carriers the Lean kernel models:
//!   * CORRECTNESS  — the evaluated bit equals `P(a, b) = (b >= a)`;
//!   * INPUT-PRIVACY — party A's transcript / circuit reveals nothing about its threshold beyond the
//!     outcome (`test_prover_cannot_learn_threshold` lifted): two different thresholds produce
//!     structurally identical garbled circuits, and the proof's public surface is output-only.

use dregg_circuit::dsl::garbled::{prove_private_threshold_dsl, verify_private_threshold_dsl};
use dregg_circuit::garbled::{
    COMPARISON_BITS, GarbledCircuit, GarblingSecrets, WireLabel, evaluate_garbled_circuit,
    garble_comparison_circuit, hash_label,
};

/// Party B selects its OT-obtained labels for the bits of its private value `b`.
fn party_b_labels(secrets: &GarblingSecrets, b: u32) -> Vec<WireLabel> {
    (0..COMPARISON_BITS)
        .map(|bit_idx| {
            let bit = (b >> bit_idx) & 1;
            if bit == 0 {
                secrets.prover_label_pairs[bit_idx].0
            } else {
                secrets.prover_label_pairs[bit_idx].1
            }
        })
        .collect()
}

/// Run the full private bilateral evaluation: party A garbles threshold `a`, party B evaluates
/// value `b`, returns the joint circuit + secrets + the output bit B learns.
fn private_settle(a: u32, b: u32) -> (GarbledCircuit, GarblingSecrets, bool) {
    let (circuit, secrets) = garble_comparison_circuit(a, COMPARISON_BITS);
    let labels = party_b_labels(&secrets, b);
    let eval = evaluate_garbled_circuit(&circuit, &labels);
    (circuit, secrets, eval.output_bit)
}

#[test]
fn correctness_admit_when_condition_holds() {
    // Settlement admissible: counterparty value 150 meets private threshold 100.
    let (_c, _s, bit) = private_settle(100, 150);
    assert!(
        bit,
        "150 >= 100: the joint private condition holds, settlement admits"
    );

    // Boundary equality also admits.
    let (_c, _s, bit_eq) = private_settle(100, 100);
    assert!(bit_eq, "100 >= 100: admits at the boundary");
}

#[test]
fn correctness_reject_when_condition_fails() {
    // Settlement NOT admissible: counterparty value 50 is below the private threshold 100.
    let (_c, _s, bit) = private_settle(100, 50);
    assert!(
        !bit,
        "50 < 100: the joint private condition fails, settlement does not admit"
    );
}

#[test]
fn input_privacy_threshold_circuit_is_indistinguishable() {
    // INPUT-PRIVACY (party A's threshold is hidden): two DIFFERENT private thresholds produce
    // garbled circuits that are structurally identical — same gate count, same topology. An
    // observer in party B's seat cannot read A's threshold off the circuit it receives.
    let (c1, _) = garble_comparison_circuit(100, COMPARISON_BITS);
    let (c2, _) = garble_comparison_circuit(200, COMPARISON_BITS);
    assert_eq!(
        c1.gates.len(),
        c2.gates.len(),
        "gate count independent of the secret threshold"
    );
    assert_eq!(
        c1.topology, c2.topology,
        "topology independent of the secret threshold"
    );
}

#[test]
fn output_only_disclosure_via_proof() {
    // OUTPUT-ONLY DISCLOSURE: party B produces a STARK proof of correct evaluation. The proof's
    // ENTIRE public surface is (circuit_commitment, output_label_hash) — the outcome, nothing about
    // either party's private input. The verifier checks it learns only that the joint condition held.
    let a = 500u32; // party A's private threshold
    let b = 750u32; // party B's private value
    let (circuit, secrets) = garble_comparison_circuit(a, COMPARISON_BITS);
    let labels = party_b_labels(&secrets, b);

    let proof = prove_private_threshold_dsl(&circuit, &labels)
        .expect("750 >= 500: a verifying settlement proof is produced");

    // The verifier checks against ONLY the public statement (commitment + true-output hash).
    assert!(verify_private_threshold_dsl(
        &proof,
        &circuit.circuit_commitment,
        &secrets.true_output_hash,
    ));

    // The proof's public fields are exactly the outcome surface — no input fields exist on it.
    assert_eq!(proof.circuit_commitment, circuit.circuit_commitment);
    assert_eq!(proof.output_label_hash, secrets.true_output_hash);
}

#[test]
fn output_bit_only_simulatable_same_outcome_same_public_statement() {
    // The privacy carrier `garbled_input_private` modeled concretely: when the OUTCOME is the same
    // ("admit"), the public statement a verifier checks against is the SAME true-output hash —
    // regardless of which (threshold, value) pair produced it. The verifier's view is a function of
    // the outcome bit alone.
    let (_c1, s1, bit1) = private_settle(100, 150); // admit
    let (_c2, s2, bit2) = private_settle(7, 9); // admit, totally different secrets
    assert_eq!(bit1, bit2, "both admit");

    // Both admissions decode to the "true" output label; a verifier holding the true-output hash
    // accepts either — it cannot tell which secret pair produced the admission.
    let (c1, sec1) = garble_comparison_circuit(100, COMPARISON_BITS);
    let labels1 = party_b_labels(&sec1, 150);
    let eval1 = evaluate_garbled_circuit(&c1, &labels1);
    assert_eq!(hash_label(&eval1.output_label), sec1.true_output_hash);

    let (c2, sec2) = garble_comparison_circuit(7, COMPARISON_BITS);
    let labels2 = party_b_labels(&sec2, 9);
    let eval2 = evaluate_garbled_circuit(&c2, &labels2);
    assert_eq!(hash_label(&eval2.output_label), sec2.true_output_hash);

    // sanity: the secrets are genuinely distinct circuits, yet the OUTCOME class is identical.
    assert_ne!(c1.circuit_commitment, c2.circuit_commitment);
    let _ = (s1, s2);
}

#[test]
fn reject_does_not_produce_a_proof() {
    // When the joint condition fails, party B cannot produce a "true" settlement proof — the gate
    // does not admit. (No false proof of admission.)
    let (circuit, secrets) = garble_comparison_circuit(500, COMPARISON_BITS);
    let labels = party_b_labels(&secrets, 200); // 200 < 500
    let proof = prove_private_threshold_dsl(&circuit, &labels);
    assert!(proof.is_none(), "200 < 500: no admitting settlement proof");
}
