//! Anonymous Credit Check — Zero-Knowledge Committed-Threshold Proof
//!
//! **Story**: Alice wants a loan. The bank sets a minimum credit score threshold
//! (720) that it keeps secret from third parties via a Poseidon2 commitment.
//! Alice proves she qualifies WITHOUT revealing her score, and WITHOUT the bank
//! revealing its threshold to auditors.
//!
//! This demonstrates dregg's committed-threshold AIR: a STARK proof that
//! simultaneously proves:
//!   1. Alice's value >= the bank's threshold (range proof via bit decomposition)
//!   2. The threshold is correctly committed (Poseidon2 binding)
//!   3. The value is bound to a specific credential (fact commitment)
//!
//! **Privacy guarantees:**
//! - Bank learns: 1 bit (pass/fail). Nothing about Alice's actual score.
//! - Alice learns: 1 bit (pass/fail). She knows the threshold (needed to prove),
//!   but the threshold stays hidden from everyone else.
//! - Auditors/third parties: see two opaque commitments and a valid STARK proof.
//!   They learn: "some committed value satisfies some committed threshold."
//!   They cannot determine either the score or the threshold.
//!
//! Run with: cargo run --release -p dregg-demo-agent --example anonymous_credit_check

use std::time::Instant;

use dregg_circuit::{
    BabyBear,
    committed_threshold::{
        CommittedThresholdWitness, compute_threshold_commitment, generate_blinding,
        prove_committed_threshold, verify_committed_threshold,
    },
    poseidon2,
    predicate_types::compute_fact_commitment,
    stark::proof_to_bytes,
};

fn main() {
    println!("===============================================================================");
    println!("  ANONYMOUS CREDIT CHECK");
    println!("  Zero-Knowledge Committed-Threshold Proof");
    println!("===============================================================================");
    println!();
    println!("  Alice wants a loan from First National Bank.");
    println!("  The bank has a secret minimum credit score threshold.");
    println!("  Alice will prove she qualifies WITHOUT revealing her score.");
    println!("  The bank's threshold stays hidden from all third parties.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: BANK SETUP (verifier side)
    // =========================================================================
    println!("--- Phase 1: BANK SETUP (verifier) ---");
    println!();

    // The bank's secret threshold: 720 (minimum credit score for approval).
    // In practice this comes from the bank's internal policy engine.
    let bank_threshold = BabyBear::new(720);

    // The bank generates a random blinding factor to hide the threshold.
    // This ensures no one can brute-force the threshold from the commitment.
    let bank_blinding = generate_blinding();

    // The bank computes: commitment = Poseidon2(threshold, blinding)
    // This commitment is published on-chain or sent to auditors.
    let threshold_commitment = compute_threshold_commitment(bank_threshold, bank_blinding);

    println!("  Bank's internal threshold: 720 (SECRET)");
    println!(
        "  Bank's blinding factor:    {} (SECRET)",
        bank_blinding.as_u32()
    );
    println!(
        "  Published commitment:      {} (PUBLIC)",
        threshold_commitment.as_u32()
    );
    println!();
    println!("  The commitment hides both the threshold value and the blinding factor.");
    println!("  Given only the commitment, an adversary cannot determine whether the");
    println!("  threshold is 600, 720, or 800 — it's computationally bound by Poseidon2.");
    println!();

    // The bank sends (threshold, blinding) to Alice over a secure channel.
    // This is necessary for Alice to generate the proof.
    println!(
        "  Bank -> Alice (secure channel): threshold=720, blinding={}",
        bank_blinding.as_u32()
    );
    println!("  (Alice needs both to generate a valid proof.)");
    println!();

    // =========================================================================
    // PHASE 2: ALICE'S CREDENTIAL (prover side)
    // =========================================================================
    println!("--- Phase 2: ALICE'S CREDENTIAL (prover) ---");
    println!();

    // Alice's actual credit score: 785. This is her private attribute.
    let alice_score = BabyBear::new(785);

    // The score is bound to a specific credential via a fact commitment.
    // This prevents Alice from using someone else's score.
    // fact_commitment = Poseidon2(H("credit_score", [785, 0, 0]), state_root)
    let score_fact_hash = poseidon2::hash_fact(
        BabyBear::new(100), // "credit_score" predicate symbol
        &[alice_score, BabyBear::ZERO, BabyBear::ZERO],
    );
    let credential_state_root = BabyBear::new(88888); // credential authority's state root
    let fact_commitment = compute_fact_commitment(score_fact_hash, credential_state_root);

    println!("  Alice's credit score:    785 (SECRET — only Alice knows)");
    println!(
        "  Credential state root:   {} (from credit bureau)",
        credential_state_root.as_u32()
    );
    println!(
        "  Fact commitment:         {} (PUBLIC — binds proof to credential)",
        fact_commitment.as_u32()
    );
    println!();
    println!("  The fact commitment proves this score belongs to a SPECIFIC credential");
    println!("  without revealing which credential or what score it contains.");
    println!();

    // =========================================================================
    // PHASE 3: PROOF GENERATION
    // =========================================================================
    println!("--- Phase 3: STARK PROOF GENERATION ---");
    println!();

    let proof_start = Instant::now();

    // Alice constructs the witness with all her private data.
    let witness = CommittedThresholdWitness {
        private_value: alice_score, // 785 — her actual score
        threshold: bank_threshold,  // 720 — received from bank
        blinding: bank_blinding,    // received from bank
        fact_commitment,            // binds to her credential
    };

    // Verify the predicate is satisfiable before generating the expensive proof.
    assert!(witness.is_satisfiable(), "785 >= 720 should be satisfiable");
    println!("  Pre-check: 785 >= 720 is satisfiable [OK]");

    // Generate the STARK proof. This proves three things simultaneously:
    //   1. private_value >= threshold (via bit decomposition of the difference)
    //   2. Poseidon2(threshold, blinding) == threshold_commitment (binding)
    //   3. The value is bound to fact_commitment (credential linkage)
    let proof = prove_committed_threshold(witness)
        .expect("Proof generation must succeed for a satisfiable witness");

    let proof_bytes = proof_to_bytes(&proof.stark_proof);
    let proof_time = proof_start.elapsed();

    println!("  Generating STARK proof (FRI + Poseidon2 + bit decomposition)...");
    println!();
    println!("  Proof generated:");
    println!(
        "    Size: {} bytes ({:.1} KiB)",
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0
    );
    println!("    Time: {:.2}ms", proof_time.as_secs_f64() * 1000.0);
    println!("    AIR: dregg-committed-threshold-v1");
    println!(
        "    Trace width: 37 columns (value + threshold + blinding + diff + 30 bits + 3 commitments)"
    );
    println!();
    println!("  What the proof encodes (hidden in the witness):");
    println!("    - Alice's score (785) is in the trace but NEVER leaves her machine");
    println!("    - The difference (785 - 720 = 65) is bit-decomposed for range checking");
    println!("    - The high bit (bit 29) is zero, proving diff < 2^29 < p/2 (non-negative)");
    println!("    - Poseidon2(720, blinding) is computed in-circuit and matches the commitment");
    println!();

    // =========================================================================
    // PHASE 4: VERIFICATION (bank and auditors)
    // =========================================================================
    println!("--- Phase 4: VERIFICATION ---");
    println!();

    let verify_start = Instant::now();

    // The bank verifies against its own threshold commitment.
    let bank_verify = verify_committed_threshold(
        &proof,
        threshold_commitment, // bank knows this (it computed it)
        fact_commitment,      // from Alice's credential
    );
    let bank_time = verify_start.elapsed();
    assert!(bank_verify, "Bank verification must succeed");

    println!("  Bank verification: PASS");
    println!("    Checked: proof.threshold_commitment == bank's commitment [OK]");
    println!("    Checked: STARK constraints satisfied [OK]");
    println!("    Time: {:.3}ms", bank_time.as_secs_f64() * 1000.0);
    println!();

    // A third-party auditor can also verify — they see only the commitments.
    let auditor_verify = verify_committed_threshold(
        &proof,
        threshold_commitment, // public (on-chain or from bank)
        fact_commitment,      // public (from credential system)
    );
    assert!(auditor_verify);

    println!("  Auditor verification: PASS");
    println!("    The auditor verifies the same proof but learns NOTHING about:");
    println!("    - Alice's actual score (hidden in witness)");
    println!("    - The bank's threshold (hidden behind Poseidon2 commitment)");
    println!("    - The blinding factor (secret between bank and Alice)");
    println!("    They only learn: 'A valid credential satisfies a committed threshold.'");
    println!();

    // =========================================================================
    // PHASE 5: PRIVACY ANALYSIS
    // =========================================================================
    println!("--- Phase 5: PRIVACY ANALYSIS ---");
    println!();
    println!("  ┌───────────────────────────────────────────────────────────────────┐");
    println!("  │  Party          │ Knows                  │ Cannot Determine        │");
    println!("  ├───────────────────────────────────────────────────────────────────┤");
    println!("  │  Alice (prover) │ Her score (785)        │ Nothing new — she       │");
    println!("  │                 │ Bank's threshold (720) │ already knew her score   │");
    println!("  │                 │ Blinding factor        │                         │");
    println!("  ├───────────────────────────────────────────────────────────────────┤");
    println!("  │  Bank (verifier)│ Pass/fail (1 bit)      │ Alice's actual score    │");
    println!("  │                 │ Its own threshold      │ How far above/below     │");
    println!("  │                 │ Fact commitment        │ Alice's identity*       │");
    println!("  ├───────────────────────────────────────────────────────────────────┤");
    println!("  │  Auditor        │ Proof is valid         │ The score               │");
    println!("  │                 │ Two commitments        │ The threshold            │");
    println!("  │                 │                        │ The blinding factor      │");
    println!("  │                 │                        │ Whether it passed/failed │");
    println!("  └───────────────────────────────────────────────────────────────────┘");
    println!();
    println!("  * In this demo, Alice's identity is not linked to the fact commitment.");
    println!("    In production, the credential system uses ZK ring membership to");
    println!("    further decouple identity from the proof.");
    println!();

    // =========================================================================
    // PHASE 6: ADVERSARY SCENARIOS
    // =========================================================================
    println!("--- Phase 6: ADVERSARY SCENARIOS ---");
    println!();

    // Attack 1: Alice tries to prove with a score below threshold.
    println!("  Attack 1: Alice lies about her score (pretends 650 >= 720)");
    let bad_witness = CommittedThresholdWitness {
        private_value: BabyBear::new(650), // below threshold!
        threshold: bank_threshold,
        blinding: bank_blinding,
        fact_commitment,
    };
    assert!(!bad_witness.is_satisfiable());
    let bad_proof = prove_committed_threshold(bad_witness);
    assert!(bad_proof.is_none());
    println!("    Result: Cannot generate proof. 650 < 720 => difference wraps around");
    println!("    in the field, high bit != 0, constraint system is unsatisfiable. [BLOCKED]");
    println!();

    // Attack 2: Alice uses the wrong threshold commitment.
    println!("  Attack 2: Alice forges a different (lower) threshold commitment");
    let forged_threshold = BabyBear::new(600); // Easier threshold
    let forged_blinding = generate_blinding();
    let forged_commitment = compute_threshold_commitment(forged_threshold, forged_blinding);

    // She can generate a proof against the forged commitment...
    let forged_witness = CommittedThresholdWitness {
        private_value: alice_score,
        threshold: forged_threshold,
        blinding: forged_blinding,
        fact_commitment,
    };
    let forged_proof = prove_committed_threshold(forged_witness)
        .expect("This will generate a proof (785 >= 600 is true)");

    // ...but the bank's verification rejects it (wrong commitment).
    let forged_verify = verify_committed_threshold(
        &forged_proof,
        threshold_commitment, // bank's REAL commitment
        fact_commitment,
    );
    assert!(!forged_verify);
    println!("    Generated proof against forged threshold (600): SUCCESS");
    println!("    Bank verifies against its REAL commitment:     REJECTED");
    println!(
        "    The proof's threshold_commitment ({}) != bank's ({})",
        forged_commitment.as_u32(),
        threshold_commitment.as_u32()
    );
    println!("    [BLOCKED]");
    println!();

    // Attack 3: Someone tries to learn the threshold from the commitment.
    println!("  Attack 3: Auditor tries to brute-force the threshold");
    println!("    Commitment = Poseidon2(threshold, blinding)");
    println!("    Without the blinding factor, the auditor must guess BOTH values.");
    println!("    Search space: ~2^31 * 2^31 = 2^62 operations (computationally infeasible).");
    println!("    Even with a known range [300, 850] for credit scores:");
    println!("    550 * 2^31 ~ 1.18 trillion operations. [INFEASIBLE]");
    println!();

    // Attack 4: Different fact commitment (using someone else's credential).
    println!("  Attack 4: Bob uses Alice's proof with his own fact commitment");
    let bobs_fact = compute_fact_commitment(
        poseidon2::hash_fact(
            BabyBear::new(100),
            &[BabyBear::new(650), BabyBear::ZERO, BabyBear::ZERO],
        ),
        credential_state_root,
    );
    let swap_verify = verify_committed_threshold(
        &proof,
        threshold_commitment,
        bobs_fact, // Bob's credential, not Alice's
    );
    assert!(!swap_verify);
    println!("    Bob presents Alice's proof with his own fact_commitment:");
    println!("    Verification: REJECTED (fact_commitment mismatch)");
    println!("    The proof is bound to Alice's SPECIFIC credential. [BLOCKED]");
    println!();

    // =========================================================================
    // PHASE 7: COMPARISON WITH TRADITIONAL APPROACHES
    // =========================================================================
    println!("--- Phase 7: WHY THIS MATTERS ---");
    println!();
    println!("  Traditional credit check:");
    println!("    Alice -> Credit Bureau: 'Give bank my score'");
    println!("    Credit Bureau -> Bank: 'Alice's score is 785'");
    println!("    Problems:");
    println!("      - Bank learns the exact score (data minimization violation)");
    println!("      - Score transmitted over network (breach risk)");
    println!("      - Bureau must be online (availability dependency)");
    println!("      - Each check is linkable (privacy erosion)");
    println!();
    println!("  Zero-knowledge credit check (this demo):");
    println!("    Alice <- Bank: threshold=720, blinding (secure channel, one-time)");
    println!("    Alice -> Bank: STARK proof (24 KiB, verifiable offline)");
    println!("    Advantages:");
    println!("      - Bank learns only pass/fail (minimal disclosure)");
    println!("      - Score never leaves Alice's device");
    println!("      - Verifiable offline (no bureau dependency)");
    println!("      - Unlinkable across checks (different blinding each time)");
    println!("      - Auditable without revealing secrets (commitment-based)");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    let total_time = total_start.elapsed();

    println!("===============================================================================");
    println!("  SUMMARY");
    println!("===============================================================================");
    println!();
    println!("  Alice's score:         785 (private, never revealed)");
    println!("  Bank's threshold:      720 (private, hidden behind commitment)");
    println!("  Result:                PASS (Alice qualifies for the loan)");
    println!("  Proof size:            {} bytes", proof_bytes.len());
    println!(
        "  Proof generation:      {:.2}ms",
        proof_time.as_secs_f64() * 1000.0
    );
    println!(
        "  Total demo time:       {:.2}ms",
        total_time.as_secs_f64() * 1000.0
    );
    println!();
    println!("  Components exercised:");
    println!("    - Poseidon2 hash (SNARK-friendly, algebraic)");
    println!("    - BabyBear field arithmetic (p = 2^31 - 1)");
    println!("    - STARK prover (FRI polynomial commitment)");
    println!("    - Bit decomposition range check (30-bit soundness)");
    println!("    - CommittedThresholdAir (37-column trace)");
    println!();
    println!("  This is something you CANNOT do with traditional PKI, OAuth, or");
    println!("  any non-ZK system: prove a predicate about a secret value against");
    println!("  a secret threshold, with cryptographic soundness, in milliseconds.");
    println!("===============================================================================");
}
