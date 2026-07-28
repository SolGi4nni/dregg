//! Anonymous Credit Check — Zero-Knowledge Predicate Proof over a Credential
//!
//! **Story**: Alice wants a loan. The bank publishes a minimum credit score (720).
//! Alice proves she qualifies WITHOUT revealing her score — the bank and any auditor
//! learn one bit and nothing else about the number behind it.
//!
//! This demonstrates the deployed THIRD-PARTY predicate path. The bank does not know Alice's
//! score, so it cannot re-derive her fact commitment — which means the trusted-state entry point
//! (`prove_predicate_for_fact` / `verify_predicate_proof`) is the WRONG shape here: it is sound
//! only for a verifier who already holds the value. Instead this demo uses
//! `bridge::present::prove_predicate_for_fact_attested` / `verify_predicate_proof_third_party`,
//! which join TWO real IR-v2 descriptor STARKs:
//!   1. `dregg-predicate-arith-ge::threshold-v1` — Alice's value >= the bank's threshold, pinned
//!      to a fact commitment (the two Poseidon2 legs are welded INSIDE the circuit, so a value and
//!      a commitment naming a different value cannot be paired); and
//!   2. `dregg-attested-fact-membership::v1` — that same commitment is the blinded image of a
//!      member of the credit bureau's published `facts_root`.
//!
//! The join is what makes it sound for a stranger: the bank feeds the root IT trusts, and the
//! only commitment it will accept is the one a STARK manufactured against that root. A
//! prover-chosen commitment has nowhere to enter. (The old vacuous form of this check read the
//! expected commitment straight off the prover's own struct — the `x == x` gate.)
//!
//! **Privacy guarantees (what this code actually delivers):**
//! - Bank learns: 1 bit (pass/fail). Nothing about Alice's actual score.
//! - The attested shape carries NO decommitment (`blinding: None`), so a proof-holder has nothing
//!   to brute-force — unlike the trusted-state shape, whose disclosed opening lets a holder test
//!   candidate values over a small domain.
//!
//! # RETIRED CAPABILITY — the bank's threshold is PUBLIC here, and that is a real change
//!
//! This demo used to prove a COMMITTED threshold: the bound was hidden behind
//! `Poseidon2(threshold, blinding)` so auditors learned only "some committed value satisfies some
//! committed threshold". That AIR (`dregg_circuit::committed_threshold::{prove,verify}_committed_threshold`)
//! was deleted with the hand-STARK engine, and NO IR-v2 descriptor has been emitted to replace it —
//! `bridge::present::prove_committed_threshold` is hard-coded to return `None`, and the
//! `verify_committed_threshold_proof` that used to sit beside it returning `false` for every
//! input has been DELETED (an uncalled verifier that decides nothing reads like a check that
//! happens). There is nothing to call.
//!
//! So the threshold (720) is now a PUBLIC input, visible to every verifier. The value stays
//! private, which is the property this demo still genuinely shows. Restoring the hidden-threshold
//! variant needs an emitted committed-threshold descriptor registered in
//! `dregg_circuit::descriptor_by_name`.
//!
//! Run with: cargo run --release -p dregg-demo-agent --example anonymous_credit_check

use std::time::Instant;

use dregg_bridge::present::{
    Predicate, fresh_predicate_blinding, prove_predicate_for_fact_attested,
    verify_predicate_proof_third_party,
};
use dregg_circuit::BabyBear;
use dregg_circuit::attested_fact_membership_witness::attested_facts_root;
use dregg_circuit::predicate_arith_witness::FactBinding;
use dregg_circuit::refusal::must_refuse_or_unsat_panic;

/// The credit bureau's depth-2 co-path for Alice's score leaf in its facts tree.
///
/// The emitted `dregg-attested-fact-membership::v1` descriptor pins the member to the LEFTMOST
/// child slot at each level and is depth-2, so exactly two sibling triples are required.
fn bureau_siblings() -> [[BabyBear; 3]; 2] {
    [
        [
            BabyBear::new(0xA1),
            BabyBear::new(0xA2),
            BabyBear::new(0xA3),
        ],
        [
            BabyBear::new(0xB1),
            BabyBear::new(0xB2),
            BabyBear::new(0xB3),
        ],
    ]
}

/// The `facts_root` the credit bureau PUBLISHES at issuance, derived independently of any
/// presentation.
///
/// This is the point of the whole third-party construction: the bank verifies against THIS value,
/// never against `proof.attestation.facts_root`. Reading the root off the prover's own proof would
/// let a prover pick both the root and a fact under it, which attests nothing at all.
///
/// It delegates to `dregg_circuit`'s own `attested_facts_root` rather than recomputing the Merkle
/// legs here, so the bureau's published root cannot silently drift from the root the emitted
/// `dregg-attested-fact-membership::v1` descriptor actually authenticates.
fn bureau_facts_root(fact_hash: BabyBear, siblings: &[[BabyBear; 3]; 2]) -> BabyBear {
    attested_facts_root(fact_hash, siblings).expect("depth-2 co-path is the emitted descriptor's")
}

fn main() {
    println!("===============================================================================");
    println!("  ANONYMOUS CREDIT CHECK");
    println!("  Zero-Knowledge Predicate Proof over a Credential");
    println!("===============================================================================");
    println!();
    println!("  Alice wants a loan from First National Bank.");
    println!("  The bank publishes a minimum credit score.");
    println!("  Alice will prove she qualifies WITHOUT revealing her score.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: BANK SETUP (verifier side)
    // =========================================================================
    println!("--- Phase 1: BANK SETUP (verifier) ---");
    println!();

    // The bank's lending threshold: 720 (minimum credit score for approval).
    //
    // This is a PUBLIC input to the proof — it is `Predicate::Gte(720)`, and it travels on the
    // proof itself as `proof.predicate`. The hidden-threshold (committed) variant is retired; see
    // the module header. Nothing below pretends otherwise.
    let bank_threshold: u32 = 720;

    println!("  Bank's lending threshold:  720 (PUBLIC — it is the proof's public input)");
    println!();
    println!("  Alice needs the threshold to prove against it; so does every verifier.");
    println!("  What stays private is her SCORE, which is the point of the exercise.");
    println!();

    // =========================================================================
    // PHASE 2: ALICE'S CREDENTIAL (prover side)
    // =========================================================================
    println!("--- Phase 2: ALICE'S CREDENTIAL (prover) ---");
    println!();

    // Alice's actual credit score: 785. This is her private attribute.
    let alice_score: u32 = 785;

    // The credential's FACT IDENTITY: everything the commitment covers EXCEPT the value.
    //
    // The value is `terms[0]` and is handed to the prover separately. That is deliberate: the old
    // API took an opaque `fact_hash` beside a value, which let the two name DIFFERENT facts, and
    // for `>=` the circuit did not relate them — so the mispairing was a provable forgery rather
    // than a caller mistake. Terms are not opaque, so the pairing cannot come apart.
    let credential_state_root = BabyBear::new(88888); // credit bureau's state root
    let score_fact = FactBinding {
        predicate_sym: BabyBear::new(100), // "credit_score"
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: credential_state_root,
    };

    // ---- ISSUANCE (the credit bureau, who DOES know the score, does this once and publishes).
    let siblings = bureau_siblings();
    let alice_fact_hash = score_fact.fact_hash_of(BabyBear::from_u64(alice_score as u64));
    let published_facts_root = bureau_facts_root(alice_fact_hash, &siblings);

    println!("  Alice's credit score:    785 (SECRET — only Alice and the bureau know)");
    println!(
        "  Credential state root:   {} (PUBLISHED by the credit bureau)",
        credential_state_root.as_u32()
    );
    println!(
        "  Published facts root:    {} (PUBLISHED by the credit bureau)",
        published_facts_root.as_u32()
    );
    println!();
    println!("  The bank will verify against the PUBLISHED root above — not against anything");
    println!("  Alice hands it. That is what stops her naming a credential of her own invention.");
    println!();

    // =========================================================================
    // PHASE 3: PROOF GENERATION
    // =========================================================================
    println!("--- Phase 3: STARK PROOF GENERATION ---");
    println!();

    let proof_start = Instant::now();

    // A FRESH blinding per showing. This is what makes two presentations of the SAME credential
    // carry different commitments, so a colluding bank and auditor cannot link them.
    let showing_blinding = fresh_predicate_blinding();

    // Generate the joined STARK pair. Real proving work happens here.
    let proof = prove_predicate_for_fact_attested(
        alice_score,
        score_fact,
        showing_blinding,
        &Predicate::Gte(bank_threshold),
        &siblings,
    )
    .expect("785 >= 720 is TRUE and Alice's fact is a genuine member — this must prove");

    let proof_time = proof_start.elapsed();

    println!("  Generating STARK proofs (predicate + fact membership)...");
    println!();
    println!("  Proof generated:");
    println!("    Time: {:.2}ms", proof_time.as_secs_f64() * 1000.0);
    println!("    Descriptors: dregg-predicate-arith-ge::threshold-v1");
    println!("                 dregg-attested-fact-membership::v1");
    println!();

    // The attested shape must carry an attestation and must NOT carry a decommitment. If this
    // ever flipped, the proof would be the trusted-state shape wearing the wrong name, and the
    // bank's third-party verification below would be checking something weaker than it claims.
    assert!(
        proof.attestation.is_some(),
        "the third-party shape must carry a fact attestation"
    );
    assert!(
        proof.blinding.is_none(),
        "the third-party shape must NOT disclose the opening — there would be nothing stopping a \
         proof-holder from brute-forcing the score over the small credit-score domain"
    );

    println!("  What the proof encodes (hidden in the witness):");
    println!("    - Alice's score (785) is in the trace but NEVER leaves her machine");
    println!("    - The comparison 785 >= 720 is checked in-circuit against the PUBLIC bound");
    println!("    - The fact hash and blinding stay hidden witnesses: no opening travels");
    println!("    - The membership STARK ties the commitment to the bureau's published root");
    println!();

    // =========================================================================
    // PHASE 4: VERIFICATION (bank and auditors)
    // =========================================================================
    println!("--- Phase 4: VERIFICATION ---");
    println!();

    let verify_start = Instant::now();

    // The bank verifies against the roots the CREDIT BUREAU published. It never learned Alice's
    // score and never needed to: the membership STARK is what manufactures the commitment the
    // predicate STARK is then checked against.
    let bank_verify =
        verify_predicate_proof_third_party(&proof, published_facts_root, credential_state_root);
    let bank_time = verify_start.elapsed();
    assert!(
        bank_verify,
        "the bank must accept a genuine proof against the bureau's published roots"
    );

    // The bank must also pin WHICH statement it accepted. `verify_predicate_proof_third_party`
    // checks that the proof is valid; it does not check that the bound is the bank's bound. A
    // proof of `score >= 300` is perfectly valid and would pass the call above — so a lender that
    // skipped this check would approve on a threshold the borrower picked. See Attack 2 below.
    assert_eq!(
        proof.predicate,
        Predicate::Gte(bank_threshold),
        "the accepted proof must be about the BANK's threshold, not one Alice chose"
    );

    println!("  Bank verification: PASS");
    println!("    Checked: fact-membership STARK verifies against the bureau's published root");
    println!("    Checked: the attested commitment is the one the predicate STARK pins");
    println!("    Checked: predicate STARK verifies against that attested commitment");
    println!("    Checked: the proven bound is the bank's own 720");
    println!("    Time: {:.3}ms", bank_time.as_secs_f64() * 1000.0);
    println!();
    println!("  The bank learned exactly one bit. It still does not know whether Alice's");
    println!("  score is 720, 785, or 850 — only that it is at least 720.");
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
    println!("  │                 │ Bank's threshold (720) │ already knew her score  │");
    println!("  │                 │ Her showing blinding   │                         │");
    println!("  ├───────────────────────────────────────────────────────────────────┤");
    println!("  │  Bank (verifier)│ Pass/fail (1 bit)      │ Alice's actual score    │");
    println!("  │                 │ The threshold (public) │ How far above the bar   │");
    println!("  │                 │ Bureau's public roots  │ Alice's identity*       │");
    println!("  ├───────────────────────────────────────────────────────────────────┤");
    println!("  │  Auditor        │ Proof is valid         │ The score               │");
    println!("  │                 │ The threshold (public) │ Which bureau fact it is │");
    println!("  │                 │ One blinded commitment │ Whether two showings are│");
    println!("  │                 │                        │ the same credential     │");
    println!("  └───────────────────────────────────────────────────────────────────┘");
    println!();
    println!("  * In this demo, Alice's identity is not linked to the fact commitment.");
    println!("    In production, the credential system uses ZK ring membership to");
    println!("    further decouple identity from the proof.");
    println!();
    println!("  NOTE: the threshold is PUBLIC in the 'Cannot Determine' sense above — the");
    println!("  committed-threshold AIR that used to hide it is retired (see the module header).");
    println!();

    // =========================================================================
    // PHASE 6: ADVERSARY SCENARIOS
    // =========================================================================
    println!("--- Phase 6: ADVERSARY SCENARIOS ---");
    println!();

    // Attack 1: Alice tries to prove with a score below threshold.
    //
    // A false comparison is refused three ways, and this counts all three: the witness builder
    // declines (`None`), or a produced proof fails verification, or — WITHOUT `--release` — p3's
    // debug `check_constraints` PANICS on the unsatisfiable base gate. `must_refuse_or_unsat_panic`
    // is the discriminator that accepts exactly those and REDS on anything else, so a stray unwrap
    // can never launder itself as a refusal, and an ACCEPTED forgery aborts the demo loudly.
    println!("  Attack 1: Alice lies about her score (pretends 650 >= 720)");
    must_refuse_or_unsat_panic("Alice lies about her score (650 >= 720)", || {
        match prove_predicate_for_fact_attested(
            650, // below the bar
            score_fact,
            fresh_predicate_blinding(),
            &Predicate::Gte(bank_threshold),
            &siblings,
        ) {
            None => Err("the prover refused the false statement".to_string()),
            // If a proof object came back, it must not survive verification against the roots the
            // bank trusts. (The bureau's published root is for the 785 leaf, so a 650 fact is not
            // a member of it either — two independent reasons to refuse.)
            Some(p) => {
                if verify_predicate_proof_third_party(
                    &p,
                    published_facts_root,
                    credential_state_root,
                ) {
                    Ok(())
                } else {
                    Err("the proof failed to verify".to_string())
                }
            }
        }
    });
    println!("    Result: refused. The comparison tooth is a real constraint, not a check the");
    println!("    prover performs on itself. [BLOCKED]");
    println!();

    // Attack 2: Alice proves a TRUE statement — against a bar she picked herself.
    println!("  Attack 2: Alice proves against her own, easier threshold (785 >= 600)");
    let easier_proof = prove_predicate_for_fact_attested(
        alice_score,
        score_fact,
        fresh_predicate_blinding(),
        &Predicate::Gte(600),
        &siblings,
    )
    .expect("785 >= 600 is TRUE, so this genuinely proves");

    // NEUTERED CANARY: the proof is internally sound — it really does verify. So what refuses it
    // below is the BOUND mismatch, not a broken proof. Without this pole the assertion after it
    // could pass for the wrong reason.
    assert!(
        verify_predicate_proof_third_party(
            &easier_proof,
            published_facts_root,
            credential_state_root
        ),
        "CANARY: the easier-bar proof must itself be valid, or Attack 2 is not demonstrating a \
         BOUND mismatch"
    );
    // THE GATE: the bank compares the proven bound to its OWN policy.
    assert_ne!(
        easier_proof.predicate,
        Predicate::Gte(bank_threshold),
        "the easier-bar proof must not claim the bank's bound"
    );
    println!("    Proof against bar 600: VALID (785 >= 600 really is true)");
    println!("    Bank checks the bound it accepted: 600 != 720 => REJECTED");
    println!("    A valid proof of the WRONG statement is still the wrong statement. [BLOCKED]");
    println!();

    // Attack 3: Someone tries to recover the score from what travels.
    println!("  Attack 3: Auditor tries to recover the score from the presentation");
    println!("    The attested shape carries NO opening (blinding: None), so there is no");
    println!("    decommitment to test candidate scores against — an auditor holding the proof");
    println!("    cannot brute-force the ~550-wide credit-score domain. [INFEASIBLE]");
    println!("    (The trusted-state shape DOES disclose an opening and is brute-forceable over");
    println!("    a small domain — that is why this demo uses the third-party shape.)");
    println!();

    // Attack 4: a genuine proof about a credential from a DIFFERENT (attacker-run) bureau.
    println!(
        "  Attack 4: Mallory attests a real proof under a bureau root the bank does not trust"
    );
    let foreign_state_root = BabyBear::new(99999);
    let mallory_fact = FactBinding {
        predicate_sym: BabyBear::new(100),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
        state_root: foreign_state_root,
    };
    let mallory_score: u32 = 800;
    let mallory_proof = prove_predicate_for_fact_attested(
        mallory_score,
        mallory_fact,
        fresh_predicate_blinding(),
        &Predicate::Gte(bank_threshold),
        &siblings,
    )
    .expect("800 >= 720 is TRUE under Mallory's own root");
    let mallory_root = bureau_facts_root(
        mallory_fact.fact_hash_of(BabyBear::from_u64(mallory_score as u64)),
        &siblings,
    );

    // NEUTERED CANARY: against MALLORY'S OWN root the proof verifies. So the refusal below is
    // about the root the bank trusts, not about a malformed proof.
    assert!(
        verify_predicate_proof_third_party(&mallory_proof, mallory_root, foreign_state_root),
        "CANARY: Mallory's proof must verify against Mallory's OWN root, or Attack 4 is not \
         demonstrating a ROOT-MISMATCH refusal"
    );
    // THE GATE: against the bureau root the BANK trusts, it is refused.
    assert!(
        !verify_predicate_proof_third_party(
            &mallory_proof,
            published_facts_root,
            credential_state_root
        ),
        "SOUNDNESS: a proof attested under a root the bank does NOT trust must be REJECTED — \
         nothing ties it to the real bureau's credential"
    );
    println!("    Mallory's proof against Mallory's own root:  ACCEPTED (it is a real proof)");
    println!("    Same proof against the REAL bureau's root:   REJECTED");
    println!("    Self-issued credentials do not become real by being provable. [BLOCKED]");
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
    println!("    - IR-v2 descriptor prover (plonky3 batch STARK)");
    println!("    - dregg-predicate-arith-ge::threshold-v1   (the comparison)");
    println!("    - dregg-attested-fact-membership::v1       (the credential binding)");
    println!();
    println!("  This is something you CANNOT do with traditional PKI, OAuth, or");
    println!("  any non-ZK system: prove a predicate about a secret value held in");
    println!("  someone else's credential, to a stranger, with cryptographic");
    println!("  soundness, in milliseconds.");
    println!();
    println!("  Note the honest boundary: the STARKs above inherit the undischarged");
    println!("  FRI soundness floor, and the threshold is public (the committed-");
    println!("  threshold AIR that hid it is retired — see the module header).");
    println!("===============================================================================");
}
