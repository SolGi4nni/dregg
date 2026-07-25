//! Private Hiring — Cross-Party Predicate Flow End-to-End
//!
//! Demonstrates the complete cross-party predicate verification flow:
//!
//! 1. A credential bureau (issuer) attests the candidate's facts tree and publishes one
//!    `facts_root` per attribute. The company trusts the bureau's roots; it never sees a value.
//!
//! 2. A company (Agent A) posts a hiring intent with predicate requirements:
//!    - reputation >= 80
//!    - experience_years >= 3
//!    - salary_expectation <= 200000
//!    - skills_rust != 0 (set membership, expressed directly as NEQ from zero)
//!
//! 3. A candidate (Agent B) discovers this intent and proves all four predicates WITHOUT
//!    revealing exact values:
//!    - reputation = 95 -> proves >= 80
//!    - experience = 7 -> proves >= 3
//!    - salary = 150000 -> proves <= 200000
//!    - skills_rust = 1 -> proves != 0 (has the skill)
//!
//! 4. Agent B fulfills the intent with the predicate proofs attached.
//!
//! 5. Agent A verifies the fulfillment: every predicate proof checks out, state roots are fresh.
//!
//! 6. Conditional hire: "grant the capability IFF all four predicates verify".
//!
//! 7. Selective disclosure: the candidate reveals "experience >= 5" to stand out.
//!
//! 8. Attack resistance: unqualified candidates, invented facts, stale state, wrong thresholds.
//!
//! # Which API this runs on
//!
//! The monolithic hand-STARK predicate engine (`dregg_circuit::{prove_predicate,
//! verify_predicate}`) was RETIRED. Everything here runs on the IR-v2 descriptor prover through
//! `dregg_bridge::present`, in the THIRD-PARTY (attested) shape:
//!
//! * `prove_predicate_for_fact_attested` emits a real IR-v2 descriptor STARK for the comparison
//!   PLUS a `dregg-attested-fact-membership::v1` STARK proving the proof's `fact_commitment` is the
//!   blinded image of a `fact_hash` that is a MEMBER of the issuer's `facts_root`, at a pinned
//!   `state_root`. It carries NO decommitment (`blinding: None`) — nothing for a proof-holder to
//!   brute-force.
//! * `verify_predicate_proof_third_party(proof, facts_root, state_root)` is what the company runs.
//!   The trusted-state entry point (`verify_predicate_proof`) is deliberately NOT used here: it is
//!   sound only for a verifier that already KNOWS the value it derives the expected commitment
//!   from, and the whole point of this demo is that the company does not. Feeding a proof's own
//!   `fact_commitment` back into it is the `x == x` gate that accepts everything.
//!
//! The `facts_root` fed to every verification below comes from the ISSUER (`issuer_facts_root`),
//! never from `proof.attestation.facts_root`. That is the parameter that refuses a candidate who
//! proves a true statement about a fact it INVENTED — Attack 3.
//!
//! # ⚑ THE COMPOUND REQUIREMENT IS COMPOSED VERIFIER-SIDE, NOT IN ONE CIRCUIT
//!
//! Phase 6 combines the four requirements with `dsl::predicates::evaluate_formula` over a
//! `BooleanFormula::And`. Each CONJUNCT is STARK-backed — four real descriptor proofs, each
//! independently verified. The AND itself is **evaluated by the verifier in plain Rust, after
//! checking each proof**. It is NOT proven inside one circuit, and this is NOT "a single compound
//! proof": `dregg_circuit::dsl::predicates::{prove_compound_predicate, verify_compound_predicate}`
//! were DELETED with the hand-STARK engine, and while a `compound_predicate_circuit_descriptor()`
//! still exists in `circuit/src/dsl/predicates/compound.rs` it is NOT registered in
//! `dregg_circuit::descriptor_by_name`, so there is no way to produce or check an in-circuit
//! compound proof today. The in-circuit compound capability is RETIRED. What survives — and what
//! runs below — is: N independent STARKs, one boolean each, combined by the verifier.
//!
//! The booleans fed to `evaluate_formula` are the RETURN VALUES of
//! `verify_predicate_proof_third_party`. Never a hardcoded `vec![true; 4]`.
//!
//! # Privacy Properties
//!
//! - Company never learns: exact reputation score, exact years of experience, exact salary
//!   expectation, or any other capabilities the candidate holds.
//! - Candidate never learns: who else applied, what other roles are open, or the company's
//!   identity (anonymous commitment).
//! - Observers learn: NOTHING. The fulfillment is sent directly (not broadcast).
//!
//! # Self-checking
//!
//! Every "PASSED" this prints is backed by an `assert!` on the actual verification result, and
//! every attack pole asserts the REFUSAL. Running this to completion is the claim.
//!
//! Run with: cargo run --release -p dregg-demo-agent --example private_hiring

use std::time::Instant;

use dregg_bridge::BridgePredicateProof;
use dregg_bridge::present::{
    FactTerms, Predicate, fresh_predicate_blinding, prove_predicate_for_fact_attested,
    verify_predicate_proof_third_party,
};
use dregg_circuit::attested_fact_membership_witness::attested_facts_root;
use dregg_circuit::dsl::predicates::{BooleanFormula, evaluate_formula};
use dregg_circuit::predicate_arith_witness::FactBinding;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_circuit::{BabyBear, poseidon2};
use dregg_intent::fulfillment::{
    self, FulfillOptions, FulfillmentError, FulfillmentWithPredicates,
    verify_fulfillment_with_predicates_and_key,
};
use dregg_intent::matcher::{HeldCapability, Sensitivity};
use dregg_intent::{
    ActionPattern, CommitmentId, Intent, IntentKind, Match, MatchSpec, PredicateRequirement,
    VerificationMode,
};
use dregg_sdk::AgentCipherclerk;

// =============================================================================
// Helpers
// =============================================================================

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// Convert a 32-byte value into a BabyBear field element via Poseidon2.
///
/// Identical to `AgentCipherclerk::bytes_to_babybear`, so the attribute symbols here name the same
/// facts the SDK's intent-predicate path names.
fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = dregg_circuit::effect_vm::bytes32_to_8_limbs(bytes);
    poseidon2::hash_many(&limbs)
}

/// The identity of the fact an attribute names, at a given state root — everything the fact
/// commitment covers EXCEPT the value, which is supplied to the prover separately as `terms[0]`.
///
/// `term1`/`term2` are ZERO: the old shape hashed `[value, 0, 0]`, and with the value flowing in as
/// `terms[0]` the remaining terms stay zero. Putting the value in `term1` would name a DIFFERENT
/// fact.
fn attribute_fact(attribute: &str, state_root: BabyBear) -> FactBinding {
    let attr_bytes = blake3::hash(attribute.as_bytes());
    FactTerms {
        predicate_sym: bytes_to_babybear(attr_bytes.as_bytes()),
        term1: BabyBear::ZERO,
        term2: BabyBear::ZERO,
    }
    .bind(state_root)
}

/// The candidate's co-path in the credential bureau's facts tree (depth 2, member pinned to the
/// leftmost slot — the shape `dregg-attested-fact-membership::v1` emits).
///
/// In production this is drawn from the issuer's real facts tree and is a SECRET witness of the
/// candidate's: only the ROOT is published. Here it is a fixed constant so the demo's issuer and
/// candidate can both build the same tree in one process; that is the one place this file stands in
/// for infrastructure rather than running it.
fn facts_copath() -> Vec<[BabyBear; 3]> {
    vec![
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

/// The `facts_root` the CREDENTIAL BUREAU publishes for `attribute = value` at `state_root`.
///
/// This is the verifier's independently-trusted parameter. The company receives these roots from
/// the bureau it trusts — it does NOT derive them (it has no value to derive from) and it does NOT
/// read them off `proof.attestation.facts_root`, which would let a candidate attest membership in a
/// tree of its own choosing.
fn issuer_facts_root(attribute: &str, value: u32, state_root: BabyBear) -> BabyBear {
    let fact = attribute_fact(attribute, state_root);
    attested_facts_root(fact.fact_hash_of(BabyBear::new(value)), &facts_copath())
        .expect("the depth-2 facts root builds")
}

/// Prove `predicate` about the candidate's private `value` for `attribute`, in the THIRD-PARTY
/// shape: a comparison STARK joined to a membership attestation, under a FRESH blinding.
///
/// Returns `None` when the statement is false — the prover's fail-closed pole.
fn prove_attribute(
    attribute: &str,
    value: u32,
    state_root: BabyBear,
    predicate: &Predicate,
) -> Option<BridgePredicateProof> {
    prove_predicate_for_fact_attested(
        value,
        attribute_fact(attribute, state_root),
        fresh_predicate_blinding(),
        predicate,
        &facts_copath(),
    )
}

/// Did the stack REFUSE this statement?
///
/// A false statement is refused two ways and both count: the prover returns `None` (the descriptor
/// pre-flight replay refuses the witness fail-closed), or — under a debug build — the p3 batch
/// prover's DOCUMENTED unsat panic fires first. [`classify`] is what makes the second legible, and
/// it REDS on any OTHER panic, so a stray unwrap can never launder itself as a refusal.
fn refuses(what: &str, attribute: &str, value: u32, state_root: BabyBear, p: &Predicate) -> bool {
    let outcome: Outcome<(), String> = classify(what, || {
        match prove_attribute(attribute, value, state_root, p) {
            None => Err("the prover refused the false statement".to_string()),
            // Release builds compile the p3 unsat checks out, so a proof may come back. It must
            // then fail the VERIFIER, against the root the issuer published for the true value.
            Some(proof) => {
                let root = issuer_facts_root(attribute, value, state_root);
                if verify_predicate_proof_third_party(&proof, root, state_root) {
                    Ok(())
                } else {
                    Err("the proof failed to verify".to_string())
                }
            }
        }
    });
    matches!(outcome, Outcome::Err(_) | Outcome::UnsatPanic(_))
}

// =============================================================================
// Main Demo
// =============================================================================

fn main() {
    println!("===============================================================================");
    println!("  PRIVATE HIRING — Cross-Party Predicate Flow End-to-End");
    println!("===============================================================================");
    println!();
    println!("  A company posts requirements. A candidate proves qualification.");
    println!("  Neither party reveals more than necessary.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: Setup — Create cipherclerks for both parties
    // =========================================================================
    println!("--- Phase 1: WALLET SETUP ---");
    println!();

    let mut company_cclerk = AgentCipherclerk::new();
    let mut candidate_cclerk = AgentCipherclerk::new();

    // Company mints a "hiring" service token (root capability)
    let company_root_key = [0x42u8; 32];
    let company_token = company_cclerk.mint_token(&company_root_key, "hiring");

    // Candidate mints a "credentials" token (holds their private attributes)
    let candidate_root_key = [0x99u8; 32];
    let candidate_token = candidate_cclerk.mint_token(&candidate_root_key, "credentials");

    println!(
        "  Company cclerk:   pk = {}",
        short_hex(&company_cclerk.public_key().0)
    );
    println!(
        "  Candidate cclerk: pk = {}",
        short_hex(&candidate_cclerk.public_key().0)
    );
    println!(
        "  Company token:    {} (can mint: {})",
        company_token.id(),
        company_token.can_mint()
    );
    println!(
        "  Candidate token:  {} (can mint: {})",
        candidate_token.id(),
        candidate_token.can_mint()
    );
    println!();

    // The candidate's PRIVATE attributes. These never leave this scope on the wire: they are
    // witnesses to the STARKs below, and the company's copy of this program never sees them.
    let candidate_reputation: u32 = 95;
    let candidate_experience: u32 = 7;
    let candidate_salary: u32 = 150000;
    let candidate_skills_rust: u32 = 1; // boolean: has rust skill

    // The attested state the proofs are bound to (the bureau's committed state root).
    let state_root = BabyBear::new(777_777);
    let state_root_block: u64 = 9950; // recent block

    // =========================================================================
    // PHASE 1b: Credential issuance — the bureau publishes the trusted roots
    // =========================================================================
    println!("--- Phase 1b: CREDENTIAL ISSUANCE (what the company gets to trust) ---");
    println!();

    // The bureau knows the real values (it issued the credential) and publishes one facts_root per
    // attribute. The COMPANY holds only these roots. Every verification below is parameterised by
    // them — not by anything the candidate hands over.
    let attributes: [(&str, u32); 4] = [
        ("reputation", candidate_reputation),
        ("experience_years", candidate_experience),
        ("salary_expectation", candidate_salary),
        ("skills_rust", candidate_skills_rust),
    ];
    let trusted_roots: Vec<BabyBear> = attributes
        .iter()
        .map(|(attr, value)| issuer_facts_root(attr, *value, state_root))
        .collect();

    println!(
        "  Bureau state root: {} (block {})",
        state_root.as_u32(),
        state_root_block
    );
    println!("  Published facts roots (the company's only handle on the candidate's state):");
    for ((attr, _), root) in attributes.iter().zip(&trusted_roots) {
        println!("    {:<20} facts_root = {}", attr, root.as_u32());
    }
    println!();
    println!("  These roots are the verifier's INDEPENDENT trust anchor. Nothing below reads a");
    println!("  root off a proof the candidate supplied.");
    println!();
    println!("  STAND-IN, stated plainly: this demo's Merkle co-path is a fixed constant in the");
    println!("  source, so a party holding both the co-path and a root here could brute-force the");
    println!(
        "  value behind it. In production the co-path is the candidate's secret witness of the"
    );
    println!("  bureau's real facts tree and only the root travels — that is what makes the root");
    println!("  value-hiding. What this demo genuinely exercises is the ATTESTATION and its");
    println!("  binding, not the tree build.");
    println!();

    // =========================================================================
    // PHASE 2: Company posts hiring intent with predicate requirements
    // =========================================================================
    println!("--- Phase 2: COMPANY POSTS HIRING INTENT ---");
    println!();

    let company_commitment = CommitmentId::derive(b"acme-corp-secret", "hiring-intent");

    // The requirements: what the company needs proven.
    //
    // `skills_rust` is a set membership ("has the Rust skill"), and NEQ-from-zero is now directly
    // expressible as `Predicate::Neq(0)` — the old `gte 1` workaround is gone.
    let requirements = vec![
        PredicateRequirement {
            attribute: "reputation".into(),
            predicate_type: "gte".into(),
            threshold: 80,
            upper_bound: None,
            state_root_freshness: 100, // state root must be within 100 blocks
        },
        PredicateRequirement {
            attribute: "experience_years".into(),
            predicate_type: "gte".into(),
            threshold: 3,
            upper_bound: None,
            state_root_freshness: 100,
        },
        PredicateRequirement {
            attribute: "salary_expectation".into(),
            predicate_type: "lte".into(),
            threshold: 200000,
            upper_bound: None,
            state_root_freshness: 100,
        },
        PredicateRequirement {
            attribute: "skills_rust".into(),
            predicate_type: "neq".into(),
            threshold: 0, // != 0, i.e. the skill is present
            upper_bound: None,
            state_root_freshness: 100,
        },
    ];

    let match_spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some("apply".into()),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some("hiring/senior-rust-dev".into()),
        compound: None,
        predicate_requirements: requirements.clone(),
        strict_resource_matching: false,
    };

    let intent = Intent::new(
        IntentKind::Need,
        match_spec,
        company_commitment,
        u64::MAX, // no expiry for demo
        None,
    );

    println!("  Intent ID: {}", short_hex(&intent.id));
    println!("  Kind: Need (company is looking for someone)");
    println!("  Resource: hiring/senior-rust-dev");
    println!("  Predicate requirements:");
    for (i, req) in requirements.iter().enumerate() {
        println!(
            "    [{}] {} {} {}",
            i, req.attribute, req.predicate_type, req.threshold
        );
    }
    println!();
    println!("  PRIVACY: The intent reveals WHAT is needed, not WHO needs it.");
    println!(
        "           Company identity is hidden behind commitment: {}",
        short_hex(&company_commitment.0)
    );
    println!();

    // =========================================================================
    // PHASE 3: Candidate discovers intent and proves predicates
    // =========================================================================
    println!("--- Phase 3: CANDIDATE PROVES PREDICATES (Zero-Knowledge) ---");
    println!();

    println!("  Candidate's PRIVATE state (never transmitted):");
    println!("    reputation       = {candidate_reputation} (will prove >= 80)");
    println!("    experience_years = {candidate_experience} (will prove >= 3)");
    println!("    salary_expect    = {candidate_salary} (will prove <= 200000)");
    println!("    skills_rust      = {candidate_skills_rust} (will prove != 0)");
    println!();

    // The four predicates, one per requirement, each a real IR-v2 descriptor STARK joined to a
    // membership attestation. Each `expect` is load-bearing: a false statement returns `None`.
    let predicates: [Predicate; 4] = [
        Predicate::Gte(80),
        Predicate::Gte(3),
        Predicate::Lte(200000),
        Predicate::Neq(0),
    ];

    let proof_start = Instant::now();
    let proofs: Vec<BridgePredicateProof> = attributes
        .iter()
        .zip(&predicates)
        .map(|((attr, value), predicate)| {
            prove_attribute(attr, *value, state_root, predicate).unwrap_or_else(|| {
                panic!("a TRUE statement about {attr} must prove: {predicate:?}")
            })
        })
        .collect();
    let proof_time = proof_start.elapsed();

    println!("  Predicate proofs generated in {proof_time:?}");
    println!("  Number of proofs: {}", proofs.len());
    for (idx, proof) in proofs.iter().enumerate() {
        println!(
            "    [{}] {:?} — commitment: {} (attested: {})",
            idx,
            proof.predicate,
            proof.fact_commitment.as_u32(),
            proof.attestation.is_some()
        );
    }
    // The third-party shape carries an attestation and NO decommitment. Both halves are asserted:
    // a proof without the attestation has no sound source for its expected commitment, and a proof
    // that leaked its blinding would let a proof-holder brute-force the value.
    for (idx, proof) in proofs.iter().enumerate() {
        assert!(
            proof.attestation.is_some(),
            "proof {idx} must carry a fact attestation (third-party shape)"
        );
        assert!(
            proof.blinding.is_none(),
            "proof {idx} must NOT carry a decommitment — nothing to brute-force"
        );
    }
    println!();
    println!("  PRIVACY: Each proof reveals ONLY that the predicate holds.");
    println!("           The company will learn:");
    println!("             - reputation >= 80     (but NOT that it's 95)");
    println!("             - experience >= 3      (but NOT that it's 7)");
    println!("             - salary <= 200000     (but NOT that it's 150000)");
    println!("             - skills_rust != 0     (but NOT what other skills exist)");
    println!();

    // =========================================================================
    // PHASE 4: Candidate builds fulfillment with predicate proofs
    // =========================================================================
    println!("--- Phase 4: CANDIDATE BUILDS FULFILLMENT ---");
    println!();

    let candidate_commitment = CommitmentId::derive(b"candidate-secret-key", "hiring-fulfillment");

    // The candidate's held capability (what token they're using to fulfill)
    let candidate_capability = HeldCapability {
        token_id: candidate_token.id().to_string(),
        actions: vec!["apply".into()],
        resource: "hiring/*".into(),
        app_id: None,
        service: Some("credentials".into()),
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: Some(u64::MAX),
        budget: None,
        sensitivity: Sensitivity::Normal,
    };

    let matched = Match {
        intent_id: intent.id,
        satisfier: candidate_commitment,
        proof: None,
        mode: VerificationMode::Trusted, // base fulfillment uses trusted mode
    };

    let fulfill_options = FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some(candidate_root_key),
        ..Default::default()
    };

    let base_fulfillment = fulfillment::fulfill(
        &intent,
        &matched,
        &candidate_capability,
        candidate_commitment,
        &fulfill_options,
    )
    .expect("base fulfillment should succeed");

    // Assemble the full fulfillment with predicate proofs, indexed by requirement.
    let full_fulfillment = FulfillmentWithPredicates {
        base: base_fulfillment,
        predicate_proofs: proofs.iter().cloned().enumerate().collect(),
        state_root,
        state_root_block,
    };

    println!("  Fulfillment assembled:");
    println!(
        "    Intent ID: {}",
        short_hex(&full_fulfillment.base.intent_id)
    );
    println!(
        "    Fulfiller: {} (anonymous commitment)",
        short_hex(&full_fulfillment.base.fulfiller.0)
    );
    println!("    Mode: {:?}", full_fulfillment.base.mode);
    println!(
        "    Granted actions: {:?}",
        full_fulfillment.base.granted_actions
    );
    println!(
        "    Granted resource: {}",
        full_fulfillment.base.granted_resource
    );
    println!(
        "    State root block: {}",
        full_fulfillment.state_root_block
    );
    println!(
        "    Predicate proofs attached: {}",
        full_fulfillment.predicate_proofs.len()
    );
    println!();
    println!("  PRIVACY: The fulfillment is sent DIRECTLY to the company (not broadcast).");
    println!("           No observer can learn that this candidate applied.");
    println!();

    // =========================================================================
    // PHASE 5: Company verifies fulfillment + predicate proofs
    // =========================================================================
    println!("--- Phase 5: COMPANY VERIFIES (Cryptographic) ---");
    println!();

    let current_block: u64 = 10000; // current block height
    let verify_start = Instant::now();

    // The verifier's TRUSTED state root is passed in — the fulfillment path pins every predicate
    // proof's membership attestation to it, so a proof bound to a foreign state root is refused
    // (Attack 4). `VerificationMode::Trusted` also requires the macaroon root key to check the
    // attenuated token's HMAC chain; in this demo the company holds it out-of-band, which is what
    // "Trusted" mode means. A `None` here would (correctly) fail closed.
    let verification_result = verify_fulfillment_with_predicates_and_key(
        &full_fulfillment,
        &intent,
        state_root,
        current_block,
        Some(&candidate_root_key),
    );
    let verify_time = verify_start.elapsed();

    // The assert IS the claim. It fires before anything is printed about success.
    assert!(
        verification_result.is_ok(),
        "fulfillment verification must pass: {:?}",
        verification_result.as_ref().err()
    );

    println!("  VERIFICATION PASSED in {verify_time:?}");
    println!();
    println!("  The company now knows with cryptographic certainty:");
    println!("    [x] Candidate reputation >= 80");
    println!("    [x] Candidate experience >= 3 years");
    println!("    [x] Candidate salary expectation <= 200,000");
    println!("    [x] Candidate has Rust skill (skills_rust != 0)");
    println!(
        "    [x] State root is fresh (block {} within {} of current {})",
        full_fulfillment.state_root_block, requirements[0].state_root_freshness, current_block
    );
    println!();
    println!("  RESIDUAL, stated plainly: on THIS path (`verify_predicate_requirement` in");
    println!("  intent/src/fulfillment.rs) the STATE ROOT binding is real, but the facts_root is");
    println!("  taken from the proof's own attestation — the intent verifier has no independently");
    println!("  trusted facts_root threaded to it yet. Phase 6 closes that leg by re-verifying");
    println!("  each proof against the BUREAU's published roots.");
    println!();
    println!("  The company DOES NOT know:");
    println!("    [ ] Exact reputation score (could be 80, 95, or 100)");
    println!("    [ ] Exact years of experience (could be 3, 7, or 20)");
    println!("    [ ] Exact salary expectation (could be 50k, 150k, or 200k)");
    println!("    [ ] What other skills the candidate has");
    println!("    [ ] What other tokens/capabilities the candidate holds");
    println!("    [ ] The candidate's real identity");
    println!();

    // =========================================================================
    // PHASE 6: The compound requirement — VERIFIER-SIDE composition
    // =========================================================================
    println!("--- Phase 6: COMPOUND REQUIREMENT (verifier-side AND over four STARKs) ---");
    println!();
    println!("  Each conjunct is STARK-backed. The AND is evaluated BY THE VERIFIER, after");
    println!("  checking each proof — it is NOT proven inside one circuit. There is no single");
    println!("  compound proof here: the in-circuit compound-predicate capability was RETIRED");
    println!("  with the hand-STARK engine and its descriptor is not registered, so N independent");
    println!("  proofs plus a verifier-side formula is the surviving capability.");
    println!();

    let compound_start = Instant::now();

    // Each boolean is the RETURN VALUE of a real verification against the ISSUER's root.
    let verified_results: Vec<bool> = attributes
        .iter()
        .zip(&proofs)
        .zip(&trusted_roots)
        .map(|(((attr, _), proof), root)| {
            let ok = verify_predicate_proof_third_party(proof, *root, state_root);
            println!(
                "    {:<20} {:?} -> verified = {}",
                attr, proof.predicate, ok
            );
            ok
        })
        .collect();

    let formula = BooleanFormula::And(vec![0, 1, 2, 3]);
    let all_hold = evaluate_formula(&formula, &verified_results);
    let compound_time = compound_start.elapsed();

    println!();
    println!(
        "  Formula: AND(reputation >= 80, experience >= 3, salary <= 200000, skills_rust != 0)"
    );
    println!("  Composed in {compound_time:?} -> {all_hold}");
    println!();

    for (idx, ok) in verified_results.iter().enumerate() {
        assert!(
            *ok,
            "predicate proof {idx} must verify against the issuer's facts root"
        );
    }
    assert!(
        all_hold,
        "the conjunction of four verified predicates must hold"
    );

    // NON-VACUITY of the composition itself: if any conjunct had failed to verify, the formula
    // must say so. A `vec![true; 4]` would pass the line above and mean nothing; this does not.
    let mut one_failed = verified_results.clone();
    one_failed[2] = false;
    assert!(
        !evaluate_formula(&formula, &one_failed),
        "the AND must REJECT when one conjunct fails to verify — otherwise the composition is a \
         constant and proves nothing"
    );
    println!("  Non-vacuity: flipping one conjunct to `false` makes the AND reject. [checked]");
    println!();

    // The conditional turn: the capability is granted IFF the composed formula holds.
    let hire_granted = all_hold;
    println!("  CONDITIONAL TURN: grant 'hire' capability IFF the formula holds -> {hire_granted}");
    assert!(
        hire_granted,
        "the hire grant is gated on the composed result"
    );
    println!();

    // =========================================================================
    // PHASE 7: Selective disclosure — candidate reveals extra strength
    // =========================================================================
    println!("--- Phase 7: SELECTIVE DISCLOSURE (Optional Strength Signal) ---");
    println!();
    println!("  The candidate may optionally reveal STRONGER facts to stand out:");
    println!("    'I have >= 5 years experience' (stronger than the required >= 3)");
    println!("  while STILL hiding salary and exact reputation.");
    println!();

    let selective_start = Instant::now();
    let stronger_proof = prove_attribute(
        "experience_years",
        candidate_experience,
        state_root,
        &Predicate::Gte(5),
    )
    .expect("7 >= 5 is true and must prove");
    let selective_time = selective_start.elapsed();

    // Verified against the SAME published root as the >= 3 proof: it is the same attested fact.
    let stronger_valid =
        verify_predicate_proof_third_party(&stronger_proof, trusted_roots[1], state_root);
    assert!(
        stronger_valid,
        "the selective-disclosure proof must verify against the issuer's experience root"
    );

    // UNLINKABILITY, asserted: a fresh blinding per showing means the two proofs about the SAME
    // fact publish DIFFERENT commitments. A party holding only the commitments cannot tell they
    // describe one candidate.
    assert_ne!(
        stronger_proof.fact_commitment, proofs[1].fact_commitment,
        "two showings of the same fact must carry DIFFERENT commitments (per-showing blinding)"
    );

    println!("  Selective disclosure proof: experience >= 5");
    println!("  Generated in {selective_time:?}, verified: {stronger_valid}");
    println!(
        "  Commitment differs from the >= 3 showing ({} vs {}) — unlinkable. [checked]",
        stronger_proof.fact_commitment.as_u32(),
        proofs[1].fact_commitment.as_u32()
    );
    println!();
    println!("  What the company NOW knows (with disclosure):");
    println!("    [x] experience >= 5   (voluntary disclosure, stronger than required)");
    println!("    [ ] exact experience   (still hidden: could be 5, 7, 10, 20...)");
    println!("    [ ] salary expectation (still hidden behind predicate proof)");
    println!("    [ ] exact reputation   (still hidden)");
    println!();

    // =========================================================================
    // PHASE 8: Attack scenarios — every pole asserted
    // =========================================================================
    println!("--- Phase 8: ATTACK RESISTANCE ---");
    println!();

    // Attack 1: an UNQUALIFIED candidate. Reputation 50 against the required >= 80.
    println!("  Attack 1: unqualified candidate (reputation 50, requirement >= 80)");
    let unqualified_refused = refuses(
        "unqualified-candidate",
        "reputation",
        50,
        state_root,
        &Predicate::Gte(80),
    );
    assert!(
        unqualified_refused,
        "a candidate who does not meet the requirement must be REFUSED"
    );
    println!("    Result: REFUSED. A candidate below the bar cannot produce an accepted proof.");
    println!();

    // Attack 2: candidate lies about salary (actual 250000, claims <= 200000).
    println!("  Attack 2: candidate lies about salary (actual 250000, claims <= 200000)");
    let lie_refused = refuses(
        "salary-lie",
        "salary_expectation",
        250000,
        state_root,
        &Predicate::Lte(200000),
    );
    assert!(lie_refused, "a false salary statement must be REFUSED");
    println!("    Result: REFUSED. The prover cannot produce an accepted proof of a false claim.");
    println!();

    // Attack 3: INVENTED FACT. A SECOND applicant, whose bureau-attested reputation is 50, proves
    // a perfectly TRUE statement — 95 >= 80 — about a value it made up, attesting membership in a
    // facts tree OF ITS OWN. Every internal leg of this proof is genuine: the weld holds, the
    // arithmetic is true, the attestation is a valid STARK. Its only lie is about WHICH TREE the
    // fact lives in, and the trusted `facts_root` parameter is what catches it.
    println!(
        "  Attack 3: invented fact (applicant attested at 50; proves 95 >= 80 in its own tree)"
    );
    let bureau_root_for_50 = issuer_facts_root("reputation", 50, state_root);
    let forged = prove_attribute("reputation", 95, state_root, &Predicate::Gte(80))
        .expect("95 >= 80 is a TRUE statement — the forgery is in the FACT, not the arithmetic");
    let forged_accepted =
        verify_predicate_proof_third_party(&forged, bureau_root_for_50, state_root);
    assert!(
        !forged_accepted,
        "a proof about an INVENTED fact must be REFUSED against the bureau's published root"
    );
    // Non-vacuity for this pole: the same proof DOES verify against the root of the tree it was
    // actually built in, so the refusal above is about provenance, not a verifier that says no to
    // everything.
    assert!(
        verify_predicate_proof_third_party(
            &forged,
            issuer_facts_root("reputation", 95, state_root),
            state_root
        ),
        "NON-VACUITY: the forged proof must verify against ITS OWN tree — otherwise Attack 3 \
         proves nothing about the facts_root parameter"
    );
    println!("    Result: REFUSED. The arithmetic is true; the fact is not the bureau's.");
    println!("    (Non-vacuity: the same proof verifies against its own root. [checked])");
    println!();

    // Attack 4: CROSS-STATE. The honest reputation proof, checked against a state root the
    // verifier does not trust.
    println!("  Attack 4: cross-state (honest proof, foreign state root 424242)");
    let foreign_state_root = BabyBear::new(424_242);
    let cross_state_accepted =
        verify_predicate_proof_third_party(&proofs[0], trusted_roots[0], foreign_state_root);
    assert!(
        !cross_state_accepted,
        "a proof bound to a different state root must be REFUSED"
    );
    println!("    Result: REFUSED. The membership STARK is pinned to the trusted state root.");
    println!();

    // Attack 5: STALE STATE ROOT (block 9800, current 10000, freshness 100).
    println!("  Attack 5: stale state root (block 9800, current 10000, freshness 100)");
    let stale_fulfillment = FulfillmentWithPredicates {
        base: full_fulfillment.base.clone(),
        predicate_proofs: full_fulfillment.predicate_proofs.clone(),
        state_root,
        state_root_block: 9800, // too old!
    };
    let stale_result = verify_fulfillment_with_predicates_and_key(
        &stale_fulfillment,
        &intent,
        state_root,
        current_block,
        Some(&candidate_root_key),
    );
    // Asserting the VARIANT, not merely `is_err()`: an error for some unrelated reason would not
    // demonstrate freshness enforcement.
    assert!(
        matches!(stale_result, Err(FulfillmentError::StaleStateRoot(_))),
        "a stale state root must be rejected AS stale, got: {stale_result:?}"
    );
    println!("    Result: REJECTED as StaleStateRoot. [checked]");
    println!();

    // Attack 6: WRONG THRESHOLD. The candidate proves a true-but-weaker statement (reputation
    // >= 50) and submits it against a requirement of >= 80.
    println!("  Attack 6: wrong threshold (proves reputation >= 50 against a >= 80 requirement)");
    let weak_proof = prove_attribute(
        "reputation",
        candidate_reputation,
        state_root,
        &Predicate::Gte(50),
    )
    .expect("95 >= 50 is true and proves fine — the mismatch is with the REQUIREMENT");
    let mut swapped = full_fulfillment.predicate_proofs.clone();
    swapped[0] = (0, weak_proof);
    let weak_fulfillment = FulfillmentWithPredicates {
        base: full_fulfillment.base.clone(),
        predicate_proofs: swapped,
        state_root,
        state_root_block,
    };
    let weak_result = verify_fulfillment_with_predicates_and_key(
        &weak_fulfillment,
        &intent,
        state_root,
        current_block,
        Some(&candidate_root_key),
    );
    assert!(
        matches!(weak_result, Err(FulfillmentError::PredicateProofFailed(_))),
        "a proof carrying the wrong threshold must be rejected, got: {weak_result:?}"
    );
    println!("    Result: REJECTED. The verifier pins the proof's predicate to the requirement.");
    println!();

    // =========================================================================
    // PHASE 9: Timing summary
    // =========================================================================
    println!("--- Phase 9: TIMING SUMMARY ---");
    println!();

    let total_time = total_start.elapsed();
    println!("  Four attested predicate proofs:    {proof_time:?}");
    println!("  Fulfillment verification:          {verify_time:?}");
    println!("  Verifier-side composition (4x):    {compound_time:?}");
    println!("  Selective disclosure proof:        {selective_time:?}");
    println!("  Total demo time:                   {total_time:?}");
    println!();

    // =========================================================================
    // PHASE 10: Privacy summary
    // =========================================================================
    println!("--- Phase 10: PRIVACY SUMMARY ---");
    println!();
    println!("  +---------------------------+-------------------+-------------------+");
    println!("  | Information               | Company learns    | Observers learn   |");
    println!("  +---------------------------+-------------------+-------------------+");
    println!("  | Reputation >= 80          | YES (proven)      | NO                |");
    println!("  | Exact reputation (95)     | NO                | NO                |");
    println!("  | Experience >= 3           | YES (proven)      | NO                |");
    println!("  | Exact experience (7)      | NO                | NO                |");
    println!("  | Salary <= 200k            | YES (proven)      | NO                |");
    println!("  | Exact salary (150k)       | NO                | NO                |");
    println!("  | Has Rust skill            | YES (proven)      | NO                |");
    println!("  | Other skills              | NO                | NO                |");
    println!("  | Candidate identity        | NO (commitment)   | NO                |");
    println!("  | Company identity          | NO (commitment)   | NO                |");
    println!("  | That someone applied      | YES (direct msg)  | NO                |");
    println!("  +---------------------------+-------------------+-------------------+");
    println!();
    println!("  Key insight: predicates enable a MARKET for credentials without");
    println!("  creating a surveillance system. The hiring company gets cryptographic");
    println!("  certainty about qualifications, the candidate retains privacy about");
    println!("  exact values, and observers learn nothing at all.");
    println!();
    println!("  What that certainty rests on: four IR-v2 descriptor STARKs and four membership");
    println!("  attestations, each checked against a root the bureau published — composed by the");
    println!("  verifier, not by a circuit. The proof system's own soundness floor (FRI) is");
    println!("  inherited, not discharged here.");
    println!();
    println!("===============================================================================");
    println!("  DEMO COMPLETE — every claim above was asserted, not printed.");
    println!("===============================================================================");
}
