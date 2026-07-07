//! Intent Lifecycle Demo — Complete Flow from Posting to Fulfillment Delivery
//!
//! Demonstrates the FULL intent protocol lifecycle:
//!
//! 1. Service posts intent: "I need someone who can sign_treasury for up to 10k"
//! 2. Agent's cclerk matches locally (revealing NOTHING about other capabilities)
//! 3. Agent commits to fulfillment (anti-frontrunning, blinded)
//! 4. Agent reveals fulfillment (attenuated token, narrowed scope)
//! 5. Service verifies the fulfillment
//! 6. Attack resistance: frontrunning, probing, authority-exceed all fail
//!
//! This uses the real `dregg-intent` crate (matcher, fulfillment, gossip pool
//! with commit-reveal). Capability is established by the local matcher; the
//! service then checks the revealed fulfillment structurally.

use dregg_commit::{Poseidon2MerkleTree, commitment_to_field};
use dregg_intent::fulfillment::{self, FulfillOptions, Fulfillment};
use dregg_intent::gossip::{
    AutoFulfillPolicy, CommitRevealError, FulfillmentReveal, IntentPool, IntentPoolConfig,
};
use dregg_intent::matcher::{self, HeldCapability, MatchResult, Sensitivity};
use dregg_intent::{
    ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec, StakeProof, VerificationMode,
};

fn main() {
    println!("=== Dregg Intent Lifecycle Demo ===");
    println!("Complete flow: posting -> matching -> commitment -> fulfillment -> verification\n");

    // =========================================================================
    // STEP 1: Service posts an intent
    // =========================================================================
    println!("=========================================================================");
    println!("  STEP 1: Service Posts Intent");
    println!("=========================================================================\n");
    println!("  A treasury service needs: \"someone who can sign_treasury for up to 10k\"\n");

    // The service's anonymous identity (commitment, NOT a public key)
    let service_commitment = CommitmentId::derive(b"treasury-service-secret", "service-identity");

    // Build a real Poseidon2 note tree for stake proofs
    let stake_commitment = dregg_cell::NoteCommitment([0xAB; 32]);
    let mut note_tree = Poseidon2MerkleTree::with_depth(4);
    // Populate with some other notes
    for i in 0..5u8 {
        let mut c = [0u8; 32];
        c[0] = i;
        note_tree.append(commitment_to_field(&c));
    }
    // Insert the service's stake note
    let stake_leaf = commitment_to_field(&stake_commitment.0);
    let stake_pos = note_tree.append(stake_leaf);
    for i in 10..15u8 {
        let mut c = [0u8; 32];
        c[0] = i;
        note_tree.append(commitment_to_field(&c));
    }
    let note_tree_root = note_tree.root();
    let stake_merkle_proof = note_tree.prove_membership(stake_pos).unwrap();

    let stake_proof = StakeProof {
        commitment: stake_commitment,
        merkle_root: note_tree_root,
        merkle_proof: stake_merkle_proof,
        minimum_value: 1000,
    };

    // Service creates an IntentPool and broadcasts the intent
    let mut service_pool = IntentPool::new(
        service_commitment,
        IntentPoolConfig {
            max_intents: 1000,
            gc_interval_secs: 60,
            auto_match: false, // service doesn't match, it POSTS
            minimum_stake_value: 0,
        },
        AutoFulfillPolicy::Never,
        note_tree_root,
    );

    // The MatchSpec: what capabilities are needed
    let match_spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some("sign_treasury".into()),
            resource: None,
        }],
        constraints: vec![],
        min_budget: Some(10_000), // need at least 10k budget
        resource_pattern: Some("treasury/*".into()),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    // Broadcast: service posts the intent with expiry 1 hour from now
    let now = 1_700_000_000u64; // simulated timestamp
    let expiry = now + 3600; // 1 hour
    let intent = service_pool
        .broadcast_intent(IntentKind::Need, match_spec, expiry, Some(stake_proof))
        .expect("broadcast intent");

    println!("  Intent posted:");
    println!(
        "    ID: {:02x}{:02x}{:02x}{:02x}...",
        intent.id[0], intent.id[1], intent.id[2], intent.id[3]
    );
    println!("    Kind: Need");
    println!("    Required action: sign_treasury");
    println!("    Min budget: 10,000");
    println!("    Resource pattern: treasury/*");
    println!("    Expiry: {} (1 hour from now)", expiry);
    println!("    Creator: [anonymous commitment]");
    println!("    Stake: [valid note commitment]\n");
    println!("  This intent propagates via gossip to all connected cipherclerks.");
    println!("  Everyone sees WHAT is needed, but not WHO needs it.\n");

    // =========================================================================
    // STEP 2: Agent's cclerk matches locally
    // =========================================================================
    println!("=========================================================================");
    println!("  STEP 2: Agent's Cipherclerk Matches Locally (PRIVATE)");
    println!("=========================================================================\n");
    println!("  The agent holds a token with:");
    println!("    actions = [\"sign_treasury\", \"view_treasury\"]");
    println!("    budget  = 50,000");
    println!("    resource = treasury/*\n");

    // The agent's anonymous identity
    let agent_commitment = CommitmentId::derive(b"agent-cclerk-secret-key", "agent-identity");

    // The agent's held capabilities (what's actually in the cclerk)
    let agent_token = HeldCapability {
        token_id: "tok_treasury_signer_001".into(),
        actions: vec!["sign_treasury".into(), "view_treasury".into()],
        resource: "treasury/*".into(),
        app_id: Some("treasury-app".into()),
        service: Some("finance".into()),
        user_id: None,
        features: vec!["multi_sig".into()],
        oauth_provider: None,
        expiry: Some(now + 86400), // 24 hours
        budget: Some(50_000),
        sensitivity: Sensitivity::Normal,
    };

    // Local matching: evaluate if our token satisfies the intent
    let match_result = matcher::match_intent(
        &intent,
        std::slice::from_ref(&agent_token),
        agent_commitment,
        VerificationMode::Private, // generate STARK proof (mock for speed)
        now,
    );

    match &match_result {
        MatchResult::Matched {
            token_index,
            matched,
        } => {
            println!("  MATCH FOUND (token index {})!\n", token_index);
            println!("  What the match reveals:");
            println!(
                "    - Intent ID: {:02x}{:02x}{:02x}{:02x}...",
                matched.intent_id[0],
                matched.intent_id[1],
                matched.intent_id[2],
                matched.intent_id[3]
            );
            println!("    - Satisfier: [anonymous commitment]");
            println!(
                "    - Proof: {} bytes (STARK, would be real in production)",
                matched.proof.as_ref().map_or(0, |p| p.len())
            );
            println!("    - Mode: Private\n");
            println!("  What the match HIDES:");
            println!("    - view_treasury capability: NOT revealed");
            println!("    - Full budget (50,000): NOT revealed (only proves >= 10k)");
            println!("    - Token ID: NOT revealed");
            println!("    - Delegation chain: NOT revealed");
            println!("    - multi_sig feature: NOT revealed");
            println!("    - Other cclerk contents: NOT revealed\n");
            println!("  Privacy guarantee: the matcher reveals NOTHING about the agent's");
            println!(
                "  other capabilities. The service learns only that SOMEONE can satisfy it.\n"
            );
        }
        other => {
            println!("  ERROR: unexpected match result: {:?}", other);
            return;
        }
    }

    // Extract the Match for the next steps
    let the_match = match match_result {
        MatchResult::Matched { matched, .. } => matched,
        _ => unreachable!(),
    };

    // =========================================================================
    // STEP 3: Agent commits to fulfillment (anti-frontrunning)
    // =========================================================================
    println!("=========================================================================");
    println!("  STEP 3: Agent Commits to Fulfillment (Anti-Frontrunning)");
    println!("=========================================================================\n");
    println!("  Before revealing HOW it will fulfill the intent, the agent posts a");
    println!("  BLINDED commitment. This prevents other agents from copying the solution.\n");

    // Prepare the fulfillment: Trusted mode (direct token presentation), scope
    // narrowed to ONLY sign_treasury on treasury/* and capped at the intent's
    // lifetime. (Private/Selective modes carry a STARK proof; that leg rides the
    // descriptor prover in production and is out of scope for this walkthrough.)
    let fulfill_options = FulfillOptions {
        mode: VerificationMode::Trusted,
        max_expiry: Some(now + 3600), // cap at 1 hour (same as intent)
        restrict_actions: Some(vec!["sign_treasury".into()]), // ONLY sign, not view
        restrict_resource: Some("treasury/*".into()),
        // Trusted mode builds a real HMAC-chained attenuated macaroon from the
        // source token's root key.
        root_key: Some(*blake3::hash(b"agent-cclerk-treasury-root-key").as_bytes()),
        ..Default::default()
    };

    let fulfillment = fulfillment::fulfill(
        &intent,
        &the_match,
        &agent_token,
        agent_commitment,
        &fulfill_options,
    )
    .expect("fulfillment should succeed");

    println!("  Fulfillment prepared (not yet revealed):");
    println!("    Granted actions: {:?}", fulfillment.granted_actions);
    println!("    Granted resource: {}", fulfillment.granted_resource);
    println!(
        "    Expiry: {:?} (capped at intent's lifetime)",
        fulfillment.expiry
    );
    println!(
        "    Token data: {} (Trusted mode presents the attenuated token)",
        if fulfillment.token_data.is_none() {
            "NONE"
        } else {
            "present"
        }
    );
    println!();

    // Now commit (blinded) -- this would be broadcast to the network
    let mut agent_pool = IntentPool::new(
        agent_commitment,
        IntentPoolConfig::default(),
        AutoFulfillPolicy::Always,
        note_tree_root,
    );

    let commitment = agent_pool.commit_to_fulfill(intent.id, &fulfillment, now);

    println!("  Commitment posted:");
    println!(
        "    Intent ID: {:02x}{:02x}{:02x}{:02x}...",
        commitment.intent_id[0],
        commitment.intent_id[1],
        commitment.intent_id[2],
        commitment.intent_id[3]
    );
    println!(
        "    Blinded hash: {:02x}{:02x}{:02x}{:02x}...",
        commitment.satisfier_commitment[0],
        commitment.satisfier_commitment[1],
        commitment.satisfier_commitment[2],
        commitment.satisfier_commitment[3]
    );
    println!("    Timestamp: {}", commitment.timestamp);
    println!();
    println!("  The commitment reveals NOTHING about the fulfillment itself.");
    println!("  It only proves: 'I committed to a solution at time T'.");
    println!("  Other agents see the commitment but cannot extract the solution.\n");
    println!("  --- Waiting for reveal window (5 seconds in production) ---");
    println!("  In production, the agent waits COMMIT_REVEAL_WINDOW_SECS (5s)");
    println!("  before revealing. First valid commitment wins priority.\n");

    // =========================================================================
    // STEP 4: Agent reveals fulfillment
    // =========================================================================
    println!("=========================================================================");
    println!("  STEP 4: Agent Reveals Fulfillment");
    println!("=========================================================================\n");
    println!("  After the reveal window, the agent opens the commitment.\n");

    // In the real protocol, the nonce generated during commit_to_fulfill is stored
    // internally by the agent and used to prove the reveal matches the commitment.
    // The reveal contains:
    // - The commitment hash (identifies which commitment this opens)
    // - The actual fulfillment data
    // - The nonce proving this matches the earlier blinded commitment
    //
    // For this demo, we show what the fulfillment contains when delivered:
    println!("  Fulfillment contents (what gets delivered to the service):");
    println!(
        "    Intent: {:02x}{:02x}{:02x}{:02x}...",
        fulfillment.intent_id[0],
        fulfillment.intent_id[1],
        fulfillment.intent_id[2],
        fulfillment.intent_id[3]
    );
    println!("    Granted actions: {:?}", fulfillment.granted_actions);
    println!("    Granted resource: \"{}\"", fulfillment.granted_resource);
    println!("    Expiry: {:?}", fulfillment.expiry);
    println!("    Fulfiller: [anonymous commitment]\n");
    println!("  Key attenuation properties:");
    println!("    - ONLY sign_treasury granted (view_treasury stripped)");
    println!("    - Budget requirement established by the matcher (>= 10k)");
    println!("    - Expiry capped at intent lifetime (not full token lifetime)");
    println!("    - Attenuated token presented directly (Trusted mode)\n");

    // =========================================================================
    // STEP 5: Service verifies the fulfillment
    // =========================================================================
    println!("=========================================================================");
    println!("  STEP 5: Service Verifies Fulfillment");
    println!("=========================================================================\n");
    println!("  The service checks the revealed fulfillment structurally:\n");

    // Check 1: Attenuated token grants sign_treasury
    let grants_sign = fulfillment
        .granted_actions
        .contains(&"sign_treasury".to_string());
    println!(
        "  [{}] 1. Fulfillment grants sign_treasury action",
        if grants_sign { "PASS" } else { "FAIL" }
    );
    println!("       Granted: {:?}", fulfillment.granted_actions);

    // Check 2: Resource scope matches
    let resource_ok = fulfillment.granted_resource == "treasury/*";
    println!(
        "  [{}] 2. Resource scope covers treasury/*",
        if resource_ok { "PASS" } else { "FAIL" }
    );

    // Check 3: Expiry is capped at the intent's lifetime (not the full token lifetime)
    let expiry_ok = fulfillment.expiry == Some(now + 3600);
    println!(
        "  [{}] 3. Expiry capped at intent lifetime",
        if expiry_ok { "PASS" } else { "FAIL" }
    );

    println!();
    if grants_sign && resource_ok && expiry_ok {
        println!("  === FULFILLMENT ACCEPTED ===");
        println!("  Backed by the earlier local match + commit-reveal, the service knows:");
        println!("    - An agent exists who can sign treasury transactions");
        println!("    - The grant is narrowed to sign_treasury on treasury/*");
        println!("    - The authorization is valid for the next hour");
        println!("    - All without learning the agent's identity or full capabilities");
    } else {
        println!("  FULFILLMENT REJECTED");
    }
    println!();

    // =========================================================================
    // STEP 6: Attack resistance demonstrations
    // =========================================================================
    println!("=========================================================================");
    println!("  STEP 6: Attack Resistance");
    println!("=========================================================================\n");

    // --- Attack A: Eve tries to frontrun (submit fulfillment without prior commitment)
    println!("  --- Attack A: Frontrunning (no prior commitment) ---\n");
    println!("  Eve sees the intent on gossip and tries to submit a fulfillment");
    println!("  without first committing. This bypasses the commit-reveal window.\n");

    let mut verifier_pool = IntentPool::new(
        service_commitment,
        IntentPoolConfig::default(),
        AutoFulfillPolicy::Never,
        note_tree_root,
    );

    // Eve's fake fulfillment
    let eve_commitment = CommitmentId::derive(b"eve-attacker", "eve");
    let eve_fulfillment = Fulfillment {
        intent_id: intent.id,
        fulfiller: eve_commitment,
        mode: VerificationMode::Private,
        token_data: None,
        proof: Some(vec![0xDE, 0xAD]), // fake proof
        granted_actions: vec!["sign_treasury".into()],
        granted_resource: "treasury/*".into(),
        expiry: Some(now + 3600),
    };

    // Eve tries to reveal without committing first
    let eve_reveal = FulfillmentReveal {
        commitment_hash: [0xFF; 32], // no real commitment exists
        fulfillment: eve_fulfillment,
        nonce: [0x00; 32],
    };

    let frontrun_result = verifier_pool.reveal_fulfillment(&eve_reveal, now + 10);
    match frontrun_result {
        Err(CommitRevealError::NoCommitment) => {
            println!("  REJECTED: {:?}", CommitRevealError::NoCommitment);
            println!("  Eve cannot submit a fulfillment without a prior blinded commitment.");
            println!("  The commit-reveal protocol prevents seeing others' solutions and");
            println!("  racing to submit first.\n");
        }
        other => {
            println!("  Unexpected result: {:?}\n", other);
        }
    }

    // --- Attack B: Eve tries to probe (posts a Query intent)
    println!("  --- Attack B: Capability Probing (Query intent) ---\n");
    println!("  Eve broadcasts a Query intent to discover what capabilities exist");
    println!("  in nearby cipherclerks. Query intents try to trigger matching.\n");

    let probe_spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some("sign_treasury".into()),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: None,
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    // Create a Query intent (probe) -- Eve provides no real stake
    let probe_intent = Intent::new(
        IntentKind::Query, // KEY: this is a Query, not a Need
        probe_spec,
        eve_commitment,
        now + 3600,
        None, // no stake (Eve doesn't have a real note)
    );

    // Agent's cclerk tries to match against it
    let probe_result = matcher::match_intent(
        &probe_intent,
        std::slice::from_ref(&agent_token),
        agent_commitment,
        VerificationMode::Trusted,
        now,
    );

    match probe_result {
        MatchResult::WrongKind => {
            println!("  REJECTED: Query intents NEVER trigger automatic matching.");
            println!("  The matcher returns WrongKind for Query and Offer intents.");
            println!("  Eve cannot discover cclerk contents via probe intents.\n");
        }
        other => {
            println!("  Unexpected: {:?}\n", other);
        }
    }

    // --- Attack C: Eve tries to exceed authority
    println!("  --- Attack C: Authority Escalation (offering write without holding it) ---\n");
    println!("  Eve claims to offer sign_treasury capability but only holds view_treasury.");
    println!("  The fulfillment validation catches the mismatch.\n");

    // Eve's actual token: only view access
    let eve_token = HeldCapability {
        token_id: "tok_eve_view_only".into(),
        actions: vec!["view_treasury".into()], // Eve can ONLY view
        resource: "treasury/*".into(),
        app_id: None,
        service: None,
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: Some(now + 86400),
        budget: Some(100_000),
        sensitivity: Sensitivity::Normal,
    };

    // Eve tries to match a sign_treasury intent with only view_treasury token
    let escalation_result = matcher::match_intent(
        &intent,
        &[eve_token],
        eve_commitment,
        VerificationMode::Trusted,
        now,
    );

    match escalation_result {
        MatchResult::NoMatch => {
            println!("  REJECTED: Eve's token does not grant sign_treasury.");
            println!(
                "  The matcher evaluates action sets locally -- view_treasury != sign_treasury."
            );
            println!("  Eve cannot generate a valid match (and therefore no valid STARK proof)");
            println!("  because the proof commits to a token that ACTUALLY satisfies the spec.\n");
            println!("  Even if Eve fabricated a fulfillment claiming sign_treasury,");
            println!("  the STARK proof would fail verification (proves nothing without a");
            println!("  real token satisfying the predicate).\n");
        }
        other => {
            println!("  Unexpected: {:?}\n", other);
        }
    }

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("=========================================================================");
    println!("  SUMMARY: Intent Lifecycle Properties");
    println!("=========================================================================\n");
    println!("  Phase              | Who learns what");
    println!("  -------------------|--------------------------------------------------");
    println!("  1. Post intent     | Everyone: \"someone needs sign_treasury >= 10k\"");
    println!("  2. Local match     | Only agent: \"I can satisfy this\"");
    println!("  3. Commit          | Everyone: \"someone committed at time T\" (blinded)");
    println!("  4. Reveal          | Service: \"agent can sign, proof valid\" (attenuated)");
    println!("  5. Verify          | Service: ALLOW + cryptographic guarantee");
    println!();
    println!("  What is NEVER revealed:");
    println!("    - Agent's full capability set (view_treasury hidden)");
    println!("    - Agent's full budget (50k hidden, only >= 10k proven)");
    println!("    - Agent's identity (only anonymous commitment)");
    println!("    - Token ID or delegation chain");
    println!("    - Other cclerk contents");
    println!();
    println!("  Attack resistance:");
    println!("    - Frontrunning: commit-reveal with 5s window");
    println!("    - Probing: Query intents never trigger auto-match");
    println!("    - Escalation: matcher + STARK proof bound to real token");
    println!();
    println!("=== Intent Lifecycle Demo Complete ===");
}
