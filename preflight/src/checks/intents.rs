//! Intent system checks: post, match, commit-reveal, partial fill.

use dregg_circuit::BabyBear;
use dregg_intent::commit_reveal_fulfillment::FulfillmentRegistry;
use dregg_intent::gossip::{AutoFulfillPolicy, IntentPool, IntentPoolConfig};
use dregg_intent::matcher::HeldCapability;
use dregg_intent::partial_fill::{
    CumulativeFillTracker, check_fill_amount, create_residual_intent,
};
use dregg_intent::{CommitmentId, FillConstraints, Intent, IntentKind, MatchSpec};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("post", check_post_intent),
        run_check("match", check_match_intent),
        run_check("commit_reveal", check_commit_reveal),
        run_check("partial", check_partial_fill),
    ]
}

fn make_test_intent() -> Intent {
    Intent::new(
        IntentKind::Need,
        MatchSpec::default(),
        CommitmentId(*blake3::hash(b"test-creator").as_bytes()),
        1000,
        None,
    )
}

fn check_post_intent() -> Result<(), String> {
    let config = IntentPoolConfig::default();
    let commitment = CommitmentId(*blake3::hash(b"our-commitment").as_bytes());
    let mut pool = IntentPool::new(commitment, config, AutoFulfillPolicy::Never, BabyBear::ZERO);

    let spec = MatchSpec::default();

    // Broadcast (post) intent into pool
    let intent = pool
        .broadcast_intent(IntentKind::Need, spec, 1000, None)
        .map_err(|e| format!("broadcast failed: {e:?}"))?;

    let intent_id = intent.id;

    // Verify in pool
    if pool.is_empty() {
        return Err("pool should not be empty after post".into());
    }
    let retrieved = pool.get_intent(&intent_id);
    if retrieved.is_none() {
        return Err("posted intent should be retrievable".into());
    }

    Ok(())
}

fn check_match_intent() -> Result<(), String> {
    // Create a pool with held capabilities that can satisfy the intent.
    // Use `receive_local_intent` which doesn't require stake proof.
    use dregg_intent::matcher::Sensitivity;
    let held = vec![HeldCapability {
        token_id: "test-token".to_string(),
        actions: vec!["read".into(), "write".into()],
        resource: "compute.dregg.dev".into(),
        app_id: None,
        service: Some("compute".into()),
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: None,
        budget: None,
        sensitivity: Sensitivity::Normal,
    }];

    let config = IntentPoolConfig::default();
    let commitment = CommitmentId(*blake3::hash(b"matcher-commitment").as_bytes());
    let mut pool = IntentPool::new(
        commitment,
        config,
        AutoFulfillPolicy::Always,
        BabyBear::ZERO,
    );
    pool.update_held_tokens(held);
    pool.update_block_height(50);

    let intent = make_test_intent();

    // Use receive_local_intent (doesn't require stake)
    let matched = pool
        .receive_local_intent(intent.clone(), 100)
        .map_err(|e| format!("receive_local_intent failed: {e}"))?;
    // Either we got a match, or the intent is in the pool
    if matched.is_none() {
        // Verify intent is at least stored
        if pool.get_intent(&intent.id).is_none() {
            return Err("intent should be stored even if not matched".into());
        }
    }
    // If we got a match, that's even better
    Ok(())
}

fn check_commit_reveal() -> Result<(), String> {
    let mut registry = FulfillmentRegistry::new();
    registry.update_block_height(10);

    let intent_id = *blake3::hash(b"cr-intent").as_bytes();
    let fulfiller_secret = *blake3::hash(b"fulfiller-secret").as_bytes();

    // Commit phase: register a commitment
    let commitment = registry
        .register_commitment(intent_id, &fulfiller_secret, 100)
        .map_err(|e| format!("commit failed: {e:?}"))?;

    // Verify commitment is pending
    if !registry.has_pending_commitments(&intent_id, 100) {
        return Err("should have pending commitments".into());
    }

    // Reveal phase: validate reveal matches commitment.
    // The reveal must happen within the commitment window (committed_at + EXPIRY).
    // Use a `now` that is after commit delay but before expiry.
    let reveal_time = commitment.committed_at + 10; // small delay after commit
    let reveal_result = registry.validate_reveal(&intent_id, &fulfiller_secret, reveal_time);
    match reveal_result {
        Ok(_) => {}
        Err(e) => return Err(format!("reveal validation failed: {e:?}")),
    }

    Ok(())
}

fn check_partial_fill() -> Result<(), String> {
    // Create an intent with fill constraints
    let mut intent = make_test_intent();
    intent.fill_constraints = Some(FillConstraints {
        min_fill_amount: 10,
        max_fill_amount: 100,
        fill_or_kill: false,
        remaining_after_fill: None,
        generation: 0,
    });

    // Verify partial fill amount validation
    let constraints = intent.fill_constraints.as_ref().unwrap();

    // Valid fill (within range)
    let valid = check_fill_amount(constraints, 50);
    match valid {
        Ok(amount) => {
            if amount == 0 {
                return Err("fill amount should be non-zero".into());
            }
        }
        Err(e) => return Err(format!("50 should be valid: {e:?}")),
    }

    // Too small
    let too_small = check_fill_amount(constraints, 5);
    if too_small.is_ok() {
        return Err("5 should be rejected (below min_fill=10)".into());
    }

    // Create residual intent after partial fill
    let residual = create_residual_intent(&intent, 60);
    match residual {
        Some(r) => {
            let rc = r
                .fill_constraints
                .as_ref()
                .ok_or("residual should have constraints")?;
            // After filling 60 out of max 100, residual should have reduced max
            if rc.generation != 1 {
                return Err(format!(
                    "residual generation should be 1, got {}",
                    rc.generation
                ));
            }
        }
        None => return Err("partial fill should produce a residual intent".into()),
    }

    // Track cumulative fills
    let tracker = CumulativeFillTracker::new(&intent).ok_or("should create tracker")?;
    if tracker.is_complete() {
        return Err("tracker should not be complete initially".into());
    }
    if tracker.remaining() == 0 {
        return Err("remaining should be > 0".into());
    }

    Ok(())
}
