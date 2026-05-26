//! Budget and audit gaming tests.
//!
//! Tests that the audit system correctly detects:
//! - Attempts to "forget" usage events
//! - Underreporting of usage counts
//! - Concurrent usage from multiple verifiers
//! - Budget race conditions

use dregg_audit::proofs::{BudgetProof, ConsistencyProof, CountProof};
use dregg_audit::{AuditLog, BudgetEnforcer, BudgetExhausted, BudgetSpec, LogSnapshot, UsageEvent};

use std::time::Duration;

// =============================================================================
// Helper functions
// =============================================================================

fn make_event(token_id: [u8; 32], seq: u64, ts: i64) -> UsageEvent {
    let action = blake3::hash(format!("action-{seq}").as_bytes());
    UsageEvent::new(token_id, ts, *action.as_bytes(), [0xBB; 32], seq)
}

fn make_event_verifier(token_id: [u8; 32], seq: u64, ts: i64, verifier: [u8; 32]) -> UsageEvent {
    let action = blake3::hash(format!("action-{seq}").as_bytes());
    UsageEvent::new(token_id, ts, *action.as_bytes(), verifier, seq)
}

// =============================================================================
// 1. Attempting to "forget" usage events
// =============================================================================

#[test]
fn consistency_proof_detects_missing_events() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    // Append 5 events
    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // Take a snapshot
    let snapshot = log.snapshot();
    assert_eq!(snapshot.size, 5);

    // Append more events
    for i in 5..10 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // Generate consistency proof (old -> new)
    let consistency = log.prove_consistency(&snapshot).unwrap();
    assert!(consistency.verify_structure());
    assert_eq!(consistency.old_size, 5);
    assert_eq!(consistency.new_size, 10);
}

#[test]
fn fake_snapshot_with_smaller_size_detected() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // Create a fake snapshot claiming more events than exist
    let fake_snapshot = LogSnapshot {
        root: [0xFF; 32],
        size: 100,
    };

    // Should fail because we only have 5 events
    let result = log.prove_consistency(&fake_snapshot);
    assert!(
        result.is_none(),
        "Cannot prove consistency for a fake future snapshot"
    );
}

#[test]
fn consistency_proof_detects_wrong_old_root() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // Take real snapshot
    let real_snapshot = log.snapshot();

    for i in 5..10 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // Create a fake snapshot with wrong root but correct size
    let fake_snapshot = LogSnapshot {
        root: [0xDE; 32], // wrong root
        size: real_snapshot.size,
    };

    let result = log.prove_consistency(&fake_snapshot);
    assert!(
        result.is_none(),
        "Fake root must not produce a consistency proof"
    );
}

#[test]
fn append_only_property_verified() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    // Build up log gradually, taking snapshots at each step
    let mut snapshots = Vec::new();
    for i in 0..10 {
        log.append(make_event(token, i, 1000 + i as i64));
        snapshots.push(log.snapshot());
    }

    // Every earlier snapshot should be consistent with the final state
    let final_snapshot = snapshots.last().unwrap().clone();
    for (i, snap) in snapshots.iter().enumerate() {
        if snap.size < final_snapshot.size {
            let proof = log.prove_consistency(snap).unwrap();
            assert!(
                proof.verify_structure(),
                "Consistency proof from snapshot {i} must verify"
            );
            assert_eq!(proof.old_root, snap.root);
        }
    }
}

// =============================================================================
// 2. Underreporting usage count
// =============================================================================

#[test]
fn count_proof_rejects_inflated_count() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..3 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    let mut proof = log.prove_count(&token);
    // Tamper: claim 1 use instead of 3
    proof.count = 1;

    assert!(!proof.verify(), "Deflated count must fail verification");
}

#[test]
fn count_proof_rejects_deflated_count() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..3 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    let mut proof = log.prove_count(&token);
    // Tamper: claim 5 uses instead of 3
    proof.count = 5;

    assert!(!proof.verify(), "Inflated count must fail verification");
}

#[test]
fn count_proof_rejects_tampered_index_commitment() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    let mut proof = log.prove_count(&token);
    // Tamper with index commitment
    proof.index_commitment = [0xAA; 32];

    assert!(!proof.verify(), "Tampered index commitment must fail");
}

#[test]
fn count_proof_rejects_duplicate_indices() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    let mut proof = log.prove_count(&token);
    // Duplicate an event proof to inflate count
    if let Some(first) = proof.event_proofs.first().cloned() {
        proof.event_proofs.push(first);
        proof.count += 1;
    }

    assert!(!proof.verify(), "Duplicate indices must fail verification");
}

// =============================================================================
// 3. Concurrent usage from multiple verifiers
// =============================================================================

#[test]
fn concurrent_verifiers_both_record_correctly() {
    let token = [1u8; 32];
    let verifier_a = [0xAA; 32];
    let verifier_b = [0xBB; 32];

    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(10));

    // Verifier A records a use
    let event_a = make_event_verifier(token, 0, 1000, verifier_a);
    let receipt_a = enforcer.record_use(event_a).unwrap();
    assert!(receipt_a.inclusion_proof.verify(&receipt_a.log_root_after));

    // Verifier B records a use
    let event_b = make_event_verifier(token, 1, 1001, verifier_b);
    let receipt_b = enforcer.record_use(event_b).unwrap();
    assert!(receipt_b.inclusion_proof.verify(&receipt_b.log_root_after));

    // Both events are recorded
    assert_eq!(enforcer.uses_consumed(1001), 2);

    // Both receipts prove their respective inclusions
    // (receipt_a is for the first root, receipt_b for the second)
    assert_ne!(receipt_a.log_root_after, receipt_b.log_root_after);
}

#[test]
fn concurrent_verifiers_with_budget_exhaustion() {
    let token = [1u8; 32];
    let verifier_a = [0xAA; 32];
    let verifier_b = [0xBB; 32];

    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(2));

    // First use by verifier A
    let event_a = make_event_verifier(token, 0, 1000, verifier_a);
    enforcer.record_use(event_a).unwrap();

    // Second use by verifier B
    let event_b = make_event_verifier(token, 1, 1001, verifier_b);
    enforcer.record_use(event_b).unwrap();

    // Third use by either verifier should fail
    let event_c = make_event_verifier(token, 2, 1002, verifier_a);
    let result = enforcer.record_use(event_c);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert_eq!(err.uses_consumed, 2);
    assert_eq!(err.budget_limit, 2);
}

#[test]
fn interleaved_verifier_events_maintain_order() {
    let token = [1u8; 32];
    let verifier_a = [0xAA; 32];
    let verifier_b = [0xBB; 32];

    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(100));

    // Interleave events from two verifiers
    for i in 0..20 {
        let verifier = if i % 2 == 0 { verifier_a } else { verifier_b };
        let event = make_event_verifier(token, i, 1000 + i as i64, verifier);
        let receipt = enforcer.record_use(event).unwrap();
        assert_eq!(receipt.global_index, i);
    }

    assert_eq!(enforcer.uses_consumed(1020), 20);
}

// =============================================================================
// 4. Budget racing / exceeding budget
// =============================================================================

#[test]
fn budget_exactly_at_limit() {
    let token = [1u8; 32];
    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(5));

    // Use exactly 5 times
    for i in 0..5 {
        let event = make_event(token, i, 1000 + i as i64);
        enforcer.record_use(event).unwrap();
    }

    // 6th use fails
    let event = make_event(token, 5, 1005);
    let result = enforcer.record_use(event);
    assert!(result.is_err());
    assert_eq!(enforcer.remaining(1005), 0);
}

#[test]
fn windowed_budget_race_at_boundary() {
    let token = [1u8; 32];
    let window = Duration::from_secs(100);
    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::windowed(2, window));

    // Use twice in window [0, 100)
    enforcer.record_use(make_event(token, 0, 50)).unwrap();
    enforcer.record_use(make_event(token, 1, 99)).unwrap();

    // Third use at t=99 (same window) should fail
    let result = enforcer.record_use(make_event(token, 2, 99));
    assert!(result.is_err());

    // But at t=100 (new window) should succeed
    assert!(enforcer.can_use(100));
    enforcer.record_use(make_event(token, 2, 100)).unwrap();
}

#[test]
fn budget_proof_detects_count_manipulation() {
    let token = [1u8; 32];
    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(10));

    for i in 0..4 {
        enforcer
            .record_use(make_event(token, i, 1000 + i as i64))
            .unwrap();
    }

    let mut proof = enforcer.prove_budget_status(1004);
    assert!(proof.verify());

    // Tamper: claim fewer uses consumed
    proof.uses_consumed = 2;
    proof.remaining = 8;
    assert!(!proof.verify(), "Manipulated budget proof must fail");
}

#[test]
fn budget_proof_arithmetic_tamper() {
    let token = [1u8; 32];
    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(10));

    for i in 0..3 {
        enforcer
            .record_use(make_event(token, i, 1000 + i as i64))
            .unwrap();
    }

    let mut proof = enforcer.prove_budget_status(1003);
    assert!(proof.verify());

    // Tamper: wrong arithmetic (remaining != limit - consumed)
    proof.remaining = 99;
    assert!(
        !proof.verify(),
        "Wrong arithmetic in budget proof must fail"
    );
}

#[test]
fn budget_proof_wrong_token_id() {
    let token = [1u8; 32];
    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(10));

    enforcer.record_use(make_event(token, 0, 1000)).unwrap();

    let mut proof = enforcer.prove_budget_status(1000);
    assert!(proof.verify());

    // Tamper: change token_id
    proof.token_id = [0xFF; 32];
    assert!(!proof.verify(), "Wrong token ID in budget proof must fail");
}

// =============================================================================
// 5. Receipt forgery
// =============================================================================

#[test]
fn receipt_inclusion_proof_tampered() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    let event = make_event(token, 0, 1000);
    let mut receipt = log.append(event);

    // Receipt verifies with correct root
    assert!(receipt.inclusion_proof.verify(&receipt.log_root_after));

    // Tamper with the inclusion proof
    if let Some(sibs) = receipt.inclusion_proof.siblings.first_mut() {
        sibs[0] = [0xDE; 32];
    }

    assert!(
        !receipt.inclusion_proof.verify(&receipt.log_root_after),
        "Tampered inclusion proof must fail"
    );
}

#[test]
fn receipt_against_wrong_root() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    let event = make_event(token, 0, 1000);
    let receipt = log.append(event);

    // Receipt should not verify against a different root
    let fake_root = [0xFF; 32];
    assert!(
        !receipt.inclusion_proof.verify(&fake_root),
        "Receipt must not verify against wrong root"
    );
}

#[test]
fn receipt_leaf_hash_tampered() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    let event = make_event(token, 0, 1000);
    let mut receipt = log.append(event);

    // Tamper with leaf hash
    receipt.inclusion_proof.leaf_hash = [0xAA; 32];

    assert!(
        !receipt.inclusion_proof.verify(&receipt.log_root_after),
        "Receipt with wrong leaf hash must fail"
    );
}

// =============================================================================
// 6. Range proof attacks
// =============================================================================

#[test]
fn range_proof_fails_when_events_outside_range() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    // Events at timestamps 1000, 1001, 1002, 1003, 1004
    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // Try to prove all events are in [1002, 1004] (but events at 1000, 1001 are outside)
    let proof = log.prove_range(&token, 1002, 1004);
    assert!(
        !proof.verify(),
        "Range proof including out-of-range events must fail"
    );
}

#[test]
fn range_proof_valid_when_all_in_range() {
    let token = [1u8; 32];
    let mut log = AuditLog::new();

    for i in 0..5 {
        log.append(make_event(token, i, 1000 + i as i64));
    }

    // All events are in [999, 1005]
    let proof = log.prove_range(&token, 999, 1005);
    assert!(
        proof.verify(),
        "Range proof with all events in range must verify"
    );
}

// =============================================================================
// 7. Multiple independent budgets
// =============================================================================

#[test]
fn separate_token_budgets_are_independent() {
    let token_a = [1u8; 32];
    let token_b = [2u8; 32];

    let mut enforcer_a = BudgetEnforcer::new(token_a, BudgetSpec::total(2));
    let mut enforcer_b = BudgetEnforcer::new(token_b, BudgetSpec::total(3));

    // Exhaust token A
    enforcer_a.record_use(make_event(token_a, 0, 1000)).unwrap();
    enforcer_a.record_use(make_event(token_a, 1, 1001)).unwrap();
    assert!(!enforcer_a.can_use(1002));

    // Token B should still be usable
    assert!(enforcer_b.can_use(1002));
    enforcer_b.record_use(make_event(token_b, 0, 1002)).unwrap();
    enforcer_b.record_use(make_event(token_b, 1, 1003)).unwrap();
    enforcer_b.record_use(make_event(token_b, 2, 1004)).unwrap();
    assert!(!enforcer_b.can_use(1005));
}

#[test]
fn budget_proof_for_zero_uses() {
    let token = [1u8; 32];
    let mut enforcer = BudgetEnforcer::new(token, BudgetSpec::total(5));

    let proof = enforcer.prove_budget_status(1000);
    assert_eq!(proof.uses_consumed, 0);
    assert_eq!(proof.remaining, 5);
    assert!(proof.verify());
}
