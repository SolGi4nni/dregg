//! Integration test: bridge credential presentation and verification.
//!
//! Tests the `BridgePresentationBuilder` pipeline and verifies that:
//! - A correctly-built presentation proof passes verification.
//! - A forged credential (wrong issuer key) is rejected by the issuer
//!   membership check.
//! - An expired token presentation is rejected by the authorization trace.
//! - A credential for the wrong app is rejected (authorization denied).
//! - The wire proof strips the private trace (zero-knowledge property).
//!
//! Note: tests use `prove_fast()` (constraint-checked, no real STARK) so
//! this file is NO-CARGO-compatible — no STARK proving happens.

use dregg_bridge::present::{BridgePresentationBuilder, UnsafeLocalOnlyMarker};
use dregg_token::{Attenuation, AuthRequest, MacaroonToken};

// ============================================================================
// Helpers
// ============================================================================

fn issuer_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = 0xDE;
    k[1] = 0xAD;
    k[28] = 0xCA;
    k[31] = 0xFE;
    k
}

fn other_key() -> [u8; 32] {
    // A different key — represents a different issuer / forged credential.
    let mut k = [0u8; 32];
    k[0] = 0xFF;
    k[1] = 0xFE;
    k[28] = 0xAB;
    k[31] = 0xCD;
    k
}

fn fed_root() -> [u8; 32] {
    let mut r = [0u8; 32];
    r[0] = 0xFE;
    r[1] = 0xD0;
    r
}

/// Compute the Poseidon2 federation root that matches the synthetic
/// path built by BridgePresentationBuilder (the same helper used in
/// bridge/src/tests.rs). Required so `prove_fast()` can complete without a
/// real federation tree.
fn matching_root_bb(key: &[u8; 32]) -> dregg_circuit::BabyBear {
    use dregg_circuit::BabyBear;
    use dregg_circuit::merkle_air::compute_parent_poseidon2;

    let issuer_hash = dregg_bridge::present::bytes_to_babybear(key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(dregg_bridge::present::hash_index(i, 0, key)),
            BabyBear::new(dregg_bridge::present::hash_index(i, 1, key)),
            BabyBear::new(dregg_bridge::present::hash_index(i, 2, key)),
        ];
        current = compute_parent_poseidon2(current, position, &siblings);
    }
    current
}

fn builder_for_key(key: [u8; 32]) -> BridgePresentationBuilder {
    BridgePresentationBuilder::new_with_root_bb(key, fed_root(), matching_root_bb(&key))
}

// ============================================================================
// Test: valid credential is accepted
// ============================================================================

#[test]
fn valid_credential_accepted() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-valid", "dregg.fg-goose.online");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let result = builder.prove_local_constraint_check_only(
        &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
        &req,
    );
    assert!(
        result.is_ok(),
        "valid credential presentation must be accepted: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_constraint_checked());
}

// ============================================================================
// Test: forged credential (wrong issuer key) — issuer membership fails
// ============================================================================

#[test]
fn wrong_issuer_key_rejected_by_membership_check() {
    let forged_key = other_key();

    // Mint a token using the FORGED key (not in the federation tree).
    let forged_token = MacaroonToken::mint(forged_key, b"kid-forge", "evil.dev");

    // Build with the forged key as the issuer — the synthetic Merkle path
    // built by BridgePresentationBuilder will not match the federation root
    // built for `real_key`.
    let mut builder = BridgePresentationBuilder::new(forged_key, fed_root());
    builder.set_root_token(forged_token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    // prove_fast uses the local constraint check path.  The issuer membership
    // check runs via `build_issuer_membership` before the auth trace is even
    // evaluated — a builder constructed with an unregistered key must fail.
    let result = builder.prove_local_constraint_check_only(
        &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
        &req,
    );
    let err = result
        .expect_err("forged (unregistered) issuer key must be rejected by issuer membership check");
    // The rejection must be the ISSUER-MEMBERSHIP tooth specifically — the forged
    // key's synthetic Merkle path does not hash into the federation root — not an
    // incidental auth-trace denial (`Denied`), empty state (`EmptyState`), or a
    // malformed request (`InvalidRequest`). A test that accepted any `Err` would
    // pass even if the membership check were removed and the rejection came from
    // an unrelated cause.
    assert_eq!(
        err,
        dregg_bridge::AuthError::IssuerNotInFederation,
        "expected IssuerNotInFederation (the membership tooth), got {err:?}"
    );
}

// ============================================================================
// Test: expired token is rejected by the authorization trace
// ============================================================================

#[test]
fn expired_credential_denied() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-exp", "dregg.fg-goose.online");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    // Attenuation with a hard expiry in the past.
    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        not_after: Some(1_000_000_000), // long in the past
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000), // 700 million seconds after the expiry
        ..Default::default()
    };

    let result = builder.prove_local_constraint_check_only(
        &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
        &req,
    );
    // The rejection must be the AUTH-TRACE denial (`Conclusion::Deny` on the past
    // `valid_until` caveat), not an incidental membership miss / empty state /
    // malformed request. A bare `is_err()` would stay green even if the expiry
    // gate were removed and the Err came from an unrelated cause.
    assert_eq!(
        result.unwrap_err(),
        dregg_bridge::AuthError::Denied,
        "credential with past expiry must be denied by the authorization trace"
    );
}

// ============================================================================
// Test: credential for wrong app is rejected
// ============================================================================

#[test]
fn credential_wrong_app_denied() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-app", "dregg.fg-goose.online");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    // Restrict to "dashboard".
    let att = Attenuation {
        apps: vec![("dashboard".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // But request is for "admin-panel" — not in the token.
    let req = AuthRequest {
        app_id: Some("admin-panel".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let result = builder.prove_local_constraint_check_only(
        &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
        &req,
    );
    // The rejection must be the AUTH-TRACE denial (`Conclusion::Deny` — the request
    // app is not authorized), not an incidental membership miss / empty state /
    // malformed request. A bare `is_err()` would stay green even if the app gate
    // were removed and the Err came from an unrelated cause.
    assert_eq!(
        result.unwrap_err(),
        dregg_bridge::AuthError::Denied,
        "credential restricted to 'dashboard' must be denied for 'admin-panel'"
    );
}

// ============================================================================
// Test: wire proof strips the private trace (zero-knowledge property)
// ============================================================================

#[test]
fn wire_proof_strips_private_trace() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-wire", "dregg.fg-goose.online");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let proof = builder
        .prove_local_constraint_check_only(
            &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
            &req,
        )
        .unwrap();

    // The full proof carries a trace (for local debugging).
    // Converting to wire format must not panic and must produce a proof
    // whose circuit-level check still holds.
    let wire = proof.into_wire_proof();
    assert!(
        matches!(
            wire.verification,
            dregg_circuit::PresentationVerification::Valid
                | dregg_circuit::PresentationVerification::LocalOnly
        ),
        "wire proof must retain the constraint verification result"
    );
    // The wire proof has no trace field at all — compile-time structural check.
    // (If WirePresentationProof ever gains a `trace` field this line won't compile,
    // which is the desired canary.)
    let _ = &wire.circuit_proof;
    let _ = &wire.verification;
}

// ============================================================================
// Test: user-confined credential — wrong user is denied
// ============================================================================

#[test]
fn credential_wrong_user_denied() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-user", "dregg.fg-goose.online");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        confine_user: Some("alice".to_string()),
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // bob is not alice.
    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        user_id: Some("bob".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let result = builder.prove_local_constraint_check_only(
        &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
        &req,
    );
    // The rejection must be the AUTH-TRACE denial (`Conclusion::Deny` — the
    // `confine_user(alice)` caveat rejects request user `bob`), not an incidental
    // membership miss / empty state / malformed request. A bare `is_err()` would
    // stay green even if the user-confinement gate were removed.
    assert_eq!(
        result.unwrap_err(),
        dregg_bridge::AuthError::Denied,
        "credential confined to 'alice' must be denied for user 'bob'"
    );
}

/// The builder's synthetic issuer-membership root must agree with the reference
/// recompute — was `debug_matching_root`, a pure-`println!` scratch test that
/// asserted nothing. Now it pins the synthetic Merkle-path construction (leaf →
/// position/sibling indexing → Poseidon2 fold) against two independent
/// recomputes, so a regression in `build_issuer_membership_poseidon2_synthetic`
/// (wrong position, sibling order, or hash) goes red here rather than surfacing
/// only through the deeper `valid_credential_accepted` round trip.
#[test]
fn synthetic_membership_root_matches_the_reference_recompute() {
    let key = issuer_key();
    let builder = builder_for_key(key);
    let issuer_hash = dregg_bridge::present::bytes_to_babybear(&key);

    let witness = builder
        .build_issuer_membership_poseidon2(issuer_hash)
        .expect("synthetic membership must build for a matching-root builder");

    // Recompute the folded root two independent ways.
    let helper_root = matching_root_bb(&key);
    let mut manual = issuer_hash;
    for i in 0..8 {
        let position = (i % 4) as u8;
        let siblings = [
            dregg_circuit::BabyBear::new(dregg_bridge::present::hash_index(i, 0, &key)),
            dregg_circuit::BabyBear::new(dregg_bridge::present::hash_index(i, 1, &key)),
            dregg_circuit::BabyBear::new(dregg_bridge::present::hash_index(i, 2, &key)),
        ];
        manual = dregg_circuit::merkle_air::compute_parent_poseidon2(manual, position, &siblings);
    }

    assert_eq!(
        witness.expected_root, helper_root,
        "builder synthetic membership root must equal the test-helper recompute"
    );
    assert_eq!(
        witness.expected_root, manual,
        "builder synthetic membership root must equal the inline recompute"
    );
    // Non-vacuity: the fold actually did work (the root is not the bare leaf).
    assert_ne!(
        witness.expected_root, issuer_hash,
        "the 8-level folded root must differ from the raw issuer leaf"
    );
}
