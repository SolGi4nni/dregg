//! Executor-invoking integration tests for the identity credential lifecycle.
//!
//! Unlike `credential_lifecycle.rs` (which calls `issue`/`present`/`verify`
//! directly), these tests drive `EmbeddedExecutor::submit_action` with the
//! turn-builder actions and assert observable `TurnReceipt` outcomes —
//! `emitted_events`, `action_count`, and `is_err()`.
//!
//! This is what the Python `cross-app-e2e/` demo does NOT cover: the demo
//! verifies canonical commitment encoding; it never calls `submit_action`
//! and therefore never exercises:
//!
//! - The executor's authorization-signature check on issuance/revocation
//!   actions.
//! - The `emitted_events` produced by `build_issue_credential_action` and
//!   `build_verify_presentation_action`.
//! - The accept-flag encoding in the `presentation-verified` event.
//! - Revocation root monotonicity enforcement through the executor.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::{CellProgram, StateConstraint};
use starbridge_identity::{
    AttrValue, CredentialAttributes, IssuerKeys, Predicate, PredicateRequest, PresentationOptions,
    REVOCATION_ROOT_SLOT, RevocationRegistry, VerificationOptions, build_issue_credential_action,
    build_present_credential_action, build_revoke_credential_action,
    build_verify_presentation_action, issue, kyc_schema, present, present_anonymous, revoke,
};

// =============================================================================
// Fixtures
// =============================================================================

fn fixture_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
}

fn fixture_executor(cipherclerk: &AppCipherclerk) -> (EmbeddedExecutor, CellId) {
    let executor = EmbeddedExecutor::new(cipherclerk, "default");
    let cell = executor.cell_id();
    // Install the minimal program that enforces revocation-root monotonicity,
    // so the executor rejects rollback attempts in the adversarial test.
    executor.install_program(
        cell,
        CellProgram::Predicate(vec![StateConstraint::Monotonic {
            index: REVOCATION_ROOT_SLOT as u8,
        }]),
    );
    (executor, cell)
}

fn fixture_issuer() -> IssuerKeys {
    // Poseidon2-path federation root (matches hash_4_to_1 / DSL circuit).
    IssuerKeys::new(
        [100u8; 32],
        [
            3, 154, 242, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ],
        b"integration-test",
        "starbridge-identity",
    )
}

fn fixture_attributes() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Alice".into()))
        .with("family_name", AttrValue::Text("Doe".into()))
        .with("dob", AttrValue::Date(10_000))
        .with("verification_level", AttrValue::Integer(2))
}

// =============================================================================
// Test 1: issue → executor emits credential-issued event with correct id
// =============================================================================

/// Drive `build_issue_credential_action` through the embedded executor.
/// The receipt must carry a `credential-issued` event whose first data
/// field equals the credential's canonical 32-byte id.
#[test]
fn executor_issue_credential_emits_receipt_with_credential_issued_event() {
    let cipherclerk = fixture_cipherclerk();
    let (executor, issuer_cell) = fixture_executor(&cipherclerk);

    let schema = kyc_schema();
    let credential = issue(
        &fixture_issuer(),
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .expect("issuance must succeed");

    let action =
        build_issue_credential_action(&cipherclerk, issuer_cell, &credential, 1, [0u8; 32]);

    let receipt = executor
        .submit_action(&cipherclerk, action)
        .expect("issue_credential action must be accepted by the executor");

    assert_eq!(receipt.action_count, 1, "expected one action in the turn");
    assert!(
        !receipt.emitted_events.is_empty(),
        "issue_credential must emit at least one event"
    );

    // The emitted event's first data field must be the credential id.
    let ev = &receipt.emitted_events[0];
    assert_eq!(
        ev.data[0],
        credential.id(),
        "credential-issued event's first field must equal the credential id"
    );
}

// =============================================================================
// Test 2: issue → present → build_verify → executor emits accepted event
// =============================================================================

/// Full pipeline through the executor:
/// 1. Issue a credential (executor sees `issue_credential` action).
/// 2. Build a presentation (pure crypto, no executor call).
/// 3. Submit `build_present_credential_action` (executor sees `present_credential`).
/// 4. Submit `build_verify_presentation_action` (executor sees `verify_presentation`).
///
/// The final receipt must include an event with accept_flag = 1.
#[test]
fn executor_full_issue_present_verify_pipeline_accept_flag_is_one() {
    let cipherclerk = fixture_cipherclerk();
    let (executor, cell) = fixture_executor(&cipherclerk);

    let schema = kyc_schema();
    let credential = issue(
        &fixture_issuer(),
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Step 1: Issue.
    let issue_action = build_issue_credential_action(&cipherclerk, cell, &credential, 1, [0u8; 32]);
    executor
        .submit_action(&cipherclerk, issue_action)
        .expect("issue must succeed");

    // Step 2: Present.
    let options = PresentationOptions::new()
        .disclose("verification_level")
        .predicate(PredicateRequest::new(
            "verification_level",
            Predicate::Gte(1),
        ));
    let presentation = present(
        &credential,
        &dregg_token::AuthRequest {
            action: Some("read".into()),
            app_id: Some("integration-test".into()),
            user_id: Some(
                "0909090909090909090909090909090909090909090909090909090909090909".into(),
            ),
            now: Some(1_700_000_000),
            ..Default::default()
        },
        &options,
    )
    .expect("presentation must succeed");

    // Step 3: Anchor the presentation on the holder's cell.
    let present_action = build_present_credential_action(&cipherclerk, cell, &presentation);
    executor
        .submit_action(&cipherclerk, present_action)
        .expect("present_credential action must succeed");

    // Step 4: Verify — executor-bound.
    let verify_opts = VerificationOptions {
        expected_schema: Some(schema),
        expected_disclosure: vec!["verification_level".into()],
        expected_predicates: vec![PredicateRequest::new(
            "verification_level",
            Predicate::Gte(1),
        )],
        ..Default::default()
    };
    let verify_action =
        build_verify_presentation_action(&cipherclerk, cell, &presentation, &verify_opts);
    let verify_receipt = executor
        .submit_action(&cipherclerk, verify_action)
        .expect("verify_presentation action must be accepted by the executor");

    assert!(!verify_receipt.emitted_events.is_empty());
    let ev = &verify_receipt.emitted_events[0];
    // event.data[1] is accept_flag; 1 = accepted.
    assert_eq!(
        ev.data[1][31], 1,
        "accept_flag in presentation-accepted event must be 1 (accepted)"
    );
}

// =============================================================================
// Test 3: revoke → executor emits credential-revoked event, monotonic root
// =============================================================================

/// Issue then revoke a credential through the executor.
/// - The `revoke_credential` action must produce a receipt.
/// - The emitted event's second field must equal the new revocation root.
/// - A second revocation attempt with a smaller root must be rejected by
///   the `Monotonic(REVOCATION_ROOT_SLOT)` caveat.
#[test]
fn executor_revoke_emits_credential_revoked_event_and_monotonic_blocks_root_rollback() {
    let cipherclerk = fixture_cipherclerk();
    let (executor, issuer_cell) = fixture_executor(&cipherclerk);

    let schema = kyc_schema();
    let credential = issue(
        &fixture_issuer(),
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Issue the credential first (establishes issuance counter state).
    let issue_action =
        build_issue_credential_action(&cipherclerk, issuer_cell, &credential, 1, [0u8; 32]);
    executor
        .submit_action(&cipherclerk, issue_action)
        .expect("issuance must succeed");

    // Revoke the credential.
    let registry = RevocationRegistry::new();
    let revocation_proof = revoke(&registry, &credential);
    assert!(
        revocation_proof.revoked,
        "registry must mark credential as revoked"
    );

    let new_root = registry.root();
    let rev_action =
        build_revoke_credential_action(&cipherclerk, issuer_cell, credential.id(), new_root);
    let rev_receipt = executor
        .submit_action(&cipherclerk, rev_action)
        .expect("revoke_credential action must succeed");

    assert!(!rev_receipt.emitted_events.is_empty());
    let ev = &rev_receipt.emitted_events[0];
    // event.data[0] = credential id; event.data[1] = new revocation root.
    assert_eq!(
        ev.data[0],
        credential.id(),
        "revocation event must carry the credential id"
    );
    assert_eq!(
        ev.data[1], new_root,
        "revocation event must carry the new revocation root"
    );

    // Adversarial: attempt to rewind the revocation root to [0u8; 32].
    // The `Monotonic(REVOCATION_ROOT_SLOT)` caveat must reject this.
    let rollback_action = build_revoke_credential_action(
        &cipherclerk,
        issuer_cell,
        credential.id(),
        [0u8; 32], // zero root — below the current non-zero root
    );
    let rollback_result = executor.submit_action(&cipherclerk, rollback_action);
    assert!(
        rollback_result.is_err(),
        "rolling back the revocation root below its current value must be rejected; got: {rollback_result:?}"
    );
}

// =============================================================================
// Test 4: verify rejects presentation of revoked credential → reject event
// =============================================================================

/// Issue → revoke → present (holder doesn't know) → verify (verifier knows).
/// The `build_verify_presentation_action` must emit a `presentation-rejected`
/// event (accept_flag = 0) when the verifier supplies the non-revocation
/// proof confirming revocation.
#[test]
fn executor_verify_revoked_presentation_emits_reject_event() {
    let cipherclerk = fixture_cipherclerk();
    let (executor, issuer_cell) = fixture_executor(&cipherclerk);

    let schema = kyc_schema();
    let credential = issue(
        &fixture_issuer(),
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Issue.
    let issue_action =
        build_issue_credential_action(&cipherclerk, issuer_cell, &credential, 1, [0u8; 32]);
    executor
        .submit_action(&cipherclerk, issue_action)
        .expect("issuance must succeed");

    // Revoke.
    let registry = RevocationRegistry::new();
    let revocation_proof = revoke(&registry, &credential);
    let rev_action =
        build_revoke_credential_action(&cipherclerk, issuer_cell, credential.id(), registry.root());
    executor
        .submit_action(&cipherclerk, rev_action)
        .expect("revocation must succeed");

    // Holder presents (doesn't yet know it's revoked).
    let presentation = present(
        &credential,
        &dregg_token::AuthRequest {
            action: Some("read".into()),
            app_id: Some("integration-test".into()),
            user_id: Some(
                "0909090909090909090909090909090909090909090909090909090909090909".into(),
            ),
            now: Some(1_700_000_000),
            ..Default::default()
        },
        &PresentationOptions::new(),
    )
    .expect("presentation builds even for revoked credential");

    // Verifier checks with the revocation proof → must reject.
    let verify_opts = VerificationOptions {
        revocation: Some(revocation_proof),
        ..Default::default()
    };
    let verify_action =
        build_verify_presentation_action(&cipherclerk, issuer_cell, &presentation, &verify_opts);
    let verify_receipt = executor.submit_action(&cipherclerk, verify_action).expect(
        "verify_presentation action must be accepted as a valid action (rejection is in the event)",
    );

    assert!(!verify_receipt.emitted_events.is_empty());
    let ev = &verify_receipt.emitted_events[0];
    // accept_flag (ev.data[1][31]) must be 0 = rejected.
    assert_eq!(
        ev.data[1][31], 0,
        "accept_flag in presentation-rejected event must be 0 (rejected)"
    );
}

// =============================================================================
// Test 5: anonymous presentation — executor records without PII
// =============================================================================

/// An anonymous presentation's `present_credential` action must produce a
/// receipt whose emitted event's second data field (holder_commitment) is
/// `[0u8; 32]` — the anonymous sentinel. This verifies that the action's
/// no-PII-leak guarantee is enforced at the executor boundary.
#[test]
fn executor_anonymous_presentation_action_emits_zero_holder_commitment() {
    let cipherclerk = fixture_cipherclerk();
    let (executor, cell) = fixture_executor(&cipherclerk);

    let schema = kyc_schema();
    let credential = issue(
        &fixture_issuer(),
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    let presentation = present_anonymous(
        &credential,
        &dregg_token::AuthRequest {
            action: Some("read".into()),
            app_id: Some("integration-test".into()),
            user_id: Some(
                "0909090909090909090909090909090909090909090909090909090909090909".into(),
            ),
            now: Some(1_700_000_000),
            ..Default::default()
        },
        &PresentationOptions::new().disclose("verification_level"),
    )
    .expect("anonymous presentation must succeed");

    assert!(
        presentation.anonymous,
        "presentation must be marked anonymous"
    );

    let present_action = build_present_credential_action(&cipherclerk, cell, &presentation);
    let receipt = executor
        .submit_action(&cipherclerk, present_action)
        .expect("anonymous present_credential must be accepted by executor");

    assert!(!receipt.emitted_events.is_empty());
    let ev = &receipt.emitted_events[0];
    // For anonymous presentations the holder_commitment is the zero field.
    assert_eq!(
        ev.data[1], [0u8; 32],
        "anonymous presentation must emit zero holder_commitment (no PII)"
    );
    // The anonymous_flag field (data[2][31]) must be 1.
    assert_eq!(
        ev.data[2][31], 1,
        "anonymous_flag in credential-presented event must be 1"
    );
}
