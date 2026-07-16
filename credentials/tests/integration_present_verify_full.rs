//! Integration test: full credential lifecycle with selective disclosure + tamper rejection.
//!
//! Exercises the four canonical credential operations on a real composed flow:
//!
//! 1. Issuer creates a multi-attribute credential.
//! 2. Holder builds a presentation disclosing only one attribute.
//! 3. Verifier checks: correct schema, correct disclosed attribute, no undisclosed leakage.
//! 4. Tamper: holder modifies the disclosed value in the presentation — verifier rejects.
//! 5. Tamper: holder changes which attributes are disclosed vs. what the verifier expects — reject.
//! 6. Predicate-only presentation (no cleartext disclosure): verifier checks `age >= 18`.
//! 7. Anonymous presentation (blinded membership): verifier accepts with `require_anonymous = true`.
//! 8. Schema mismatch on disclose: presenting an attribute name not in schema → `PresentationError`.

use dregg_credentials::{
    AttrValue, CredentialAttributes, CredentialSchema, IssuerKeys, Predicate, PredicateRequest,
    PresentationOptions, RevocationRegistry, VerificationOptions, issue, present,
    present_anonymous, revoke, verify, verify_anonymous,
};
use dregg_token::AuthRequest;

// ── fixture helpers ──────────────────────────────────────────────────────────

fn fixture_issuer() -> IssuerKeys {
    // Poseidon2-path federation root for key [11u8; 32].
    IssuerKeys::new(
        [11u8; 32],
        [
            33, 181, 62, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ],
        b"integration-test-kid",
        "integration-test-issuer",
    )
}

fn fixture_schema() -> CredentialSchema {
    CredentialSchema::new(
        "employee-v1",
        vec![
            "age".into(),
            "department".into(),
            "clearance_level".into(),
            "active".into(),
        ],
    )
}

fn fixture_attrs() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("age", AttrValue::Integer(32))
        .with("department", AttrValue::Text("Engineering".into()))
        .with("clearance_level", AttrValue::Integer(3))
        .with("active", AttrValue::Bool(true))
}

fn fixture_request() -> AuthRequest {
    AuthRequest {
        action: Some("api:read".into()),
        app_id: Some("employee-portal".into()),
        user_id: Some("4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    }
}

fn holder() -> [u8; 32] {
    [77u8; 32]
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn selective_disclosure_one_attribute() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred =
        issue(&issuer, &schema, h, attrs, 1_700_000_000, None).expect("issuance must succeed");

    // Present disclosing only `department`.
    let opts = PresentationOptions::new().disclose("department");
    let presentation =
        present(&cred, &fixture_request(), &opts).expect("presentation must succeed");

    assert_eq!(
        presentation.disclosed.len(),
        1,
        "only one attribute should be disclosed"
    );
    assert_eq!(presentation.disclosed[0].0, "department");
    match &presentation.disclosed[0].1 {
        AttrValue::Text(s) => assert_eq!(s, "Engineering"),
        other => panic!("expected Text(Engineering), got {other:?}"),
    }

    // Verifier expects `department` in the disclosure.
    let verify_opts = VerificationOptions {
        expected_schema: Some(schema.clone()),
        expected_disclosure: vec!["department".into()],
        ..Default::default()
    };
    let verified = verify(&presentation, &verify_opts).expect("verification must succeed");
    assert_eq!(verified.disclosed.len(), 1);
    assert_eq!(verified.disclosed[0].0, "department");
}

#[test]
fn tampered_disclosed_value_is_caught_by_verifier() {
    // A holder that swaps the cleartext disclosed value after presentation
    // construction must be REJECTED: the STARK binds
    // `proof.revealed_facts_commitment` as a public input, and the verifier
    // recomputes that commitment from the cleartext it was handed.
    //
    // 2026-07-16 — this test used to assert NOTHING. It ran `verify()` on the
    // tampered presentation and then said:
    //
    //     if let Ok(ref vp) = result { assert_eq!(vp.disclosed[0].1, Integer(99)); }
    //
    // i.e. if the verifier ACCEPTED the tamper, the test checked that the value
    // it accepted was exactly the attacker's value — and passed. Twenty lines of
    // prose ("Either outcome is documented") talked this into sounding like a
    // boundary. Its name claimed the tamper "is_caught_by_verifier"; nothing in
    // the body required that, and in fact the verifier had no revealed-facts
    // check at all. The real break — present honestly, then lie in the cleartext —
    // went unflagged. It now fails closed and this test requires the rejection.

    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();
    let opts = PresentationOptions::new().disclose("clearance_level");
    let mut presentation = present(&cred, &fixture_request(), &opts).unwrap();

    // Tamper: replace the disclosed value with a different integer.
    presentation.disclosed[0].1 = AttrValue::Integer(99); // was 3

    // Verifier expects clearance_level to be disclosed.
    let verify_opts = VerificationOptions {
        expected_disclosure: vec!["clearance_level".into()],
        ..Default::default()
    };

    // The tamper must be REJECTED. No "either outcome is documented".
    match verify(&presentation, &verify_opts) {
        Err(dregg_credentials::VerificationError::RevealedFactsMismatch) => {}
        Err(other) => panic!("expected RevealedFactsMismatch, got {other:?}"),
        Ok(vp) => panic!(
            "SOUNDNESS: verify() ACCEPTED a tampered disclosure and reported \
             clearance_level = {:?} (the credential says 3). The holder presented a \
             genuine proof and then rewrote the cleartext beside it.",
            vp.disclosed[0].1
        ),
    }
}

#[test]
fn stripped_disclosure_is_caught_by_verifier() {
    // The companion to the tamper: a holder who DELETES the cleartext disclosure
    // from a proof that committed to one must not be able to downgrade to
    // "disclosed nothing". The commitment the STARK binds is non-zero; an empty
    // cleartext recomputes to WideHash::ZERO, so this fails closed.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();
    let opts = PresentationOptions::new().disclose("clearance_level");
    let mut presentation = present(&cred, &fixture_request(), &opts).unwrap();

    presentation.disclosed.clear();

    // A verifier that asks for nothing in particular must still refuse: the proof
    // it was handed does not match the cleartext it was handed.
    match verify(&presentation, &VerificationOptions::new()) {
        Err(dregg_credentials::VerificationError::RevealedFactsMismatch) => {}
        Err(other) => panic!("expected RevealedFactsMismatch, got {other:?}"),
        Ok(_) => panic!(
            "SOUNDNESS: verify() ACCEPTED a presentation whose cleartext disclosures \
             were stripped away from a proof that commits to them"
        ),
    }
}

#[test]
fn missing_expected_disclosure_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();
    // Holder discloses `age` but verifier expects `department`.
    let opts = PresentationOptions::new().disclose("age");
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();

    let verify_opts = VerificationOptions {
        expected_disclosure: vec!["department".into()],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "missing expected disclosure must cause verification to fail"
    );
    match result.unwrap_err() {
        dregg_credentials::VerificationError::MissingDisclosure(attr) => {
            assert_eq!(attr, "department");
        }
        other => panic!("expected MissingDisclosure(department), got {other:?}"),
    }
}

#[test]
fn predicate_age_gte_18_without_cleartext_disclosure() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs(); // age = 32
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();

    // No cleartext disclosure; only a predicate proof for age >= 18.
    let opts =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(18)));
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();

    assert_eq!(
        presentation.disclosed.len(),
        0,
        "no cleartext attributes should be disclosed"
    );
    assert_eq!(presentation.predicate_proofs.len(), 1);
    assert_eq!(presentation.predicate_proofs[0].attribute, "age");

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    verify(&presentation, &verify_opts).expect("predicate-only verification must succeed");
}

#[test]
fn predicate_on_text_attribute_fails_at_presentation_time() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();

    // `department` is a Text attribute — it has no numeric predicate value.
    let opts = PresentationOptions::new()
        .predicate(PredicateRequest::new("department", Predicate::Gte(0)));
    let result = present(&cred, &fixture_request(), &opts);
    assert!(
        result.is_err(),
        "predicate on a Text attribute must fail at presentation time"
    );
    match result.unwrap_err() {
        dregg_credentials::PresentationError::NonPredicateAttribute(name) => {
            assert_eq!(name, "department");
        }
        other => panic!("expected NonPredicateAttribute(department), got {other:?}"),
    }
}

#[test]
fn anonymous_presentation_accepted_by_verify_anonymous() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();
    let opts = PresentationOptions::new().disclose("active");
    let presentation = present_anonymous(&cred, &fixture_request(), &opts)
        .expect("anonymous presentation must succeed");

    assert!(
        presentation.anonymous,
        "presentation must be marked anonymous"
    );

    let verify_opts = VerificationOptions {
        expected_disclosure: vec!["active".into()],
        require_anonymous: true,
        ..Default::default()
    };
    let verified =
        verify_anonymous(&presentation, &verify_opts).expect("anonymous verification must succeed");
    assert!(verified.anonymous);
    assert_eq!(verified.disclosed.len(), 1);
    match &verified.disclosed[0].1 {
        AttrValue::Bool(b) => assert!(*b),
        other => panic!("expected Bool(true), got {other:?}"),
    }
}

#[test]
fn non_anonymous_presentation_rejected_when_anonymous_required() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();
    let opts = PresentationOptions::new();
    // Present via the non-anonymous path.
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();
    assert!(!presentation.anonymous);

    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "non-anonymous presentation must be rejected when anonymous required"
    );
    match result.unwrap_err() {
        dregg_credentials::VerificationError::AnonymityMismatch => {}
        other => panic!("expected AnonymityMismatch, got {other:?}"),
    }
}

#[test]
fn revoked_credential_presentation_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attrs();
    let h = holder();

    let cred = issue(&issuer, &schema, h, attrs, 1_700_000_000, None).unwrap();
    let registry = RevocationRegistry::new();

    // Issue + present before revocation — must succeed.
    let pre_opts = PresentationOptions::new();
    let pre_presentation = present(&cred, &fixture_request(), &pre_opts).unwrap();
    let pre_verify = VerificationOptions::default();
    verify(&pre_presentation, &pre_verify).expect("pre-revocation verification must succeed");

    // Revoke.
    let proof = revoke(&registry, &cred);
    assert!(proof.revoked);
    assert!(registry.is_revoked(&cred.id()));

    // Same presentation — now fails with revocation proof attached.
    let post_verify = VerificationOptions {
        revocation: Some(proof),
        ..Default::default()
    };
    let result = verify(&pre_presentation, &post_verify);
    assert!(result.is_err(), "post-revocation verification must fail");
    match result.unwrap_err() {
        dregg_credentials::VerificationError::Revoked => {}
        other => panic!("expected Revoked, got {other:?}"),
    }
}

#[test]
fn credential_id_is_stable_and_unique_per_issuance() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();

    let cred1 = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();
    let cred2 = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_001, None).unwrap();

    // IDs must be stable (same credential re-computed → same ID).
    assert_eq!(
        cred1.id(),
        cred1.id(),
        "credential ID must be deterministic"
    );
    // Two credentials issued at different times must have different IDs.
    assert_ne!(
        cred1.id(),
        cred2.id(),
        "credentials issued at different times must have distinct IDs"
    );
}
