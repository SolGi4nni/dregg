//! Adversarial tests for the credential anonymity-soundness fixes.
//!
//! These are FAIL-before / PASS-after tests for the four holes a prior
//! audit found in `credentials/src/{presentation,verification}.rs`:
//!
//! (a) `verify_anonymous` must REJECT non-cryptographic `LocalOnly` proofs.
//! (b) Predicate proofs must be bound cryptographically to the proven
//!     statement, not matched by attribute NAME only.
//! (c) Two anonymous presentations of the same credential must be
//!     unlinkable (different `blinded_leaf` public inputs).
//! (d) A revoked credential must be rejected by a real non-membership
//!     check (not a self-asserted `revoked` boolean).

use dregg_credentials::{
    AttrValue, CredentialAttributes, CredentialSchema, IssuerKeys, Predicate, PredicateRequest,
    PresentationOptions, RevocationRegistry, UnsafeLocalOnlyMarker, VerificationOptions, issue,
    present, present_anonymous, present_local_only_unsafe, revoke, verify, verify_anonymous,
};
use dregg_token::AuthRequest;

// ── fixtures ─────────────────────────────────────────────────────────────────

fn fixture_issuer() -> IssuerKeys {
    IssuerKeys::new(
        [11u8; 32],
        [
            33, 181, 62, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ],
        b"anonymity-soundness-kid",
        "anonymity-soundness-issuer",
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
        now: Some(1_700_000_000),
        ..Default::default()
    }
}

fn holder() -> [u8; 32] {
    [77u8; 32]
}

/// Extract the issuer-membership `blinded_leaf` public input from the blinded
/// ring-membership descriptor wire (the flip off the hand-STARK issuer proof).
/// Its vk encodes `[blinded_leaf, root]` as one canonical little-endian `u32`
/// per 4 bytes, so `blinded_leaf` (PI slot 0) is the first 4 vk bytes. Two
/// presentations of the same credential must produce different values
/// (unlinkability — a distinct blinding factor per show).
fn blinded_leaf(p: &dregg_credentials::Presentation) -> u32 {
    let real = p
        .proof
        .real_stark_proof
        .as_ref()
        .expect("anonymous presentation must carry a real STARK proof");
    let vk = &real.blinded_membership.vk;
    assert!(
        vk.len() >= 4,
        "blinded ring-membership vk must carry at least the blinded_leaf public input"
    );
    u32::from_le_bytes([vk[0], vk[1], vk[2], vk[3]])
}

// ── (a) LocalOnly rejected for anonymous verification ─────────────────────────

/// Build a genuinely LocalOnly (non-cryptographic) presentation — the thing a
/// verifier must refuse. This is the ONLY way to get one out of this crate now;
/// `present()` produces a real STARK.
fn local_only_presentation() -> dregg_credentials::Presentation {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let cred = issue(
        &issuer,
        &schema,
        holder(),
        fixture_attrs(),
        1_700_000_000,
        None,
    )
    .unwrap();
    let opts = PresentationOptions::new().disclose("active");
    let marker = UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound();
    let p = present_local_only_unsafe(&cred, &fixture_request(), &opts, &marker).unwrap();
    assert!(
        p.proof.real_stark_proof.is_none(),
        "fixture precondition: the LocalOnly path must carry no STARK"
    );
    p
}

#[test]
fn local_only_proof_rejected_by_verify_anonymous() {
    let local_only = local_only_presentation();
    assert!(
        !local_only.anonymous,
        "the LocalOnly path must not be marked anonymous"
    );

    // Asking for an anonymous verification of a LocalOnly proof must FAIL:
    // the unlinkability guarantee was never cryptographically proven.
    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    let result = verify_anonymous(&local_only, &verify_opts);
    assert!(
        result.is_err(),
        "verify_anonymous must reject a non-cryptographic LocalOnly proof"
    );
    match result.unwrap_err() {
        dregg_credentials::VerificationError::AnonymityMismatch
        | dregg_credentials::VerificationError::LocalOnlyRejected => {}
        other => panic!("expected LocalOnlyRejected/AnonymityMismatch, got {other:?}"),
    }
}

// ── (a2) LocalOnly rejected by the DEFAULT verify() — the real tooth ──────────
//
// 2026-07-16. The test above never bit the thing it named: it fed `verify_anonymous`
// a NON-anonymous proof, so check 1 (`AnonymityMismatch`) fired before the LocalOnly
// check was ever reached — and it accepted either error. Meanwhile the DEFAULT path
// (`require_anonymous: false`, which is `Default`) waved LocalOnly straight through.
// So the crate's own present()+verify() round trip did zero cryptographic
// verification and returned a `VerifiedPresentation` for it.
//
// This test pins the fail-closed contract at the DEFAULT settings, where the hole was.

#[test]
fn local_only_proof_rejected_by_default_verify() {
    let local_only = local_only_presentation();

    // The DEFAULT verifier: require_anonymous is false. This is what every
    // caller who did not think about anonymity gets.
    let verify_opts = VerificationOptions::new();
    let result = verify(&local_only, &verify_opts);

    match result {
        Err(dregg_credentials::VerificationError::LocalOnlyRejected) => {}
        Err(other) => panic!("expected LocalOnlyRejected, got {other:?}"),
        Ok(v) => panic!(
            "SOUNDNESS: default verify() ACCEPTED a non-cryptographic LocalOnly proof \
             and returned a VerifiedPresentation ({v:?}). The 'verification' that ran \
             happened on the presenter's own machine and was never re-checked."
        ),
    }
}

// ── (a3) present() must produce a REAL STARK, not a local constraint check ────
//
// The companion half. `present()`'s doc has always claimed "Full STARK ... suitable
// for cross-trust-boundary verification"; until 2026-07-16 it called
// `prove_local_constraint_check_only` for every non-anonymous presentation. If this
// regresses, (a2) turns the crate's default round trip red rather than silently
// restoring the mock.

#[test]
fn present_produces_a_real_stark_proof() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let cred = issue(
        &issuer,
        &schema,
        holder(),
        fixture_attrs(),
        1_700_000_000,
        None,
    )
    .unwrap();

    let opts = PresentationOptions::new().disclose("active");
    let p = present(&cred, &fixture_request(), &opts).unwrap();

    assert!(
        p.proof.real_stark_proof.is_some(),
        "present() must carry a real STARK proof — a verifier who did not run the \
         prover has nothing to check otherwise"
    );
    assert!(
        p.proof.is_valid(),
        "present()'s proof must be cryptographically valid, not LocalOnly"
    );
    verify(&p, &VerificationOptions::new()).expect("a real present() proof must verify by default");
}

#[test]
fn real_anonymous_proof_accepted_by_verify_anonymous() {
    // Positive control: the genuine ring-blinded anonymous path passes.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts = PresentationOptions::new().disclose("active");
    let p = present_anonymous(&cred, &fixture_request(), &opts).unwrap();
    assert!(p.anonymous);

    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    verify_anonymous(&p, &verify_opts).expect("real anonymous proof must verify");
}

// ── (b) name-only predicate spoof rejected ────────────────────────────────────

#[test]
fn name_only_predicate_spoof_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    // Holder proves a WEAK statement about `age` (age >= 1, trivially true)
    // but the verifier requires `age >= 18`. With name-only matching this
    // would have passed (attribute "age" is present); with cryptographic
    // binding the proven statement (Gte(1)) ≠ requested (Gte(18)) → reject.
    let opts =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(1)));
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();
    assert_eq!(presentation.predicate_proofs.len(), 1);
    assert_eq!(presentation.predicate_proofs[0].attribute, "age");

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "a predicate proof for a different statement must be rejected, not matched by name"
    );
    match result.unwrap_err() {
        dregg_credentials::VerificationError::PredicateMismatch { attribute } => {
            assert_eq!(attribute, "age");
        }
        other => panic!("expected PredicateMismatch(age), got {other:?}"),
    }
}

#[test]
fn relabelled_predicate_proof_rejected() {
    // Stronger spoof: take a genuine proof generated for `clearance_level`
    // and relabel its NamedPredicateProof.attribute to "age". The verifier
    // asks for `age >= 18`. Name-only matching would accept (the relabelled
    // attribute is "age"); cryptographic binding rejects because the proven
    // statement is Gte(1) (clearance proof) ≠ the requested Gte(18), and the
    // STARK is bound to clearance_level's fact commitment, not age's.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts = PresentationOptions::new()
        .predicate(PredicateRequest::new("clearance_level", Predicate::Gte(1)));
    let mut presentation = present(&cred, &fixture_request(), &opts).unwrap();

    // Relabel the attribute name to "age" — a pure-string forgery.
    presentation.predicate_proofs[0].attribute = "age".to_string();

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "a relabelled predicate proof must be rejected by cryptographic binding"
    );
}

// ── (b') CROSS-CREDENTIAL predicate FORGERY — the live hole ───────────────────
//
// `relabelled_predicate_proof_rejected` above only bites on a THRESHOLD MISMATCH
// (a clearance `Gte(1)` proof relabelled onto an `age Gte(18)` request → the
// `predicate != expected.predicate` guard fires FIRST). It gives ZERO assurance
// against a SAME-THRESHOLD, DIFFERENT-CREDENTIAL attach, which this test exposes.
//
// THE HOLE (verification.rs, step (iii)): each predicate proof is verified with
// the BARE `verify_predicate_proof(&p.proof, p.proof.fact_commitment)` — against
// the proof's OWN commitment. That equality is `x == x`, vacuous. Nothing binds
// the commitment to (i) THIS presentation's credential / `final_state_root` or
// (ii) the requested attribute beyond the holder-controlled
// `NamedPredicateProof.attribute` string. The predicate STARK proves only "SOME
// fact with this commitment satisfies the predicate" — for a commitment the
// prover supplied.
//
// FORGERY: a holder owns a legit credential X (age 32) and mints a GENUINE
// `Gte(18)` proof from it. They then present a DIFFERENT credential A (age 15,
// which FAILS `age >= 18`), attach X's genuine proof under `attribute = "age"`
// (same threshold), and `verify()` ACCEPTS — handing the verifier a
// `VerifiedPresentation` asserting A's holder is >= 18. A predicate forgery
// across credentials.
//
// #[ignore]d because the SOUND fix is a multi-part ripple not yet wired:
//   1. the presentation STARK must expose a `facts_root` PUBLIC INPUT — a proven
//      Merkle root over the token's REAL fact set (not just disclosed facts);
//   2. the producer (presentation.rs) must attach a
//      `dregg_bridge::present::BridgeFactAttestation` to each predicate proof
//      (Merkle membership of the predicate fact under that facts_root), via
//      `prove_predicate_for_fact_attested` instead of `prove_predicate_for_fact`;
//   3. `verify()` must route through
//      `dregg_bridge::present::verify_predicate_proof_third_party(&p.proof,
//      facts_root, final_state_root)` — facts_root taken from (1), NOT from the
//      proof.
// Until (1)–(3) land, running this test with `--ignored` FAILS at the final
// assert (verify returns Ok — the forgery). That failure IS the executable proof
// of the live hole; un-ignore it when the binding lands.
#[test]
#[ignore = "LIVE credential-forgery hole: a predicate proof is verified against its OWN \
            commitment (x==x), never bound to this presentation's credential/attribute. A genuine \
            same-threshold proof from a DIFFERENT credential is accepted. Un-ignore once the \
            presentation STARK exposes facts_root + producer attaches a BridgeFactAttestation + \
            verify() routes through verify_predicate_proof_third_party. See module note (b')."]
fn cross_credential_predicate_forgery_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();

    // Credential X: age 32 — legitimately satisfies `age >= 18`.
    let cred_x = issue(
        &issuer,
        &schema,
        [0x11u8; 32],
        CredentialAttributes::new()
            .with("age", AttrValue::Integer(32))
            .with("department", AttrValue::Text("Engineering".into()))
            .with("clearance_level", AttrValue::Integer(3))
            .with("active", AttrValue::Bool(true)),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Credential A: age 15 — FAILS `age >= 18`. A DIFFERENT credential (different
    // holder, different attributes ⇒ different fold-chain `final_state_root`).
    let cred_a = issue(
        &issuer,
        &schema,
        [0x22u8; 32],
        CredentialAttributes::new()
            .with("age", AttrValue::Integer(15))
            .with("department", AttrValue::Text("Interns".into()))
            .with("clearance_level", AttrValue::Integer(0))
            .with("active", AttrValue::Bool(true)),
        1_700_000_000,
        None,
    )
    .unwrap();

    // A GENUINE `age >= 18` proof, minted from X (age 32).
    let x_opts =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(18)));
    let x_pres = present(&cred_x, &fixture_request(), &x_opts).unwrap();
    assert_eq!(x_pres.predicate_proofs.len(), 1);
    let stolen = x_pres.predicate_proofs[0].clone();
    assert_eq!(stolen.attribute, "age");
    assert_eq!(stolen.proof.predicate, Predicate::Gte(18));

    // Present A with NO predicate of its own, then ATTACH X's genuine proof. The
    // threshold matches exactly (both `Gte(18)`), so the `PredicateMismatch`
    // guard that `relabelled_predicate_proof_rejected` relies on does NOT fire.
    let mut a_pres = present(&cred_a, &fixture_request(), &PresentationOptions::new()).unwrap();
    assert!(a_pres.predicate_proofs.is_empty());
    a_pres.predicate_proofs.push(stolen);

    // Verifier asks: does A's holder satisfy `age >= 18`? A is 15 — the true
    // answer is NO.
    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    let result = verify(&a_pres, &verify_opts);
    assert!(
        result.is_err(),
        "SOUNDNESS: a predicate proof minted from a DIFFERENT credential must NOT satisfy this \
         presentation's predicate — credential A (age 15) is not >= 18. Today verify() ACCEPTS \
         (the forgery); this assert is exactly what the facts_root binding must make hold."
    );
}

#[test]
fn matching_predicate_proof_accepted() {
    // Positive control: a genuine `age >= 18` proof for the matching request
    // verifies cryptographically.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(18)));
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    verify(&presentation, &verify_opts).expect("genuine matching predicate proof must verify");
}

// ── (c) two anonymous presentations are unlinkable ────────────────────────────

#[test]
fn two_anonymous_presentations_are_unlinkable() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts = PresentationOptions::new().disclose("active");
    let p1 = present_anonymous(&cred, &fixture_request(), &opts).unwrap();
    let p2 = present_anonymous(&cred, &fixture_request(), &opts).unwrap();

    let leaf1 = blinded_leaf(&p1);
    let leaf2 = blinded_leaf(&p2);

    assert_ne!(
        leaf1, leaf2,
        "two anonymous shows of the SAME credential must produce different blinded leaves (unlinkable)"
    );

    // Both must still verify as anonymous.
    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    verify_anonymous(&p1, &verify_opts).expect("first anonymous show must verify");
    verify_anonymous(&p2, &verify_opts).expect("second anonymous show must verify");
}

// ── (d) revoked credential rejected by a real non-membership check ────────────

#[test]
fn revoked_credential_rejected_by_real_non_membership() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();
    let registry = RevocationRegistry::new();

    let presentation = present(&cred, &fixture_request(), &PresentationOptions::new()).unwrap();

    // Before revocation: a non-revocation proof must let verification pass,
    // anchored against the registry's published root.
    let pre_proof = registry.prove_non_revocation(cred.id());
    let pre_opts = VerificationOptions {
        revocation: Some(pre_proof),
        expected_revocation_root: Some(registry.root()),
        ..Default::default()
    };
    verify(&presentation, &pre_opts).expect("pre-revocation verification must succeed");

    // Revoke, then verify against the new root: must fail with Revoked.
    let post_proof = revoke(&registry, &cred);
    assert!(post_proof.revoked);
    let post_opts = VerificationOptions {
        revocation: Some(post_proof),
        expected_revocation_root: Some(registry.root()),
        ..Default::default()
    };
    let result = verify(&presentation, &post_opts);
    assert!(result.is_err(), "revoked credential must be rejected");
    match result.unwrap_err() {
        dregg_credentials::VerificationError::Revoked => {}
        other => panic!("expected Revoked, got {other:?}"),
    }
}

#[test]
fn revocation_witness_tamper_rejected() {
    // A holder cannot escape revocation by dropping their own id from the
    // witness set: the recomputed root then no longer matches the claimed
    // root (or the trusted expected root), so the proof is rejected rather
    // than silently treated as non-revoked.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();
    let registry = RevocationRegistry::new();

    let presentation = present(&cred, &fixture_request(), &PresentationOptions::new()).unwrap();

    // Revoke this credential and capture the published (trusted) root.
    let mut tampered = revoke(&registry, &cred);
    let trusted_root = registry.root();

    // Holder tampers: removes its own id from the witness to fake absence,
    // but leaves the (real, revoked) root claimed.
    tampered.revoked_set.retain(|id| id != &cred.id());
    tampered.revoked = false; // and flips the convenience flag

    let opts = VerificationOptions {
        revocation: Some(tampered),
        expected_revocation_root: Some(trusted_root),
        ..Default::default()
    };
    let result = verify(&presentation, &opts);
    assert!(
        result.is_err(),
        "a tampered non-revocation witness must be rejected (root no longer binds)"
    );
}
