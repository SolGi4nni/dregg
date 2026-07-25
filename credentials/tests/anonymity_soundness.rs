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
    verify_wire,
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

/// The verifier's expectations for the fixture issuer + request, sound-path ready.
///
/// Since 2026-07-26 `verify()` routes through the bridge STARK verifier
/// (`verify_proof_complete`), which REQUIRES an external trusted federation root
/// and binds the committed action/resource. This helper supplies the fixture
/// issuer's root (held out-of-band), the fixture request's action/resource
/// binding (`api:read` on `employee-portal`), and leaves freshness off
/// (`now = None`). A `VerificationOptions::default()` (no trusted root) now
/// fail-closes with `MissingTrustedFederationRoot`, so every positive control
/// extends this base.
fn base_verify_opts() -> VerificationOptions {
    VerificationOptions {
        expected_federation_root: Some(fixture_issuer().federation_root),
        expected_action: "api:read".into(),
        expected_resource: "employee-portal".into(),
        ..Default::default()
    }
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
    // Verify through the SOUND path: a trusted federation root + the request's
    // action/resource binding. (Pre-2026-07-26 this passed `VerificationOptions::new()`
    // and "verified" without running any STARK — the F1 hole.)
    verify(&p, &base_verify_opts())
        .expect("a real present() proof must verify through the bridge STARK verifier");
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
        ..base_verify_opts()
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
        ..base_verify_opts()
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
        ..base_verify_opts()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "a relabelled predicate proof must be rejected by cryptographic binding"
    );
}

// ── (b') CROSS-CREDENTIAL predicate FORGERY — the replay is CLOSED ────────────
//
// `relabelled_predicate_proof_rejected` above only bites on a THRESHOLD MISMATCH
// (a clearance `Gte(1)` proof relabelled onto an `age Gte(18)` request → the
// `predicate != expected.predicate` guard fires FIRST). It gives ZERO assurance
// against a SAME-THRESHOLD, DIFFERENT-CREDENTIAL attach, which this test exposes.
//
// THE HOLE THAT WAS (verification.rs, step (iii)): each predicate proof used to be
// verified with the BARE `verify_predicate_proof(&p.proof, p.proof.fact_commitment)`
// — against the proof's OWN commitment. That equality was `x == x`, vacuous. Nothing
// bound the commitment to THIS presentation's credential / `final_state_root`, so the
// STARK proved only "SOME fact with this commitment satisfies the predicate" for a
// commitment the prover supplied.
//
// THE FORGERY: a holder owns a legit credential X (age 32) and mints a GENUINE
// `Gte(18)` proof from it. They then present a DIFFERENT credential A (age 15,
// which FAILS `age >= 18`), attach X's genuine proof under `attribute = "age"`
// (same threshold). Under the old x==x gate `verify()` ACCEPTED it — a predicate
// forgery across credentials.
//
// THE FIX (now landed): the producer attaches a `BridgeFactAttestation` bound to the
// presentation's `final_state_root`, and `verify()` routes through
// `verify_predicate_proof_third_party(&p, facts_root, final_state_root)` with the
// TRUSTED `final_state_root`. X's stolen proof commits to X's state root, so its
// attestation fails closed under A's `final_state_root` and the forgery is REFUSED.
// (RESIDUAL: `facts_root` is not yet a presentation PI, so a fact fabricated under A's
// OWN state root but an invented `facts_root` is still open — see the note on the test.)
//
// FIXED (un-ignored) — the cross-credential REPLAY forgery is now a RED gate that
// PASSES (the forgery is refused). Two of the three ripple parts landed in Rust:
//   2. the producer (presentation.rs) attaches a
//      `dregg_bridge::present::BridgeFactAttestation` to each predicate proof via
//      `prove_predicate_for_fact_attested`, bound to this presentation's
//      `final_state_root`; and
//   3. `verify()` routes through
//      `dregg_bridge::present::verify_predicate_proof_third_party(&p.proof,
//      facts_root, final_state_root)` with the TRUSTED `final_state_root` (a genuine
//      presentation-STARK public input), never the vacuous `verify_predicate_proof(&p,
//      p.fact_commitment)` (x==x).
// This refuses THIS test's forgery because credential X's stolen proof commits to X's
// state root, not A's `final_state_root`, so its attestation fails closed under A's
// presentation.
//   1. (RESIDUAL AIR GAP — Lean, out of Rust scope): the presentation STARK still does
//      NOT expose `facts_root` as a proven public input over the token's REAL fact set,
//      so `verify()` reads `facts_root` off the attestation. The state-root binding above
//      closes the cross-credential REPLAY tested here; a WEAKER forgery — a fact fabricated
//      under A's OWN `final_state_root` but an INVENTED `facts_root` — remains open until
//      that PI lands. See the RESIDUAL AIR GAP note in verification.rs.
// The predicate proof also inherits the deployed STARK/FRI floor
// (project-fri-soundness-reality) — this gate means "no longer vacuous above the floor",
// NOT "sound".
#[test]
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
        ..base_verify_opts()
    };
    let result = verify(&a_pres, &verify_opts);
    // ⚠ READ THIS GREEN AT ITS ACTUAL RESOLUTION. The message here used to say "Today
    // verify() ACCEPTS (the forgery)" — that was true when written and is now STALE.
    // Since the 2026-07-24 fail-close (`credentials/src/verification.rs`, the
    // `expected_predicates` loop returns `PredicateProofInvalid` UNCONDITIONALLY), this
    // refusal is NOT a soundness verdict about the forgery: verify() refuses EVERY
    // presentation carrying an expected predicate, genuine or forged. Its paired positive
    // control `matching_predicate_proof_accepted` was inverted to `.is_err()` for the same
    // reason, so NO test in this file can currently distinguish a working predicate
    // verifier from a deleted one. That is a deliberate fail-closed posture, not coverage.
    //
    // This test becomes a real falsifier again — and only then — when the presentation
    // STARK exposes a trusted `facts_root` public input and the accept path is restored.
    // Restore BOTH polarities in the same commit, or the pair stays vacuous.
    assert!(
        result.is_err(),
        "a predicate proof minted from a DIFFERENT credential must not satisfy this \
         presentation's predicate — credential A (age 15) is not >= 18. NOTE: today this \
         passes via the blanket fail-close, not via a facts_root binding; see the comment above."
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
        ..base_verify_opts()
    };
    // FAIL-CLOSED (2026-07-24): even a GENUINE matching predicate proof is refused today — predicate
    // accept is fail-closed until the facts_root AIR binding lands (credentials/src/verification.rs;
    // its paired falsifier cross_credential_predicate_forgery_rejected shows the old accept was
    // vacuous). This positive control asserts the honest refusal for now; RESTORE it to
    // `.expect("...must verify")` when the presentation STARK exposes facts_root as a public input.
    assert!(
        verify(&presentation, &verify_opts).is_err(),
        "predicate accept is fail-closed pending the facts_root AIR binding (positive control disabled)"
    );
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
        ..base_verify_opts()
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
        ..base_verify_opts()
    };
    verify(&presentation, &pre_opts).expect("pre-revocation verification must succeed");

    // Revoke, then verify against the new root: must fail with Revoked.
    let post_proof = revoke(&registry, &cred);
    assert!(post_proof.revoked);
    let post_opts = VerificationOptions {
        revocation: Some(post_proof),
        expected_revocation_root: Some(registry.root()),
        ..base_verify_opts()
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
        ..base_verify_opts()
    };
    let result = verify(&presentation, &opts);
    assert!(
        result.is_err(),
        "a tampered non-revocation witness must be rejected (root no longer binds)"
    );
}

// ── (F1/F5) verify() ACTUALLY runs the STARK — the canonical forgery hole ─────
//
// Until 2026-07-26 `dregg_credentials::verify()` ran NO STARK verifier: it accepted
// on the prover-controlled `proof.verification == Valid` field plus `is_valid()`
// (which only checks `real_stark_proof.is_some()` — presence, not validity), and
// compared federation membership to the prover-supplied `proof.federation_root`
// pub field. A zero-secret forgery followed: mint your own IssuerKeys, issue
// yourself a credential, present it, set the pub fields to whatever the verifier
// expects → `verify()` returned `Ok`. The fix routes `verify()` through the SOUND
// bridge verifier `dregg_bridge::present::verify_proof_complete`, which runs the
// STARK, binds the federation root to the STARK public inputs (not a pub field),
// and binds the action + freshness. These tests are its adversarial gate.

/// POSITIVE CONTROL: a genuine presentation verifies through the sound path. The
/// falsifiers below are only meaningful if this passes — a verifier that refuses
/// everything is not a verifier.
#[test]
fn genuine_presentation_verifies_through_sound_path() {
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

    let verified = verify(&p, &base_verify_opts())
        .expect("a genuine presentation must verify through the bridge STARK verifier");
    assert_eq!(
        verified.federation_root, issuer.federation_root,
        "the verified root is the trusted anchor bound to the STARK PI, not a prover field"
    );
    assert_eq!(verified.disclosed.len(), 1);
    assert_eq!(verified.disclosed[0].0, "active");
}

/// FALSIFIER: keep the EXACT shape the old hole accepted on — `verification == Valid`
/// and `real_stark_proof.is_some()` — but CORRUPT the STARK bytes. The old no-op
/// verify() returned Ok on this; a verifier that actually runs the STARK REFUSES it.
#[test]
fn forged_garbage_stark_proof_refused() {
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
    let mut forged = present(&cred, &fixture_request(), &opts).unwrap();

    // Precondition: the presentation is in the exact shape the OLD verify() accepted
    // on — a real STARK object present and `verification == Valid`.
    assert!(forged.proof.real_stark_proof.is_some());
    assert!(
        forged.proof.is_valid(),
        "precondition: verification field is Valid + a STARK object is present"
    );

    // Inject garbage into the committed STARK blob. Its bytes no longer decode/verify
    // as a valid `Ir2BatchProof`, so `verify_wire_typed` fails closed (StarkInvalid).
    {
        let real = forged
            .proof
            .real_stark_proof
            .as_mut()
            .expect("real STARK present");
        let blob = &mut real.blinded_membership.blob;
        assert!(blob.len() > 32, "STARK blob must be non-trivial to corrupt");
        let start = blob.len() / 2;
        for b in &mut blob[start..start + 16] {
            *b ^= 0xff;
        }
    }

    let result = verify(&forged, &base_verify_opts());
    assert!(
        result.is_err(),
        "a presentation carrying a CORRUPTED STARK must be REFUSED — the STARK is verified \
         now, not trusted on the `verification` field. Got {result:?}"
    );
}

/// FALSIFIER (F1 + F2): a GENUINE proof, but bound to the issuer's real federation
/// root while the verifier trusts a DIFFERENT root. The attacker spoofs the
/// (now-ignored) `proof.federation_root` pub field to the verifier's value — the
/// exact pre-2026-07-26 attack, where verify() compared `expected == proof.federation_root`
/// and accepted. The root now lives in the STARK public inputs, so the spoof is inert.
#[test]
fn spoofed_federation_root_field_refused() {
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
    let mut forged = present(&cred, &fixture_request(), &opts).unwrap();

    // The federation root the verifier actually trusts — NOT the issuer's real root.
    let verifier_trusted_root = [0x99u8; 32];
    assert_ne!(verifier_trusted_root, issuer.federation_root);

    // The attacker spoofs the pub wire field to match the verifier's expectation.
    forged.proof.federation_root = verifier_trusted_root;

    let verify_opts = VerificationOptions {
        expected_federation_root: Some(verifier_trusted_root),
        expected_action: "api:read".into(),
        expected_resource: "employee-portal".into(),
        ..Default::default()
    };
    let result = verify(&forged, &verify_opts);
    assert!(
        result.is_err(),
        "a proof bound (in the STARK) to the issuer's real root must NOT verify against a \
         different trusted root, even with the pub `federation_root` field spoofed. Got {result:?}"
    );
}

/// FALSIFIER (F1 structural + action binding): the sound path works on a REMOTE
/// holder's WIRE presentation, not only a locally-constructed one. A wire proof
/// bound to `api:read` must not verify against `api:write` (the STARK's committed
/// action is checked).
#[test]
fn wire_presentation_verifies_and_wrong_action_refused() {
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

    // The wire form (trace stripped) is the shape a verifier receives from a remote
    // holder; it carries no `AuthorizationTrace` and no `federation_root` field.
    let wire = p.to_wire();

    verify_wire(&wire, &base_verify_opts())
        .expect("a remote holder's wire proof must verify through verify_wire");

    let mut wrong = base_verify_opts();
    wrong.expected_action = "api:write".into();
    assert!(
        verify_wire(&wire, &wrong).is_err(),
        "a wire proof bound to `api:read` must not verify against `api:write` (action binding)"
    );
}

/// FALSIFIER (F7): the sound path enforces freshness. A proof stamped at T verified
/// a day later with a 60s window is REFUSED; disabling freshness (or a wide window)
/// accepts it.
#[test]
fn stale_presentation_refused_by_freshness() {
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
    // The fixture request stamps the proof at now = 1_700_000_000.
    let p = present(&cred, &fixture_request(), &opts).unwrap();

    // Within the window: verifies.
    let mut fresh = base_verify_opts();
    fresh.now = Some(1_700_000_000);
    fresh.max_age_secs = 300;
    verify(&p, &fresh).expect("a proof inside the freshness window must verify");

    // A day later with a 60s window: refused (Expired).
    let mut stale = base_verify_opts();
    stale.now = Some(1_700_000_000 + 86_400);
    stale.max_age_secs = 60;
    assert!(
        verify(&p, &stale).is_err(),
        "a proof older than max_age_secs must be refused (freshness / replay window)"
    );
}

/// FAIL-CLOSED: with no trusted federation root, `verify()` refuses — there is no
/// sound verification without a trust anchor (the old code trusted the proof's own
/// claimed root, which was the hole).
#[test]
fn missing_trusted_root_fails_closed() {
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

    // Default options carry no `expected_federation_root`.
    let result = verify(&p, &VerificationOptions::new());
    assert!(
        matches!(
            result,
            Err(dregg_credentials::VerificationError::MissingTrustedFederationRoot)
        ),
        "verify() with no trusted root must fail closed, got {result:?}"
    );
}
