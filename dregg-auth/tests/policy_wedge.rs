//! The adoption wedge, on the proven core: the `policy` surface is the
//! productized `grant <agent> --tools … --until …` shape, the verifying
//! middleware, and the offline verify path — every decision routed through the
//! machine-checked credential core (not the Datalog biscuit surface).
//!
//! Every test here is the product's claim ("prove your agent cannot exceed the
//! grant") made executable on the path a stranger actually touches.

use dregg_auth::policy::{Call, Grant, Policy, PolicyError, Verifier};

const T0: u64 = 1_800_000_000; // a fixed "now" for deterministic time checks
const FRIDAY: u64 = 1_800_604_800; // T0 + 7 days

fn polis_and_token() -> (Policy, String) {
    let polis = Policy::generate();
    let token = polis
        .issue(
            Grant::to("ci-bot")
                .tools(["read", "pr-create"])
                .until(FRIDAY),
        )
        .unwrap()
        .encode();
    (polis, token)
}

#[test]
fn grant_allows_its_own_tools() {
    let (polis, token) = polis_and_token();
    let gate = Verifier::new(polis.public_key_hex());
    for tool in ["read", "pr-create"] {
        let v = gate.admit(&token, &Call::tool(tool).at(T0));
        assert!(
            v.admitted(),
            "tool `{tool}` should be allowed: {}",
            v.reason()
        );
        // The subject is recovered FROM THE TOKEN (a checked fact), not the call.
        assert_eq!(v.receipt.subject.as_deref(), Some("ci-bot"));
    }
}

#[test]
fn grant_denies_tools_outside_it() {
    // THE headline test: a tool that was never granted is refused, with terms.
    let (polis, token) = polis_and_token();
    let gate = Verifier::new(polis.public_key_hex());
    for tool in ["delete-repo", "force-push", "merge", "admin"] {
        let v = gate.admit(&token, &Call::tool(tool).at(T0));
        assert!(
            !v.admitted(),
            "tool `{tool}` is NOT in the grant and must be denied"
        );
        // The proven Refusal names which requirement failed.
        assert!(
            v.reason().contains("refused") || v.reason().contains("denied"),
            "{}",
            v.reason()
        );
    }
}

#[test]
fn attenuated_grant_cannot_regain_dropped_tools() {
    // No-amplify, on the proven core: narrow to `read`, then `pr-create` is gone.
    let (polis, _) = polis_and_token();
    let issued = polis
        .issue(
            Grant::to("ci-bot")
                .tools(["read", "pr-create"])
                .until(FRIDAY),
        )
        .unwrap();
    let narrowed = Grant::attenuate_token(issued, Some(&["read".to_string()]), None).unwrap();
    let token = narrowed.encode();
    let gate = Verifier::new(polis.public_key_hex());

    assert!(
        gate.admit(&token, &Call::tool("read").at(T0)).admitted(),
        "read must survive the narrowing"
    );
    assert!(
        !gate
            .admit(&token, &Call::tool("pr-create").at(T0))
            .admitted(),
        "pr-create was attenuated away and must not be re-grantable"
    );

    // ...and re-attenuating "back up" to include pr-create cannot widen it: the
    // older `AnyOf([read])` block still gates (the proven meet keeps the
    // narrowest binding), so pr-create stays refused for good.
    let issued = polis
        .issue(
            Grant::to("ci-bot")
                .tools(["read", "pr-create"])
                .until(FRIDAY),
        )
        .unwrap();
    let narrowed2 = Grant::attenuate_token(issued, Some(&["read".to_string()]), None).unwrap();
    let widened = Grant::attenuate_token(
        narrowed2,
        Some(&["read".to_string(), "pr-create".to_string()]),
        None,
    )
    .unwrap();
    let widened_token = widened.encode();
    assert!(
        !gate
            .admit(&widened_token, &Call::tool("pr-create").at(T0))
            .admitted(),
        "attenuation can never amplify — pr-create stays gone"
    );
}

#[test]
fn expired_grant_denies_everything() {
    let (polis, token) = polis_and_token();
    let gate = Verifier::new(polis.public_key_hex());
    // Before expiry: allowed.
    assert!(gate.admit(&token, &Call::tool("read").at(T0)).admitted());
    // After expiry: denied, even for a granted tool.
    let v = gate.admit(&token, &Call::tool("read").at(FRIDAY + 1));
    assert!(
        !v.admitted(),
        "an expired grant must deny even its own tools: {}",
        v.reason()
    );
}

#[test]
fn missing_clock_refuses_an_expiring_grant_fail_closed() {
    // A call with NO clock cannot satisfy the expiry caveat — fail-closed (the
    // proven `Unbound::Clock` discipline), never silently allowed.
    let (polis, token) = polis_and_token();
    let gate = Verifier::new(polis.public_key_hex());
    let v = gate.admit(&token, &Call::tool("read")); // no .at(..)
    assert!(
        !v.admitted(),
        "an expiring grant with no clock must refuse: {}",
        v.reason()
    );
}

#[test]
fn offline_verification_needs_only_the_public_key() {
    // Issue with the private authority; verify with ONLY the hex public key.
    let polis = Policy::generate();
    let pubkey_hex = polis.public_key_hex();
    let token = polis
        .issue(Grant::to("agent").tool("read").until(FRIDAY))
        .unwrap()
        .encode();
    drop(polis); // the issuer is GONE; only (token, pubkey_hex) strings remain.

    let gate = Verifier::new(pubkey_hex);
    assert!(
        gate.admit(&token, &Call::tool("read").at(T0)).admitted(),
        "public-key-only verify must succeed"
    );
    assert!(
        !gate.admit(&token, &Call::tool("write").at(T0)).admitted(),
        "and still deny out-of-grant tools"
    );
}

#[test]
fn wrong_public_key_is_rejected() {
    let issuer = Policy::generate();
    let impostor = Policy::generate();
    let token = issuer
        .issue(Grant::to("a").tool("read").until(FRIDAY))
        .unwrap()
        .encode();
    // Verifying under a DIFFERENT root key must fail the signature chain.
    let gate = Verifier::new(impostor.public_key_hex());
    let v = gate.admit(&token, &Call::tool("read").at(T0));
    assert!(
        !v.admitted(),
        "a token must not verify under the wrong root key"
    );
}

#[test]
fn wrong_subject_is_refused() {
    // The subject is SIGNATURE-BOUND, not merely an advisory annotation. At
    // `admit` the subject gate is self-referential (the Verifier binds the
    // subject FROM the token, then the `subject == …` caveat checks it against
    // that same recovered value — so on its own the caveat cannot fail). The real
    // integrity of the agent identity is therefore the SIGNATURE over the caveat
    // chain: a forger who rewrites the subject to a different agent breaks the
    // binding and the credential no longer verifies. This test forges exactly
    // that — a token issued to `ci-bot` re-stamped to `cx-bot` — and proves it is
    // REFUSED (not silently admitted under the forged identity).
    use base64::Engine;
    use base64::engine::general_purpose::URL_SAFE_NO_PAD;

    let polis = Policy::generate();
    let token = polis
        .issue(Grant::to("ci-bot").tool("read").until(FRIDAY))
        .unwrap()
        .encode();
    let gate = Verifier::new(polis.public_key_hex());

    // Non-vacuity: the honest token admits and its subject is recovered from the
    // signed chain (the checked fact, held).
    assert!(gate.admit(&token, &Call::tool("read").at(T0)).admitted());
    let (_, subject) = gate.parse(&token).unwrap();
    assert_eq!(subject.as_deref(), Some("ci-bot"));

    // FORGE a different agent identity: rewrite the `subject` bytes inside the
    // signed postcard payload (same length, so the framing stays valid) from
    // "ci-bot" to "cx-bot".
    let payload_b64 = token.strip_prefix("dga1_").expect("credential wire prefix");
    let mut bytes = URL_SAFE_NO_PAD
        .decode(payload_b64)
        .expect("token payload is base64url");
    let needle = b"ci-bot";
    let replacement = b"cx-bot";
    let pos = bytes
        .windows(needle.len())
        .position(|w| w == needle)
        .expect("the subject bytes appear in the signed payload");
    bytes[pos..pos + needle.len()].copy_from_slice(replacement);
    let forged = format!("dga1_{}", URL_SAFE_NO_PAD.encode(&bytes));

    // The forged token still PARSES and now carries a DIFFERENT subject — proving
    // the subject caveat is not ignored: a forger who swaps the identity really
    // does get `cx-bot` recovered out of the chain.
    let (_, forged_subject) = gate
        .parse(&forged)
        .expect("the tampered token still parses structurally (same-length swap)");
    assert_eq!(
        forged_subject.as_deref(),
        Some("cx-bot"),
        "the forge installed a different subject caveat"
    );

    // ...but admission is REFUSED: rewriting the subject broke the credential
    // chain's signature binding, so `Credential::verify` fails. The agent
    // identity cannot be swapped without invalidating the token.
    let v = gate.admit(&forged, &Call::tool("read").at(T0));
    assert!(
        !v.admitted(),
        "a token presented under a forged subject must be refused (signature-bound): {}",
        v.reason()
    );
}

#[test]
fn unscoped_grant_is_refused_at_issue() {
    // The whole point: you cannot mint an unscoped agent token by accident.
    let polis = Policy::generate();
    let err = polis.issue(Grant::to("agent")); // no tools
    assert!(
        matches!(err, Err(PolicyError::Unscoped)),
        "an unscoped grant must be refused"
    );
}

#[test]
fn empty_narrowing_is_refused() {
    // Attenuation must narrow at least one dimension.
    let polis = Policy::generate();
    let issued = polis
        .issue(Grant::to("agent").tool("read").until(FRIDAY))
        .unwrap();
    let err = Grant::attenuate_token(issued, None, None);
    assert!(matches!(err, Err(PolicyError::EmptyNarrowing)));
}

#[test]
fn attenuating_tightens_expiry() {
    // Narrow the expiry from FRIDAY to T0+1h; after the tighter deadline it
    // refuses even though the ORIGINAL grant would still be valid.
    let polis = Policy::generate();
    let issued = polis
        .issue(Grant::to("agent").tool("read").until(FRIDAY))
        .unwrap();
    let tighter = T0 + 3600;
    let narrowed = Grant::attenuate_token(issued, None, Some(tighter)).unwrap();
    let token = narrowed.encode();
    let gate = Verifier::new(polis.public_key_hex());
    assert!(gate.admit(&token, &Call::tool("read").at(T0)).admitted());
    let v = gate.admit(&token, &Call::tool("read").at(tighter + 1));
    assert!(
        !v.admitted(),
        "past the tightened expiry must refuse: {}",
        v.reason()
    );
    // ...but BEFORE the original FRIDAY, proving the new gate is the binding one.
    assert!(tighter + 1 < FRIDAY);
}

#[test]
fn middleware_emits_auditable_receipts() {
    let polis = Policy::generate();
    let token = polis
        .issue(
            Grant::to("ci-bot")
                .tools(["read", "pr-create"])
                .until(FRIDAY),
        )
        .unwrap()
        .encode();
    let gate = Verifier::new(polis.public_key_hex());

    // Admitted call → ALLOW receipt, recovers subject, carries args.
    let ok = gate.admit(
        &token,
        &Call::tool("pr-create").arg("repo", "acme/widgets").at(T0),
    );
    assert!(
        ok.admitted(),
        "granted tool should be admitted: {}",
        ok.reason()
    );
    assert!(ok.receipt.line().contains("ALLOW"));
    assert_eq!(ok.receipt.subject.as_deref(), Some("ci-bot"));
    assert!(ok.receipt.args.iter().any(|a| a == "repo=acme/widgets"));
    assert!(ok.receipt.json().contains("\"allowed\":true"));

    // Denied call → DENY receipt, still auditable.
    let bad = gate.admit(&token, &Call::tool("delete-repo").at(T0));
    assert!(!bad.admitted());
    assert!(bad.receipt.line().contains("DENY"));
    assert!(bad.receipt.json().contains("\"allowed\":false"));
}

#[test]
fn malformed_token_denies_with_a_reason_not_a_panic() {
    let polis = Policy::generate();
    let gate = Verifier::new(polis.public_key_hex());
    for bad in ["", "garbage", "dga9_AAAA", "eb2_AAAA"] {
        let v = gate.admit(bad, &Call::tool("read").at(T0));
        assert!(!v.admitted(), "malformed token `{bad}` must deny");
        assert!(v.reason().contains("denied"), "reason: {}", v.reason());
    }
}

#[test]
fn secret_hex_roundtrips_the_authority() {
    // Persist the authority by its secret hex and reconstruct it — the same
    // public key, the same tokens verify (the golden-vector discipline).
    let polis = Policy::generate();
    let secret = polis.secret_hex();
    let token = polis
        .issue(Grant::to("agent").tool("read").until(FRIDAY))
        .unwrap()
        .encode();

    let reloaded = Policy::from_secret_hex(&secret).unwrap();
    assert_eq!(reloaded.public_key_hex(), polis.public_key_hex());
    let gate = Verifier::new(reloaded.public_key_hex());
    assert!(gate.admit(&token, &Call::tool("read").at(T0)).admitted());
}

#[test]
fn explain_names_the_subject_and_terms() {
    let polis = Policy::generate();
    let token = polis
        .issue(
            Grant::to("ci-bot")
                .tools(["read", "pr-create"])
                .until(FRIDAY),
        )
        .unwrap();
    let explained = token.explain();
    assert!(explained.contains("grant to `ci-bot`"), "{explained}");
    assert!(explained.contains("subject"), "{explained}");
    assert!(explained.contains("read"), "{explained}");
    assert!(explained.contains("expiry gate"), "{explained}");
}
