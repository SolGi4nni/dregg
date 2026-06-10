//! The headline property: an agent CANNOT exceed its grant.
//!
//! These tests are the product's claim made executable. Every one of them is a
//! way an over-reaching agent gets stopped — offline, with only a public key.

use dregg_auth::mcp::{OfflineGate, ToolCall, ToolGate};
use dregg_auth::{Grant, Rate, Request, Root, Token, verify_offline};

const T0: i64 = 1_800_000_000; // a fixed "now" for deterministic time checks
const FRIDAY: i64 = 1_800_604_800; // T0 + 7 days

fn root_and_grant() -> (Root, Token) {
    let root = Root::generate();
    let grant = Grant::new("ci-bot")
        .tools(["read", "pr-create"])
        .until(FRIDAY);
    let token = root.issue(&grant).unwrap();
    (root, token)
}

#[test]
fn grant_allows_its_own_tools() {
    let (root, token) = root_and_grant();
    let pk = root.public_key_hex();
    let encoded = token.encode().unwrap();

    for tool in ["read", "pr-create"] {
        let d = verify_offline(&encoded, &pk, &Request::tool(tool).at(T0));
        assert!(d.allowed(), "tool `{tool}` should be allowed: {}", d.reason());
    }
}

#[test]
fn grant_denies_tools_outside_it() {
    // THE headline test: a tool that was never granted is refused.
    let (root, token) = root_and_grant();
    let pk = root.public_key_hex();
    let encoded = token.encode().unwrap();

    for tool in ["delete-repo", "force-push", "merge", "admin"] {
        let d = verify_offline(&encoded, &pk, &Request::tool(tool).at(T0));
        assert!(
            !d.allowed(),
            "tool `{tool}` is NOT in the grant and must be denied"
        );
        assert!(d.reason().contains("denied"), "reason: {}", d.reason());
    }
}

#[test]
fn attenuated_grant_cannot_regain_dropped_tools() {
    // No-amplify, structurally: narrow to `read`, then `pr-create` is gone for good.
    let (root, token) = root_and_grant();
    let pk = root.public_key_hex();

    let narrowed = token.attenuate(&Grant::new("_").tool("read")).unwrap();
    let encoded = narrowed.encode().unwrap();

    // read still works
    assert!(
        verify_offline(&encoded, &pk, &Request::tool("read").at(T0)).allowed(),
        "read must survive the narrowing"
    );
    // pr-create was dropped and CANNOT be recovered
    let d = verify_offline(&encoded, &pk, &Request::tool("pr-create").at(T0));
    assert!(
        !d.allowed(),
        "pr-create was attenuated away and must not be re-grantable: {}",
        d.reason()
    );

    // ...even attempting to "attenuate back up" to pr-create cannot widen it.
    let attempt = narrowed
        .attenuate(&Grant::new("_").tools(["read", "pr-create"]))
        .unwrap();
    let attempt_enc = attempt.encode().unwrap();
    assert!(
        !verify_offline(&attempt_enc, &pk, &Request::tool("pr-create").at(T0)).allowed(),
        "attenuation can never amplify — pr-create stays gone"
    );
}

#[test]
fn expired_grant_denies_everything() {
    let (root, token) = root_and_grant();
    let pk = root.public_key_hex();
    let encoded = token.encode().unwrap();

    // Before expiry: allowed.
    assert!(verify_offline(&encoded, &pk, &Request::tool("read").at(T0)).allowed());

    // After expiry (FRIDAY + 1s): denied, even for a granted tool.
    let after = FRIDAY + 1;
    let d = verify_offline(&encoded, &pk, &Request::tool("read").at(after));
    assert!(
        !d.allowed(),
        "an expired grant must deny even its own tools: {}",
        d.reason()
    );
}

#[test]
fn offline_verification_needs_only_the_public_key() {
    // Issue with the private root; verify with ONLY the hex public key string.
    // Nothing else — no Root, no network, no node — is in scope here.
    let root = Root::generate();
    let pubkey_hex: String = root.public_key_hex();
    let encoded: String = root
        .issue(&Grant::new("agent").tool("read").until(FRIDAY))
        .unwrap()
        .encode()
        .unwrap();
    drop(root); // the issuer is GONE; only (encoded, pubkey_hex) strings remain.

    let d = verify_offline(&encoded, &pubkey_hex, &Request::tool("read").at(T0));
    assert!(d.allowed(), "public-key-only verify must succeed: {}", d.reason());

    let d2 = verify_offline(&encoded, &pubkey_hex, &Request::tool("write").at(T0));
    assert!(!d2.allowed(), "and still deny out-of-grant tools");
}

#[test]
fn wrong_public_key_is_rejected() {
    let issuer = Root::generate();
    let impostor = Root::generate();
    let encoded = issuer
        .issue(&Grant::new("a").tool("read").until(FRIDAY))
        .unwrap()
        .encode()
        .unwrap();

    // Verifying under a DIFFERENT root key must fail the signature chain.
    let d = verify_offline(&encoded, &impostor.public_key_hex(), &Request::tool("read").at(T0));
    assert!(!d.allowed(), "a token must not verify under the wrong root key");
}

#[test]
fn unscoped_grant_is_refused_at_issue() {
    // The whole point: you cannot mint an unscoped agent token by accident.
    let root = Root::generate();
    let err = root.issue(&Grant::new("agent")); // no tools
    assert!(err.is_err(), "an unscoped grant must be refused");
}

#[test]
fn rate_is_carried_as_metadata() {
    // L1 is stateless; the rate rides along advisorily and does not block the
    // structural decision (which is over tools + time).
    let root = Root::generate();
    let g = Grant::new("bot")
        .tool("read")
        .until(FRIDAY)
        .rate(Rate::parse("30/h").unwrap());
    let token = root.issue(&g).unwrap();
    let d = verify_offline(
        &token.encode().unwrap(),
        &root.public_key_hex(),
        &Request::tool("read").at(T0),
    );
    assert!(d.allowed(), "rate is advisory at L1: {}", d.reason());
}

#[test]
fn mcp_gate_admits_and_denies_with_receipts() {
    let root = Root::generate();
    let encoded = root
        .issue(&Grant::new("ci-bot").tools(["read", "pr-create"]).until(FRIDAY))
        .unwrap()
        .encode()
        .unwrap();

    let gate = OfflineGate::new(root.public_key_hex());

    // Admitted call → receipt says ALLOW and recovers the subject.
    let ok = gate.admit(
        &encoded,
        &ToolCall::new("pr-create").arg("repo", "acme/widgets").at(T0),
    );
    assert!(ok.admitted(), "granted tool should be admitted: {}", ok.receipt.reason);
    assert!(ok.receipt.line().contains("ALLOW"));
    assert_eq!(ok.receipt.subject.as_deref(), Some("ci-bot"));
    assert!(ok.receipt.args.iter().any(|a| a.contains("repo=acme/widgets")));

    // Denied call → receipt says DENY, still auditable.
    let bad = gate.admit(&encoded, &ToolCall::new("delete-repo").at(T0));
    assert!(!bad.admitted());
    assert!(bad.receipt.line().contains("DENY"));

    // The receipt serializes to a JSON audit line (the L2 seed).
    assert!(ok.receipt.json().contains("\"allowed\":true"));
}
