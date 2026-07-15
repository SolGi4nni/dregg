//! `webauth-core` — dregg-cap forward-auth **decision core** for the web edge,
//! ported dregg-native from the prior operated layer (everything except its HTTP
//! server).
//!
//! A gated web surface requires one named **capability** string; a user holds an
//! attenuable, offline-verifiable `dga1_` credential; a reverse proxy's
//! `forward_auth` (or any native serving edge) calls [`decide`] once per request
//! and maps the [`Verdict`] to `200`/`401`/`403`. No password anywhere.
//!
//! ## The pieces
//! - [`credext`] — the forward-auth reads over the real `dregg_agent::cred`
//!   core (chain-only verify, expiry probe, bearer-key proof-of-possession).
//! - [`account_id`] — the stable key-derived account identity (the id IS the
//!   substrate identity-cell id).
//! - [`grant`] — the web-surface capability vocabulary (cap sets, re-anchored
//!   session mint, the `vat:<cell-id>` per-computer grammar).
//! - [`config::WebAuthConfig`] — runtime config (root pubkey, host→cap map,
//!   revocation deny-set, break-glass override).
//! - [`challenge`] — the stateless, replica-safe login challenge (keyed-BLAKE3
//!   self-authenticating nonce).
//! - [`decide`] — the per-request authorization decision.
//! - [`server`] — the pure-`std` forward-auth HTTP server that turns a reverse
//!   proxy's `forward_auth` subrequest into a `200`/`401`/`403` over [`decide`],
//!   plus the `/login` proof-of-possession flow and a `/whoami` session probe.
//!   The serving binary is `src/bin/webauth-edge.rs`.

pub mod account_id;
pub mod challenge;
pub mod config;
pub mod credext;
pub mod grant;
pub mod server;

use config::WebAuthConfig;
use credext::CredentialExt;
use dregg_agent::cred::{Credential, PublicKey};

/// The outcome of a forward-auth decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// Admit. Carries the identity headers to echo back to the proxy (so the
    /// upstream surface sees who authenticated).
    Admit {
        /// How the request was admitted (for the `X-Dregg-Auth` header / logs).
        how: String,
        /// The cap that was satisfied, if a credential decision (not break-glass).
        cap: Option<String>,
    },
    /// Refuse with a human-readable reason (named requirement).
    ///
    /// `authenticated` splits the two refusal classes the forward-auth edge maps
    /// to distinct statuses:
    ///  * `false` — no genuine session (missing / malformed / forged-signature /
    ///    revoked / expired credential): the presenter is UNAUTHENTICATED → `401`
    ///    (a browser is bounced to the login page).
    ///  * `true` — a genuine, non-revoked, non-expired session was presented but
    ///    it lacks the *capability* this surface requires: the presenter is
    ///    AUTHENTICATED but not authorized → `403` (re-login will not help; they
    ///    need a wider capability).
    Deny { reason: String, authenticated: bool },
}

impl Verdict {
    pub fn admitted(&self) -> bool {
        matches!(self, Verdict::Admit { .. })
    }
    /// The HTTP status this verdict maps to at the forward-auth edge: `200`
    /// admit, `403` authenticated-but-uncapped, `401` otherwise.
    pub fn status(&self) -> u16 {
        match self {
            Verdict::Admit { .. } => 200,
            Verdict::Deny {
                authenticated: true,
                ..
            } => 403,
            Verdict::Deny { .. } => 401,
        }
    }
}

/// A denial from an UNAUTHENTICATED presenter (→ 401).
fn deny(reason: impl Into<String>) -> Verdict {
    Verdict::Deny {
        reason: reason.into(),
        authenticated: false,
    }
}

/// The inputs a forward-auth decision needs, extracted from the HTTP request by
/// the serving edge (or by a test).
#[derive(Clone, Debug, Default)]
pub struct AuthInput {
    /// The presented credential (`dga1_…`), from the session cookie or a
    /// `Authorization: Bearer`/`X-Dregg-Credential` header. `None` = none presented.
    pub credential: Option<String>,
    /// The value of the break-glass header/cookie, if any.
    pub break_glass: Option<String>,
    /// The capability required for this surface (already resolved from the
    /// query or the host map).
    pub required_cap: Option<String>,
    /// The verifier's clock (unix seconds). Supplied for deterministic checks;
    /// the server fills wall-clock.
    pub now: u64,
}

/// The core authorization decision — pure, offline, deterministic.
///
/// Order: break-glass override first (so a broken cap flow never locks the
/// operator out), then the credential cap-verify.
pub fn decide(cfg: &WebAuthConfig, input: &AuthInput) -> Verdict {
    // 1. Break-glass override — constant set in config, matched in constant-ish
    //    time. Only active when configured.
    if let (Some(expected), Some(presented)) = (&cfg.break_glass, &input.break_glass) {
        if constant_time_eq(expected.as_bytes(), presented.as_bytes()) {
            return Verdict::Admit {
                how: "break-glass override".to_string(),
                cap: None,
            };
        }
    }

    // 2. The required capability must be known; an unmapped surface fails closed.
    let Some(cap) = &input.required_cap else {
        return deny(
            "no required capability resolved for this surface (host not mapped, no ?cap=)",
        );
    };

    // 3. A root public key must be configured to verify under.
    let Some(pk_hex) = &cfg.root_pubkey_hex else {
        return deny(
            "auth service has no root public key configured (set DREGG_WEBAUTH_ROOT_PUBKEY)",
        );
    };
    let root = match PublicKey::from_hex(pk_hex) {
        Ok(pk) => pk,
        Err(e) => return deny(format!("misconfigured root key: {e}")),
    };

    // 4. A credential must be presented.
    let Some(enc) = &input.credential else {
        return deny(format!("no dregg credential presented for cap `{cap}`"));
    };

    // 5. Decode.
    let credential = match Credential::decode(enc) {
        Ok(c) => c,
        Err(e) => return deny(format!("credential did not decode: {e}")),
    };

    // 5a. Revocation deny-set (Tier 0 compromise response). A revoked credential
    //     is refused even though its signature + caps would otherwise admit it:
    //     a leaked token can be proactively killed (by tail) and a compromised
    //     account can be killed wholesale (by subject) without waiting for the
    //     expiry caveat. Revoked = UNAUTHENTICATED (401): the session is dead,
    //     present a live one.
    let tail_hex = credential.tail_hex();
    let subject = subject_of_credential(&credential);
    if cfg.is_revoked(&tail_hex, subject.as_deref()) {
        return deny(format!("credential is revoked (deny-set) for cap `{cap}`"));
    }

    // 5b. The signature chain + proof-of-possession must be genuine under the
    //     issuer root. A forged/tampered/bad-signature credential is
    //     UNAUTHENTICATED (401) — never a 403.
    if let Err(refusal) = credential.verify_chain(&root) {
        return deny(format!(
            "credential is not genuine under the issuer root: {refusal}"
        ));
    }

    // 5c. An expired-but-genuine session is UNAUTHENTICATED (401): the presenter
    //     had a real session, it lapsed — re-login. Distinct from lacking the
    //     cap (403), which re-login cannot fix.
    if credential.is_expired(input.now) {
        return deny(format!(
            "session credential has expired for cap `{cap}` — re-login"
        ));
    }

    // 6. The per-surface capability meet. The `acct` claim is an issuer-vouched
    //    annotation (signed by the root chain, so untamperable), not an access
    //    gate: bind it from the credential's own claim so its caveat is
    //    self-consistent and `verify` decides on the CAP, not the subject label.
    let mut ctx = grant::cap_context(cap, input.now);
    if let Some(acct) = credential.first_attr(account_id::ACCT_CAVEAT_KEY) {
        ctx = ctx.attr(account_id::ACCT_CAVEAT_KEY, acct);
    }
    match credential.verify(&root, &ctx) {
        Ok(()) => Verdict::Admit {
            how: "dregg credential".to_string(),
            cap: Some(cap.clone()),
        },
        // The chain already verified, the session is live and not revoked — so a
        // refusal here is exactly "genuine session, but it lacks capability
        // `cap`": AUTHENTICATED but not authorized → 403.
        Err(refusal) => Verdict::Deny {
            reason: format!("session lacks capability `{cap}`: {refusal}"),
            authenticated: true,
        },
    }
}

/// A subject label recoverable from an admitted credential, for the identity
/// header echoed to the upstream surface — and the key every consumer scopes a
/// resource to.
///
/// ## The re-anchor (Tier 1)
///
/// A re-anchored session credential carries an explicit, **stable, key-derived
/// account id** in an `acct` first-party caveat
/// ([`account_id::ACCT_CAVEAT_KEY`]). When present, the subject IS that account
/// id (`dregg:<account-id-hex>`) — so re-minting the session (a key rotation,
/// a recovery, a fresh login) yields the SAME subject, and the account's
/// resources survive. The account id is the substrate **identity-cell id**
/// (`dregg_types::CellId::derive_raw` over the *inception* key), so an account
/// and its rotatable substrate identity cell are the same principal.
///
/// ## Backward compatibility
///
/// A legacy credential (no `acct` caveat) falls back to the original
/// tail-commitment subject (`dregg:<hex(tail)[..16]>`), so already-issued
/// credentials keep working unchanged until they are re-issued.
pub fn subject_of(enc: &str) -> Option<String> {
    let cred = Credential::decode(enc).ok()?;
    subject_of_credential(&cred)
}

/// [`subject_of`] over an already-decoded credential (the hot path in
/// [`decide`], which has the credential in hand).
pub fn subject_of_credential(cred: &Credential) -> Option<String> {
    if let Some(acct) = cred.first_attr(account_id::ACCT_CAVEAT_KEY) {
        return Some(format!("dregg:{acct}"));
    }
    Some(format!("dregg:{}", &cred.tail_hex()[..16]))
}

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grant::{attenuate_caps, mint_caps, mint_session, mint_session_for};
    use dregg_agent::cred::RootKey;

    fn cfg_for(root: &RootKey) -> WebAuthConfig {
        WebAuthConfig {
            root_pubkey_hex: Some(root.public().to_hex()),
            break_glass: Some("rescue-me-123".to_string()),
            ..WebAuthConfig::default()
        }
    }

    #[test]
    fn valid_cap_admits() {
        let root = RootKey::from_seed([11u8; 32]);
        let cfg = cfg_for(&root);
        let token = mint_caps(&root, ["ops-admin"], None).encode();
        let v = decide(
            &cfg,
            &AuthInput {
                credential: Some(token),
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(v.admitted(), "{v:?}");
    }

    #[test]
    fn missing_credential_denied() {
        let root = RootKey::from_seed([12u8; 32]);
        let cfg = cfg_for(&root);
        let v = decide(
            &cfg,
            &AuthInput {
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(!v.admitted());
    }

    #[test]
    fn garbage_credential_denied() {
        let root = RootKey::from_seed([13u8; 32]);
        let cfg = cfg_for(&root);
        let v = decide(
            &cfg,
            &AuthInput {
                credential: Some("dga1_not-a-real-token".to_string()),
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(!v.admitted());
    }

    #[test]
    fn wrong_root_denied() {
        let root = RootKey::from_seed([14u8; 32]);
        let attacker = RootKey::from_seed([99u8; 32]);
        // Token minted by an attacker root, but the service trusts `root`.
        let token = mint_caps(&attacker, ["ops-admin"], None).encode();
        let cfg = cfg_for(&root);
        let v = decide(
            &cfg,
            &AuthInput {
                credential: Some(token),
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(!v.admitted());
    }

    #[test]
    fn attenuation_holds_grafana_cant_reach_ops() {
        let root = RootKey::from_seed([15u8; 32]);
        let cfg = cfg_for(&root);
        // A wide credential (ops-admin + grafana-view), narrowed to grafana-view.
        let wide = mint_caps(&root, ["ops-admin", "grafana-view"], None);
        let narrowed = attenuate_caps(wide, ["grafana-view"], None).encode();
        // grafana-view surface: admits.
        let g = decide(
            &cfg,
            &AuthInput {
                credential: Some(narrowed.clone()),
                required_cap: Some("grafana-view".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(g.admitted(), "grafana-view should admit: {g:?}");
        // ops-admin surface: the narrowed credential cannot reach it.
        let o = decide(
            &cfg,
            &AuthInput {
                credential: Some(narrowed),
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(
            !o.admitted(),
            "ops-admin must be refused for a grafana-only cap"
        );
    }

    #[test]
    fn break_glass_admits_without_credential() {
        let root = RootKey::from_seed([16u8; 32]);
        let cfg = cfg_for(&root);
        let v = decide(
            &cfg,
            &AuthInput {
                break_glass: Some("rescue-me-123".to_string()),
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(v.admitted());
        // A wrong break-glass token does NOT admit.
        let v = decide(
            &cfg,
            &AuthInput {
                break_glass: Some("wrong".to_string()),
                required_cap: Some("ops-admin".to_string()),
                now: 1000,
                ..Default::default()
            },
        );
        assert!(!v.admitted());
    }

    #[test]
    fn expired_credential_denied() {
        let root = RootKey::from_seed([17u8; 32]);
        let cfg = cfg_for(&root);
        let token = mint_caps(&root, ["ops-admin"], Some(1_000)).encode();
        let ok = decide(
            &cfg,
            &AuthInput {
                credential: Some(token.clone()),
                required_cap: Some("ops-admin".to_string()),
                now: 999,
                ..Default::default()
            },
        );
        assert!(ok.admitted());
        let expired = decide(
            &cfg,
            &AuthInput {
                credential: Some(token),
                required_cap: Some("ops-admin".to_string()),
                now: 1_001,
                ..Default::default()
            },
        );
        assert!(!expired.admitted());
    }

    // =======================================================================
    // TIER 0 — compromise response: revocation deny-set + default expiry.
    // =======================================================================

    fn admit(cfg: &WebAuthConfig, token: &str) -> Verdict {
        decide(
            cfg,
            &AuthInput {
                credential: Some(token.to_string()),
                required_cap: Some("ops-admin".to_string()),
                now: 1_000,
                ..Default::default()
            },
        )
    }

    /// A leaked session token is killed proactively by adding its TAIL to the
    /// deny-set: it was admitting, and now it is refused. A DIFFERENT token for
    /// the same account still admits (tail-keying kills exactly one session).
    #[test]
    fn revoked_by_tail_is_refused() {
        let root = RootKey::from_seed([21u8; 32]);
        let mut cfg = cfg_for(&root);
        let leaked = mint_session(&root, "acct-abc", ["ops-admin"], 0, 100_000);
        let other = mint_session(&root, "acct-abc", ["ops-admin"], 0, 100_000);
        let leaked_enc = leaked.encode();
        let other_enc = other.encode();
        assert!(
            admit(&cfg, &leaked_enc).admitted(),
            "fresh leaked token admits"
        );

        // Operator/customer revokes the leaked token by its tail.
        cfg.revoked.insert(leaked.tail_hex());
        assert!(
            !admit(&cfg, &leaked_enc).admitted(),
            "revoked-by-tail must refuse"
        );
        // A different session for the SAME account is untouched.
        assert!(
            admit(&cfg, &other_enc).admitted(),
            "tail-keying kills only the one session"
        );
    }

    /// A compromised account is killed WHOLESALE by adding its SUBJECT to the
    /// deny-set: every session for that account (any tail) is refused, while a
    /// session for another account still admits. This is the proactive
    /// "rotate-out" companion — kill all sessions, then rotate the account key.
    #[test]
    fn revoked_by_subject_kills_every_session() {
        let root = RootKey::from_seed([22u8; 32]);
        let mut cfg = cfg_for(&root);
        let victim_pk = [0xA1u8; 32];
        let other_pk = [0xB2u8; 32];
        let s1 = mint_session_for(&root, &victim_pk, ["ops-admin"], 0, 100_000).encode();
        let s2 = mint_session_for(&root, &victim_pk, ["ops-admin"], 0, 100_000).encode();
        let bystander = mint_session_for(&root, &other_pk, ["ops-admin"], 0, 100_000).encode();
        assert!(admit(&cfg, &s1).admitted());

        cfg.revoked.insert(account_id::account_subject(&victim_pk));
        assert!(
            !admit(&cfg, &s1).admitted(),
            "session 1 of the killed account refused"
        );
        assert!(
            !admit(&cfg, &s2).admitted(),
            "session 2 of the killed account refused"
        );
        assert!(
            admit(&cfg, &bystander).admitted(),
            "another account is unaffected"
        );
    }

    /// `mint_session` stamps the Tier-0 default expiry: the token admits before
    /// its TTL elapses and self-expires after — bounding a leaked token's life
    /// even with no explicit revocation.
    #[test]
    fn mint_session_self_expires() {
        let root = RootKey::from_seed([23u8; 32]);
        let cfg = cfg_for(&root);
        let token = mint_session(&root, "acct-x", ["ops-admin"], 1_000, 60).encode();
        let before = decide(
            &cfg,
            &AuthInput {
                credential: Some(token.clone()),
                required_cap: Some("ops-admin".to_string()),
                now: 1_050,
                ..Default::default()
            },
        );
        assert!(before.admitted(), "within TTL admits");
        let after = decide(
            &cfg,
            &AuthInput {
                credential: Some(token),
                required_cap: Some("ops-admin".to_string()),
                now: 1_061,
                ..Default::default()
            },
        );
        assert!(!after.admitted(), "past TTL self-expires");
    }

    /// The revocation list parser accepts inline + multi-line + comments, and a
    /// `decide` over a parsed cfg refuses a listed tail.
    #[test]
    fn revoked_list_parsing_round_trip() {
        let root = RootKey::from_seed([24u8; 32]);
        let token = mint_session(&root, "acct-y", ["ops-admin"], 0, 100_000);
        let tail = token.tail_hex();
        let raw = format!("# revoked tokens\n{tail}, dregg:deadbeef\n  # a comment\n");
        let mut cfg = cfg_for(&root);
        cfg.revoked = config::parse_revoked(&raw);
        assert!(cfg.is_revoked(&tail, None));
        assert!(!admit(&cfg, &token.encode()).admitted());
    }

    // =======================================================================
    // TIER 1 — the re-anchor: a stable, key-derived account subject.
    // =======================================================================

    /// Two DIFFERENT session credentials (different tails, even minted under
    /// different issuer keys — a rotation) for the SAME account resolve to the
    /// SAME subject. This is account continuity: the subject is the account's
    /// key-derived identity, not the token's tail, so re-issuing a session (login
    /// / rotation / recovery) preserves the account and its resources.
    #[test]
    fn reanchored_subject_is_stable_across_reissue() {
        let pk = [0x7Eu8; 32];
        let root_a = RootKey::from_seed([30u8; 32]);
        let root_b = RootKey::from_seed([31u8; 32]); // a rotated issuer key
        let s1 = mint_session_for(&root_a, &pk, ["ops-admin"], 0, 100_000).encode();
        let s2 = mint_session_for(&root_a, &pk, ["grafana-view"], 50, 100_000).encode();
        let s3 = mint_session_for(&root_b, &pk, ["ops-admin"], 100, 100_000).encode();

        let want = account_id::account_subject(&pk);
        assert_eq!(subject_of(&s1).as_deref(), Some(want.as_str()));
        assert_eq!(subject_of(&s2).as_deref(), Some(want.as_str()));
        assert_eq!(subject_of(&s3).as_deref(), Some(want.as_str()));
        // Different tails (distinct tokens) but one stable account subject.
        assert_ne!(
            Credential::decode(&s1).unwrap().tail_hex(),
            Credential::decode(&s2).unwrap().tail_hex()
        );
    }

    /// A different account gets a different subject (the id is key-derived).
    #[test]
    fn distinct_accounts_distinct_subjects() {
        let root = RootKey::from_seed([32u8; 32]);
        let a = mint_session_for(&root, &[0x01u8; 32], ["ops-admin"], 0, 100_000).encode();
        let b = mint_session_for(&root, &[0x02u8; 32], ["ops-admin"], 0, 100_000).encode();
        assert_ne!(subject_of(&a), subject_of(&b));
    }

    /// Backward compatibility: a LEGACY credential (no `acct` caveat) falls back
    /// to the original tail-commitment subject, so already-issued credentials
    /// keep working unchanged.
    #[test]
    fn legacy_credential_keeps_tail_subject() {
        let root = RootKey::from_seed([33u8; 32]);
        let legacy = mint_caps(&root, ["ops-admin"], None);
        let enc = legacy.encode();
        let subj = subject_of(&enc).unwrap();
        assert_eq!(subj, format!("dregg:{}", &legacy.tail_hex()[..16]));
        // 16-hex legacy form, not a 64-hex account id.
        assert_eq!(subj.len(), "dregg:".len() + 16);
    }

    /// Attenuating a re-anchored session (the agent-confinement path) preserves
    /// the account subject: the `acct` claim is on the root block, which
    /// attenuation cannot drop.
    #[test]
    fn attenuated_session_keeps_account_subject() {
        let pk = [0x5Au8; 32];
        let root = RootKey::from_seed([34u8; 32]);
        let session = mint_session_for(&root, &pk, ["ops-admin", "grafana-view"], 0, 100_000);
        let narrowed = attenuate_caps(session, ["grafana-view"], None).encode();
        assert_eq!(
            subject_of(&narrowed),
            Some(account_id::account_subject(&pk))
        );
    }
}
