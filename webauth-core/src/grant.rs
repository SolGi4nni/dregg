// PORTED dregg-native from the prior operated layer (verbatim; core types from dregg_agent::cred).

//! The web-surface capability vocabulary on top of the `dregg_agent::cred` core.
//!
//! A gated web surface (ops, grafana, the gateway admin) requires one named
//! **capability** string — `ops-admin`, `grafana-view`, `gateway-admin`. A
//! credential grants a set of caps via a single first-party caveat:
//!
//! ```text
//! AnyOf([ AttrEq{cap, "ops-admin"}, AttrEq{cap, "grafana-view"} ])
//! ```
//!
//! The forward-auth service verifies the presented credential against a context
//! binding `cap = <the surface's required capability>` and `clock = now`. The
//! `AnyOf` admits iff the requested cap is one the credential was granted. To
//! confine to a sub-agent, [`attenuate_caps`] appends a *narrower* `AnyOf` — the
//! caveat meet then rejects any cap outside the narrowed set, so a `grafana-view`
//! credential can never reach `ops-admin` (the no-amplify property, proven in
//! `cred::tests::attenuation_only_narrows`).

use crate::account_id::{self, ACCT_CAVEAT_KEY};
use dregg_agent::cred::{Caveat, Context, Credential, Pred, RootKey};

/// The request attribute key a capability is matched on.
pub const CAP_KEY: &str = "cap";

/// Build the single caveat that grants exactly `caps`.
fn cap_caveat(caps: &[String]) -> Caveat {
    Caveat::FirstParty(Pred::AnyOf(
        caps.iter()
            .map(|c| Pred::AttrEq {
                key: CAP_KEY.to_string(),
                value: c.clone(),
            })
            .collect(),
    ))
}

/// Mint a credential granting `caps`, optionally expiring at `until` (a unix
/// second / clock reading; `None` = no expiry).
pub fn mint_caps(
    root: &RootKey,
    caps: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let mut caveats = vec![cap_caveat(&caps)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    root.mint(caveats)
}

/// Narrow an existing credential to a subset of caps (and/or a tighter expiry).
/// Appends a confining `AnyOf` caveat — can only ever *remove* reach.
pub fn attenuate_caps(
    cred: Credential,
    caps: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let mut caveats = vec![cap_caveat(&caps)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    cred.attenuate(caveats)
}

/// Build the verification context for a request to `required_cap` at clock `now`.
pub fn cap_context(required_cap: &str, now: u64) -> Context {
    Context::new().at(now).attr(CAP_KEY, required_cap)
}

/// Mint a **re-anchored session credential** (Tier 1): a short-lived auth token
/// for the account whose stable, key-derived id is `account_id_hex`
/// ([`account_id::account_id_hex`] of the account's inception key), granting
/// `caps`, expiring `ttl_secs` after `issued_at`.
///
/// The credential carries:
///  * an `acct = <account-id-hex>` first-party caveat — so [`crate::subject_of`]
///    returns the SAME `dregg:<account-id>` subject across every re-issue (a key
///    rotation, a guardian recovery, a fresh login). The account — and every
///    resource `org`/`dregg-secrets`/`console`/`guard`/`billing` scopes to it —
///    survives, because the subject is the account's identity, not this token's
///    tail;
///  * the cap grant;
///  * a `NotAfter` expiry — the Tier-0 default that bounds a leaked token's life.
///
/// The token is minted under `root` (the control-plane issuer's authoritative
/// key for the account); the offline forward-auth verifier stays a pure session
/// checker. Rotation/recovery/revocation of the account happen on the substrate
/// identity cell whose id IS `account_id_hex` — the depend-on-substrate weld.
pub fn mint_session(
    root: &RootKey,
    account_id_hex: &str,
    caps: impl IntoIterator<Item = impl Into<String>>,
    issued_at: u64,
    ttl_secs: u64,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let caveats = vec![
        Caveat::FirstParty(Pred::AttrEq {
            key: ACCT_CAVEAT_KEY.to_string(),
            value: account_id_hex.to_string(),
        }),
        cap_caveat(&caps),
        Caveat::FirstParty(Pred::NotAfter {
            at: issued_at.saturating_add(ttl_secs),
        }),
    ];
    root.mint(caveats)
}

// ---------------------------------------------------------------------------
// HAVE A DREGG COMPUTER (weld 2 of `DREGG-COMPUTER.md`): the per-VAT capability.
// ---------------------------------------------------------------------------

/// The capability-string prefix that scopes a credential to exactly ONE vat
/// (a persistent server whose identity is its content-addressed substrate cell
/// id, the control-plane server record cell id). The full grammar is
/// `vat:<cell-id-hex>` — one cap per vat, minted by [`vat_cap`].
pub const VAT_CAP_PREFIX: &str = "vat:";

/// The capability string that reaches exactly the vat whose substrate cell id
/// is `cell_id` (the 64-hex `CellId` — the vat's dregg identity, NOT its random
/// `srv_…` row key). [`crate::decide`] already flows an arbitrary cap string
/// through [`cap_context`], so no core-verify change is needed: a surface whose
/// `required_cap` is `vat_cap(id)` admits ONLY a credential granted that exact
/// cap. Presenting a genuine session against another vat's cap yields
/// `Verdict::Deny { authenticated: true }` — the 403, not a 401 (re-login
/// cannot widen a capability).
pub fn vat_cap(cell_id: &str) -> String {
    format!("{VAT_CAP_PREFIX}{cell_id}")
}

/// Parse the vat cell id back out of a `vat:<cell-id>` capability string.
/// `None` for a cap outside the vat grammar.
pub fn vat_cell_id(cap: &str) -> Option<&str> {
    cap.strip_prefix(VAT_CAP_PREFIX).filter(|id| !id.is_empty())
}

/// Mint the **per-vat credential** a renter holds for their Dregg Computer: a
/// re-anchored session ([`mint_session`]) for the account whose stable id is
/// `account_id_hex`, granting exactly ONE cap — `vat:<cell_id>` — and expiring
/// `ttl_secs` after `issued_at`.
///
/// The `acct` caveat rides the root block, so [`crate::subject_of`] resolves
/// this credential to the SAME `dregg:<account-id>` subject as the account's
/// session — the vat key still names its owner (the gateway's owner-scoped
/// reads keep working), while the cap grant reaches nothing but the one vat.
pub fn mint_vat_session(
    root: &RootKey,
    account_id_hex: &str,
    cell_id: &str,
    issued_at: u64,
    ttl_secs: u64,
) -> Credential {
    mint_session(
        root,
        account_id_hex,
        [vat_cap(cell_id)],
        issued_at,
        ttl_secs,
    )
}

/// Narrow an existing credential down to exactly ONE vat (and optionally a
/// tighter expiry) — the no-amplify hand-off for a sub-agent that should reach
/// `vat:<cell_id>` and nothing else. Attenuation only ever *removes* reach
/// (`cred::tests::attenuation_only_narrows`), so the result admits **iff** the
/// source credential was itself granted that vat's cap: narrowing a session
/// that never reached the vat yields a credential that reaches nothing, never
/// one that reaches more. The `acct` claim survives (it is on the root block),
/// so the narrowed credential still resolves to the owner's subject.
pub fn attenuate_to_vat(cred: Credential, cell_id: &str, until: Option<u64>) -> Credential {
    attenuate_caps(cred, [vat_cap(cell_id)], until)
}

/// Re-anchor an existing session for the same account under a fresh issue: drop
/// the old expiry, mint a new token carrying the SAME `acct` claim and a fresh
/// TTL. Convenience over [`mint_session`] when the inception pubkey is in hand.
pub fn mint_session_for(
    root: &RootKey,
    inception_pubkey: &[u8; 32],
    caps: impl IntoIterator<Item = impl Into<String>>,
    issued_at: u64,
    ttl_secs: u64,
) -> Credential {
    mint_session(
        root,
        &account_id::account_id_hex(inception_pubkey),
        caps,
        issued_at,
        ttl_secs,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::WebAuthConfig;
    use crate::{AuthInput, Verdict, decide, subject_of};

    fn cfg_for(root: &RootKey) -> WebAuthConfig {
        WebAuthConfig {
            root_pubkey_hex: Some(root.public().to_hex()),
            ..WebAuthConfig::default()
        }
    }

    /// `decide` over a presented token against a surface requiring `cap`.
    fn verdict(cfg: &WebAuthConfig, token: &str, cap: &str) -> Verdict {
        decide(
            cfg,
            &AuthInput {
                credential: Some(token.to_string()),
                required_cap: Some(cap.to_string()),
                now: 1_000,
                ..Default::default()
            },
        )
    }

    const VAT_A: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const VAT_B: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    #[test]
    fn vat_cap_grammar_round_trips() {
        let cap = vat_cap(VAT_A);
        assert_eq!(cap, format!("vat:{VAT_A}"));
        assert_eq!(vat_cell_id(&cap), Some(VAT_A));
        // Outside the grammar: no cell id.
        assert_eq!(vat_cell_id("ops-admin"), None);
        assert_eq!(vat_cell_id("vat:"), None, "an empty cell id is not a vat");
    }

    /// THE SCOPING TOOTH (weld 2 of `DREGG-COMPUTER.md`): a minted vat credential
    /// reaches exactly its own vat. Presented against ANOTHER vat's required cap
    /// it is `Deny { authenticated: true }` — the 403 (genuine session, wrong
    /// capability; re-login cannot help), never a 401 and never an admit.
    #[test]
    fn a_vat_credential_reaches_only_its_own_vat() {
        let root = RootKey::from_seed([41u8; 32]);
        let cfg = cfg_for(&root);
        let token = mint_vat_session(&root, "acct-alice", VAT_A, 0, 100_000).encode();

        // Its own vat: admitted, with the exact cap echoed.
        let own = verdict(&cfg, &token, &vat_cap(VAT_A));
        assert!(own.admitted(), "{own:?}");

        // Another vat: authenticated-but-uncapped → 403.
        let other = verdict(&cfg, &token, &vat_cap(VAT_B));
        assert!(
            matches!(
                &other,
                Verdict::Deny {
                    authenticated: true,
                    ..
                }
            ),
            "expected authenticated deny, got {other:?}"
        );
        assert_eq!(other.status(), 403, "wrong vat is a 403, not a 401");

        // …and it reaches no operator surface either (one cap, one vat).
        assert!(!verdict(&cfg, &token, "ops-admin").admitted());
    }

    /// The vat credential still names its OWNER: the `acct` caveat rides the
    /// root block, so the subject is the account's stable `dregg:<id>` — the
    /// same subject the gateway's owner-scoped reads key on.
    #[test]
    fn a_vat_credential_keeps_the_account_subject() {
        let root = RootKey::from_seed([42u8; 32]);
        let token = mint_vat_session(&root, "acct-alice", VAT_A, 0, 100_000).encode();
        assert_eq!(subject_of(&token).as_deref(), Some("dregg:acct-alice"));
    }

    /// No-amplify over the vat grammar: a session granted TWO vats, narrowed to
    /// one ([`attenuate_to_vat`]), reaches that one and no longer the sibling;
    /// and narrowing a session that never held a vat cap yields a credential
    /// that reaches NO vat (attenuation cannot mint reach).
    #[test]
    fn attenuate_to_vat_only_narrows() {
        let root = RootKey::from_seed([43u8; 32]);
        let cfg = cfg_for(&root);

        // A two-vat session, narrowed down to vat A.
        let wide = mint_session(
            &root,
            "acct-alice",
            [vat_cap(VAT_A), vat_cap(VAT_B)],
            0,
            100_000,
        );
        let narrowed = attenuate_to_vat(wide, VAT_A, None);
        let enc = narrowed.encode();
        assert!(verdict(&cfg, &enc, &vat_cap(VAT_A)).admitted());
        assert!(
            !verdict(&cfg, &enc, &vat_cap(VAT_B)).admitted(),
            "the narrowed credential must not reach the sibling vat"
        );
        // The owner subject survives the attenuation (acct is on the root block).
        assert_eq!(subject_of(&enc).as_deref(), Some("dregg:acct-alice"));

        // Narrowing a vat-less session mints NO reach: the caveat meet of
        // `AnyOf[ops-admin]` and `AnyOf[vat:A]` is empty.
        let no_vat = mint_session(&root, "acct-bob", ["ops-admin"], 0, 100_000);
        let forged = attenuate_to_vat(no_vat, VAT_A, None).encode();
        assert!(
            !verdict(&cfg, &forged, &vat_cap(VAT_A)).admitted(),
            "attenuation must never amplify into a vat"
        );
    }
}
