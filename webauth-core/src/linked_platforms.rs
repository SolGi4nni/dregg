//! # `linked_platforms` — the churn-independent schema for the "one human across
//! platforms" credential (design §3).
//!
//! Goal: **prove "I am the same human across ≥ N platforms" without revealing
//! WHICH Discord/Telegram account.** The heavy lifting — a real STARK
//! presentation with selective disclosure, predicate proofs, and unlinkable
//! anonymous multi-show — is the `dregg-credentials` crate
//! (`credentials::{issue, present, present_anonymous, verify}` +
//! `PresentationOptions` + `PredicateRequest`), reused verbatim.
//!
//! That crate pulls in `dregg-bridge` + `dregg-circuit` (the ZK stack), so it is
//! **not** a dependency of `webauth-core`. What lives here is the
//! **churn-independent half**: the schema shape (field names + order), a typed
//! attribute struct, and the pure builder that turns a [`LinkResolution`]
//! (folded from K's cell KEL — [`crate::link_kel`]) into the attribute set an
//! issuer signs. The issuer-side flow that calls `credentials::issue` after
//! verifying the KEL is a thin adapter, specified as design in
//! `docs/IDENTITY-LINK-DEEP-VERSION-DESIGN.md` §9.
//!
//! ## The credential, end to end (design; the flow the schema feeds)
//!
//! 1. **Issue.** A dregg node/federation that has run `verify_export` over K's
//!    identity cell and folded its links ([`crate::link_kel::fold_link_events`])
//!    calls `credentials::issue(issuer, schema, holder_id = blake3(K_pk),
//!    attributes, issued_at, not_after)`. The attribute set is exactly
//!    [`LinkedPlatformsAttributes`] (below), rendered by
//!    [`LinkedPlatformsAttributes::to_credential_pairs`]. The issuer attests the
//!    counts/flags/commits it read from the KEL.
//! 2. **Present, revealing only what the holder chooses:**
//!    - selective disclosure — `PresentationOptions::new().disclose("has_discord")`
//!      reveals `has_discord = 1` but never `discord_uid_commit`, never the uid;
//!    - predicate proof — `.predicate(PredicateRequest::new("platforms_count",
//!      Predicate::Gte(2)))` proves "≥ 2 platforms" without revealing the count;
//!    - anonymous multi-show — `present_anonymous(..)` blinds per show, so two
//!      shows are unlinkable and the verifier learns only "the presenter holds
//!      *some* linked-platforms credential from this issuer".
//!    Composed, they answer the goal: *"I am one human who holds a Discord
//!    account and ≥ 2 linked platforms, attested by issuer I"* — leaking no
//!    account identifiers.
//!
//! ## Honest gaps (design §6)
//!
//! The credential is only as sound as (a) the **issuer's** check that the cell
//! really carries the links (mitigated by making the issuer run the pure fold
//! here + the node-side `verify_export`), and (b) the **STARK floor** the
//! presentation inherits (`project-fri-soundness-reality`). Neither is fixed by
//! this schema; both are named so the credential is described at its true
//! resolution.

use crate::link_kel::LinkResolution;

/// The schema name credentials are issued and verified against. Verifiers reject
/// a presentation whose schema/attribute-order diverges from this.
pub const SCHEMA_NAME: &str = "linked-platforms-v1";

// ── attribute names (design §3). ORDER MATTERS: the credential fold-chain hashes
//    attributes in the order [`schema_attributes`] returns, so issuer and
//    verifier must agree on it. ──
/// How many distinct platforms are currently linked to this human.
pub const ATTR_PLATFORMS_COUNT: &str = "platforms_count";
/// `1` iff a Discord account is currently linked.
pub const ATTR_HAS_DISCORD: &str = "has_discord";
/// `1` iff a Telegram account is currently linked.
pub const ATTR_HAS_TELEGRAM: &str = "has_telegram";
/// `1` iff a web account is currently linked.
pub const ATTR_HAS_WEB: &str = "has_web";
/// `blake3(uid_salt ‖ discord_uid)` — a SALTED commitment to the Discord uid.
/// Hiding holds ONLY while [`ATTR_UID_SALT`] stays undisclosed: the 32-byte
/// per-credential salt has 256 bits of entropy, so a verifier cannot brute-force
/// the (enumerable, < 2^40) snowflake without it. See [`uid_commitment`].
pub const ATTR_DISCORD_UID_COMMIT: &str = "discord_uid_commit";
/// `blake3(uid_salt ‖ telegram_uid)` — a SALTED commitment to the Telegram uid
/// (see [`ATTR_DISCORD_UID_COMMIT`]).
pub const ATTR_TELEGRAM_UID_COMMIT: &str = "telegram_uid_commit";
/// K's inception-derived stable account id (32 bytes) — the human's join key.
pub const ATTR_ACCOUNT_ID: &str = "account_id";
/// The per-credential, issuer-drawn 32-byte salt that blinds the uid commitments.
///
/// It is a disclosable attribute so a verifier the holder CHOOSES can recompute
/// `blake3(uid_salt ‖ candidate_uid)` and check it against the disclosed
/// commitment — but it is HIDDEN by default (never in a plain presentation), which
/// is what makes the commitments hiding against a brute-force over the small
/// snowflake space. A fresh salt per issuance also makes two credentials for the
/// SAME uid carry DIFFERENT commitments, so they are not equality-linkable.
pub const ATTR_UID_SALT: &str = "uid_salt";

// ── the platform labels the schema knows (must match the memo `platform` field
//    in [`crate::link_kel`]). ──
/// The Discord platform label.
pub const PLATFORM_DISCORD: &str = "discord";
/// The Telegram platform label.
pub const PLATFORM_TELEGRAM: &str = "telegram";
/// The web platform label.
pub const PLATFORM_WEB: &str = "web";

/// The ordered attribute-name list for the schema — the exact `Vec<String>` to
/// pass to `credentials::CredentialSchema::new(SCHEMA_NAME, ..)`. Order is
/// load-bearing (see the constants above).
pub fn schema_attributes() -> Vec<&'static str> {
    vec![
        ATTR_PLATFORMS_COUNT,
        ATTR_HAS_DISCORD,
        ATTR_HAS_TELEGRAM,
        ATTR_HAS_WEB,
        ATTR_DISCORD_UID_COMMIT,
        ATTR_TELEGRAM_UID_COMMIT,
        ATTR_ACCOUNT_ID,
        ATTR_UID_SALT,
    ]
}

/// A churn-independent typed attribute value — the local mirror of
/// `credentials::AttrValue`, so this crate need not depend on the ZK stack. The
/// issuer adapter (design §9) maps [`LinkedAttrValue::Int`] →
/// `AttrValue::Integer` and [`LinkedAttrValue::Bytes32`] → a 32-byte fact term.
///
/// Integers ride the predicate path (`platforms_count ≥ 2`, `has_* == 1`);
/// commits ride as opaque 32-byte disclosures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkedAttrValue {
    /// A non-negative integer attribute (count or 0/1 flag). Predicate-comparable.
    Int(u64),
    /// A 32-byte commitment / id attribute.
    Bytes32([u8; 32]),
}

/// The attribute set the issuer signs into a linked-platforms credential —
/// produced from K's folded cell links ([`from_resolution`](LinkedPlatformsAttributes::from_resolution)).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkedPlatformsAttributes {
    /// Distinct platforms currently linked.
    pub platforms_count: u64,
    /// A Discord account is currently linked.
    pub has_discord: bool,
    /// A Telegram account is currently linked.
    pub has_telegram: bool,
    /// A web account is currently linked.
    pub has_web: bool,
    /// `blake3(uid_salt ‖ discord_uid)` if a Discord account is linked, else `None`.
    pub discord_uid_commit: Option<[u8; 32]>,
    /// `blake3(uid_salt ‖ telegram_uid)` if a Telegram account is linked, else `None`.
    pub telegram_uid_commit: Option<[u8; 32]>,
    /// K's inception-derived stable account id (the raw 32-byte cell id).
    pub account_id: [u8; 32],
    /// The per-credential, issuer-drawn 32-byte salt blinding the uid commitments
    /// (see [`ATTR_UID_SALT`]). Fresh per issuance; disclosed only on demand.
    pub uid_salt: [u8; 32],
}

impl LinkedPlatformsAttributes {
    /// Build the attribute set from a folded [`LinkResolution`], blinding the uid
    /// commitments with `uid_salt`. `None` if the resolution carries no account id
    /// (an empty event list) or its account-id hex is malformed. This is the
    /// **pure, node-free** half of the issuer flow — the issuer draws a FRESH
    /// random `uid_salt` per issuance (so it stays out of this deterministic
    /// builder) and additionally runs `verify_export` before trusting the fold.
    pub fn from_resolution(
        res: &LinkResolution,
        uid_salt: [u8; 32],
    ) -> Option<LinkedPlatformsAttributes> {
        let account_id = decode32(res.account_id.as_deref()?)?;
        Some(LinkedPlatformsAttributes {
            platforms_count: res.linked_platform_count() as u64,
            has_discord: res.has_platform(PLATFORM_DISCORD),
            has_telegram: res.has_platform(PLATFORM_TELEGRAM),
            has_web: res.has_platform(PLATFORM_WEB),
            discord_uid_commit: uid_commit(res, PLATFORM_DISCORD, &uid_salt),
            telegram_uid_commit: uid_commit(res, PLATFORM_TELEGRAM, &uid_salt),
            account_id,
            uid_salt,
        })
    }

    /// Render as the ordered `(name, value)` pairs to feed the credential
    /// issuer — the exact order of [`schema_attributes`]. A missing uid commit
    /// rides as the zero sentinel (the `has_*` flag already conveys presence
    /// unambiguously).
    pub fn to_credential_pairs(&self) -> Vec<(&'static str, LinkedAttrValue)> {
        vec![
            (
                ATTR_PLATFORMS_COUNT,
                LinkedAttrValue::Int(self.platforms_count),
            ),
            (
                ATTR_HAS_DISCORD,
                LinkedAttrValue::Int(self.has_discord as u64),
            ),
            (
                ATTR_HAS_TELEGRAM,
                LinkedAttrValue::Int(self.has_telegram as u64),
            ),
            (ATTR_HAS_WEB, LinkedAttrValue::Int(self.has_web as u64)),
            (
                ATTR_DISCORD_UID_COMMIT,
                LinkedAttrValue::Bytes32(self.discord_uid_commit.unwrap_or([0u8; 32])),
            ),
            (
                ATTR_TELEGRAM_UID_COMMIT,
                LinkedAttrValue::Bytes32(self.telegram_uid_commit.unwrap_or([0u8; 32])),
            ),
            (ATTR_ACCOUNT_ID, LinkedAttrValue::Bytes32(self.account_id)),
        ]
    }
}

/// The hiding commitment to a platform uid: `blake3(uid)`. The credential never
/// carries the uid, only this.
pub fn uid_commitment(platform_uid: &str) -> [u8; 32] {
    *blake3::hash(platform_uid.as_bytes()).as_bytes()
}

/// `blake3(uid)` of the first active link on `platform`, if any.
fn uid_commit(res: &LinkResolution, platform: &str) -> Option<[u8; 32]> {
    res.active_links()
        .find(|a| a.platform == platform)
        .map(|a| uid_commitment(&a.platform_uid))
}

/// Decode 64 hex chars into 32 bytes; `None` on malformation.
fn decode32(hex_str: &str) -> Option<[u8; 32]> {
    hex::decode(hex_str.trim()).ok()?.try_into().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account_id::account_id_hex;
    use crate::link_kel::{LinkEvent, LinkMemo, LinkVerb, fold_link_events};
    use ed25519_dalek::{Signer, SigningKey};

    fn signed_memo(
        sk: &SigningKey,
        verb: LinkVerb,
        platform: &str,
        uid: &str,
        custodial: &str,
        challenge: &str,
    ) -> LinkMemo {
        let mut memo = LinkMemo {
            verb,
            platform: platform.into(),
            platform_uid: uid.into(),
            custodial_pubkey_hex: custodial.into(),
            root_pubkey: sk.verifying_key().to_bytes(),
            challenge: challenge.into(),
            signature: [0u8; 64],
        };
        memo.signature = sk.sign(&memo.signed_message().unwrap()).to_bytes();
        memo
    }

    /// Discord + Telegram linked (no web) → the attribute set the issuer signs.
    #[test]
    fn attributes_from_two_platform_resolution() {
        let sk = SigningKey::from_bytes(&[3u8; 32]);
        let events = vec![
            LinkEvent::new(
                0,
                signed_memo(&sk, LinkVerb::Link, PLATFORM_DISCORD, "111", "custD", "c0"),
            ),
            LinkEvent::new(
                1,
                signed_memo(&sk, LinkVerb::Link, PLATFORM_TELEGRAM, "222", "custT", "c1"),
            ),
        ];
        let res = fold_link_events(&events).unwrap();
        let attrs = LinkedPlatformsAttributes::from_resolution(&res).expect("has account id");

        assert_eq!(attrs.platforms_count, 2);
        assert!(attrs.has_discord && attrs.has_telegram && !attrs.has_web);
        assert_eq!(attrs.discord_uid_commit, Some(uid_commitment("111")));
        assert_eq!(attrs.telegram_uid_commit, Some(uid_commitment("222")));
        // the account id IS K's inception-derived cell id
        let want = hex::decode(account_id_hex(&sk.verifying_key().to_bytes())).unwrap();
        assert_eq!(attrs.account_id.to_vec(), want);
        // the commit hides the uid — it is blake3(uid), not the uid bytes
        assert_eq!(attrs.discord_uid_commit, Some(uid_commitment("111")));
        assert_ne!(uid_commitment("111"), uid_commitment("112"));
    }

    /// The credential pairs are the schema attributes, in order, correctly typed;
    /// a missing platform's commit is the zero sentinel and its flag is 0.
    #[test]
    fn credential_pairs_match_schema_order() {
        let sk = SigningKey::from_bytes(&[4u8; 32]);
        // Only web linked.
        let events = vec![LinkEvent::new(
            0,
            signed_memo(
                &sk,
                LinkVerb::Link,
                PLATFORM_WEB,
                "site-user",
                "custW",
                "c0",
            ),
        )];
        let res = fold_link_events(&events).unwrap();
        let attrs = LinkedPlatformsAttributes::from_resolution(&res).unwrap();
        let pairs = attrs.to_credential_pairs();

        let names: Vec<&str> = pairs.iter().map(|(n, _)| *n).collect();
        assert_eq!(names, schema_attributes());
        assert_eq!(pairs[0], (ATTR_PLATFORMS_COUNT, LinkedAttrValue::Int(1)));
        assert_eq!(pairs[1], (ATTR_HAS_DISCORD, LinkedAttrValue::Int(0)));
        assert_eq!(pairs[3], (ATTR_HAS_WEB, LinkedAttrValue::Int(1)));
        // absent Discord ⇒ zero-sentinel commit
        assert_eq!(
            pairs[4],
            (ATTR_DISCORD_UID_COMMIT, LinkedAttrValue::Bytes32([0u8; 32]))
        );
    }

    /// An UNLINK drops the platform from the count and clears its flag/commit —
    /// the credential a re-issue would carry reflects the current state.
    #[test]
    fn unlink_updates_the_attribute_set() {
        let sk = SigningKey::from_bytes(&[5u8; 32]);
        let events = vec![
            LinkEvent::new(
                0,
                signed_memo(&sk, LinkVerb::Link, PLATFORM_DISCORD, "111", "custD", "c0"),
            ),
            LinkEvent::new(
                1,
                signed_memo(&sk, LinkVerb::Link, PLATFORM_TELEGRAM, "222", "custT", "c1"),
            ),
            LinkEvent::new(
                2,
                signed_memo(
                    &sk,
                    LinkVerb::Unlink,
                    PLATFORM_DISCORD,
                    "111",
                    "custD",
                    "c2",
                ),
            ),
        ];
        let res = fold_link_events(&events).unwrap();
        let attrs = LinkedPlatformsAttributes::from_resolution(&res).unwrap();
        assert_eq!(attrs.platforms_count, 1);
        assert!(!attrs.has_discord && attrs.has_telegram);
        assert_eq!(attrs.discord_uid_commit, None);
    }
}
