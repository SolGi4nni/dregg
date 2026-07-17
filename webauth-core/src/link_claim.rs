//! # `link_claim` — cross-platform identity linking.
//!
//! The problem: each dregg frontend derives a SILOED custodial identity (Discord under
//! `"dregg-discord-bot-v1"`, Telegram under `"dregg-telegram-bot-v1"`, each with its own master
//! secret + uid namespace). A Discord user and a Telegram user who are the SAME human get
//! different dregg identities. This module is the trust root of collapsing them into one.
//!
//! The model: both platforms link to ONE user-held **root key K** (the key the extension /
//! passkey custody stack holds). K signs a **link claim** binding a platform's `(uid,
//! custodial_pubkey)` to `root_pubkey(K)`. A frontend verifies the claim *inside* an already-
//! authenticated platform interaction (a Discord slash command, or an initData-verified Mini App
//! request) — that authenticated context is the platform's half of the proof, exactly as the
//! existing `discord-bot` `/link-prove` ceremony trusts the slash command's Discord identity.
//!
//! What a verified claim asserts: *the holder of K attests that this platform account
//! (`platform`/`platform_uid`), whose custodial dregg key is `custodial_pubkey`, is controlled by
//! K* — fresh within the [`crate::challenge`] window. Cross-platform "same human" then becomes an
//! identity-RESOLUTION seam (`custodial_pubkey → root_pubkey`), never a signing change:
//! `Attribution` stays honest (the turn was signed by the custodial derivation; the resolution to
//! K is backed by K's own signature here).
//!
//! Reuses, does not reinvent: the [`crate::challenge`] stateless nonce'd freshness token (fixes
//! the deterministic-challenge replay wound in the current Discord ceremony) and the strict
//! ed25519 discipline of `discord-bot`'s `check_link_proof`. The canonical message follows the
//! byte-pinned, NUL-delimited discipline of `dreggnet_offerings::signed` — with the NUL-in-field
//! guard that made the extension signer collision-free.

use ed25519_dalek::{Signature, VerifyingKey};

use crate::challenge::{self, ChallengeError};

/// The domain-separation prefix of the link-claim canonical message. PINNED: changing it rotates
/// every claim ever signed. Distinct from the offering-turn domain (`dregg-offering-turn-v1:`) so
/// a link claim can never be replayed as a turn or vice versa.
pub const LINK_CLAIM_DOMAIN: &str = "dregg-identity-link-v1:";

/// Why a link claim was REFUSED — each variant one fail-closed gate of [`verify_link_claim`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkClaimError {
    /// A message field carried a NUL byte (the field delimiter). Refused so two distinct field
    /// tuples can never render to the same signed bytes (the collision the extension signer's
    /// NUL-hardening closed).
    FieldContainsNul,
    /// The freshness challenge was expired, forged, or malformed (from [`crate::challenge`]).
    /// Single-use replay defense is the caller's (record the spent challenge via [`crate::replay`]).
    StaleChallenge(ChallengeError),
    /// `root_pubkey` is not a valid ed25519 point.
    BadRootKey,
    /// The signature did not `verify_strict` under the root key over the canonical message —
    /// a forged claim, a tampered field, or a cross-platform splice.
    BadSignature,
}

/// Build the canonical link-claim message — the ONE function both the signer (client / extension)
/// and [`verify_link_claim`] use, so a divergence is a red pin test, not a silent forkable seam.
///
/// `LINK_CLAIM_DOMAIN ‖ platform ‖ 0 ‖ platform_uid ‖ 0 ‖ custodial_pubkey_hex ‖ 0 ‖
///  root_pubkey_hex ‖ 0 ‖ challenge`
///
/// Every field is NUL-checked: a NUL in any field is [`LinkClaimError::FieldContainsNul`] (the
/// delimiter must be unambiguous). All real fields are NUL-free by construction (ascii platform,
/// decimal uid, hex keys, base64url challenge) — the guard is defensive.
pub fn link_claim_message(
    platform: &str,
    platform_uid: &str,
    custodial_pubkey_hex: &str,
    root_pubkey_hex: &str,
    challenge: &str,
) -> Result<Vec<u8>, LinkClaimError> {
    for field in [
        platform,
        platform_uid,
        custodial_pubkey_hex,
        root_pubkey_hex,
        challenge,
    ] {
        if field.as_bytes().contains(&0) {
            return Err(LinkClaimError::FieldContainsNul);
        }
    }
    let mut m = Vec::with_capacity(
        LINK_CLAIM_DOMAIN.len()
            + platform.len()
            + platform_uid.len()
            + custodial_pubkey_hex.len()
            + root_pubkey_hex.len()
            + challenge.len()
            + 4,
    );
    m.extend_from_slice(LINK_CLAIM_DOMAIN.as_bytes());
    m.extend_from_slice(platform.as_bytes());
    m.push(0);
    m.extend_from_slice(platform_uid.as_bytes());
    m.push(0);
    m.extend_from_slice(custodial_pubkey_hex.as_bytes());
    m.push(0);
    m.extend_from_slice(root_pubkey_hex.as_bytes());
    m.push(0);
    m.extend_from_slice(challenge.as_bytes());
    Ok(m)
}

/// Verify a link claim, in gate order:
///
/// 1. the `challenge` is fresh + integral ([`crate::challenge::verify`]) — `now` and the
///    `server_key` are the caller's (the frontend that issued the challenge);
/// 2. the canonical message is rebuilt with the CANONICAL lowercase hex of the actual
///    `root_pubkey` (so a claim can never name a different root hex than the key that signed it);
/// 3. the `signature` `verify_strict`s under `root_pubkey` over that message.
///
/// On `Ok(())` the claim is proven: the holder of `root_pubkey` attests control of this platform
/// account whose custodial key is `custodial_pubkey_hex`. The CALLER then records the binding
/// (`custodial_pubkey → root_pubkey`) and marks the challenge spent ([`crate::replay`]).
#[allow(clippy::too_many_arguments)]
pub fn verify_link_claim(
    server_key: &[u8; 32],
    platform: &str,
    platform_uid: &str,
    custodial_pubkey_hex: &str,
    root_pubkey: &[u8; 32],
    challenge: &str,
    signature: &[u8; 64],
    now: u64,
) -> Result<(), LinkClaimError> {
    // 1. Freshness first — cheapest gate, and refuses a replayed/stale envelope before any crypto.
    challenge::verify(server_key, challenge, now).map_err(LinkClaimError::StaleChallenge)?;

    // 2. Canonical message with the ACTUAL root key's hex (never a caller-claimed string).
    let root_hex = hex::encode(root_pubkey);
    let msg = link_claim_message(
        platform,
        platform_uid,
        custodial_pubkey_hex,
        &root_hex,
        challenge,
    )?;

    // 3. Strict signature by the root key.
    let vk = VerifyingKey::from_bytes(root_pubkey).map_err(|_| LinkClaimError::BadRootKey)?;
    let sig = Signature::from_bytes(signature);
    vk.verify_strict(&msg, &sig)
        .map_err(|_| LinkClaimError::BadSignature)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    const SERVER_KEY: [u8; 32] = [7u8; 32];
    const NOW: u64 = 1_784_300_000;

    fn root_key() -> SigningKey {
        SigningKey::from_bytes(&[3u8; 32])
    }

    /// A helper that plays the CLIENT: build the canonical message and sign it with the root key
    /// — exactly what the extension `dregg.signLinkClaim` sibling will do in-browser.
    fn sign_claim(
        sk: &SigningKey,
        platform: &str,
        uid: &str,
        custodial_hex: &str,
        challenge: &str,
    ) -> [u8; 64] {
        let root_hex = hex::encode(sk.verifying_key().to_bytes());
        let msg = link_claim_message(platform, uid, custodial_hex, &root_hex, challenge).unwrap();
        sk.sign(&msg).to_bytes()
    }

    /// The wire drift killer: the exact canonical bytes for a fixed input. If the message builder
    /// ever changes, this pin goes red — the client signer and this verifier can never silently
    /// diverge.
    #[test]
    fn the_link_claim_message_is_pinned_byte_for_byte() {
        let msg = link_claim_message(
            "discord",
            "6913902526",
            "aa".repeat(32).as_str(),
            "bb".repeat(32).as_str(),
            "chal-xyz",
        )
        .unwrap();
        let mut expected = Vec::new();
        expected.extend_from_slice(b"dregg-identity-link-v1:discord\x00");
        expected.extend_from_slice(b"6913902526\x00");
        expected.extend_from_slice("aa".repeat(32).as_bytes());
        expected.push(0);
        expected.extend_from_slice("bb".repeat(32).as_bytes());
        expected.push(0);
        expected.extend_from_slice(b"chal-xyz");
        assert_eq!(msg, expected);
    }

    #[test]
    fn a_genuine_claim_verifies() {
        let sk = root_key();
        let root_pk = sk.verifying_key().to_bytes();
        let custodial = hex::encode([9u8; 32]);
        let chal = challenge::issue(&SERVER_KEY, NOW, 120);
        let sig = sign_claim(&sk, "telegram", "42", &custodial, &chal);
        assert_eq!(
            verify_link_claim(
                &SERVER_KEY,
                "telegram",
                "42",
                &custodial,
                &root_pk,
                &chal,
                &sig,
                NOW + 5
            ),
            Ok(())
        );
    }

    #[test]
    fn a_forged_signature_by_a_different_key_is_refused() {
        let real = root_key();
        let attacker = SigningKey::from_bytes(&[99u8; 32]);
        let root_pk = real.verifying_key().to_bytes();
        let custodial = hex::encode([9u8; 32]);
        let chal = challenge::issue(&SERVER_KEY, NOW, 120);
        // attacker signs, but the claim names the REAL root pk
        let sig = sign_claim(&attacker, "telegram", "42", &custodial, &chal);
        assert_eq!(
            verify_link_claim(
                &SERVER_KEY,
                "telegram",
                "42",
                &custodial,
                &root_pk,
                &chal,
                &sig,
                NOW + 5
            ),
            Err(LinkClaimError::BadSignature)
        );
    }

    #[test]
    fn a_cross_platform_splice_is_refused() {
        // A claim signed FOR discord replayed as a telegram claim → the message differs → refused.
        let sk = root_key();
        let root_pk = sk.verifying_key().to_bytes();
        let custodial = hex::encode([9u8; 32]);
        let chal = challenge::issue(&SERVER_KEY, NOW, 120);
        let sig_for_discord = sign_claim(&sk, "discord", "42", &custodial, &chal);
        assert_eq!(
            verify_link_claim(
                &SERVER_KEY,
                "telegram",
                "42",
                &custodial,
                &root_pk,
                &chal,
                &sig_for_discord,
                NOW + 5
            ),
            Err(LinkClaimError::BadSignature)
        );
    }

    #[test]
    fn a_tampered_uid_is_refused() {
        let sk = root_key();
        let root_pk = sk.verifying_key().to_bytes();
        let custodial = hex::encode([9u8; 32]);
        let chal = challenge::issue(&SERVER_KEY, NOW, 120);
        let sig = sign_claim(&sk, "telegram", "42", &custodial, &chal);
        // verify with a different uid than was signed
        assert_eq!(
            verify_link_claim(
                &SERVER_KEY,
                "telegram",
                "99",
                &custodial,
                &root_pk,
                &chal,
                &sig,
                NOW + 5
            ),
            Err(LinkClaimError::BadSignature)
        );
    }

    #[test]
    fn a_stale_challenge_is_refused_before_any_crypto() {
        let sk = root_key();
        let root_pk = sk.verifying_key().to_bytes();
        let custodial = hex::encode([9u8; 32]);
        let chal = challenge::issue(&SERVER_KEY, NOW, 120);
        let sig = sign_claim(&sk, "telegram", "42", &custodial, &chal);
        // now is well past the 120s TTL
        let r = verify_link_claim(
            &SERVER_KEY,
            "telegram",
            "42",
            &custodial,
            &root_pk,
            &chal,
            &sig,
            NOW + 10_000,
        );
        assert!(matches!(r, Err(LinkClaimError::StaleChallenge(_))));
    }

    #[test]
    fn a_nul_in_a_field_is_refused() {
        assert_eq!(
            link_claim_message("tele\0gram", "42", "aa", "bb", "c"),
            Err(LinkClaimError::FieldContainsNul)
        );
    }
}
