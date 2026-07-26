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

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

use crate::challenge::{self, ChallengeError};

/// The domain-separation prefix of the link-claim canonical message. PINNED: changing it rotates
/// every claim ever signed. Distinct from the offering-turn domain (`dregg-offering-turn-v1:`) so
/// a link claim can never be replayed as a turn or vice versa.
pub const LINK_CLAIM_DOMAIN: &str = "dregg-identity-link-v1:";

// ─────────────────────────────────────────────────────────────────────────────
// THE PHRASE-LINK CEREMONY: the shared half of "a web player and a Discord player are one human".
//
// The pre-existing `/tg/link` + `/da/link` ceremonies hold root key K in the BROWSER (WebAuthn-PRF
// or a PBKDF2-wrapped blob in `localStorage`). A player whose root key is 24 BIP39 words
// (`dreggnet-web`'s `seed_identity`) has no such blob: their key exists only while the phrase is in
// hand. That player needs a ceremony whose signing step can happen inside ONE request — which means
// the platform's half of the proof has to arrive as a PASTEABLE, self-authenticating code rather
// than as a live platform-authenticated session.
//
// The three functions below are that code's whole trust story, and they live HERE rather than in
// either frontend for the reason `dreggnet-discord-identity` exists: the issuer (a Discord slash
// command, in the excluded `discord-bot` workspace) and the verifier (`dreggnet-web`) are separate
// processes, and a MIRRORED key derivation is the drift class. ONE impl, two callers.
// ─────────────────────────────────────────────────────────────────────────────

/// The BLAKE3 `derive_key` domain of the phrase-link challenge key.
///
/// ⚑ DELIBERATELY a THIRD domain, distinct from both existing link-challenge keys —
/// `discord-bot`'s `"dregg-discord-link-challenge-v1"` (the `/link-cipherclerk` → `/link-prove`
/// external-cell ceremony) and `dreggnet-web`'s `"dregg-discord-link-claim-v1"` (the ticket-gated
/// `/da/link` ceremony). A code minted for THIS ceremony must not verify in either of those, and
/// theirs must not verify here: the three prove different things about who is present.
pub const PHRASE_LINK_KEY_DOMAIN: &str = "dregg-web-phrase-link-v1";

/// The domain tag mixed into [`account_challenge_key`], so the per-account key can never collide
/// with any other keyed hash taken under the same base key.
const ACCOUNT_CHALLENGE_DOMAIN: &[u8] = b"dregg-phrase-link-account-v1:";

/// **How long a phrase-link code is good for: 15 minutes.** ONE value with three readers — the bot
/// that mints (`discord-bot`'s `/identity link-web`), the web page that tells the player the window,
/// and the tests. Kept here rather than once per side, because a page promising a window its issuer
/// does not honour is exactly the kind of quiet lie a second constant produces.
///
/// Sized on what the ceremony actually costs: switch apps, find a piece of paper, type 24 words.
/// Matches `/link-cipherclerk`'s existing window.
pub const PHRASE_LINK_CODE_TTL_SECS: u64 = 900;

/// The separator between the platform uid and the challenge in a link code
/// ([`format_link_code`]). `:` appears in NEITHER half — a uid is decimal, and a
/// [`crate::challenge`] string is `base64url` (`A–Z a–z 0–9 - _`) `.` `hex` — so splitting on the
/// FIRST `:` is unambiguous by construction.
pub const LINK_CODE_SEP: char = ':';

/// **The base phrase-link challenge key for a platform's identity master secret** —
/// `BLAKE3_derive_key(`[`PHRASE_LINK_KEY_DOMAIN`]`, bot_secret)`.
///
/// Only a holder of the platform's `bot_secret` can mint a code that verifies under this, which is
/// what makes the pasted code an assertion BY THE BOT rather than by the person pasting it.
pub fn phrase_link_challenge_key(bot_secret: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key(PHRASE_LINK_KEY_DOMAIN, bot_secret)
}

/// **Bind a platform account INTO the challenge key** — `blake3_keyed(base,
/// ACCOUNT_CHALLENGE_DOMAIN ‖ platform ‖ 0 ‖ platform_uid)`.
///
/// ⚑ THIS IS WHY THE PASTED UID IS NOT MERELY ASSERTED. [`crate::challenge`]'s envelope is a fixed
/// `nonce(16) ‖ exp(8)`, so it has nowhere to carry a uid — and a uid the player simply types
/// alongside the challenge would let anyone claim anyone's account. Deriving a DISTINCT server key
/// per `(platform, uid)` moves the binding into the key: a code minted for uid `A` fails
/// [`challenge::verify`] the instant the verifier recomputes the key with uid `B`
/// ([`ChallengeError::BadTag`]). The verifier therefore never trusts the pasted uid — it *tests* it.
///
/// The custodial pubkey is deliberately NOT in this key: the verifier DERIVES it from the uid with
/// the same `seed_for` the bot uses, so there is nothing for a caller to lie about.
pub fn account_challenge_key(base: &[u8; 32], platform: &str, platform_uid: &str) -> [u8; 32] {
    let mut input = Vec::with_capacity(
        ACCOUNT_CHALLENGE_DOMAIN.len() + platform.len() + platform_uid.len() + 1,
    );
    input.extend_from_slice(ACCOUNT_CHALLENGE_DOMAIN);
    input.extend_from_slice(platform.as_bytes());
    input.push(0);
    input.extend_from_slice(platform_uid.as_bytes());
    *blake3::keyed_hash(base, &input).as_bytes()
}

/// Render the pasteable link code a platform hands its user: `<platform_uid>:<challenge>`.
///
/// `None` if `platform_uid` itself carries the separator (it never does — uids are decimal), so the
/// encoding is injective and [`parse_link_code`] cannot mis-split.
pub fn format_link_code(platform_uid: &str, challenge: &str) -> Option<String> {
    if platform_uid.contains(LINK_CODE_SEP) || platform_uid.is_empty() {
        return None;
    }
    Some(format!("{platform_uid}{LINK_CODE_SEP}{challenge}"))
}

/// Split a pasted link code into `(platform_uid, challenge)`. Splits on the FIRST
/// [`LINK_CODE_SEP`], surrounding whitespace trimmed (a code copied out of a chat client arrives
/// with newlines). `None` for anything without both halves non-empty.
///
/// This parse is NOT a gate: it authenticates nothing. Both halves are checked by
/// [`challenge::verify`] under [`account_challenge_key`], which is where a wrong uid dies.
pub fn parse_link_code(code: &str) -> Option<(&str, &str)> {
    let (uid, challenge) = code.trim().split_once(LINK_CODE_SEP)?;
    let uid = uid.trim();
    let challenge = challenge.trim();
    if uid.is_empty() || challenge.is_empty() {
        return None;
    }
    Some((uid, challenge))
}

/// **Mint the pasteable link code for a platform account** — the ISSUER half of the phrase-link
/// ceremony, and the only place a code is produced.
///
/// It lives HERE rather than beside either caller because the issuer and the verifier are different
/// processes in different workspaces: `discord-bot` (excluded workspace, has `webauth-core` and NOT
/// `dreggnet-web`) mints, and `dreggnet-web` verifies. A key derivation copied into both is the drift
/// class `dreggnet-discord-identity` exists to prevent — so both call this.
///
/// `now` and `ttl_secs` are the caller's (the issuing process owns its clock). `None` only if
/// `platform_uid` is empty or carries [`LINK_CODE_SEP`], which no real platform uid does.
pub fn mint_phrase_link_code(
    bot_secret: &[u8; 32],
    platform: &str,
    platform_uid: &str,
    now: u64,
    ttl_secs: u64,
) -> Option<String> {
    let key = account_challenge_key(
        &phrase_link_challenge_key(bot_secret),
        platform,
        platform_uid,
    );
    format_link_code(platform_uid, &challenge::issue(&key, now, ttl_secs))
}

/// **Sign a link claim with a root key held as a 32-byte Ed25519 seed** — the client half of
/// [`verify_link_claim`], and the ONLY place in the tree that produces a link-claim signature
/// server-side.
///
/// Returns `(root_pubkey, signature)`. The message is built by [`link_claim_message`] over the
/// CANONICAL hex of the derived public key, which is exactly the string
/// [`verify_link_claim`] rebuilds — so signer and verifier cannot diverge: they are the same
/// function called twice. (The `sign_claim` helper in this module's tests was previously the only
/// signer, i.e. the signing half existed only in test code.)
///
/// The caller owns the seed's lifetime and should wrap it in `Zeroizing`; nothing is retained here.
pub fn sign_link_claim(
    root_seed: &[u8; 32],
    platform: &str,
    platform_uid: &str,
    custodial_pubkey_hex: &str,
    challenge: &str,
) -> Result<([u8; 32], [u8; 64]), LinkClaimError> {
    let sk = SigningKey::from_bytes(root_seed);
    let root_pubkey = sk.verifying_key().to_bytes();
    let msg = link_claim_message(
        platform,
        platform_uid,
        custodial_pubkey_hex,
        &hex::encode(root_pubkey),
        challenge,
    )?;
    Ok((root_pubkey, sk.sign(&msg).to_bytes()))
}

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

    // ─────────────────────────────────────────────────────────────────────────
    // The phrase-link ceremony.
    // ─────────────────────────────────────────────────────────────────────────

    const BOT_SECRET: [u8; 32] = [0x5au8; 32];

    /// [`sign_link_claim`] and [`verify_link_claim`] are one function called twice: a claim signed
    /// by the seed verifies under the pubkey the signer derived, with NO hex threaded by hand.
    #[test]
    fn a_claim_signed_from_a_seed_verifies_under_its_own_derived_root() {
        let seed = [0x11u8; 32];
        let custodial = hex::encode([9u8; 32]);
        let base = phrase_link_challenge_key(&BOT_SECRET);
        let key = account_challenge_key(&base, "discord", "6913902526");
        let chal = challenge::issue(&key, NOW, 900);
        let (root, sig) =
            sign_link_claim(&seed, "discord", "6913902526", &custodial, &chal).expect("signs");
        assert_eq!(
            root,
            SigningKey::from_bytes(&seed).verifying_key().to_bytes(),
            "the returned root pubkey IS the seed's own public key"
        );
        assert_eq!(
            verify_link_claim(
                &key,
                "discord",
                "6913902526",
                &custodial,
                &root,
                &chal,
                &sig,
                NOW + 30
            ),
            Ok(())
        );
    }

    /// ⚑ THE UID TOOTH. The pasted uid is not merely asserted: a code minted for uid A does not
    /// verify when the verifier recomputes the challenge key for uid B, so a player cannot paste
    /// somebody else's account id and be linked to it. Refused at the CHALLENGE gate — before any
    /// signature is even considered.
    #[test]
    fn a_code_minted_for_one_uid_does_not_verify_for_another() {
        let seed = [0x22u8; 32];
        let custodial = hex::encode([7u8; 32]);
        let base = phrase_link_challenge_key(&BOT_SECRET);
        let victim_key = account_challenge_key(&base, "discord", "111");
        let chal = challenge::issue(&victim_key, NOW, 900);

        // The attacker holds a genuine code for uid 111 and re-presents it as uid 222, signing the
        // 222 claim correctly with their OWN root key. The verifier derives the 222 key.
        let (root, sig) =
            sign_link_claim(&seed, "discord", "222", &custodial, &chal).expect("signs");
        let attacker_key = account_challenge_key(&base, "discord", "222");
        assert!(matches!(
            verify_link_claim(
                &attacker_key,
                "discord",
                "222",
                &custodial,
                &root,
                &chal,
                &sig,
                NOW + 30
            ),
            Err(LinkClaimError::StaleChallenge(ChallengeError::BadTag))
        ));
        // NON-VACUOUS: the same code with the SAME uid it was minted for still works.
        let (root2, sig2) =
            sign_link_claim(&seed, "discord", "111", &custodial, &chal).expect("signs");
        assert_eq!(
            verify_link_claim(
                &victim_key,
                "discord",
                "111",
                &custodial,
                &root2,
                &chal,
                &sig2,
                NOW + 30
            ),
            Ok(())
        );
    }

    /// A code minted for one PLATFORM does not verify as another (`discord` ↛ `telegram`), even for
    /// the same uid string — the platform is in the challenge key as well as in the signed message.
    #[test]
    fn a_code_is_bound_to_its_platform() {
        let base = phrase_link_challenge_key(&BOT_SECRET);
        assert_ne!(
            account_challenge_key(&base, "discord", "5"),
            account_challenge_key(&base, "telegram", "5")
        );
        // …and the `platform ‖ 0 ‖ uid` framing is not splice-able: ("a", "b") ≠ ("ab", "").
        assert_ne!(
            account_challenge_key(&base, "a", "b"),
            account_challenge_key(&base, "ab", "")
        );
    }

    /// The phrase-link key is a THIRD, distinct key: a code from this ceremony must not verify in
    /// either pre-existing link-challenge ceremony, and vice versa.
    #[test]
    fn the_phrase_link_key_is_distinct_from_both_older_link_challenge_keys() {
        let phrase = phrase_link_challenge_key(&BOT_SECRET);
        // `discord-bot`'s `/link-prove` key and `dreggnet-web`'s `/da/link` key, recomputed inline
        // so a drift in either of those constants is caught HERE rather than silently merging keys.
        let discord_bot_key = blake3::derive_key("dregg-discord-link-challenge-v1", &BOT_SECRET);
        let da_link_key = blake3::derive_key("dregg-discord-link-claim-v1", &BOT_SECRET);
        assert_ne!(phrase, discord_bot_key);
        assert_ne!(phrase, da_link_key);
        assert_eq!(PHRASE_LINK_KEY_DOMAIN, "dregg-web-phrase-link-v1");
    }

    /// The code round-trips, splits on the FIRST separator (a challenge's own `.`/`-`/`_` never
    /// confuse it), and survives the newlines a copy out of a chat client brings.
    #[test]
    fn a_link_code_round_trips_through_a_paste() {
        let key = account_challenge_key(&phrase_link_challenge_key(&BOT_SECRET), "discord", "42");
        let chal = challenge::issue(&key, NOW, 900);
        let code = format_link_code("42", &chal).expect("a decimal uid encodes");
        assert_eq!(parse_link_code(&code), Some(("42", chal.as_str())));
        assert_eq!(
            parse_link_code(&format!("  \n{code}\n  ")),
            Some(("42", chal.as_str())),
            "a pasted code arrives with whitespace"
        );
        assert!(!chal.contains(LINK_CODE_SEP), "the challenge is `:`-free");
        // ⚑ THE URL-SAFETY PIN. The bot puts a code into a `?code=` query value with NO
        // percent-encoding, and the web page reads it back and compares it byte-for-byte. Every
        // character a code can contain must therefore be legal, unescaped, in a query value:
        // `base64url` (`A-Za-z0-9-_`), `.`, decimal digits, and the `:` separator — all unreserved or
        // sub-delims per RFC 3986. A code carrying anything else would arrive mangled and refuse.
        assert!(
            code.chars().all(|c| c.is_ascii_alphanumeric()
                || c == '-'
                || c == '_'
                || c == '.'
                || c == LINK_CODE_SEP),
            "a code must survive a URL query value unescaped: {code}"
        );
        for junk in ["", "42", "42:", ":abc", "   ", "no-separator-here"] {
            assert_eq!(parse_link_code(junk), None, "accepted junk: {junk:?}");
        }
        assert_eq!(format_link_code("4:2", &chal), None);
        assert_eq!(format_link_code("", &chal), None);
    }
}
