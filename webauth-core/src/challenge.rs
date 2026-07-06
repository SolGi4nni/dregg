// PORTED dregg-native from the prior operated layer (verbatim; hex from credext).

//! The login **challenge** — a stateless, server-authenticated nonce for the
//! proof-of-possession login handshake.
//!
//! ## Why a challenge at all
//!
//! A `dga1_` credential is a bearer token, so *holding the encoded string* is
//! possession. The challenge adds two things a bare paste does not:
//!
//!  1. **Freshness / anti-replay** — the login POST is bound to a server-issued
//!     nonce that expires in ~2 minutes, so a captured `POST /login` body cannot
//!     be replayed later to mint a fresh session.
//!  2. **A clean client contract** — the cipherclerk extension can `GET` a
//!     challenge, `sign` it with the credential's bearer tail key, and `POST`
//!     `{credential, challenge, signature}` — never dumping the raw token into a
//!     form field, and proving *active* possession at login time.
//!
//! ## Stateless construction (no server-side nonce store)
//!
//! The forward-auth service that may run as several replicas and is
//! restarted on redeploy; a server-side nonce table would be a shared-state
//! liability. Instead a challenge is **self-authenticating**:
//!
//! ```text
//! body      = nonce(16) ‖ exp_unix_be(8)
//! challenge = base64url(body) ‖ "." ‖ hex( blake3_keyed(server_key, body) )
//! ```
//!
//! [`verify`] recomputes the keyed BLAKE3 tag under the server key and checks the
//! embedded expiry — so a challenge is accepted iff *this* service (its
//! `server_key`) minted it and it has not expired. No storage, restart-safe
//! within the key's lifetime. The `server_key` is `DREGG_WEBAUTH_CHALLENGE_KEY`
//! (hex) or a per-process random key (a pending challenge simply does not
//! survive a restart, which is fine for a 2-minute window).

use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;

use crate::credext::hex;

/// The domain tag the client signs together with the challenge string. The
/// signed message is `LOGIN_CHALLENGE_CTX ‖ challenge`. Published so the
/// cipherclerk extension (a sibling lane) signs the identical bytes.
pub const LOGIN_CHALLENGE_CTX: &[u8] = b"dregg-webauth login challenge v1";

/// The recommended challenge lifetime: 120 seconds. Long enough for a human to
/// approve a wallet prompt, short enough that a captured challenge is useless.
pub const DEFAULT_CHALLENGE_TTL_SECS: u64 = 120;

/// Why a presented challenge was rejected.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ChallengeError {
    #[error("challenge is malformed (expected `<base64url>.<hex-tag>`)")]
    Malformed,
    #[error("challenge tag does not authenticate under this service's key (forged or foreign)")]
    BadTag,
    #[error("challenge has expired — request a fresh one")]
    Expired,
}

/// Mint a fresh challenge string valid until `now + ttl_secs`, authenticated
/// under `server_key`. `nonce` are 16 random bytes the caller supplies (so the
/// server owns randomness); use [`issue`] for the wall-clock + OS-random path.
pub fn issue_with(server_key: &[u8; 32], nonce: [u8; 16], now: u64, ttl_secs: u64) -> String {
    let exp = now.saturating_add(ttl_secs);
    let mut body = Vec::with_capacity(24);
    body.extend_from_slice(&nonce);
    body.extend_from_slice(&exp.to_be_bytes());
    let tag = blake3::keyed_hash(server_key, &body);
    format!("{}.{}", URL_SAFE_NO_PAD.encode(&body), hex(tag.as_bytes()))
}

/// Mint a fresh challenge from OS randomness at wall-clock `now`.
pub fn issue(server_key: &[u8; 32], now: u64, ttl_secs: u64) -> String {
    let mut nonce = [0u8; 16];
    getrandom::fill(&mut nonce).expect("operating-system randomness is available");
    issue_with(server_key, nonce, now, ttl_secs)
}

/// Verify a challenge string: it must authenticate under `server_key` (the keyed
/// BLAKE3 tag matches) AND not be expired at `now`. Constant-time on the tag.
pub fn verify(server_key: &[u8; 32], challenge: &str, now: u64) -> Result<(), ChallengeError> {
    let (b64, tag_hex) = challenge.split_once('.').ok_or(ChallengeError::Malformed)?;
    let body = URL_SAFE_NO_PAD
        .decode(b64)
        .map_err(|_| ChallengeError::Malformed)?;
    if body.len() != 24 {
        return Err(ChallengeError::Malformed);
    }
    let expect = blake3::keyed_hash(server_key, &body);
    // constant-time compare of the presented hex tag against the recomputed tag
    let presented = hex(expect.as_bytes());
    if !constant_time_eq(presented.as_bytes(), tag_hex.as_bytes()) {
        return Err(ChallengeError::BadTag);
    }
    let mut exp_bytes = [0u8; 8];
    exp_bytes.copy_from_slice(&body[16..24]);
    let exp = u64::from_be_bytes(exp_bytes);
    if now > exp {
        return Err(ChallengeError::Expired);
    }
    Ok(())
}

/// The exact bytes a client signs to prove possession: the domain tag followed
/// by the challenge string. Both server and the cipherclerk extension build the
/// message this way, so signatures agree.
pub fn signing_message(challenge: &str) -> Vec<u8> {
    let mut m = Vec::with_capacity(LOGIN_CHALLENGE_CTX.len() + challenge.len());
    m.extend_from_slice(LOGIN_CHALLENGE_CTX);
    m.extend_from_slice(challenge.as_bytes());
    m
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

    #[test]
    fn issue_then_verify_round_trips() {
        let key = [7u8; 32];
        let c = issue(&key, 1_000, 120);
        assert!(verify(&key, &c, 1_050).is_ok(), "fresh challenge verifies");
    }

    #[test]
    fn expired_challenge_rejected() {
        let key = [8u8; 32];
        let c = issue(&key, 1_000, 120);
        assert_eq!(verify(&key, &c, 1_200), Err(ChallengeError::Expired));
    }

    #[test]
    fn foreign_key_rejected() {
        let key = [9u8; 32];
        let other = [10u8; 32];
        let c = issue(&key, 1_000, 120);
        assert_eq!(verify(&other, &c, 1_050), Err(ChallengeError::BadTag));
    }

    #[test]
    fn tampered_challenge_rejected() {
        let key = [11u8; 32];
        let c = issue_with(&key, [1u8; 16], 1_000, 120);
        // Flip the last hex nibble of the tag.
        let mut bytes: Vec<char> = c.chars().collect();
        let last = bytes.len() - 1;
        bytes[last] = if bytes[last] == 'a' { 'b' } else { 'a' };
        let tampered: String = bytes.into_iter().collect();
        assert!(verify(&key, &tampered, 1_050).is_err());
    }

    #[test]
    fn malformed_challenge_rejected() {
        let key = [12u8; 32];
        assert_eq!(
            verify(&key, "no-dot-here", 1_000),
            Err(ChallengeError::Malformed)
        );
        assert_eq!(
            verify(&key, "not-base64!.deadbeef", 1_000),
            Err(ChallengeError::Malformed)
        );
    }
}
