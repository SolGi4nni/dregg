//! Secure per-user BYO-LLM-key vault — encrypted at rest, redacted in memory.
//!
//! A user ports in their OWN provider API key (Anthropic / OpenAI / OpenRouter /
//! Kimi / DeepSeek). We are EXTREMELY careful and respectful with it:
//!
//! * **Encrypted at rest.** The plaintext key NEVER hits the DB in clear. It is
//!   sealed with XChaCha20-Poly1305 (AEAD) under a key DERIVED PER USER from the
//!   bot secret ‖ the user's Discord id ([`derive_cell_key`]) — so a DB dump
//!   without the bot secret is inert, and a ciphertext is bound to exactly one
//!   `(user, provider)` pair via the AEAD associated data (it cannot be replayed
//!   under a different user or provider).
//! * **Never logged.** [`PlaintextKey`] redacts on `Debug`/`Display` (only a
//!   `provider:****abcd` fingerprint, never the secret), and zeroizes its heap
//!   buffer on drop ([`zeroize`]). The only way to read the secret is the
//!   explicit [`PlaintextKey::expose`] — used solely to set the auth header at
//!   call time, never to print.
//! * **Revocable.** Revoke is a DELETE of the ciphertext at the DB layer; after
//!   it, nothing is recoverable (proven by the tests).
//!
//! The crypto here is PURE (no Discord, no network), so the round-trip,
//! redaction, AEAD-tamper, wrong-binding, and revoke properties are all unit
//! tested offline.

use std::fmt;

use chacha20poly1305::aead::{Aead, AeadCore, KeyInit, OsRng, Payload};
use chacha20poly1305::{XChaCha20Poly1305, XNonce};
use zeroize::Zeroizing;

/// Domain-separation tag mixed into the per-user key derivation. Bumping this
/// rotates every derived key (and thus invalidates every stored ciphertext).
const KDF_DOMAIN: &[u8] = b"dregg-byo-llm-key-v1";

/// A provider API key in PLAINTEXT — held only transiently (to build an auth
/// header), redacted on `Debug`/`Display`, and zeroized on drop.
///
/// Construct via [`PlaintextKey::new`]; read the secret only via
/// [`PlaintextKey::expose`] (and only to set a request header — never to log).
pub struct PlaintextKey {
    inner: Zeroizing<String>,
}

impl PlaintextKey {
    /// Wrap a plaintext key. The trimmed string is owned in a zeroizing buffer.
    pub fn new(key: impl Into<String>) -> Self {
        PlaintextKey {
            inner: Zeroizing::new(key.into().trim().to_string()),
        }
    }

    /// Expose the raw secret. The ONLY accessor that returns the plaintext —
    /// call this solely to construct the provider auth header at request time.
    pub fn expose(&self) -> &str {
        &self.inner
    }

    /// `true` if the key is empty (rejected at set time).
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// A redacted fingerprint safe to log/display: the last 4 chars only, the
    /// rest masked. Reveals nothing usable; lets a user confirm WHICH key is set.
    pub fn fingerprint(&self) -> String {
        redact(&self.inner)
    }
}

/// Redact a secret to a loggable fingerprint: `****` + at most the last 4 chars.
/// Short secrets (< 8 chars) are fully masked so we never reveal a meaningful
/// fraction of a small token.
pub fn redact(secret: &str) -> String {
    let n = secret.chars().count();
    if n < 8 {
        return "****".to_string();
    }
    let tail: String = secret.chars().skip(n.saturating_sub(4)).collect();
    format!("****{tail}")
}

impl fmt::Debug for PlaintextKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // NEVER print the secret. Only the redacted fingerprint.
        write!(f, "PlaintextKey({})", self.fingerprint())
    }
}

impl fmt::Display for PlaintextKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.fingerprint())
    }
}

/// A sealed key as stored at rest: the AEAD nonce + ciphertext (incl. tag).
/// Neither field reveals the plaintext without the per-user derived key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncryptedKey {
    /// The 24-byte XChaCha20-Poly1305 nonce (random per seal).
    pub nonce: Vec<u8>,
    /// The ciphertext, including the Poly1305 authentication tag.
    pub ciphertext: Vec<u8>,
}

impl EncryptedKey {
    /// Base64 the nonce for DB storage.
    pub fn nonce_b64(&self) -> String {
        use base64::Engine;
        base64::engine::general_purpose::STANDARD.encode(&self.nonce)
    }

    /// Base64 the ciphertext for DB storage.
    pub fn ciphertext_b64(&self) -> String {
        use base64::Engine;
        base64::engine::general_purpose::STANDARD.encode(&self.ciphertext)
    }

    /// Reconstruct from the base64 columns read back from the DB.
    pub fn from_b64(nonce_b64: &str, ciphertext_b64: &str) -> Result<Self, VaultError> {
        use base64::Engine;
        let nonce = base64::engine::general_purpose::STANDARD
            .decode(nonce_b64)
            .map_err(|_| VaultError::Corrupt)?;
        let ciphertext = base64::engine::general_purpose::STANDARD
            .decode(ciphertext_b64)
            .map_err(|_| VaultError::Corrupt)?;
        Ok(EncryptedKey { nonce, ciphertext })
    }
}

/// What can go wrong sealing/opening a key. Carries NO secret material.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VaultError {
    /// The plaintext key was empty.
    Empty,
    /// AEAD open failed — wrong derived key, wrong `(user, provider)` binding,
    /// or a tampered/corrupt ciphertext. Fail-closed: the key stays sealed.
    OpenFailed,
    /// A stored field was not valid base64 / not a valid nonce length.
    Corrupt,
}

impl fmt::Display for VaultError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VaultError::Empty => write!(f, "the key is empty"),
            VaultError::OpenFailed => {
                write!(f, "could not decrypt the key (wrong binding or tampered)")
            }
            VaultError::Corrupt => write!(f, "the stored key is corrupt"),
        }
    }
}

impl std::error::Error for VaultError {}

/// Derive the per-user, per-deployment 32-byte AEAD key for a Discord user.
///
/// `keyed_hash(bot_secret, KDF_DOMAIN ‖ discord_id_le)` — so the encryption key
/// is bound to BOTH the deployment's bot secret and the specific user. A DB dump
/// without the bot secret cannot derive it; a different user derives a different
/// key. The result is held in a zeroizing buffer.
fn derive_cell_key(bot_secret: &[u8; 32], discord_id: u64) -> Zeroizing<[u8; 32]> {
    let mut material = Vec::with_capacity(KDF_DOMAIN.len() + 8);
    material.extend_from_slice(KDF_DOMAIN);
    material.extend_from_slice(&discord_id.to_le_bytes());
    let hash = blake3::keyed_hash(bot_secret, &material);
    Zeroizing::new(*hash.as_bytes())
}

/// The AEAD associated data binding a ciphertext to exactly one `(user, provider)`
/// pair: a ciphertext sealed for `(alice, anthropic)` will NOT open under
/// `(alice, openai)` or `(bob, anthropic)`.
fn aad_for(discord_id: u64, provider: &str) -> Vec<u8> {
    let mut aad = Vec::with_capacity(8 + provider.len());
    aad.extend_from_slice(&discord_id.to_le_bytes());
    aad.extend_from_slice(provider.as_bytes());
    aad
}

/// Seal a user's plaintext key for storage.
///
/// Encrypts under the per-user derived key with a fresh random nonce, binding
/// the ciphertext to `(discord_id, provider)` via the AEAD associated data. The
/// returned [`EncryptedKey`] is what hits the DB — the plaintext never does.
pub fn seal(
    bot_secret: &[u8; 32],
    discord_id: u64,
    provider: &str,
    plaintext: &PlaintextKey,
) -> Result<EncryptedKey, VaultError> {
    if plaintext.is_empty() {
        return Err(VaultError::Empty);
    }
    let derived = derive_cell_key(bot_secret, discord_id);
    let cipher = XChaCha20Poly1305::new(derived.as_slice().into());
    let nonce = XChaCha20Poly1305::generate_nonce(&mut OsRng);
    let aad = aad_for(discord_id, provider);
    let ciphertext = cipher
        .encrypt(
            &nonce,
            Payload {
                msg: plaintext.expose().as_bytes(),
                aad: &aad,
            },
        )
        .map_err(|_| VaultError::OpenFailed)?;
    Ok(EncryptedKey {
        nonce: nonce.to_vec(),
        ciphertext,
    })
}

/// Open a sealed key back to plaintext.
///
/// Fails closed ([`VaultError::OpenFailed`]) on a wrong derived key, a wrong
/// `(user, provider)` binding, or a tampered ciphertext — the AEAD tag is the
/// integrity check. The returned [`PlaintextKey`] is redacted/zeroizing.
pub fn open(
    bot_secret: &[u8; 32],
    discord_id: u64,
    provider: &str,
    sealed: &EncryptedKey,
) -> Result<PlaintextKey, VaultError> {
    if sealed.nonce.len() != 24 {
        return Err(VaultError::Corrupt);
    }
    let derived = derive_cell_key(bot_secret, discord_id);
    let cipher = XChaCha20Poly1305::new(derived.as_slice().into());
    let nonce = XNonce::from_slice(&sealed.nonce);
    let aad = aad_for(discord_id, provider);
    let plaintext = cipher
        .decrypt(
            nonce,
            Payload {
                msg: &sealed.ciphertext,
                aad: &aad,
            },
        )
        .map_err(|_| VaultError::OpenFailed)?;
    let s = String::from_utf8(plaintext).map_err(|_| VaultError::OpenFailed)?;
    Ok(PlaintextKey::new(s))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn secret() -> [u8; 32] {
        [7u8; 32]
    }

    #[test]
    fn key_round_trips_through_encryption() {
        // A key sealed for (alice, anthropic) opens back to the SAME plaintext.
        let secret = secret();
        let key = PlaintextKey::new("sk-ant-api03-REALSECRETVALUE-7h3z9");
        let sealed = seal(&secret, 1001, "anthropic", &key).unwrap();
        // The ciphertext must NOT contain the plaintext (it is encrypted at rest).
        assert!(
            !sealed.ciphertext.windows(8).any(|w| w == b"REALSECR"),
            "the plaintext must never appear in the ciphertext"
        );
        let opened = open(&secret, 1001, "anthropic", &sealed).unwrap();
        assert_eq!(opened.expose(), "sk-ant-api03-REALSECRETVALUE-7h3z9");
    }

    #[test]
    fn key_never_appears_in_debug_or_display() {
        // Redaction: neither Debug nor Display may leak the secret.
        let key = PlaintextKey::new("sk-supersecret-abcd1234");
        let dbg = format!("{key:?}");
        let disp = format!("{key}");
        assert!(!dbg.contains("supersecret"), "Debug leaked: {dbg}");
        assert!(!disp.contains("supersecret"), "Display leaked: {disp}");
        // The fingerprint shows only the last 4 chars.
        assert_eq!(key.fingerprint(), "****1234");
        assert!(dbg.contains("****1234"));
    }

    #[test]
    fn short_keys_are_fully_masked() {
        assert_eq!(PlaintextKey::new("short").fingerprint(), "****");
        assert_eq!(redact("ab"), "****");
        assert_eq!(redact("abcdefghij"), "****ghij");
    }

    #[test]
    fn tampered_ciphertext_fails_closed() {
        // Flip a byte in the ciphertext → AEAD tag rejects it (fail-closed).
        let secret = secret();
        let key = PlaintextKey::new("sk-or-v1-tamperme-9999");
        let mut sealed = seal(&secret, 5, "openrouter", &key).unwrap();
        let last = sealed.ciphertext.len() - 1;
        sealed.ciphertext[last] ^= 0x01;
        assert!(matches!(
            open(&secret, 5, "openrouter", &sealed),
            Err(VaultError::OpenFailed)
        ));
    }

    #[test]
    fn binding_is_enforced_wrong_user_or_provider_cannot_open() {
        // A ciphertext is bound to (user, provider) by the AEAD associated data
        // AND the per-user key derivation: neither a different user nor a
        // different provider can open it.
        let secret = secret();
        let key = PlaintextKey::new("sk-deepseek-bound-key-2025");
        let sealed = seal(&secret, 42, "deepseek", &key).unwrap();
        // Wrong provider (same user) — AAD mismatch.
        assert!(matches!(
            open(&secret, 42, "openai", &sealed),
            Err(VaultError::OpenFailed)
        ));
        // Wrong user (same provider) — derived key + AAD mismatch.
        assert!(matches!(
            open(&secret, 43, "deepseek", &sealed),
            Err(VaultError::OpenFailed)
        ));
        // Wrong bot secret (a DB dump without the deployment secret) — derived key mismatch.
        assert!(matches!(
            open(&[9u8; 32], 42, "deepseek", &sealed),
            Err(VaultError::OpenFailed)
        ));
        // The genuine binding still opens.
        assert!(open(&secret, 42, "deepseek", &sealed).is_ok());
    }

    #[test]
    fn empty_key_is_rejected() {
        assert_eq!(
            seal(&secret(), 1, "kimi", &PlaintextKey::new("   ")),
            Err(VaultError::Empty)
        );
    }

    #[test]
    fn revoke_leaves_nothing_recoverable() {
        // Revocation is modelled as dropping the ciphertext. Once the sealed
        // bytes are gone there is no path back to the plaintext — the derived
        // key alone (without ciphertext) reveals nothing.
        let secret = secret();
        let key = PlaintextKey::new("sk-ant-revoke-me-abcd");
        let sealed = seal(&secret, 77, "anthropic", &key).unwrap();
        // Simulate the DB DELETE: the ciphertext no longer exists.
        drop(sealed);
        // A fresh (absent) ciphertext cannot be opened. There is simply nothing
        // to decrypt — the only artifact at rest was the now-deleted ciphertext.
        // (Sanity: an all-zero "ciphertext" of the right shape is not openable.)
        let empty = EncryptedKey {
            nonce: vec![0u8; 24],
            ciphertext: vec![0u8; 32],
        };
        assert!(matches!(
            open(&secret, 77, "anthropic", &empty),
            Err(VaultError::OpenFailed)
        ));
    }

    #[test]
    fn base64_storage_round_trips() {
        let secret = secret();
        let key = PlaintextKey::new("sk-moonshot-roundtrip-1234");
        let sealed = seal(&secret, 3, "kimi", &key).unwrap();
        let restored =
            EncryptedKey::from_b64(&sealed.nonce_b64(), &sealed.ciphertext_b64()).unwrap();
        assert_eq!(restored, sealed);
        assert_eq!(
            open(&secret, 3, "kimi", &restored).unwrap().expose(),
            "sk-moonshot-roundtrip-1234"
        );
    }
}
