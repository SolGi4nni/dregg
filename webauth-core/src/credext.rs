//! `credext` — the forward-auth reads and proof-of-possession verbs over the
//! real `dga1_` [`Credential`], ported from the prior operated layer.
//!
//! Everything here is derived from `dregg_agent::cred`'s public surface
//! (`verify`, the canonical wire form) — no parallel implementation of the
//! chain or its digests. The native credential already carries `tail_hex` and
//! `first_attr` as inherent methods; this module adds the four the web edge
//! still needs:
//!
//! - [`CredentialExt::is_expired`] — the 401-vs-403 expiry probe;
//! - [`CredentialExt::verify_chain`] — chain-only genuineness (the login gate);
//! - [`CredentialExt::proof_public`] / [`CredentialExt::sign_challenge`] — the
//!   bearer-tail-key proof-of-possession pair, with [`verify_pop`] the server
//!   side.
//!
//! The named parent-crate ask stands: `dregg_agent::cred` exposing
//! `proof_public()` / `sign_challenge()` / a public caveat iterator would let
//! the wire round-trip below be deleted.

use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::Deserialize;

use dregg_agent::cred::{
    CREDENTIAL_PREFIX, Caveat, Context, Credential, KeyError, Pred, PublicKey, Refusal,
};

/// The forward-auth reads and PoP verbs over the real [`Credential`].
pub trait CredentialExt {
    /// Is this credential expired at wall-clock `now`? True iff any
    /// first-party `NotAfter { at }` (or a `Within` upper bound) it carries is
    /// already past. Used at the auth edge to distinguish an EXPIRED-but-genuine
    /// session (→ 401, re-login) from a genuine session that merely lacks the
    /// surface's cap (→ 403).
    fn is_expired(&self, now: u64) -> bool;

    /// Verify ONLY the ed25519 signature chain + the proof-of-possession, with
    /// NO caveat evaluation — establishes "this is a genuine, untampered
    /// credential issued by `root`, and the presenter holds its bearer tail
    /// key" independent of any per-surface context.
    ///
    /// The **login gate** rides this: at login the target surface (and thus
    /// its required capability) is not yet known, so login proves genuine
    /// issuance + possession here, and the per-surface caveat meet is then
    /// enforced on every auth check by [`Credential::verify`].
    fn verify_chain(&self, root: &PublicKey) -> Result<(), Refusal>;

    /// The public half of the credential's **bearer tail key** — the key a
    /// [`Credential::attenuate`] would sign the next block under, and the key
    /// a holder proves possession of by signing a login challenge
    /// ([`CredentialExt::sign_challenge`] / [`verify_pop`]).
    fn proof_public(&self) -> [u8; 32];

    /// Sign an opaque login challenge with the bearer tail key — the client
    /// side of the proof-of-possession handshake. The verifier checks it with
    /// [`verify_pop`] against [`CredentialExt::proof_public`].
    fn sign_challenge(&self, msg: &[u8]) -> [u8; 64];
}

impl CredentialExt for Credential {
    fn is_expired(&self, now: u64) -> bool {
        for caveat in wire_caveats(self) {
            if let Caveat::FirstParty(p) = caveat {
                match p {
                    Pred::NotAfter { at } if now > at => return true,
                    Pred::Within { not_after, .. } if now > not_after => return true,
                    _ => {}
                }
            }
        }
        false
    }

    fn verify_chain(&self, root: &PublicKey) -> Result<(), Refusal> {
        // `Credential::verify` checks proof-of-possession and the ed25519
        // block chain strictly BEFORE any caveat evaluation, so probing with
        // an empty context isolates the chain verdict exactly: a chain-class
        // refusal is decisive, and a caveat/discharge refusal can only arise
        // once the chain has already verified.
        match self.verify(root, &Context::new()) {
            Err(
                chain @ (Refusal::ProofMismatch
                | Refusal::BadSignature { .. }
                | Refusal::MalformedKey { .. }),
            ) => Err(chain),
            _ => Ok(()),
        }
    }

    fn proof_public(&self) -> [u8; 32] {
        bearer_key(self).verifying_key().to_bytes()
    }

    fn sign_challenge(&self, msg: &[u8]) -> [u8; 64] {
        bearer_key(self).sign(msg).to_bytes()
    }
}

// ---------------------------------------------------------------------------
// The bearer tail key + caveats, read back from the crate's own canonical wire
// form.
//
// A `dga1_` credential is a BEARER token: the encoded form carries the tail
// (proof-of-possession / attenuation) key seed and every block's caveats.
// `dregg_agent::cred` does not (yet) expose the tail key or a public caveat
// iterator on the in-memory `Credential`, so the verbs above round-trip through
// `Credential::encode` — the crate's own canonical serialization — and read the
// v1 schema (`CredentialWire { nonce, blocks[{caveats, next_pub, sig}],
// proof_seed }`, whose field/variant order is the load-bearing postcard layout
// shared with breadstuffs `dregg-auth`). This is the ONE piece of wire-schema
// knowledge kept locally.
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
#[allow(dead_code)] // postcard is positional: leading fields must parse to reach the rest
struct BearerBlockWire {
    caveats: Vec<Caveat>,
    next_pub: [u8; 32],
    sig: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(dead_code)]
struct BearerWire {
    nonce: [u8; 32],
    blocks: Vec<BearerBlockWire>,
    proof_seed: [u8; 32],
}

fn wire(cred: &Credential) -> BearerWire {
    let enc = cred.encode();
    let body = enc
        .strip_prefix(CREDENTIAL_PREFIX)
        .expect("encode always emits the dga1_ prefix");
    let bytes = URL_SAFE_NO_PAD
        .decode(body)
        .expect("encode always emits base64url");
    postcard::from_bytes(&bytes).expect("encode always emits the v1 schema")
}

fn bearer_key(cred: &Credential) -> SigningKey {
    SigningKey::from_bytes(&wire(cred).proof_seed)
}

/// Every caveat across all blocks, in block order (the expiry scan).
fn wire_caveats(cred: &Credential) -> Vec<Caveat> {
    wire(cred)
        .blocks
        .into_iter()
        .flat_map(|b| b.caveats)
        .collect()
}

/// Verify a proof-of-possession signature: does `sig` over `msg` verify under
/// the ed25519 public key `pubkey`? The server side of the login handshake —
/// `pubkey` is the presented credential's [`CredentialExt::proof_public`],
/// `msg` is the domain-tagged login challenge. Fail-closed: a malformed
/// key/sig is `false`.
pub fn verify_pop(pubkey: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
    match VerifyingKey::from_bytes(pubkey) {
        Ok(vk) => vk.verify(msg, &Signature::from_bytes(sig)).is_ok(),
        Err(_) => false,
    }
}

// ===========================================================================
// Small hex helpers (display/config plumbing; the credential parsers are
// dregg-agent's)
// ===========================================================================

/// Lowercase hex of arbitrary bytes.
pub fn hex(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

/// Parse exactly 64 hex chars into 32 bytes.
pub fn unhex32(s: &str) -> Result<[u8; 32], KeyError> {
    let s = s.trim();
    if s.len() != 64 || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(KeyError("expected 64 hex chars".to_string()));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = (chunk[0] as char).to_digit(16).unwrap() as u8;
        let lo = (chunk[1] as char).to_digit(16).unwrap() as u8;
        out[i] = (hi << 4) | lo;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::cred::RootKey;

    #[test]
    fn expiry_reads_the_wire_caveats() {
        let root = RootKey::from_seed([1u8; 32]);
        let cred = root.mint([Caveat::FirstParty(Pred::NotAfter { at: 1_000 })]);
        assert!(!cred.is_expired(999));
        assert!(cred.is_expired(1_001));
        // An attenuated tighter expiry also reads (caveats across ALL blocks).
        let tight = cred.attenuate([Caveat::FirstParty(Pred::NotAfter { at: 500 })]);
        assert!(tight.is_expired(501));
    }

    #[test]
    fn verify_chain_isolates_genuineness_from_caveats() {
        let root = RootKey::from_seed([2u8; 32]);
        let attacker = RootKey::from_seed([3u8; 32]);
        // A credential with an (unsatisfiable-here) caveat still chain-verifies…
        let cred = root.mint([Caveat::FirstParty(Pred::AttrEq {
            key: "cap".into(),
            value: "ops-admin".into(),
        })]);
        assert!(cred.verify_chain(&root.public()).is_ok());
        // …but not under the wrong root.
        assert!(cred.verify_chain(&attacker.public()).is_err());
    }

    #[test]
    fn pop_round_trips_and_fails_closed() {
        let root = RootKey::from_seed([4u8; 32]);
        let cred = root.mint([]);
        let msg = b"login challenge bytes";
        let sig = cred.sign_challenge(msg);
        assert!(verify_pop(&cred.proof_public(), msg, &sig));
        // Wrong message / wrong key → refused.
        assert!(!verify_pop(&cred.proof_public(), b"other", &sig));
        let other = root.mint([]);
        assert!(!verify_pop(&other.proof_public(), msg, &sig));
    }

    #[test]
    fn hex_round_trips() {
        let bytes = [0xABu8; 32];
        assert_eq!(unhex32(&hex(&bytes)).unwrap(), bytes);
        assert!(unhex32("zz").is_err());
    }
}
