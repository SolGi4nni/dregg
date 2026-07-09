//! The canonical ML-DSA-65 (FIPS 204) signing primitive: one from-seed
//! derivation, one sign, one fail-closed verify. Domain separation (FIPS 204
//! `ctx`) is supplied by the caller on every call, so the same key material can
//! never produce a signature valid on two surfaces.

use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};

/// Serialized length of an ML-DSA-65 public key (FIPS 204 = 1952 bytes).
pub const ML_DSA_PK_LEN: usize = ml_dsa_65::PK_LEN;

/// Serialized length of an ML-DSA-65 signature (FIPS 204).
pub const ML_DSA_SIG_LEN: usize = ml_dsa_65::SIG_LEN;

/// The post-quantum half of a hybrid identity: an ML-DSA-65 signing key plus its
/// serialized public key, derived DETERMINISTICALLY from the SAME 32-byte
/// ed25519 seed the classical identity uses.
#[derive(Clone)]
pub struct MlDsaKey {
    secret: ml_dsa_65::PrivateKey,
    public_bytes: [u8; ml_dsa_65::PK_LEN],
}

impl core::fmt::Debug for MlDsaKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MlDsaKey(..)")
    }
}

impl MlDsaKey {
    /// Derive the ML-DSA-65 keypair DETERMINISTICALLY from a 32-byte ed25519
    /// seed (`ML-DSA.KeyGen` from `ξ = seed`). Same seed → same PQ key, so the
    /// PQ public key matches across cipherclerk / node / genesis with no
    /// separate ceremony.
    pub fn from_ed25519_seed(seed: &[u8; 32]) -> Self {
        let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(seed);
        Self {
            secret: sk,
            public_bytes: pk.into_bytes(),
        }
    }

    /// The serialized ML-DSA-65 public key — the value a verifier ENROLLS and
    /// PINS to this holder's identity.
    pub fn public_bytes(&self) -> Vec<u8> {
        self.public_bytes.to_vec()
    }

    /// Sign `message` under the caller-supplied FIPS 204 `ctx` (hedged from OS
    /// entropy). Panics only on the vanishingly rare internal RNG failure — use
    /// [`MlDsaKey::try_sign`] where a fail-closed (absent-half) result is wanted.
    pub fn sign(&self, ctx: &[u8], message: &[u8]) -> Vec<u8> {
        self.try_sign(ctx, message)
            .expect("ml-dsa sign failed (internal RNG)")
    }

    /// Sign `message` under the caller-supplied FIPS 204 `ctx`. `None` only on
    /// the vanishingly rare internal RNG failure, which then fails CLOSED at
    /// verification (a present-but-absent PQ half rejects the hybrid).
    pub fn try_sign(&self, ctx: &[u8], message: &[u8]) -> Option<Vec<u8>> {
        self.secret.try_sign(message, ctx).ok().map(|s| s.to_vec())
    }
}

/// The ML-DSA-65 public key of the signer holding `seed`, derived
/// deterministically (`ML-DSA.KeyGen(ξ = seed)`). Convenience for enrollment
/// flows that never keep the signing key.
pub fn ml_dsa_public_from_seed(seed: &[u8; 32]) -> Vec<u8> {
    MlDsaKey::from_ed25519_seed(seed).public_bytes()
}

/// Sign `message` under `ctx` with the ML-DSA-65 key derived from `seed`.
/// `None` only on the vanishingly rare internal RNG failure. Convenience for
/// surfaces that sign straight from a seed without keeping a key struct.
pub fn ml_dsa_sign_from_seed(seed: &[u8; 32], ctx: &[u8], message: &[u8]) -> Option<Vec<u8>> {
    MlDsaKey::from_ed25519_seed(seed).try_sign(ctx, message)
}

/// Verify an ML-DSA-65 signature over `message` under the caller-supplied FIPS
/// 204 `ctx`.
///
/// Returns `false` — never a panic — on a wrong-length public key, a
/// wrong-length signature, an undecodable key, or a failed cryptographic check.
/// This is the fail-CLOSED primitive: a present-but-invalid (or malformed) PQ
/// half must make the whole hybrid verification reject.
pub fn ml_dsa_verify(public_bytes: &[u8], ctx: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
    let Ok(pk_arr) = <[u8; ml_dsa_65::PK_LEN]>::try_from(public_bytes) else {
        return false;
    };
    let Ok(sig) = <[u8; ml_dsa_65::SIG_LEN]>::try_from(sig_bytes) else {
        return false;
    };
    let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else {
        return false;
    };
    vk.verify(message, &sig, ctx)
}

#[cfg(test)]
mod tests {
    use super::*;

    const CTX: &[u8] = b"dregg-pq-unit-test-ctx-v1";

    #[test]
    fn from_seed_is_deterministic() {
        let seed = [7u8; 32];
        let a = MlDsaKey::from_ed25519_seed(&seed);
        let b = MlDsaKey::from_ed25519_seed(&seed);
        assert_eq!(a.public_bytes(), b.public_bytes());
        assert_eq!(a.public_bytes().len(), ML_DSA_PK_LEN);
        // The free helper agrees with the key-struct derivation.
        assert_eq!(ml_dsa_public_from_seed(&seed), a.public_bytes());
        // A different seed yields a different key.
        let c = MlDsaKey::from_ed25519_seed(&[8u8; 32]);
        assert_ne!(a.public_bytes(), c.public_bytes());
    }

    #[test]
    fn sign_then_verify_roundtrips() {
        let key = MlDsaKey::from_ed25519_seed(&[3u8; 32]);
        let msg = b"the same canonical signing message both halves cover";
        let sig = key.sign(CTX, msg);
        assert!(ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig));
        // The from-seed sign helper produces an equally valid signature.
        let sig2 = ml_dsa_sign_from_seed(&[3u8; 32], CTX, msg).expect("sign");
        assert!(ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig2));
    }

    #[test]
    fn ctx_separates_domains() {
        // A signature minted under one ctx must not verify under another —
        // domain separation is load-bearing and rides the caller's ctx.
        let key = MlDsaKey::from_ed25519_seed(&[5u8; 32]);
        let msg = b"canonical message";
        let sig = key.sign(b"surface-A-v1", msg);
        assert!(ml_dsa_verify(
            &key.public_bytes(),
            b"surface-A-v1",
            msg,
            &sig
        ));
        assert!(!ml_dsa_verify(
            &key.public_bytes(),
            b"surface-B-v1",
            msg,
            &sig
        ));
    }

    #[test]
    fn forged_and_malformed_rejected_fail_closed() {
        let key = MlDsaKey::from_ed25519_seed(&[3u8; 32]);
        let msg = b"canonical message";
        let mut sig = key.sign(CTX, msg);
        // Flip one byte: a present-but-invalid PQ half must fail closed.
        sig[0] ^= 0xff;
        assert!(!ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig));

        // A signature by an attacker's OWN key over the SAME message, verified
        // against the honest holder's enrolled public key, must REJECT.
        let attacker = MlDsaKey::from_ed25519_seed(&[99u8; 32]);
        let forged = attacker.sign(CTX, msg);
        assert!(!ml_dsa_verify(&key.public_bytes(), CTX, msg, &forged));
        // (the forged signature IS valid under the attacker's own key — proving
        //  the rejection is the pin, not a broken signature)
        assert!(ml_dsa_verify(&attacker.public_bytes(), CTX, msg, &forged));

        // Wrong message under a valid signature rejects.
        let good = key.sign(CTX, msg);
        assert!(!ml_dsa_verify(
            &key.public_bytes(),
            CTX,
            b"different message",
            &good
        ));
        // Empty / malformed inputs reject rather than panic.
        assert!(!ml_dsa_verify(&[], CTX, msg, &good));
        assert!(!ml_dsa_verify(&key.public_bytes(), CTX, msg, &[]));
    }
}
