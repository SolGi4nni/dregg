//! Post-quantum (ML-DSA-65 / FIPS 204) key material for the HYBRID block
//! signature.
//!
//! A blocklace [`crate::Block`] is signed by BOTH ed25519 (classical) and
//! ML-DSA-65 (post-quantum). The two halves sign the SAME canonical bytes
//! (`Block::id()`), and a verifier accepts only when BOTH verify. Forging a
//! block therefore requires breaking ed25519 discrete log AND module-lattice
//! SIS/LWE simultaneously — a quantum adversary that breaks the classical half
//! still cannot inject blocks under another creator's identity.
//!
//! # Enroll + PIN (NOT self-carried)
//!
//! The ML-DSA signing key is DERIVED from the SAME 32-byte seed as the
//! creator's ed25519 identity ([`MlDsaSigningKey::from_seed`], keyed on
//! `SigningKey::to_bytes()`). The verifier does NOT trust a public key carried
//! inside the block; it pins the block's ML-DSA signature to the creator's
//! ENROLLED public key (the committee roster, e.g. from genesis). See
//! [`crate::Blocklace::enroll_pq`] and [`crate::Block::verify_signature`].
//!
//! This pins `dregg_federation::frost`'s ML-DSA domain separation exactly (same
//! derivation, same shared `dregg-pq` leaf primitive), with a block-specific
//! [`BLOCK_PQ_CTX`]; the newtype names live here because `dregg-blocklace` sits
//! BELOW `dregg-federation` in the dependency graph.

use serde::{Deserialize, Serialize};

/// Domain-separation context (FIPS 204 `ctx`) bound into every hybrid-block
/// ML-DSA signature. Sign and verify MUST agree on it. Distinct from the
/// federation quorum context so a block signature can never be replayed as a
/// quorum signature or vice versa.
pub const BLOCK_PQ_CTX: &[u8] = b"dregg-blocklace-block-pq-v1";

/// Byte length of a serialized ML-DSA-65 public key (FIPS 204, 1952 bytes).
pub const PK_LEN: usize = dregg_pq::ML_DSA_PK_LEN;

/// Byte length of an ML-DSA-65 signature (FIPS 204, 3309 bytes).
pub const SIG_LEN: usize = dregg_pq::ML_DSA_SIG_LEN;

/// An ML-DSA-65 public key, as its FIPS 204 serialized bytes.
///
/// This is the ENROLLED key a verifier pins a block's PQ half against — never
/// a key carried inside the block. Validated (`try_from_bytes`) at verify time;
/// an undecodable key rejects any block that names its creator.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MlDsaPublicKey(#[serde(with = "serde_pk")] pub [u8; PK_LEN]);

impl std::fmt::Debug for MlDsaPublicKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // 1952 bytes of key material is noise in a debug dump; show a prefix.
        write!(f, "MlDsaPublicKey({}..)", hex_prefix(&self.0))
    }
}

impl MlDsaPublicKey {
    /// Verify an ML-DSA-65 signature over `message` under [`BLOCK_PQ_CTX`].
    ///
    /// Returns `false` on a wrong-length signature, an undecodable key, or a
    /// signature that does not verify. Fails CLOSED on every malformed input.
    pub fn verify(&self, message: &[u8], sig_bytes: &[u8]) -> bool {
        dregg_pq::ml_dsa_verify(&self.0, BLOCK_PQ_CTX, message, sig_bytes)
    }
}

/// An ML-DSA-65 signing key, DERIVED from a block creator's ed25519 seed.
///
/// Held only by the creator (it never leaves the node); the corresponding
/// [`MlDsaPublicKey`] is enrolled in the committee roster. Every signature it
/// produces is bound to [`BLOCK_PQ_CTX`].
///
/// A thin newtype over the shared [`dregg_pq::MlDsaKey`] primitive.
#[derive(Clone)]
pub struct MlDsaSigningKey(dregg_pq::MlDsaKey);

impl std::fmt::Debug for MlDsaSigningKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MlDsaSigningKey(..)")
    }
}

impl MlDsaSigningKey {
    /// Deterministic keypair from a 32-byte seed `ξ` (FIPS 204 `keygen_from_seed`).
    ///
    /// Called with the creator's ed25519 seed (`SigningKey::to_bytes()`) so the
    /// PQ identity is bound to the same seed as the classical identity — exactly
    /// how the node derives its PQ key in `node/src/blocklace_sync.rs`.
    pub fn from_seed(xi: &[u8; 32]) -> (MlDsaPublicKey, Self) {
        let key = dregg_pq::MlDsaKey::from_ed25519_seed(xi);
        let pk = MlDsaPublicKey(
            key.public_bytes()
                .try_into()
                .expect("ML-DSA-65 public key is PK_LEN bytes"),
        );
        (pk, Self(key))
    }

    /// Sign `message` under [`BLOCK_PQ_CTX`] (hedged from OS entropy).
    ///
    /// `None` only on a transient OS-entropy failure during hedged signing.
    pub fn sign(&self, message: &[u8]) -> Option<Vec<u8>> {
        self.0.try_sign(BLOCK_PQ_CTX, message)
    }
}

/// Derive the enrollable ML-DSA-65 public key for a creator whose ed25519
/// seed is `seed`. This is the roster entry: `enroll_pq(creator_pubkey, …)`.
pub fn public_from_ed25519_seed(seed: &[u8; 32]) -> MlDsaPublicKey {
    MlDsaSigningKey::from_seed(seed).0
}

fn hex_prefix(bytes: &[u8]) -> String {
    bytes
        .iter()
        .take(8)
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

/// Serde helper for the 1952-byte ML-DSA-65 public key array (serde derives
/// Serialize/Deserialize only for arrays up to `[T; 32]`).
mod serde_pk {
    use super::PK_LEN;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(
        bytes: &[u8; PK_LEN],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        AsRef::<[u8]>::as_ref(bytes).serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<[u8; PK_LEN], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected ML-DSA-65 public key bytes"))
    }
}
