//! ML-DSA-65 (FIPS 204) half of the **HYBRID** credential block chain.
//!
//! Each attenuation block of a [`Credential`](super::Credential) is signed by
//! its delegator under BOTH ed25519 AND ML-DSA-65 over the *same* canonical
//! block digest. A block verifies only when BOTH halves check
//! (`classical ∧ pq`), so forging a delegation/attenuation requires breaking
//! ed25519 discrete-log AND module-lattice SIS/LWE simultaneously — a quantum
//! adversary that breaks only ed25519 still cannot forge the chain.
//!
//! ## Deterministic derivation (no second ceremony)
//!
//! The ML-DSA key of any signer is derived DETERMINISTICALLY from the SAME
//! 32-byte ed25519 seed that signer already holds (FIPS 204
//! `ML-DSA.KeyGen(ξ = seed)`), exactly as the turn-authorization perimeter does
//! (`turn/src/pq.rs` `MlDsaTurnKey::from_ed25519_seed`). A root, a delegator,
//! and every fresh attenuation key thus have a PQ public key with no separate
//! keygen step: the 32-byte ed25519 seed IS the hybrid identity.
//!
//! ## Enroll + pin, never self-carried
//!
//! The verifier cannot derive a party's ML-DSA *public* key from their ed25519
//! *public* key, so each block CARRIES the next block's ML-DSA public key — but
//! that carried key is covered by the parent block's ed25519 ∧ ML-DSA
//! signatures (it is hashed into [`super::chain`]'s `block_digest`). The chain's
//! PQ integrity therefore roots at the verifier's ENROLLED hybrid root key
//! ([`super::HybridRootPublic`]), not at a self-asserted per-block key: a block
//! whose ML-DSA key is not authorized by its parent's (hybrid) signature — up
//! to the enrolled root — fails to verify.
//!
//! Fail-closed throughout: a missing or malformed PQ half makes
//! [`ml_dsa_verify`] return `false`, never panic.

use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};

/// Serialized length of an ML-DSA-65 public key (FIPS 204 = 1952 bytes).
pub(crate) const ML_DSA_PK_LEN: usize = ml_dsa_65::PK_LEN;

/// Serialized length of an ML-DSA-65 signature (FIPS 204).
pub(crate) const ML_DSA_SIG_LEN: usize = ml_dsa_65::SIG_LEN;

/// Domain-separation context (FIPS 204 `ctx`) for the ML-DSA half of a HYBRID
/// *credential* block signature. Distinct from the turn-path
/// (`dregg-hybrid-turn-v1`) and consensus (`dregg-hybrid-qc-v1`) contexts, so a
/// credential-chain PQ signature can never be replayed as a turn or
/// quorum-certificate half, and vice versa.
const CRED_PQ_CTX: &[u8] = b"dregg-auth v1 credential mldsa";

/// The ML-DSA-65 public key of the signer holding `seed`, derived
/// deterministically (`ML-DSA.KeyGen(ξ = seed)`). Same seed → same PQ key.
pub(crate) fn ml_dsa_public_from_seed(seed: &[u8; 32]) -> [u8; ML_DSA_PK_LEN] {
    let (pk, _sk) = ml_dsa_65::KG::keygen_from_seed(seed);
    pk.into_bytes()
}

/// Sign `message` under [`CRED_PQ_CTX`] with the ML-DSA key derived from `seed`
/// (hedged from OS entropy). `None` only on the vanishingly rare internal RNG
/// failure.
pub(crate) fn ml_dsa_sign(seed: &[u8; 32], message: &[u8]) -> Option<[u8; ML_DSA_SIG_LEN]> {
    let (_pk, sk) = ml_dsa_65::KG::keygen_from_seed(seed);
    sk.try_sign(message, CRED_PQ_CTX).ok()
}

/// Verify an ML-DSA-65 signature over `message` under [`CRED_PQ_CTX`].
///
/// Returns `false` — never a panic — on a wrong-length public key, a
/// wrong-length signature, an undecodable key, or a failed cryptographic check.
/// This is the fail-CLOSED primitive: a present-but-invalid (or absent) PQ half
/// must make the whole hybrid verification reject.
pub(crate) fn ml_dsa_verify(public_bytes: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
    let Ok(pk_arr) = <[u8; ML_DSA_PK_LEN]>::try_from(public_bytes) else {
        return false;
    };
    let Ok(sig) = <[u8; ML_DSA_SIG_LEN]>::try_from(sig_bytes) else {
        return false;
    };
    let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else {
        return false;
    };
    vk.verify(message, &sig, CRED_PQ_CTX)
}
