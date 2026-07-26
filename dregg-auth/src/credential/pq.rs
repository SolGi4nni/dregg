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

use std::sync::{Arc, RwLock};

/// Serialized length of an ML-DSA-65 public key (FIPS 204 = 1952 bytes).
pub(crate) const ML_DSA_PK_LEN: usize = dregg_pq::ML_DSA_PK_LEN;

/// Serialized length of an ML-DSA-65 signature (FIPS 204).
pub(crate) const ML_DSA_SIG_LEN: usize = dregg_pq::ML_DSA_SIG_LEN;

/// Domain-separation context (FIPS 204 `ctx`) for the ML-DSA half of a HYBRID
/// *credential* block signature. Distinct from the turn-path
/// (`dregg-hybrid-turn-v1`) and consensus (`dregg-hybrid-qc-v1`) contexts, so a
/// credential-chain PQ signature can never be replayed as a turn or
/// quorum-certificate half, and vice versa.
const CRED_PQ_CTX: &[u8] = b"dregg-auth v1 credential mldsa";

/// The ML-DSA-65 public key of the signer holding `seed`, derived
/// deterministically (`ML-DSA.KeyGen(ξ = seed)`). Same seed → same PQ key.
///
/// TEST-ONLY. Every deployed path goes through [`MlDsaSeedMemo`] instead, so the
/// derivation is paid once per identity rather than once per call; this remains
/// as the independent reference the memo is checked AGAINST.
#[cfg(test)]
pub(crate) fn ml_dsa_public_from_seed(seed: &[u8; 32]) -> [u8; ML_DSA_PK_LEN] {
    dregg_pq::ml_dsa_public_from_seed(seed)
        .try_into()
        .expect("ml-dsa-65 public key is ML_DSA_PK_LEN bytes")
}

/// The serialized public key of an already-derived ML-DSA-65 key, with the same
/// length invariant [`ml_dsa_public_from_seed`] enforces.
pub(crate) fn pk_bytes(key: &dregg_pq::MlDsaKey) -> [u8; ML_DSA_PK_LEN] {
    key.public_bytes()
        .try_into()
        .expect("ml-dsa-65 public key is ML_DSA_PK_LEN bytes")
}

/// Sign `message` under [`CRED_PQ_CTX`] with the ML-DSA key derived from `seed`
/// (hedged from OS entropy). `None` only on the vanishingly rare internal RNG
/// failure.
///
/// TEST-ONLY, for the same reason as [`ml_dsa_public_from_seed`]: deployed
/// signing goes through [`MlDsaSeedMemo::sign`].
#[cfg(test)]
pub(crate) fn ml_dsa_sign(seed: &[u8; 32], message: &[u8]) -> Option<[u8; ML_DSA_SIG_LEN]> {
    let sig = dregg_pq::ml_dsa_sign_from_seed(seed, CRED_PQ_CTX, message)?;
    sig.try_into().ok()
}

/// Verify an ML-DSA-65 signature over `message` under [`CRED_PQ_CTX`].
///
/// Returns `false` — never a panic — on a wrong-length public key, a
/// wrong-length signature, an undecodable key, or a failed cryptographic check.
/// This is the fail-CLOSED primitive: a present-but-invalid (or absent) PQ half
/// must make the whole hybrid verification reject.
pub(crate) fn ml_dsa_verify(public_bytes: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
    dregg_pq::ml_dsa_verify(public_bytes, CRED_PQ_CTX, message, sig_bytes)
}

// ─────────────────────────────────────────────────────────────────────────────
// The memoised PQ half
// ─────────────────────────────────────────────────────────────────────────────

/// BLAKE3 KDF context for [`MlDsaSeedMemo`]'s seed binding. Its only job is to
/// make the cache-validity check a collision-resistant function of the ed25519
/// seed that produced the cached PQ key, so an identity can never serve a key
/// derived from a different seed than the one it is signing with.
const MEMO_BINDING_CTX: &str = "dregg-auth v1 ml-dsa key memo seed binding";

/// One memoised ML-DSA key, held beside the digest of the seed it was derived
/// FROM.
struct MemoEntry {
    /// `blake3::derive_key(MEMO_BINDING_CTX, seed)` of the ed25519 seed this key
    /// came from. A digest, not the seed: the validity check never needs the
    /// secret itself.
    seed_binding: [u8; 32],
    /// The derived PQ key, behind an `Arc` so serving it copies a pointer rather
    /// than a second copy of the ML-DSA-65 secret.
    key: Arc<dregg_pq::MlDsaKey>,
}

/// **THE MEMOISED PQ HALF** of one identity — the ML-DSA-65 key derived from
/// that identity's 32-byte ed25519 seed, held beside the digest of that seed.
///
/// `dregg_pq::MlDsaKey::from_ed25519_seed` is a pure function of the seed
/// (deterministic FIPS 204 `ML-DSA.KeyGen(ξ)`), and on the deployed build it
/// runs the Lean-verified keygen core across the FFI boundary — measured at
/// **174–227 ms of CPU per call**. Every credential mint, every attenuation and
/// every hybrid verify used to pay it afresh, twice per block.
///
/// **THE MEMO LIVES INSIDE THE IDENTITY, NOT BESIDE IT.** One of these is a
/// private field of the object that OWNS the ed25519 seed —
/// [`RootKey`](super::RootKey) owns the minting seed, a
/// [`Credential`](super::Credential) owns its tail (proof) seed. A
/// process-global map keyed by seed would work arithmetically and be wrong
/// operationally: it pools every tenant's ML-DSA secret in one process-lifetime
/// structure that outlives the objects that own them, and it makes "who may read
/// this entry" a property of a lookup key rather than of ownership. Here an
/// entry is reachable only through the identity that derived it, so two
/// identities are two memos and cross-identity sharing has no path to express
/// itself.
///
/// **The stored digest is the second wall**, and in this crate it is
/// load-bearing rather than defensive: [`Credential::attenuate`](super::Credential::attenuate)
/// RE-KEYS a credential in place (`self.proof = next`). Every read recomputes the
/// binding from the LIVE seed and serves the entry only on an exact match, so an
/// attenuated credential can never present or sign under its predecessor's PQ
/// key. A poisoned lock falls through to a fresh derivation — the memo can cost
/// latency, never correctness.
pub(crate) struct MlDsaSeedMemo {
    slot: RwLock<Option<MemoEntry>>,
}

impl Default for MlDsaSeedMemo {
    fn default() -> Self {
        Self::empty()
    }
}

impl std::fmt::Debug for MlDsaSeedMemo {
    /// Never renders key material or the binding digest.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MlDsaSeedMemo(..)")
    }
}

impl MlDsaSeedMemo {
    /// An empty memo — the first read for any seed derives.
    pub(crate) const fn empty() -> Self {
        Self {
            slot: RwLock::new(None),
        }
    }

    /// The binding digest of `seed`. Collision-resistant, domain-separated, and
    /// never the seed itself.
    fn binding(seed: &[u8; 32]) -> [u8; 32] {
        blake3::derive_key(MEMO_BINDING_CTX, seed)
    }

    /// Install a key ALREADY derived for `seed`, so the derivation a caller just
    /// paid for is not paid again.
    ///
    /// Used where a fresh identity is minted: the attenuation key's public bytes
    /// are needed for the block anyway, so the key that produced them becomes the
    /// new owner's memo instead of being dropped and re-derived on first use.
    /// Installing under `seed`'s binding means a later read with a DIFFERENT seed
    /// still misses, exactly as if the memo were empty.
    pub(crate) fn install(&self, seed: &[u8; 32], key: Arc<dregg_pq::MlDsaKey>) {
        if let Ok(mut slot) = self.slot.write() {
            *slot = Some(MemoEntry {
                seed_binding: Self::binding(seed),
                key,
            });
        }
    }

    /// The ML-DSA-65 key for `seed`, from the memo when the memo was filled by
    /// THIS seed and by derivation otherwise.
    ///
    /// The returned key is bit-identical either way; this changes latency and
    /// nothing else.
    pub(crate) fn key_for(&self, seed: &[u8; 32]) -> Arc<dregg_pq::MlDsaKey> {
        let binding = Self::binding(seed);
        if let Ok(slot) = self.slot.read()
            && let Some(entry) = slot.as_ref()
            // THE GATE: the seed being signed with, not merely "some seed once cached here".
            && entry.seed_binding == binding
        {
            return Arc::clone(&entry.key);
        }
        let key = Arc::new(dregg_pq::MlDsaKey::from_ed25519_seed(seed));
        self.install(seed, Arc::clone(&key));
        key
    }

    /// The ML-DSA-65 public key of the holder of `seed` — [`ml_dsa_public_from_seed`]
    /// with the derivation memoised.
    pub(crate) fn public_from_seed(&self, seed: &[u8; 32]) -> [u8; ML_DSA_PK_LEN] {
        pk_bytes(&self.key_for(seed))
    }

    /// Sign `message` under [`CRED_PQ_CTX`] with `seed`'s key — [`ml_dsa_sign`]
    /// with the derivation memoised.
    pub(crate) fn sign(&self, seed: &[u8; 32], message: &[u8]) -> Option<[u8; ML_DSA_SIG_LEN]> {
        self.key_for(seed)
            .try_sign(CRED_PQ_CTX, message)?
            .try_into()
            .ok()
    }
}

impl Drop for MlDsaSeedMemo {
    /// Drop the memoised PQ key with the identity that owns it, rather than
    /// waiting for the field's own drop glue: the ML-DSA secret goes away at the
    /// same moment as the ed25519 seed it was derived from.
    fn drop(&mut self) {
        if let Ok(mut slot) = self.slot.write() {
            *slot = None;
        }
    }
}
