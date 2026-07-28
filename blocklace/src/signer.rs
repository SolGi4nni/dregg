//! [`HybridBlockSigner`] — the object that OWNS a block creator's ed25519 seed and
//! the ML-DSA-65 key that seed derives, holding both TOGETHER and deriving the PQ
//! half exactly ONCE.
//!
//! # Why this type exists
//!
//! Every hybrid-signing entry point in this crate took a BARE [`SigningKey`]:
//! [`crate::finality::Block::new`], [`crate::finality::Block::hybrid_id`],
//! [`crate::finality::Block::pq_public_key`], [`crate::Block::sign`],
//! [`crate::Block::new_signed`], [`crate::Block::pq_public_key`]. There was
//! nothing for a derived key to BELONG to, so each call ran
//! [`crate::pq::MlDsaSigningKey::from_seed`] afresh — deterministic FIPS 204
//! `ML-DSA.KeyGen(ξ)`, which on a build with the verified cores installed runs the
//! Lean-verified keygen core across the FFI boundary.
//!
//! The cost was structural and it was paid in PRODUCTION, not only in tests. A
//! [`crate::finality::Blocklace`] holds its `self_key` for the process's life and
//! authored every block through `Block::new(&self.self_key, ..)` and then keyed the
//! tips map with `self_creator()` → `Block::hybrid_id(&self.self_key)`: **two full
//! ML-DSA keygens per authored block, for one unchanging identity.** A
//! [`crate::dissemination::Disseminator`] holding a signing key paid one more per
//! `create_block`.
//!
//! # THE KEY LIVES INSIDE THE SIGNER, NOT IN A LOOKUP TABLE
//!
//! Following `7a1d910a6` (which fixed this same pathology at seven other sites) and
//! `58bb885a0` before it: a process-global map keyed by seed bytes would work
//! arithmetically and be wrong operationally, because it pools every identity's
//! ML-DSA secret in one process-lifetime structure that outlives the objects owning
//! them, and makes "who may read this entry" a property of a LOOKUP KEY rather than
//! of OWNERSHIP. So the derived key is a private field of the object that owns the
//! ed25519 key, two identities are two objects, and cross-identity sharing has no
//! path to express itself.
//!
//! Every field is private and set together at construction with no mutator, so a
//! signer cannot be re-keyed in place and its halves cannot drift apart.
//!
//! # Nothing consensus-visible moves
//!
//! `creator = H(ed25519 ‖ ml_dsa_pk)` ([`dregg_types::hybrid_id_commitment`]) is a
//! consensus-visible label. `ML-DSA.KeyGen` is DETERMINISTIC in ξ, so the key this
//! signer holds is bit-identical to the one a fresh derivation from the same seed
//! produces, and so is every value computed from it. The bare-key entry points are
//! all retained as one-shots that build a signer, use it once and drop it — they
//! are the SAME CODE PATH, which is what `signer_path_is_byte_identical_to_the_one_shot`
//! and the golden `creator` vectors in [`crate::finality`] pin.
//!
//! # Secret material and its lifetime
//!
//! `fips204`'s `ml_dsa_65::PrivateKey` derives `Zeroize` + `ZeroizeOnDrop`, so the
//! 4032-byte ML-DSA secret inside [`crate::pq::MlDsaSigningKey`] is wiped when the
//! last handle drops — the [`Arc`] here means "when the last clone of this signer
//! goes away", not "at the end of the call that derived it".
//!
//! That IS a longer window than a per-call derivation had, and it is the right one:
//! the window is now exactly the window the ed25519 `SigningKey` in the same struct
//! already had, and since the ML-DSA key is a deterministic FUNCTION of that seed,
//! anyone who can read the retained seed can recompute the PQ key regardless. The
//! memo therefore exposes no material that was not already recoverable from the
//! object holding it, for exactly as long as that object lives.

use std::sync::Arc;

use ed25519_dalek::SigningKey;

/// A block creator's HYBRID signing identity: the ed25519 key and the ML-DSA-65 key
/// its seed derives, held TOGETHER and derived ONCE.
///
/// Construct one where the ed25519 key is OWNED — a [`crate::finality::Blocklace`],
/// a [`crate::dissemination::Disseminator`], a node's identity — and author every
/// block through it. The bare-`&SigningKey` entry points remain, and remain
/// byte-identical, but each one pays a full ML-DSA keygen per call.
#[derive(Clone)]
pub struct HybridBlockSigner {
    /// The classical half. Owned, so the PQ half below can never be a key derived
    /// from some OTHER seed.
    classical: SigningKey,
    /// `classical`'s verify key, cached because `creator` already commits to it and
    /// the block wire carries it on every block.
    ed25519: [u8; 32],
    /// The derived ML-DSA-65 signing key. Behind an [`Arc`] so tests can prove by
    /// OBJECT IDENTITY (`Arc::ptr_eq`), rather than by a stopwatch, that a second
    /// block reads THIS key instead of deriving another — a liveness check that
    /// cannot flake on a loaded box and goes red if the memo is removed.
    pq: Arc<crate::pq::MlDsaSigningKey>,
    /// The enrollable ML-DSA-65 public key (1952 bytes). `Arc` keeps [`Clone`] cheap:
    /// `Blocklace::clone` is on the node's `poll_finalized_blocks` snapshot path.
    pq_public: Arc<crate::pq::MlDsaPublicKey>,
    /// The HYBRID creator id `H(ed25519 ‖ ml_dsa_pk)` this identity stamps on every
    /// block it authors — a pure function of the two public halves above.
    creator: [u8; 32],
}

impl std::fmt::Debug for HybridBlockSigner {
    /// Never renders key material.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("HybridBlockSigner(..)")
    }
}

impl HybridBlockSigner {
    /// Take ownership of an ed25519 identity and derive its ML-DSA-65 half. **This is
    /// where the keygen is paid — once, for the life of the signer.**
    pub fn new(classical: SigningKey) -> Self {
        let ed25519 = classical.verifying_key().to_bytes();
        let (pq_public, pq) = crate::pq::MlDsaSigningKey::from_seed(&classical.to_bytes());
        let creator = dregg_types::hybrid_id_commitment(&ed25519, &pq_public.0);
        Self {
            classical,
            ed25519,
            pq: Arc::new(pq),
            pq_public: Arc::new(pq_public),
            creator,
        }
    }

    /// The ed25519 signing key this identity owns — the CLASSICAL half, and the seed
    /// the PQ half was derived from.
    pub fn classical(&self) -> &SigningKey {
        &self.classical
    }

    /// This identity's ed25519 verify key: the classical half a block CARRIES.
    pub fn ed25519(&self) -> [u8; 32] {
        self.ed25519
    }

    /// This identity's HYBRID creator id `H(ed25519 ‖ ml_dsa_pk)` — the value
    /// [`crate::finality::Block::new`] stamps as `creator`, and the key the roster /
    /// tips / votes / gossip `NodeId` are all keyed by.
    ///
    /// Equal to [`crate::finality::Block::hybrid_id`] on the same signing key, with
    /// no derivation.
    pub fn creator(&self) -> [u8; 32] {
        self.creator
    }

    /// This identity's enrollable ML-DSA-65 public key — the roster entry a verifier
    /// PINS this creator's blocks against ([`crate::finality::Blocklace::enroll_pq`]).
    ///
    /// Equal to [`crate::finality::Block::pq_public_key`] on the same signing key,
    /// with no derivation.
    pub fn pq_public_key(&self) -> &crate::pq::MlDsaPublicKey {
        &self.pq_public
    }

    /// Sign `message` with the held ML-DSA-65 key under
    /// [`crate::pq::BLOCK_PQ_CTX`]. `None` only on a transient OS-entropy failure
    /// during hedged signing, which then fails CLOSED at verification.
    pub fn sign_pq(&self, message: &[u8]) -> Option<Vec<u8>> {
        self.pq.sign(message)
    }

    /// The held ML-DSA key BY HANDLE, for the `Arc::ptr_eq` liveness assertions that
    /// prove the memo is live without timing anything.
    #[cfg(test)]
    pub(crate) fn pq_handle(&self) -> &Arc<crate::pq::MlDsaSigningKey> {
        &self.pq
    }
}

impl From<SigningKey> for HybridBlockSigner {
    fn from(classical: SigningKey) -> Self {
        Self::new(classical)
    }
}
