//! The deterministic test committee — the fixture this crate's tests author blocks
//! as, built ONCE per test binary instead of re-derived per call.
//!
//! Three test modules (`lib.rs`, `cross_reference.rs`, `dissemination.rs`) each
//! define the same creator-byte → key correspondence,
//! `SigningKey::from_bytes(&[id; 32])`, and each `test_lace()` enrolled 33 or 64 of
//! them by calling `Block::pq_public_key(&signing_for(c))` — **one full ML-DSA-65
//! keygen per member, per call**, at ~32 call sites. Every `make_block` paid one
//! more. Measured on persvati's `native-anchor` lane with the Lean-verified keygen
//! core installed, a single `cross_reference` test spent 29–41 s doing nothing but
//! re-deriving these same 64 keys.
//!
//! # This is a FIXTURE, not the cache the production fix refuses
//!
//! [`crate::signer`] rejects a process-global map of derived keys, and that
//! reasoning is not weakened here. What makes this admissible is not that it is
//! test code — it is that **there is no secret**. The committee's seeds are 256
//! publicly-known constants written literally in this file (`[id; 32]`); they are
//! test vectors, not key material, so there is nothing to pool and no "who may read
//! this entry" question to get wrong. The roster is a fixed, enumerable set, so
//! holding it is CONSTRUCTING THE FIXTURE ONCE, not caching secrets keyed by secret
//! input.
//!
//! It is also `#[cfg(test)]`: no part of this module exists in the shipped crate.
//!
//! # It cannot change what any test asserts
//!
//! `ML-DSA.KeyGen` is deterministic in ξ, so [`signer`] hands back exactly the key
//! `HybridBlockSigner::new(SigningKey::from_bytes(&[id; 32]))` produces on any call,
//! and every creator id, enrolled public key and signature is bit-identical to what
//! the per-call derivation produced. `committee_signer_matches_a_fresh_derivation`
//! pins that against a freshly-derived signer.

use std::sync::OnceLock;

use ed25519_dalek::SigningKey;

use crate::signer::HybridBlockSigner;

/// The deterministic ed25519 signing key for creator byte `id` — the definition all
/// three test modules share (`key_for` / `signing_for`).
pub(crate) fn signing_key(id: u8) -> SigningKey {
    SigningKey::from_bytes(&[id; 32])
}

/// One `OnceLock` per creator byte, so a test binary derives only the members it
/// actually uses and derives each of those exactly once.
static COMMITTEE: [OnceLock<HybridBlockSigner>; 256] = [const { OnceLock::new() }; 256];

/// The HYBRID signing identity for creator byte `id`, derived on first use and
/// shared thereafter.
///
/// Equal in every byte to `HybridBlockSigner::new(signing_key(id))`, and therefore
/// to `Block::hybrid_id(&signing_key(id))` / `Block::pq_public_key(&signing_key(id))`
/// on the creator id and enrolled key it reports.
pub(crate) fn signer(id: u8) -> &'static HybridBlockSigner {
    COMMITTEE[id as usize].get_or_init(|| HybridBlockSigner::new(signing_key(id)))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The fixture serves the SAME key a fresh derivation produces — so sharing it
    /// across tests cannot change any assertion that depends on an identity.
    ///
    /// Checks all four consensus-visible faces: the ed25519 half, the HYBRID creator
    /// id, the enrolled ML-DSA public key, and that a signature made by the shared
    /// signer verifies under the FRESHLY-derived identity's enrolled key.
    #[test]
    fn committee_signer_matches_a_fresh_derivation() {
        for id in [0u8, 1, 7, 32, 63, 255] {
            let shared = signer(id);
            let fresh = HybridBlockSigner::new(signing_key(id));

            assert_eq!(
                shared.ed25519(),
                fresh.ed25519(),
                "committee member {id} has a different ed25519 half than a fresh derivation"
            );
            assert_eq!(
                shared.creator(),
                fresh.creator(),
                "committee member {id} has a different HYBRID creator id than a fresh derivation \
                 — the fixture would be authoring under a different identity than the tests name"
            );
            assert_eq!(
                shared.pq_public_key().0,
                fresh.pq_public_key().0,
                "committee member {id} enrolls a different ML-DSA public key than a fresh \
                 derivation"
            );

            let msg = b"committee fixture equivalence";
            let sig = shared
                .sign_pq(msg)
                .expect("ML-DSA sign (hedged) should not fail");
            assert!(
                fresh.pq_public_key().verify(msg, &sig),
                "committee member {id}'s signature does not verify under the key a fresh \
                 derivation enrolls"
            );
        }
    }

    /// The fixture is LIVE: asking twice returns the same object, not two
    /// derivations. Proven by object identity, never by a stopwatch, so it cannot
    /// flake on a loaded box — and it goes red the moment the `OnceLock` is
    /// replaced by a per-call derivation.
    #[test]
    fn committee_derives_each_member_once() {
        assert!(
            std::ptr::eq(signer(9), signer(9)),
            "the committee re-derived member 9 instead of serving the held identity"
        );
        assert!(
            !std::ptr::eq(signer(9), signer(10)),
            "two DIFFERENT committee members resolved to the same identity"
        );
    }
}
