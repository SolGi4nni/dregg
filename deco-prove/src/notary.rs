//! **The MPC-TLS / notary capture layer — the NAMED interim.**
//!
//! ⚑ HONEST STATUS (do NOT read this as live-trustless TLS): full trustless money-in
//! needs the disclosed Stripe payment facts to provably originate from a *live TLS
//! session with Stripe's own API*. The trustless realization is a TLSNotary-style
//! **MPC-TLS** handshake (the notary co-computes the TLS session keys and learns
//! nothing, so it cannot fabricate a transcript) — or, weaker, a DECO 3-party
//! handshake. Neither is in-tree yet.
//!
//! This module is the deliberate **interim**: a *semi-honest notary* that observed the
//! real Stripe TLS session, extracted the disclosed [`PaymentFacts`], and signs
//! (real ed25519 — the SAME curve the bridge's off-AIR §8 carrier already trusts) a
//! commitment binding those facts to their Poseidon2 transcript commitment. The prover
//! holds the opening `salt`.
//!
//! ### The trust boundary (name it, do not launder it)
//!
//! * **Trusted here (the interim's gap):** the notary HONESTLY observed a genuine
//!   Stripe TLS session and did not fabricate the disclosed facts. A dishonest notary
//!   could sign facts for a payment that never settled. This is exactly the gap
//!   MPC-TLS closes (the notary co-derives the session secret and cannot forge a
//!   transcript it did not co-witness).
//! * **Already trustless (NOT the notary's job):** that the disclosed facts bind to
//!   the minted amount/recipient/intent — the STARK over the DECO leaf AIR
//!   ([`crate::prover`]) + the bridge felt-commitment binding enforce this
//!   cryptographically; a notary cannot make a forged-facts attestation mint.
//!
//! So the notary attests **origin** (this came from a Stripe session); the STARK
//! attests **integrity** (these exact facts are what was committed and minted). The
//! interim trusts the former; the latter is already proven. Flipping origin to
//! trustless = replacing this module with an MPC-TLS `tlsn`-style capture, no change to
//! [`crate::prover`] or the bridge verifier.

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

use crate::prover::StripePaymentFacts;

/// The domain-separation tag over the notary's signed message (so a notary signature
/// can never be replayed as a signature over unrelated bytes).
const NOTARY_DOMAIN: &[u8] = b"dregg/deco/notary-transcript-commitment/v1";

/// A notary's signing identity. In the interim this is a long-lived semi-honest notary
/// key; in the MPC-TLS realization it is replaced by the co-derived session binding.
pub struct NotaryKeypair {
    signing: SigningKey,
}

impl NotaryKeypair {
    /// A notary keypair from a 32-byte seed (deterministic; the ONLY constructor —
    /// the interim does not need OS randomness, and a fixed seed keeps tests + the
    /// documented trust boundary reproducible).
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        NotaryKeypair {
            signing: SigningKey::from_bytes(seed),
        }
    }

    /// The notary's public verifying key (the anchor a verifier pins).
    pub fn public_key(&self) -> [u8; 32] {
        self.signing.verifying_key().to_bytes()
    }
}

/// The Poseidon2 transcript commitment the notary attests and the DECO leaf's gate (3)
/// recomputes in-AIR: `transcriptCommit = hash_fact(payment_hash, [salt])` over the
/// canonical felt `payment_hash` of the disclosed facts, under the opening blinding
/// `salt` (held by the prover).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TranscriptCommitment {
    /// The canonical felt payment identity
    /// ([`dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt`]).
    pub payment_hash: BabyBear,
    /// `hash_fact(payment_hash, [salt])` — the leaf's gate-3 transcript commitment.
    pub transcript_commit: BabyBear,
}

impl TranscriptCommitment {
    /// Build the commitment from the disclosed facts + the opening `salt` (the SAME
    /// felt projection the DECO leaf witness carries).
    pub fn new(facts: &StripePaymentFacts, salt: BabyBear) -> Self {
        let payment_hash = facts.payment_hash();
        let transcript_commit = hash_fact(payment_hash, &[salt]);
        TranscriptCommitment {
            payment_hash,
            transcript_commit,
        }
    }

    /// The canonical byte message the notary signs: `DOMAIN || payment_hash ||
    /// transcript_commit` (little-endian canonical u32 felts).
    fn signing_bytes(&self) -> Vec<u8> {
        let mut msg = Vec::with_capacity(NOTARY_DOMAIN.len() + 8);
        msg.extend_from_slice(NOTARY_DOMAIN);
        msg.extend_from_slice(&self.payment_hash.as_u32().to_le_bytes());
        msg.extend_from_slice(&self.transcript_commit.as_u32().to_le_bytes());
        msg
    }
}

/// A notary's attestation over a disclosed Stripe payment: the transcript commitment +
/// the notary's ed25519 signature + the notary's public key. Holding one is (under the
/// interim's semi-honest-notary trust boundary) evidence the facts came from a real
/// Stripe TLS session the notary observed.
#[derive(Clone, Debug)]
pub struct NotaryAttestation {
    /// The Poseidon2 transcript commitment binding the disclosed facts.
    pub commitment: TranscriptCommitment,
    /// The notary's ed25519 signature over [`TranscriptCommitment::signing_bytes`].
    pub notary_sig: [u8; 64],
    /// The notary's public key (a verifier pins its OWN expected anchor; this echoed
    /// key is a discarded claim unless it matches).
    pub notary_pubkey: [u8; 32],
}

impl NotaryKeypair {
    /// **Sign** a transcript commitment over the disclosed facts + opening `salt` —
    /// the interim notary's capture step (stands in for the MPC-TLS session binding).
    pub fn attest(&self, facts: &StripePaymentFacts, salt: BabyBear) -> NotaryAttestation {
        let commitment = TranscriptCommitment::new(facts, salt);
        let sig: Signature = self.signing.sign(&commitment.signing_bytes());
        NotaryAttestation {
            commitment,
            notary_sig: sig.to_bytes(),
            notary_pubkey: self.public_key(),
        }
    }
}

/// The reason a notary attestation is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NotaryVerifyError {
    /// The echoed notary public key is not the anchor the verifier expected.
    WrongNotary,
    /// The public key bytes are not a valid ed25519 point.
    MalformedKey,
    /// The signature does not verify over the commitment under the notary key.
    BadSignature,
    /// The attested commitment does not match the disclosed facts + salt (the notary
    /// signed a DIFFERENT payment than the one presented).
    CommitmentMismatch,
}

/// **Verify** a notary attestation against a pinned notary anchor and the disclosed
/// facts + opening `salt`: (1) the echoed key IS the expected anchor, (2) the ed25519
/// signature verifies (strict), and (3) the attested commitment equals the recompute
/// over the presented facts + salt (so a signature over some OTHER payment cannot be
/// re-pointed at these facts). This is the interim's ORIGIN check — it does NOT by
/// itself prove a live Stripe session (the named trust boundary; module docs).
pub fn verify_notary_attestation(
    att: &NotaryAttestation,
    expected_notary: &[u8; 32],
    facts: &StripePaymentFacts,
    salt: BabyBear,
) -> Result<(), NotaryVerifyError> {
    if &att.notary_pubkey != expected_notary {
        return Err(NotaryVerifyError::WrongNotary);
    }
    let recomputed = TranscriptCommitment::new(facts, salt);
    if recomputed != att.commitment {
        return Err(NotaryVerifyError::CommitmentMismatch);
    }
    let vk = VerifyingKey::from_bytes(&att.notary_pubkey)
        .map_err(|_| NotaryVerifyError::MalformedKey)?;
    let sig = Signature::from_bytes(&att.notary_sig);
    vk.verify(&att.commitment.signing_bytes(), &sig)
        .map_err(|_| NotaryVerifyError::BadSignature)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::CellId;

    fn facts() -> StripePaymentFacts {
        StripePaymentFacts {
            payment_intent_id: "pi_notary_001".to_string(),
            amount_cents: 2500,
            currency: "usd".to_string(),
            recipient: CellId::from_bytes([7u8; 32]),
        }
    }

    #[test]
    fn honest_notary_attestation_verifies() {
        let kp = NotaryKeypair::from_seed(&[1u8; 32]);
        let salt = BabyBear::new(0x55);
        let att = kp.attest(&facts(), salt);
        assert_eq!(
            verify_notary_attestation(&att, &kp.public_key(), &facts(), salt),
            Ok(())
        );
    }

    #[test]
    fn wrong_notary_anchor_refused() {
        let kp = NotaryKeypair::from_seed(&[1u8; 32]);
        let other = NotaryKeypair::from_seed(&[2u8; 32]);
        let salt = BabyBear::new(0x55);
        let att = kp.attest(&facts(), salt);
        assert_eq!(
            verify_notary_attestation(&att, &other.public_key(), &facts(), salt),
            Err(NotaryVerifyError::WrongNotary)
        );
    }

    #[test]
    fn tampered_facts_break_the_commitment() {
        let kp = NotaryKeypair::from_seed(&[1u8; 32]);
        let salt = BabyBear::new(0x55);
        let att = kp.attest(&facts(), salt);
        // Present DIFFERENT facts (bumped amount) against the notary's signature.
        let mut forged = facts();
        forged.amount_cents = 9_999_999;
        assert_eq!(
            verify_notary_attestation(&att, &kp.public_key(), &forged, salt),
            Err(NotaryVerifyError::CommitmentMismatch)
        );
    }

    #[test]
    fn tampered_signature_refused() {
        let kp = NotaryKeypair::from_seed(&[1u8; 32]);
        let salt = BabyBear::new(0x55);
        let mut att = kp.attest(&facts(), salt);
        att.notary_sig[0] ^= 0xFF;
        assert_eq!(
            verify_notary_attestation(&att, &kp.public_key(), &facts(), salt),
            Err(NotaryVerifyError::BadSignature)
        );
    }
}
