//! **The STARK/DECO-leaf prover core** — the tractable, REAL crypto leg.
//!
//! Given disclosed Stripe payment facts + a TLS-transcript opening `salt`, produce a
//! [`DecoPaymentAttestation`] carrying a **genuine STARK proof** over the deployed DECO
//! leaf AIR ([`dregg_circuit_prove::deco_leaf_adapter`]) that binds the disclosed facts
//! to the canonical felt `payment_hash` — the proof
//! [`dregg_bridge::stripe_deco::StripeMirrorState::verify_deco_payment`] accepts for a
//! mint.
//!
//! Forgery is impossible at prove time: the DECO leaf pins its four `PaymentFacts` at
//! First-row PIs and recomputes the `hash_fact` identity IN-AIR, so a claim tuple that
//! disagrees with the witnessed facts is UNSAT (the leaf-binding tooth,
//! `deco_leaf_adapter::forged_amount_does_not_fold` / `forged_payment_hash_does_not_fold`).
//! The prover thus CANNOT emit a passing attestation for a forged fact; and if a caller
//! tampers a produced attestation post-hoc (bumping the amount without recomputing the
//! committed identity), the bridge verifier's felt-commitment binding refuses it
//! (`DecoCommitmentMismatch`).

use dregg_bridge::DecoPaymentAttestation;
use dregg_circuit::dsl::deco_payment::{stripe_payment_facts_felts, stripe_payment_hash_felt};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::deco_leaf_adapter::{
    DECO_LEAF_PAYMENT_HASH_PI, DecoLeafWitness, deco_leaf_public_inputs,
    prove_deco_leaf_with_claim, serialize_deco_leaf_proof, verify_deco_leaf_proof_bytes,
};
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_types::CellId;

/// The DECO leaf's amount range bound (`deco_payment::AMOUNT_LIMB_BITS`,
/// `Deco.lean::DecoRelation` conjunct 5): `1 ≤ amountCents < 2^30`. The prover refuses
/// to attest an out-of-range amount up front (the bridge verifier would reject it
/// anyway, and the single-felt amount limb masks above `2^30`).
const AMOUNT_LIMB_BITS: u32 = 30;

/// The disclosed Stripe payment facts a DECO attestation binds — the prover's input
/// (`Deco.lean::PaymentFacts`). These are what a notary-observed / MPC-TLS-captured
/// Stripe session discloses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StripePaymentFacts {
    /// The payment-intent id (the consume-once replay nonce).
    pub payment_intent_id: String,
    /// The amount that cleared, in cents (`1 ≤ amountCents < 2^30`).
    pub amount_cents: u64,
    /// The ISO-4217 currency.
    pub currency: String,
    /// The dregg cell to credit.
    pub recipient: CellId,
}

impl StripePaymentFacts {
    /// The canonical felt payment identity over these facts — the ONE encoder the
    /// leaf, the deployed producer, and the bridge verifier all share.
    pub fn payment_hash(&self) -> BabyBear {
        stripe_payment_hash_felt(
            self.amount_cents,
            &self.currency,
            &self.recipient.0,
            &self.payment_intent_id,
        )
    }

    /// The DECO leaf witness over these facts + the transcript opening `salt` (the four
    /// `PaymentFacts` projected to felts, the SAME projection the leaf recomputes).
    fn to_leaf_witness(&self, salt: BabyBear) -> DecoLeafWitness {
        let [amount_lo, currency_f, recipient_f, pi_f] = stripe_payment_facts_felts(
            self.amount_cents,
            &self.currency,
            &self.recipient.0,
            &self.payment_intent_id,
        );
        DecoLeafWitness {
            amount_cents: amount_lo,
            currency: currency_f,
            recipient: recipient_f,
            payment_intent: pi_f,
            salt,
        }
    }
}

/// The reason the DECO prover could not produce (or could not re-verify) an attestation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecoProveError {
    /// The disclosed amount is outside the leaf's provable range `1 ≤ amountCents < 2^30`.
    AmountOutOfRange { amount: u64 },
    /// The recursion prover failed to produce the DECO leaf proof (e.g. a forged
    /// witness that is UNSAT at the leaf, or a backend error).
    ProveFailed { reason: String },
    /// Serializing the produced leaf proof to transport bytes failed.
    SerializeFailed { reason: String },
    /// The attestation carries no STARK proof (`zk_tls_proof == None`) — nothing to
    /// re-verify.
    MissingProof,
    /// The carried STARK proof does not decode / structurally validate / expose a claim.
    ProofInvalid { reason: String },
    /// The carried proof's exposed identity does not bind the attestation's facts (the
    /// proof is genuine but attests a DIFFERENT payment than the attestation claims).
    ProofFactsMismatch,
}

impl core::fmt::Display for DecoProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecoProveError::AmountOutOfRange { amount } => {
                write!(f, "amount {amount} out of provable range 1..2^30")
            }
            DecoProveError::ProveFailed { reason } => write!(f, "deco leaf prove failed: {reason}"),
            DecoProveError::SerializeFailed { reason } => {
                write!(f, "deco leaf proof serialize failed: {reason}")
            }
            DecoProveError::MissingProof => write!(f, "attestation carries no zk_tls_proof"),
            DecoProveError::ProofInvalid { reason } => write!(f, "deco proof invalid: {reason}"),
            DecoProveError::ProofFactsMismatch => {
                write!(
                    f,
                    "deco proof exposed identity does not bind the attestation facts"
                )
            }
        }
    }
}

impl std::error::Error for DecoProveError {}

/// **PRODUCE a `DecoPaymentAttestation` with a genuine STARK proof** — the prover core.
///
/// Projects the disclosed facts to the DECO leaf witness, proves the commitment as a
/// foldable recursion leaf ([`prove_deco_leaf_with_claim`]), serializes the leaf's STARK
/// proof into `zk_tls_proof`, and returns the attestation. The result:
///   * makes [`dregg_bridge::stripe_deco::StripeMirrorState::verify_deco_payment`]
///     return `Ok` for honest facts (its `payment_hash` is the canonical recompute), and
///   * cannot be produced for a forged fact — the leaf-binding tooth makes a
///     facts↔identity mismatch UNSAT at prove time.
///
/// `salt` is the transcript-commitment opening (from the notary/MPC-TLS layer,
/// [`crate::notary`]).
pub fn prove_stripe_deco(
    facts: &StripePaymentFacts,
    salt: BabyBear,
) -> Result<DecoPaymentAttestation, DecoProveError> {
    if facts.amount_cents == 0 || facts.amount_cents >= (1u64 << AMOUNT_LIMB_BITS) {
        return Err(DecoProveError::AmountOutOfRange {
            amount: facts.amount_cents,
        });
    }

    let witness = facts.to_leaf_witness(salt);
    let pis = deco_leaf_public_inputs(&witness);
    let config = ir2_leaf_wrap_config();

    let output = prove_deco_leaf_with_claim(&witness, &pis, &config)
        .map_err(|reason| DecoProveError::ProveFailed { reason })?;
    let proof_bytes = serialize_deco_leaf_proof(&output)
        .map_err(|reason| DecoProveError::SerializeFailed { reason })?;

    // The bridge attestation over the SAME facts — its committed payment_hash is the
    // canonical recompute (== the leaf's in-AIR-exposed identity by construction).
    let att = DecoPaymentAttestation::attest(
        facts.payment_intent_id.clone(),
        facts.amount_cents,
        facts.currency.clone(),
        facts.recipient,
        Some(proof_bytes),
    );
    debug_assert_eq!(att.payment_hash, witness.payment_hash());
    Ok(att)
}

/// **Re-verify the STARK proof an attestation carries** binds its disclosed facts —
/// the transport-side crypto tooth over `zk_tls_proof`.
///
/// Decodes + structurally validates the leaf proof, reads its exposed claim, and
/// checks the exposed identity (lane [`DECO_LEAF_PAYMENT_HASH_PI`]) equals the
/// attestation's committed `payment_hash` == the canonical recompute over its facts. A
/// genuine proof for a DIFFERENT payment (or a corrupted blob) is refused here BEFORE
/// the bridge verifier runs its own felt-commitment binding.
///
/// ⚑ The FULL FRI re-verification of the leaf is performed by the recursion verifier
/// when the leaf is FOLDED into the per-turn aggregate (each child is re-verified
/// in-circuit); this is the structural + exposed-claim binding a downstream runs on the
/// bytes. A forged leaf never exists to be presented — [`prove_stripe_deco`] is UNSAT
/// for forged facts.
pub fn verify_stripe_deco_stark(att: &DecoPaymentAttestation) -> Result<(), DecoProveError> {
    let bytes = att
        .zk_tls_proof
        .as_ref()
        .ok_or(DecoProveError::MissingProof)?;
    let claim = verify_deco_leaf_proof_bytes(bytes)
        .map_err(|reason| DecoProveError::ProofInvalid { reason })?;

    // Bind the exposed identity to the attestation's committed facts.
    let recomputed = stripe_payment_hash_felt(
        att.amount_cents,
        &att.currency,
        &att.recipient.0,
        &att.payment_intent_id,
    );
    if claim[DECO_LEAF_PAYMENT_HASH_PI] != recomputed
        || claim[DECO_LEAF_PAYMENT_HASH_PI] != att.payment_hash
    {
        return Err(DecoProveError::ProofFactsMismatch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facts() -> StripePaymentFacts {
        StripePaymentFacts {
            payment_intent_id: "pi_prover_001".to_string(),
            amount_cents: 2500,
            currency: "usd".to_string(),
            recipient: CellId::from_bytes([1u8; 32]),
        }
    }

    /// FAST (no proving): the prover rejects an out-of-range amount up front — the same
    /// bound the leaf's range gadget and the bridge verifier enforce.
    #[test]
    fn out_of_range_amount_refused_before_proving() {
        let mut zero = facts();
        zero.amount_cents = 0;
        assert_eq!(
            prove_stripe_deco(&zero, BabyBear::new(1)).unwrap_err(),
            DecoProveError::AmountOutOfRange { amount: 0 }
        );
        let mut huge = facts();
        huge.amount_cents = 1u64 << AMOUNT_LIMB_BITS;
        assert!(matches!(
            prove_stripe_deco(&huge, BabyBear::new(1)),
            Err(DecoProveError::AmountOutOfRange { .. })
        ));
    }

    /// FAST: the facts→identity projection is the SAME canonical felt the bridge
    /// attestation commits — so an honest attestation's payment_hash is exactly the
    /// leaf's in-AIR identity (the anti-vacuity tie, checked without the heavy STARK).
    #[test]
    fn facts_project_to_the_canonical_identity() {
        let f = facts();
        let w = f.to_leaf_witness(BabyBear::new(0x55));
        assert_eq!(w.payment_hash(), f.payment_hash());
        let att = DecoPaymentAttestation::attest(
            f.payment_intent_id.clone(),
            f.amount_cents,
            f.currency.clone(),
            f.recipient,
            None,
        );
        assert_eq!(att.payment_hash, f.payment_hash());
    }

    /// FAST: the transport tooth rejects an attestation with no proof / a garbage blob.
    #[test]
    fn stark_reverify_fails_closed_on_missing_or_garbage() {
        let f = facts();
        let no_proof = DecoPaymentAttestation::attest(
            f.payment_intent_id.clone(),
            f.amount_cents,
            f.currency.clone(),
            f.recipient,
            None,
        );
        assert_eq!(
            verify_stripe_deco_stark(&no_proof).unwrap_err(),
            DecoProveError::MissingProof
        );
        let garbage = DecoPaymentAttestation::attest(
            f.payment_intent_id.clone(),
            f.amount_cents,
            f.currency.clone(),
            f.recipient,
            Some(vec![0xABu8; 32]),
        );
        assert!(matches!(
            verify_stripe_deco_stark(&garbage),
            Err(DecoProveError::ProofInvalid { .. })
        ));
    }
}
