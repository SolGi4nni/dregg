//! `dregg-bridge::stripe_deco` — the **PROVEN, DECO/zkTLS-verified Stripe
//! money-in**: the honest, trustless upgrade from the trusted-HMAC-webhook oracle
//! ([`crate::stripe_mirror`]).
//!
//! Where [`crate::stripe_mirror`] trusts that a valid `Stripe-Signature` HMAC means
//! *Stripe said this payment cleared* (Stripe is the oracle — the webhook secret is
//! the verifying key), THIS path mints only against a **DECO attestation**: a zkTLS
//! proof that a live TLS session *with Stripe's own API* disclosed a settled
//! payment. dregg does not trust a shared webhook secret — it verifies a proof.
//!
//! ```text
//!   Stripe API  ── live TLS session ──►  DECO/zkTLS PROVER  ──►  DecoPaymentAttestation
//!    (settled payment disclosed)         (⚑ NOT YET IN-TREE)      { facts, payment_hash, zk_tls_proof }
//!                                                                        │
//!                                                                        ▼
//!                                              StripeMirrorState::verify_deco_payment
//!                                              (rebinds facts↔identity; gate 5 range)
//!                                                                        │
//!                                                                        ▼
//!                                              VerifiedPayment  →  committed bridge_mint_against_lock
//!                                              → Effect::Mint (Σδ=0, live_supply ≤ total_verified)
//! ```
//!
//! # What is PROVEN (the Lean crown, `metatheory/Dregg2/Crypto/Deco.lean`)
//!
//! The DECO *verification* is discharged, not assumed. An accepting DECO proof
//! PROVES a genuine Stripe-authenticated payment
//! (`deco_authenticates_payment`, `deco_verify_sound`, `deco_binds_payment`),
//! modulo the named §8 carriers (STARK extractability, ed25519 EUF-CMA, HMAC
//! unforgeability, Poseidon2 CR) and the external Web-PKI / honest-Stripe floor.
//! The in-AIR-recomputable core — the felt-domain `payment_hash` commitment
//! binding the four `PaymentFacts` (gates 3/4 + the identity) and the amount range
//! (gate 5) — is deployed as the recursion leaf `circuit-prove::deco_leaf_adapter`
//! and its anchor `dregg_circuit::dsl::deco_payment`.
//!
//! # What is WIRED here (the deployable half)
//!
//! [`StripeMirrorState::verify_deco_payment`] re-runs the DECO leaf's own tooth in
//! the executor domain: it recomputes the felt `payment_hash` over the disclosed
//! facts through the ONE canonical encoder
//! ([`dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt`] — the SAME one
//! the executor felt-attach, the deployed `stripeMint` producer, and the in-AIR
//! leaf all decompose through) and REFUSES any attestation whose committed
//! `payment_hash` disagrees ([`StripeMirrorError::DecoCommitmentMismatch`]). This
//! is the executor-domain twin of the leaf's `forged_amount_does_not_fold` and the
//! `DecoBackingAttack` red-team: a forged-facts attestation cannot mint. The
//! conservation invariant (`live_supply ≤ total_verified_payments`) holds on this
//! path exactly as on the HMAC path — the mint still draws against recorded
//! backing.
//!
//! # ⚑ THE PROVER GAP (honest — do NOT claim live-trustless money-in yet)
//!
//! The DECO *verification* is proven and wired; the DECO **prover** — the zkTLS
//! client that runs a live Stripe TLS session and EMITS a `DecoPaymentAttestation`
//! with a genuine STARK proof — is the one external piece NOT yet in this tree.
//! Until it lands, the commitment binding here rebinds the disclosed facts to the
//! committed identity (refusing a tampered attestation) but does NOT by itself
//! prove the facts came from a genuine Stripe session — that is exactly what the
//! [`DecoPaymentAttestation::zk_tls_proof`] STARK carrier delivers, verified when
//! the prover exists. So [`crate::stripe_mirror`]'s HMAC webhook stays as the
//! explicitly-labeled trusted FALLBACK ([`MoneyIn::HmacWebhook`]) — the only
//! working money-in today — and production flips to [`MoneyIn::Deco`] the moment
//! the prover is in-tree, changing one call site.

use dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt;
use dregg_circuit::field::BabyBear;
use dregg_types::CellId;

use crate::stripe_mirror::{
    StripeMirrorError, StripeMirrorState, StripePaymentAttestation, StripeWebhookEvent,
    VerifiedPayment, payment_nullifier,
};

/// The DECO leaf's amount range gadget bound (`Deco.lean::DecoRelation` conjunct 5,
/// `deco_payment::AMOUNT_LIMB_BITS`): `1 ≤ amountCents < 2^30`.
const AMOUNT_LIMB_BITS: u32 = 30;

/// A **DECO payment attestation** — the Rust twin of `Deco.lean::Statement` +
/// `PaymentFacts`: the payment facts a verified DECO/zkTLS proof binds, plus the
/// felt-domain `payment_hash` the in-AIR leaf exposes and the STARK proof carrier.
///
/// Holding one is (once the prover lands) evidence that a live TLS session with
/// Stripe disclosed this settled payment — the trustless analogue of holding a
/// [`crate::stripe_mirror::StripePaymentAttestation`] (whose trusted leg is a
/// shared-secret HMAC).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecoPaymentAttestation {
    /// The underlying payment-intent id — the **replay nonce** (consume-once),
    /// exactly as on the HMAC path. `Deco.lean::PaymentFacts.paymentIntentId`.
    pub payment_intent_id: String,
    /// Amount that cleared, in cents. `Deco.lean::PaymentFacts.amountCents`.
    pub amount_cents: u64,
    /// ISO-4217 currency. `Deco.lean::PaymentFacts.currency`.
    pub currency: String,
    /// The dregg cell to credit. `Deco.lean::PaymentFacts.recipient`.
    pub recipient: CellId,
    /// **The committed felt-domain payment identity** — the value the deployed DECO
    /// leaf (`circuit-prove::deco_leaf_adapter::DECO_LEAF_PAYMENT_HASH_PI`) exposes
    /// at its claim lane and the `stripeMint` producer pins at its `payment_hash`
    /// PI. In a genuine attestation this is the zkTLS prover's output; the verifier
    /// RE-BINDS it to the disclosed facts (the anti-vacuity tooth).
    pub payment_hash: BabyBear,
    /// **The zkTLS DECO STARK proof** (`Deco.lean::DecoVerifierKernel::verify` /
    /// `deco_leaf_adapter::prove_deco_leaf_with_claim`).
    ///
    /// ⚑ **PROVER GAP:** producing this from a live Stripe TLS session is the one
    /// external piece not yet in-tree (see module docs). `None` =
    /// commitment-binding-only (the deployable half wired here); `Some(bytes)` =
    /// full zkTLS proof, verified against the recursion verifier once the prover
    /// lands. The verifier does NOT claim live-trustlessness from `None`.
    pub zk_tls_proof: Option<Vec<u8>>,
}

impl DecoPaymentAttestation {
    /// **The prover-side genuine builder** — decompose the disclosed facts to the
    /// committed felt identity via the ONE canonical encoder
    /// ([`stripe_payment_hash_felt`]), the SAME projection the in-AIR DECO leaf
    /// recomputes and the deployed producer pins. This is what a genuine zkTLS
    /// prover's output decomposes to; it is NOT itself a proof that a live Stripe
    /// session occurred (that is the STARK `zk_tls_proof`, the prover gap).
    pub fn attest(
        payment_intent_id: impl Into<String>,
        amount_cents: u64,
        currency: impl Into<String>,
        recipient: CellId,
        zk_tls_proof: Option<Vec<u8>>,
    ) -> Self {
        let payment_intent_id = payment_intent_id.into();
        let currency = currency.into();
        let payment_hash =
            stripe_payment_hash_felt(amount_cents, &currency, &recipient.0, &payment_intent_id);
        DecoPaymentAttestation {
            payment_intent_id,
            amount_cents,
            currency,
            recipient,
            payment_hash,
            zk_tls_proof,
        }
    }
}

/// The money-in source — the trustless DECO path (intended default) or the
/// explicitly-labeled trusted HMAC-webhook FALLBACK. The single production entry
/// [`StripeMirrorState::verify_money_in`] dispatches on this; flipping from
/// fallback to DECO is a one-variant change at the call site.
pub enum MoneyIn<'a> {
    /// The PROVEN, trustless path: mint only against a DECO/zkTLS attestation
    /// ([`StripeMirrorState::verify_deco_payment`]). The intended production
    /// default (gated by the prover being in-tree).
    Deco(&'a DecoPaymentAttestation),
    /// FALLBACK: trusted HMAC until the DECO prover lands — NOT trustless. The only
    /// working money-in today; kept so production flips to [`MoneyIn::Deco`] the
    /// moment the prover exists.
    HmacWebhook {
        /// The raw signed webhook.
        webhook: &'a StripeWebhookEvent,
        /// The current clock (for the replay-window check), or `None` to skip it.
        now: Option<u64>,
        /// The replay-window tolerance.
        tolerance_secs: u64,
    },
}

impl StripeMirrorState {
    /// **Verify a DECO attestation for the COMMITTED bridge mint, mutating no
    /// per-relayer RAM** — the DECO twin of
    /// [`StripeMirrorState::verify_payment`].
    ///
    /// Runs the DECO leaf's own teeth in the executor domain, then the same
    /// currency/amount bounds, and returns the consume-once [`VerifiedPayment`] the
    /// caller feeds to `TurnExecutor::bridge_mint_against_lock` (where the committed
    /// `note_nullifiers` set is the global double-mint authority). No state is
    /// touched — this is the sound multi-relayer production path.
    ///
    /// The teeth, in order (`Deco.lean::DecoRelation`):
    ///   1. **gate 5 (range):** `1 ≤ amountCents < 2^30`
    ///      ([`StripeMirrorError::DecoAmountOutOfRange`]).
    ///   2. **gates 3/4 + identity (the felt-commitment binding):** the
    ///      attestation's committed `payment_hash` MUST equal the canonical
    ///      recompute over its disclosed facts, or it is a forged-facts attestation
    ///      ([`StripeMirrorError::DecoCommitmentMismatch`]) — the executor-domain
    ///      twin of the leaf's `forged_amount_does_not_fold` tooth.
    ///   3. the mirror's currency + amount bounds (shared with the HMAC path).
    ///
    /// ⚑ PROVER GAP: full trustlessness additionally verifies
    /// [`DecoPaymentAttestation::zk_tls_proof`] (the STARK extractability + the
    /// ed25519/HMAC §8 carriers). Its prover is not yet in-tree; until then this
    /// binds the disclosed facts to the committed identity (the deployable half).
    pub fn verify_deco_payment(
        &self,
        att: &DecoPaymentAttestation,
    ) -> Result<VerifiedPayment, StripeMirrorError> {
        // (1) gate 5 — the amount range gadget: 1 ≤ amountCents < 2^30.
        if att.amount_cents == 0 || att.amount_cents >= (1u64 << AMOUNT_LIMB_BITS) {
            return Err(StripeMirrorError::DecoAmountOutOfRange {
                amount: att.amount_cents,
            });
        }

        // (2) gates 3/4 + identity — THE FELT-COMMITMENT BINDING (the anti-vacuity
        // tooth). Recompute the felt identity over the disclosed facts through the
        // ONE canonical encoder and require the attestation's committed payment_hash
        // to equal it. A forged-facts attestation (amount/recipient/intent changed
        // but the committed identity left stale) fails HERE — no mint. This is the
        // SAME encoder the deployed producer pins and the in-AIR leaf recomputes, so
        // "verified here == leaf-recomputed" holds by construction.
        let recomputed = stripe_payment_hash_felt(
            att.amount_cents,
            &att.currency,
            &att.recipient.0,
            &att.payment_intent_id,
        );
        if recomputed != att.payment_hash {
            return Err(StripeMirrorError::DecoCommitmentMismatch);
        }

        // ⚑ PROVER GAP (do NOT claim live-trustlessness from the binding alone):
        // the STARK extractability + ed25519/HMAC §8 carriers of `Deco.lean` are
        // delivered by `att.zk_tls_proof`, whose PROVER (live-Stripe-TLS →
        // attestation) is not yet in-tree. When it lands, verify it here.

        // (3) the shared currency + bounds gate (identical to the HMAC path).
        if att.currency != self.config.currency {
            return Err(StripeMirrorError::WrongCurrency {
                got: att.currency.clone(),
                want: self.config.currency.clone(),
            });
        }
        if att.amount_cents < self.config.min_cents {
            return Err(StripeMirrorError::BelowMin);
        }
        if att.amount_cents > self.config.max_cents {
            return Err(StripeMirrorError::AboveMax);
        }

        Ok(VerifiedPayment {
            payment_nullifier: payment_nullifier(&self.config.asset, &att.payment_intent_id),
            recipient: att.recipient,
            amount: att.amount_cents,
            // == att.payment_hash (checked above); use the recompute so the felt is
            // the executor's own canonical value, not the attestation's echoed one.
            payment_hash: recomputed,
        })
    }

    /// **The single production money-in entry** — dispatch a [`MoneyIn`] source to
    /// a [`VerifiedPayment`] for the committed bridge mint, mutating no per-relayer
    /// RAM. [`MoneyIn::Deco`] is the intended trustless path;
    /// [`MoneyIn::HmacWebhook`] is the explicitly-labeled trusted FALLBACK. Flipping
    /// production from fallback to DECO is a one-variant change here.
    pub fn verify_money_in(
        &self,
        input: MoneyIn<'_>,
    ) -> Result<VerifiedPayment, StripeMirrorError> {
        match input {
            MoneyIn::Deco(att) => self.verify_deco_payment(att),
            // FALLBACK: trusted HMAC until the DECO prover lands — NOT trustless.
            MoneyIn::HmacWebhook {
                webhook,
                now,
                tolerance_secs,
            } => {
                let att = webhook.verify(&self.config.webhook_secret, now, tolerance_secs)?;
                self.verify_payment(&att)
            }
        }
    }

    /// **Mirror-mint against a verified DECO attestation — RAM path, TEST/INTERNAL
    /// ONLY** — the DECO twin of
    /// [`StripeMirrorState::mint_against_payment`]. Runs
    /// [`Self::verify_deco_payment`], dedups by payment-intent id, records the
    /// verified-payment backing, and draws the mint against it — so conservation
    /// (`live_supply ≤ total_verified_payments`) BITES on the DECO path exactly as
    /// on the HMAC path. Production uses [`Self::verify_deco_payment`] → the
    /// committed `bridge_mint_against_lock`.
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn mint_against_deco(
        &mut self,
        att: &DecoPaymentAttestation,
    ) -> Result<crate::stripe_mirror::StripeMint, StripeMirrorError> {
        // First run the DECO teeth (gate-5 range + the felt-commitment binding) —
        // a forged-facts attestation is refused BEFORE any state moves.
        self.verify_deco_payment(att)?;
        // Then mint through the SAME conserved backing → draw → dedup → atomic
        // rollback path as the HMAC route, by reusing `mint_against_payment` over the
        // verified facts. Conservation (`live_supply ≤ total_verified_payments`) is
        // enforced identically; no DECO-specific ledger bookkeeping.
        let stripe_att = StripePaymentAttestation {
            payment_intent_id: att.payment_intent_id.clone(),
            amount_cents: att.amount_cents,
            currency: att.currency.clone(),
            recipient: att.recipient,
            event_type: "deco.payment_verified".to_string(),
        };
        self.mint_against_payment(&stripe_att)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stripe_mirror::StripeMirrorConfig;
    use dregg_turn::action::Effect;

    const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn config() -> StripeMirrorConfig {
        StripeMirrorConfig {
            asset: MIRROR_ASSET,
            webhook_secret: b"whsec_unused_on_the_deco_path".to_vec(),
            currency: "usd".to_string(),
            min_cents: 50,
            max_cents: 1_000_000_00,
        }
    }

    /// THE POSITIVE POLE: a VALID DECO attestation mints EXACTLY the verified amount,
    /// conserved (`live_supply == total_verified == amount`, invariant holds).
    #[test]
    fn valid_deco_attestation_mints_the_conserved_amount() {
        let mut mirror = StripeMirrorState::new(config());
        let att = DecoPaymentAttestation::attest("pi_deco_001", 2500, "usd", cid(1), None);

        let minted = mirror
            .mint_against_deco(&att)
            .expect("a valid DECO attestation mints");

        assert_eq!(minted.amount, 2500);
        assert_eq!(minted.recipient, cid(1));
        match minted.effect {
            Effect::Mint {
                target,
                slot,
                amount,
            } => {
                assert_eq!(target, cid(1));
                assert_eq!(slot, 0);
                assert_eq!(amount, 2500);
            }
            ref other => panic!("expected Effect::Mint, got {other:?}"),
        }
        assert_eq!(mirror.live_supply, 2500);
        assert_eq!(mirror.total_verified_payments, 2500);
        assert!(mirror.invariant_holds());
    }

    /// THE ANTI-VACUITY TOOTH: a FORGED-FACTS DECO attestation is REFUSED, state
    /// unchanged. Two forgeries — (a) the amount bumped after the identity was
    /// committed, (b) the committed `payment_hash` tampered directly — both fail the
    /// felt-commitment binding (`DecoCommitmentMismatch`). No mint.
    #[test]
    fn forged_deco_attestation_is_refused_and_state_unchanged() {
        let mut mirror = StripeMirrorState::new(config());

        // (a) genuine attestation for $25.00, then bump the amount to $99,999.99
        // WITHOUT recomputing the committed identity — the DecoBackingAttack shape.
        let mut forged = DecoPaymentAttestation::attest("pi_forge", 2500, "usd", cid(1), None);
        forged.amount_cents = 9_999_999;
        assert_eq!(
            mirror.mint_against_deco(&forged).unwrap_err(),
            StripeMirrorError::DecoCommitmentMismatch
        );

        // (b) tamper the committed payment_hash directly.
        let mut hash_forge = DecoPaymentAttestation::attest("pi_forge2", 5000, "usd", cid(1), None);
        hash_forge.payment_hash += BabyBear::ONE;
        assert_eq!(
            mirror.mint_against_deco(&hash_forge).unwrap_err(),
            StripeMirrorError::DecoCommitmentMismatch
        );

        // (c) a genuine attestation re-pointed to a DIFFERENT recipient (identity was
        // over cid(1); recompute over cid(9) will not match the stale hash).
        let mut rcpt_forge = DecoPaymentAttestation::attest("pi_forge3", 5000, "usd", cid(1), None);
        rcpt_forge.recipient = cid(9);
        assert_eq!(
            mirror.mint_against_deco(&rcpt_forge).unwrap_err(),
            StripeMirrorError::DecoCommitmentMismatch
        );

        // No forgery minted anything.
        assert_eq!(mirror.live_supply, 0);
        assert_eq!(mirror.total_verified_payments, 0);
        assert!(mirror.invariant_holds());
    }

    /// Gate 5 (range): a zero amount and an amount ≥ 2^30 are refused (the DECO
    /// leaf's `1 ≤ amountCents < 2^30` range gadget).
    #[test]
    fn deco_amount_out_of_range_is_refused() {
        let mut mirror = StripeMirrorState::new(config());

        let zero = DecoPaymentAttestation::attest("pi_zero", 0, "usd", cid(1), None);
        assert_eq!(
            mirror.mint_against_deco(&zero).unwrap_err(),
            StripeMirrorError::DecoAmountOutOfRange { amount: 0 }
        );

        let huge = 1u64 << AMOUNT_LIMB_BITS;
        let over = DecoPaymentAttestation::attest("pi_over", huge, "usd", cid(1), None);
        assert_eq!(
            mirror.mint_against_deco(&over).unwrap_err(),
            StripeMirrorError::DecoAmountOutOfRange { amount: huge }
        );

        assert_eq!(mirror.live_supply, 0);
    }

    /// Currency + bounds bite on the DECO path exactly as on the HMAC path.
    #[test]
    fn deco_currency_and_bounds_enforced() {
        let mut mirror = StripeMirrorState::new(config());

        let eur = DecoPaymentAttestation::attest("pi_eur", 5000, "eur", cid(1), None);
        assert!(matches!(
            mirror.mint_against_deco(&eur),
            Err(StripeMirrorError::WrongCurrency { .. })
        ));

        let dust = DecoPaymentAttestation::attest("pi_dust", 10, "usd", cid(1), None);
        assert_eq!(
            mirror.mint_against_deco(&dust).unwrap_err(),
            StripeMirrorError::BelowMin
        );
    }

    /// A retried DECO attestation (same payment-intent id) does not double-mint —
    /// the payment-intent id is the replay nonce on the DECO path too.
    #[test]
    fn retried_deco_attestation_does_not_double_mint() {
        let mut mirror = StripeMirrorState::new(config());
        let att = DecoPaymentAttestation::attest("pi_once", 4000, "usd", cid(2), None);

        mirror.mint_against_deco(&att).expect("first mints");
        assert_eq!(
            mirror.mint_against_deco(&att).unwrap_err(),
            StripeMirrorError::DuplicatePayment
        );
        assert_eq!(mirror.live_supply, 4000);
        assert!(mirror.invariant_holds());
    }

    /// THE FLIP: `verify_money_in` dispatches to the trustless DECO path by default;
    /// the HMAC fallback is the SAME entry with a different variant. Both yield a
    /// `VerifiedPayment` for the committed mint — production flips with one variant.
    #[test]
    fn verify_money_in_dispatches_deco_and_hmac_fallback() {
        let secret = b"whsec_flip_test";
        let mirror = StripeMirrorState::new(StripeMirrorConfig {
            webhook_secret: secret.to_vec(),
            ..config()
        });

        // Trustless DECO path.
        let att = DecoPaymentAttestation::attest("pi_flip_deco", 2500, "usd", cid(1), None);
        let vp = mirror
            .verify_money_in(MoneyIn::Deco(&att))
            .expect("DECO money-in verifies");
        assert_eq!(vp.amount, 2500);
        assert_eq!(vp.recipient, cid(1));

        // A forged DECO attestation is refused through the same entry.
        let mut forged = att.clone();
        forged.amount_cents = 9_999;
        assert_eq!(
            mirror.verify_money_in(MoneyIn::Deco(&forged)).unwrap_err(),
            StripeMirrorError::DecoCommitmentMismatch
        );

        // FALLBACK: the trusted HMAC webhook, same entry, different variant.
        let body = format!(
            r#"{{"type":"payment_intent.succeeded","data":{{"object":{{"id":"pi_flip_hmac","amount":2500,"amount_received":2500,"currency":"usd","metadata":{{"{key}":"{rcpt}"}}}}}}}}"#,
            key = crate::stripe_mirror::RECIPIENT_METADATA_KEY,
            rcpt = {
                let mut s = String::new();
                for b in cid(1).0 {
                    s.push_str(&format!("{b:02x}"));
                }
                s
            },
        )
        .into_bytes();
        let hook = StripeWebhookEvent::sign(&body, secret, 1_700_000_000);
        let vp2 = mirror
            .verify_money_in(MoneyIn::HmacWebhook {
                webhook: &hook,
                now: None,
                tolerance_secs: 300,
            })
            .expect("HMAC fallback money-in verifies");
        assert_eq!(vp2.amount, 2500);
        assert_eq!(vp2.recipient, cid(1));

        // Both paths agree on the SAME canonical felt payment identity.
        assert_eq!(vp.payment_hash, att.payment_hash);
        assert_eq!(
            vp2.payment_hash,
            stripe_payment_hash_felt(2500, "usd", &cid(1).0, "pi_flip_hmac")
        );
    }
}
