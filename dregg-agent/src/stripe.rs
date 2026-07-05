//! `stripe` — the **earn** rail: a genuine Stripe webhook verify + a conserved,
//! receipted mint.
//!
//! # ⚑ STANDALONE DEMO STUB — the REAL earn goes through `bridge`'s DECO money-in
//!
//! This is the open-core, dependency-light **standalone twin** of breadstuffs'
//! `bridge/src/stripe_mirror.rs` (`mint_against_webhook`). `dregg-agent` is
//! deliberately **substrate-only** (no `bridge` / `dregg-circuit` deps — see the
//! crate manifest), so this module keeps its OWN private ed25519 receipt chain
//! ([`MintReceipt`]) rather than minting a real kernel `Effect::Mint` into dregg's
//! value layer. It is a self-contained EARN demo, NOT the production money-in.
//!
//! The **real, trustless earn** is `bridge`'s DECO-verified money-in
//! (`dregg_bridge::stripe_deco::StripeMirrorState::verify_deco_payment` →
//! `MoneyIn::Deco`): mint only against a DECO/zkTLS attestation that a live Stripe
//! TLS session disclosed a settled payment, verified against the felt-commitment
//! binding `Deco.lean` proves and the deployed DECO leaf enforces in-AIR. An agent
//! that must actually mint into the shared value layer routes its earn through
//! that bridge path (with the credentials/cell it already holds), NOT through this
//! private receipt chain. This twin stays here only as the dependency-free demo of
//! the Stripe signature scheme + the conservation shape.
//!
//! What is real in this stub: it speaks the **real** Stripe signature scheme —
//! `Stripe-Signature: t=<ts>,v1=<hex(HMAC-SHA256(secret, "{ts}.{body}"))>` —
//! verifies it constant-time, enforces a replay window and amount/currency bounds,
//! dedups by `payment_intent_id` (double-mint prevention), and on success mints
//! conserved USD-credit sealed into a prev-hash-chained, ed25519-signed
//! [`MintReceipt`] a non-witness can re-verify. Like the bridge fallback, the HMAC
//! webhook is a TRUSTED oracle — not the trustless DECO path.
//!
//! The verification logic is real; only the *transport* is recorded (a fixture
//! signed webhook) so the demo is deterministic and offline. A forged signature is
//! refused; a retry of an already-minted `payment_intent_id` is refused. The minted
//! cents become the agent's spendable budget ceiling (the P&L loop closes in
//! [`crate::business`]).

use std::collections::BTreeSet;

use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use subtle::ConstantTimeEq;

use crate::receipt::{BodyHasher, ReceiptAttestation, ReceiptBody, ReceiptChain};

type HmacSha256 = Hmac<Sha256>;

/// The replay-window tolerance Stripe documents (5 minutes).
pub const DEFAULT_TOLERANCE_SECS: u64 = 300;

/// A signed Stripe webhook as it arrives at an endpoint: the raw JSON `payload`
/// and the `Stripe-Signature` header value. Construct a fixture with [`sign`] (the
/// oracle side, what Stripe's signer does); verify it with
/// [`StripeMirror::mint_against_webhook`].
///
/// [`sign`]: StripeWebhook::sign
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StripeWebhook {
    /// The raw event body bytes (the exact bytes the signature is computed over).
    pub payload: Vec<u8>,
    /// The `Stripe-Signature` header value (`t=<ts>,v1=<hex>`).
    pub signature_header: String,
}

impl StripeWebhook {
    /// Sign `payload` the way Stripe's signer does and produce the webhook — the
    /// inverse of verification, used to mint a fixture signed event for the demo.
    /// `t=<timestamp>,v1=<hex(HMAC-SHA256(secret, "{timestamp}.{body}"))>`.
    pub fn sign(payload: &[u8], secret: &[u8], timestamp: u64) -> StripeWebhook {
        let sig = hex_lower(&expected_sig(payload, secret, timestamp));
        StripeWebhook {
            payload: payload.to_vec(),
            signature_header: format!("t={timestamp},v1={sig}"),
        }
    }

    /// Tamper a signed webhook's body WITHOUT re-signing — the forged-signature
    /// case: the bytes change, the header's `v1` no longer matches.
    pub fn with_forged_body(mut self, payload: &[u8]) -> StripeWebhook {
        self.payload = payload.to_vec();
        self
    }
}

/// The HMAC-SHA256 over Stripe's signed payload `"{timestamp}.{body}"`.
fn expected_sig(payload: &[u8], secret: &[u8], timestamp: u64) -> [u8; 32] {
    let mut mac = <HmacSha256 as Mac>::new_from_slice(secret).expect("HMAC accepts any key length");
    mac.update(timestamp.to_string().as_bytes());
    mac.update(b".");
    mac.update(payload);
    mac.finalize().into_bytes().into()
}

/// A verified payment Stripe attested as cleared — extracted from a webhook only
/// after its signature verified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedPayment {
    /// The payment-intent id (the replay nonce / double-mint nullifier).
    pub payment_intent_id: String,
    /// The cleared amount, in cents.
    pub amount_cents: i64,
    /// The ISO-4217 currency (lowercase).
    pub currency: String,
    /// The Stripe event type (`payment_intent.succeeded`).
    pub event_type: String,
}

/// Why a webhook was refused (no mint, no state change).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StripeError {
    /// The `Stripe-Signature` header was not `t=<int>,v1=<hex>…`.
    MalformedSignatureHeader,
    /// No offered `v1` matched the recomputed HMAC — a FORGED webhook or wrong
    /// secret. The headline earn-path tooth.
    SignatureMismatch,
    /// The webhook timestamp is older than the replay tolerance (a replayed event).
    TimestampTooOld {
        /// How old (seconds).
        age_secs: u64,
        /// The tolerance it exceeded.
        tolerance_secs: u64,
    },
    /// The verified body is not a recognizable Stripe event.
    MalformedPayload,
    /// An event type the earn rail does not handle.
    UnhandledEventType(String),
    /// The payment currency is not the mirror's currency.
    WrongCurrency {
        /// The payment's currency.
        got: String,
        /// The mirror's currency.
        want: String,
    },
    /// The amount is below the dust floor.
    BelowMin,
    /// The amount is above the per-payment ceiling (governance required).
    AboveMax,
    /// This `payment_intent_id` was already minted — a webhook RETRY. Double-mint
    /// prevented (the dedup tooth).
    DuplicatePayment,
}

impl std::fmt::Display for StripeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StripeError::MalformedSignatureHeader => {
                write!(f, "malformed Stripe-Signature header")
            }
            StripeError::SignatureMismatch => {
                write!(
                    f,
                    "no v1 signature matched the body (forged or wrong secret)"
                )
            }
            StripeError::TimestampTooOld {
                age_secs,
                tolerance_secs,
            } => write!(
                f,
                "webhook timestamp too old: {age_secs}s > tolerance {tolerance_secs}s"
            ),
            StripeError::MalformedPayload => {
                write!(f, "webhook body is not a recognizable Stripe event")
            }
            StripeError::UnhandledEventType(t) => write!(f, "unhandled Stripe event type: {t}"),
            StripeError::WrongCurrency { got, want } => {
                write!(f, "payment currency {got} != mirror currency {want}")
            }
            StripeError::BelowMin => write!(f, "amount below the mirror minimum"),
            StripeError::AboveMax => write!(f, "amount above the per-payment maximum"),
            StripeError::DuplicatePayment => {
                write!(
                    f,
                    "payment_intent_id already minted (double-mint prevented)"
                )
            }
        }
    }
}

impl std::error::Error for StripeError {}

/// The conserved-mint record sealed when a verified payment becomes USD-credit.
/// A [`ReceiptBody`]: prev-hash-chained + ed25519-signed, so the whole earn ledger
/// re-witnesses with [`crate::receipt::verify_chain`]. A forged amount / intent id
/// breaks the signature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MintReceipt {
    /// The chain position.
    pub seq: u64,
    /// The asset minted (the USD-credit mirror; 1 unit = 1 cent).
    pub asset: String,
    /// The Stripe payment-intent id this mint backs (the dedup nullifier).
    pub payment_intent_id: String,
    /// The cents minted.
    pub amount_cents: i64,
    /// The dregg recipient credited (the agent's cell / budget subject).
    pub recipient: String,
    /// The conserved live supply AFTER this mint (≤ total verified payments).
    pub live_supply_after: i64,
    /// The chained attestation (prev-hash link + ed25519 signature).
    pub attestation: Option<ReceiptAttestation>,
}

impl ReceiptBody for MintReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"dregg-agent-stripe-mint-receipt-v1");
        h.u64(self.seq)
            .field(self.asset.as_bytes())
            .field(self.payment_intent_id.as_bytes())
            .u64(self.amount_cents as u64)
            .field(self.recipient.as_bytes())
            .u64(self.live_supply_after as u64);
        h.finalize()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attestation.as_ref()
    }
}

/// The dregg-side USD-credit mirror: it verifies inbound Stripe webhooks, enforces
/// the bounds + dedup, and mints conserved, receipted credit. `live_supply` never
/// exceeds `total_verified_payments` (conservation), so a mint with no verified
/// payment is impossible by construction.
pub struct StripeMirror {
    asset: String,
    webhook_secret: Vec<u8>,
    currency: String,
    min_cents: i64,
    max_cents: i64,
    tolerance_secs: u64,
    seen_payments: BTreeSet<String>,
    total_verified_payments: i64,
    live_supply: i64,
    chain: ReceiptChain,
    seq: u64,
}

impl StripeMirror {
    /// Open a mirror for `asset`, verifying webhooks under `webhook_secret`,
    /// accepting `currency`, between `min_cents` and `max_cents`, sealing mints
    /// under the chain seeded by `chain_seed` (deterministic for the demo).
    pub fn new(
        asset: impl Into<String>,
        webhook_secret: impl Into<Vec<u8>>,
        currency: impl Into<String>,
        min_cents: i64,
        max_cents: i64,
        chain_seed: [u8; 32],
    ) -> StripeMirror {
        StripeMirror {
            asset: asset.into(),
            webhook_secret: webhook_secret.into(),
            currency: currency.into(),
            min_cents,
            max_cents,
            tolerance_secs: DEFAULT_TOLERANCE_SECS,
            seen_payments: BTreeSet::new(),
            total_verified_payments: 0,
            live_supply: 0,
            chain: ReceiptChain::from_seed(chain_seed),
            seq: 0,
        }
    }

    /// The minted asset id.
    pub fn asset(&self) -> &str {
        &self.asset
    }

    /// The conserved live supply (cents currently minted; ≤ verified payments).
    pub fn live_supply(&self) -> i64 {
        self.live_supply
    }

    /// The public key a non-witness verifies the mint chain under.
    pub fn signer(&self) -> [u8; 32] {
        self.chain.signer_public()
    }

    /// The conservation invariant: minted credit never exceeds verified payments.
    pub fn invariant_holds(&self) -> bool {
        self.live_supply <= self.total_verified_payments
    }

    /// **Verify a Stripe webhook and mint against it, the real Stripe way.**
    ///
    /// 1. Parse `t=` + every `v1=` from the header.
    /// 2. Recompute `HMAC-SHA256(secret, "{t}.{body}")`, constant-time compare it to
    ///    each offered `v1` (a forged body / wrong secret is refused).
    /// 3. If `now` is `Some`, reject a timestamp older than the replay tolerance.
    /// 4. Parse the verified body: require `payment_intent.succeeded`, the right
    ///    currency, and an amount inside the bounds.
    /// 5. Dedup by `payment_intent_id` — a retry of an already-minted payment is
    ///    refused (double-mint prevented).
    /// 6. Raise the conserved backing + live supply and seal a [`MintReceipt`].
    ///
    /// On ANY error the mirror state is left unchanged (fail-closed).
    pub fn mint_against_webhook(
        &mut self,
        webhook: &StripeWebhook,
        recipient: &str,
        now: Option<u64>,
    ) -> Result<MintReceipt, StripeError> {
        let payment = self.verify(webhook, now)?;
        // (5) double-mint dedup.
        if self.seen_payments.contains(&payment.payment_intent_id) {
            return Err(StripeError::DuplicatePayment);
        }
        // (6) raise backing + live supply (conserved), seal the receipt.
        self.total_verified_payments += payment.amount_cents;
        self.live_supply += payment.amount_cents;
        self.seen_payments.insert(payment.payment_intent_id.clone());

        let seq = self.seq;
        self.seq += 1;
        let mut receipt = MintReceipt {
            seq,
            asset: self.asset.clone(),
            payment_intent_id: payment.payment_intent_id,
            amount_cents: payment.amount_cents,
            recipient: recipient.to_string(),
            live_supply_after: self.live_supply,
            attestation: None,
        };
        receipt.attestation = Some(self.chain.seal(receipt.body_hash(), seq, None));
        Ok(receipt)
    }

    /// Verify the signature + bounds and return the [`VerifiedPayment`] without
    /// minting (the pure check, also used by [`mint_against_webhook`]).
    pub fn verify(
        &self,
        webhook: &StripeWebhook,
        now: Option<u64>,
    ) -> Result<VerifiedPayment, StripeError> {
        let (timestamp, v1s) = parse_signature_header(&webhook.signature_header)?;

        // (2) constant-time compare against every offered v1 (rotation-safe).
        let expected = expected_sig(&webhook.payload, &self.webhook_secret, timestamp);
        let matched = v1s.iter().any(|hexsig| {
            decode_hex32(hexsig)
                .map(|got| got.ct_eq(&expected).into())
                .unwrap_or(false)
        });
        if !matched {
            return Err(StripeError::SignatureMismatch);
        }

        // (3) replay window.
        if let Some(now) = now {
            let age = now.saturating_sub(timestamp);
            if age > self.tolerance_secs {
                return Err(StripeError::TimestampTooOld {
                    age_secs: age,
                    tolerance_secs: self.tolerance_secs,
                });
            }
        }

        // (4) parse + bounds.
        let payment = parse_payment_event(&webhook.payload)?;
        if payment.currency != self.currency {
            return Err(StripeError::WrongCurrency {
                got: payment.currency,
                want: self.currency.clone(),
            });
        }
        if payment.amount_cents < self.min_cents {
            return Err(StripeError::BelowMin);
        }
        if payment.amount_cents > self.max_cents {
            return Err(StripeError::AboveMax);
        }
        Ok(payment)
    }
}

/// Parse `t=<int>` and the list of `v1=<hex>` from a `Stripe-Signature` header.
fn parse_signature_header(header: &str) -> Result<(u64, Vec<String>), StripeError> {
    let mut timestamp: Option<u64> = None;
    let mut v1s: Vec<String> = Vec::new();
    for part in header.split(',') {
        let part = part.trim();
        if let Some(t) = part.strip_prefix("t=") {
            timestamp = t.parse::<u64>().ok();
        } else if let Some(sig) = part.strip_prefix("v1=") {
            v1s.push(sig.to_string());
        }
    }
    match timestamp {
        Some(t) if !v1s.is_empty() => Ok((t, v1s)),
        _ => Err(StripeError::MalformedSignatureHeader),
    }
}

/// Parse a verified `payment_intent.succeeded` body into a [`VerifiedPayment`].
fn parse_payment_event(body: &[u8]) -> Result<VerifiedPayment, StripeError> {
    let v: serde_json::Value =
        serde_json::from_slice(body).map_err(|_| StripeError::MalformedPayload)?;
    let event_type = v
        .get("type")
        .and_then(|t| t.as_str())
        .ok_or(StripeError::MalformedPayload)?
        .to_string();
    if event_type != "payment_intent.succeeded" {
        return Err(StripeError::UnhandledEventType(event_type));
    }
    let obj = v
        .get("data")
        .and_then(|d| d.get("object"))
        .ok_or(StripeError::MalformedPayload)?;
    let payment_intent_id = obj
        .get("id")
        .and_then(|i| i.as_str())
        .ok_or(StripeError::MalformedPayload)?
        .to_string();
    let amount_cents = obj
        .get("amount_received")
        .and_then(serde_json::Value::as_i64)
        .or_else(|| obj.get("amount").and_then(serde_json::Value::as_i64))
        .ok_or(StripeError::MalformedPayload)?;
    let currency = obj
        .get("currency")
        .and_then(|c| c.as_str())
        .ok_or(StripeError::MalformedPayload)?
        .to_string();
    Ok(VerifiedPayment {
        payment_intent_id,
        amount_cents,
        currency,
        event_type,
    })
}

/// A fixture `payment_intent.succeeded` body for `amount_cents` of `currency`,
/// identified by `intent_id` — the JSON Stripe would POST.
pub fn payment_intent_succeeded(intent_id: &str, amount_cents: i64, currency: &str) -> Vec<u8> {
    serde_json::to_vec(&serde_json::json!({
        "id": format!("evt_{intent_id}"),
        "type": "payment_intent.succeeded",
        "data": { "object": {
            "id": intent_id,
            "object": "payment_intent",
            "amount": amount_cents,
            "amount_received": amount_cents,
            "currency": currency,
            "status": "succeeded"
        }}
    }))
    .expect("fixture event serializes")
}

/// Lowercase-hex encode 32 bytes.
fn hex_lower(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

/// Decode a 64-char lowercase-hex string into 32 bytes (`None` on bad input).
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = (chunk[0] as char).to_digit(16)?;
        let lo = (chunk[1] as char).to_digit(16)?;
        out[i] = (hi * 16 + lo) as u8;
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::receipt::{ChainError, verify_chain};

    const SECRET: &[u8] = b"whsec_TEST_demo_secret_do_not_use_in_prod";

    fn mirror() -> StripeMirror {
        StripeMirror::new("USD-CENTS", SECRET, "usd", 50, 10_000_000, [99u8; 32])
    }

    // ── EARN: a genuine signed webhook mints conserved, receipted credit ───────
    #[test]
    fn a_genuine_signed_webhook_mints_conserved_credit() {
        let mut m = mirror();
        let body = payment_intent_succeeded("pi_acme_001", 5000, "usd");
        let webhook = StripeWebhook::sign(&body, SECRET, 1_700_000_000);
        let r = m
            .mint_against_webhook(&webhook, "agent:acme", Some(1_700_000_010))
            .expect("a genuine webhook mints");
        assert_eq!(r.amount_cents, 5000);
        assert_eq!(r.payment_intent_id, "pi_acme_001");
        assert_eq!(m.live_supply(), 5000);
        assert!(m.invariant_holds(), "minted ≤ verified");
        // The mint receipt re-witnesses (signed, chained).
        verify_chain(std::slice::from_ref(&r)).expect("the mint receipt re-witnesses");
    }

    // ── TOOTH: a retry of an already-minted payment is REFUSED (dedup) ─────────
    #[test]
    fn a_webhook_retry_is_refused_double_mint_prevented() {
        let mut m = mirror();
        let body = payment_intent_succeeded("pi_acme_001", 5000, "usd");
        let webhook = StripeWebhook::sign(&body, SECRET, 1_700_000_000);
        m.mint_against_webhook(&webhook, "agent:acme", Some(1_700_000_010))
            .unwrap();
        // The SAME signed webhook again (a Stripe retry) — refused.
        let again = m.mint_against_webhook(&webhook, "agent:acme", Some(1_700_000_010));
        assert_eq!(again, Err(StripeError::DuplicatePayment));
        assert_eq!(m.live_supply(), 5000, "no second mint landed");
    }

    // ── TOOTH: a forged-signature webhook is REFUSED ───────────────────────────
    #[test]
    fn a_forged_signature_webhook_is_refused() {
        let mut m = mirror();
        let body = payment_intent_succeeded("pi_attacker", 999_999, "usd");
        // Sign a SMALL amount, then swap the body for a huge one without re-signing.
        let small = payment_intent_succeeded("pi_attacker", 1, "usd");
        let webhook = StripeWebhook::sign(&small, SECRET, 1_700_000_000).with_forged_body(&body);
        let r = m.mint_against_webhook(&webhook, "agent:acme", Some(1_700_000_010));
        assert_eq!(r, Err(StripeError::SignatureMismatch));
        assert_eq!(m.live_supply(), 0, "a forged webhook mints nothing");
        // And a body signed with the WRONG secret is refused too.
        let wrong = StripeWebhook::sign(&body, b"whsec_WRONG", 1_700_000_000);
        assert_eq!(
            m.mint_against_webhook(&wrong, "agent:acme", Some(1_700_000_010)),
            Err(StripeError::SignatureMismatch)
        );
    }

    // ── TOOTH: a forged amount in a minted receipt breaks the signature ────────
    #[test]
    fn a_forged_mint_amount_breaks_the_receipt() {
        let mut m = mirror();
        let body = payment_intent_succeeded("pi_acme_001", 5000, "usd");
        let webhook = StripeWebhook::sign(&body, SECRET, 1_700_000_000);
        let mut r = m
            .mint_against_webhook(&webhook, "agent:acme", Some(1_700_000_010))
            .unwrap();
        verify_chain(std::slice::from_ref(&r)).unwrap();
        // Forge "I was paid $500 not $50" after sealing → the signature breaks.
        r.amount_cents = 50_000;
        assert!(matches!(
            verify_chain(std::slice::from_ref(&r)),
            Err(ChainError::BadSignature { .. })
        ));
    }

    // ── replay window + bounds ─────────────────────────────────────────────────
    #[test]
    fn an_old_timestamp_and_out_of_bounds_amounts_are_refused() {
        let mut m = mirror();
        let body = payment_intent_succeeded("pi_old", 5000, "usd");
        let webhook = StripeWebhook::sign(&body, SECRET, 1_700_000_000);
        // 10 minutes later — past the 5-minute window.
        assert!(matches!(
            m.mint_against_webhook(&webhook, "agent:acme", Some(1_700_000_000 + 600)),
            Err(StripeError::TimestampTooOld { .. })
        ));
        // Below the dust floor.
        let dust = payment_intent_succeeded("pi_dust", 10, "usd");
        let dust_wh = StripeWebhook::sign(&dust, SECRET, 1_700_000_000);
        assert_eq!(
            m.mint_against_webhook(&dust_wh, "agent:acme", Some(1_700_000_010)),
            Err(StripeError::BelowMin)
        );
        // Wrong currency.
        let eur = payment_intent_succeeded("pi_eur", 5000, "eur");
        let eur_wh = StripeWebhook::sign(&eur, SECRET, 1_700_000_000);
        assert!(matches!(
            m.mint_against_webhook(&eur_wh, "agent:acme", Some(1_700_000_010)),
            Err(StripeError::WrongCurrency { .. })
        ));
    }
}
