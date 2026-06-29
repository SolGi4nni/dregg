//! `dregg-bridge::stripe_mirror`: mirror a verified **Stripe payment** into
//! dregg's value layer as a first-class conserved, `Payable` USD-credit asset.
//!
//! This is the [`crate::solana_mirror`] pattern with a different trusted oracle:
//! instead of a federation threshold-attesting a Solana lock, **Stripe itself**
//! attests — via a signed `payment_intent.succeeded` / `charge.succeeded`
//! webhook — that a real payment cleared. The dregg-side mechanism (replay dedup,
//! amount bounds, the conservation invariant, and the production of REAL kernel
//! [`Effect::Mint`] / [`Effect::Transfer`] effects) is identical.
//!
//! ```text
//!  Stripe: agent pays card  ──►  Stripe sends a SIGNED webhook (payment_intent.succeeded)
//!                                          │  (HMAC-SHA256 over the raw body)
//!                                          ▼
//!                              StripeWebhookEvent::verify  (real Stripe scheme)
//!                              → StripePaymentAttestation  (amount_cents, payment_intent_id)
//!                                          │
//!                                          ▼
//!                              StripeMirrorState.mint_against_payment
//!                              → Effect::Mint { target, amount }  (well-debited, Σδ=0)
//!                                          │  (ordinary dregg USD-credit asset)
//!                                          ▼
//!                              dregg_payable::resolve_pay → Effect::Transfer
//!                              → pays an execution-lease / DreggNet durable op
//! ```
//!
//! # Trust model (honest)
//!
//! This is a **trusted-oracle** mirror, exactly like [`crate::solana_mirror`].
//! dregg trusts that a valid `Stripe-Signature` header (an HMAC-SHA256 of the
//! exact request body under the endpoint's webhook signing secret) means *Stripe
//! said this payment succeeded*. dregg does NOT independently verify the card
//! network or settlement — Stripe is the payment oracle, the same way the
//! federation is the Solana-lock oracle. The webhook secret is the verifying key.
//! The replay nonce is the underlying **payment-intent id**: Stripe retries
//! webhooks (and fires both a `payment_intent.succeeded` and a `charge.succeeded`
//! for one payment), so deduping on the payment-intent id is load-bearing for
//! at-most-once minting.
//!
//! # What is real here
//!
//! The real Stripe webhook signature scheme (HMAC-SHA256 over `"{t}.{body}"`,
//! constant-time compared, with an optional timestamp-tolerance replay window),
//! replay dedup, amount bounds, the conservation invariant
//! `live_supply ≤ total_verified_payments`, and the production of REAL kernel
//! effects ([`Effect::Mint`] and the payment [`Effect::Transfer`] via
//! [`dregg_payable::resolve_pay`]). No new kernel verb is introduced.

use std::collections::BTreeSet;

use dregg_cell::Nullifier;
use dregg_turn::action::Effect;
use dregg_types::CellId;
use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

/// Domain separation for the COMMITTED consume-once payment nullifier (the
/// concurrency-safe double-mint gate, `docs/deos/BRIDGE-ARCHITECTURE-SOUNDNESS.md`
/// §3). Distinct from the Solana lock nullifier domain.
pub const STRIPE_PAYMENT_NULLIFIER_DOMAIN: &str = "dregg-stripe-payment-v1";

/// Derive the domain-separated, consume-once nullifier for a Stripe payment.
///
/// `nf = H("dregg-stripe-payment-v1" ‖ asset ‖ payment_intent_id)`. Binding the
/// mirror `asset` scopes the nullifier so a `payment_intent_id` can never
/// collide across mirrors. This is the value gated against the executor's
/// committed `note_nullifiers` set in [`dregg_turn::executor::bridge_ledger`] —
/// so a payment is minted exactly once GLOBALLY, regardless of how many relayer
/// processes (or webhook retries / sibling `charge.succeeded` events) observe it.
pub fn payment_nullifier(asset: &[u8; 32], payment_intent_id: &str) -> Nullifier {
    let mut h = blake3::Hasher::new_derive_key(STRIPE_PAYMENT_NULLIFIER_DOMAIN);
    h.update(asset);
    h.update(payment_intent_id.as_bytes());
    Nullifier(*h.finalize().as_bytes())
}

/// The verified, committed-bridge-ready facts of a Stripe payment: the
/// consume-once nullifier plus the mint target/amount. Produced by
/// [`StripeMirrorState::verify_payment`] WITHOUT mutating any per-relayer RAM —
/// the authority is committed state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedPayment {
    /// The domain-separated consume-once payment nullifier (see [`payment_nullifier`]).
    pub payment_nullifier: Nullifier,
    /// The dregg cell to credit the mirrored USD-credit.
    pub recipient: CellId,
    /// The amount (cents) to mint.
    pub amount: u64,
}

/// The metadata key, on the Stripe payment object, that carries the dregg cell
/// (hex-encoded 32-byte [`CellId`]) the minted USD-credit should be credited to.
/// An agent sets this when it creates the PaymentIntent so the mirror knows which
/// DreggNet cell funded itself.
pub const RECIPIENT_METADATA_KEY: &str = "dregg_recipient";

/// The default replay-window tolerance for the webhook timestamp (5 minutes), the
/// value Stripe's own libraries use. A webhook whose `t=` is older than this (when
/// a `now` is supplied to [`StripeWebhookEvent::verify`]) is refused.
pub const DEFAULT_TOLERANCE_SECS: u64 = 300;

// ============================================================================
// The verified payment attestation
// ============================================================================

/// A **verified** Stripe payment event: the dregg-side claim that `amount_cents`
/// of `currency` cleared for a payment identified by `payment_intent_id`, bound
/// for the dregg cell `recipient`.
///
/// This is only ever produced by [`StripeWebhookEvent::verify`] — i.e. AFTER the
/// `Stripe-Signature` HMAC checks out — so holding a `StripePaymentAttestation`
/// is evidence Stripe attested the payment. It is the analogue of
/// [`crate::solana_mirror::SolanaLockAttestation`] but the trusted leg is a Stripe
/// HMAC rather than a federation Ed25519 signature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StripePaymentAttestation {
    /// The underlying payment-intent id — the **replay nonce** (consume-once).
    /// For a `payment_intent.*` event this is the object id; for a `charge.*`
    /// event it is the charge's `payment_intent`. Both events for one payment
    /// therefore share this id, so a payment is minted at most once.
    pub payment_intent_id: String,
    /// Amount that cleared, in the currency's smallest unit (USD cents).
    pub amount_cents: u64,
    /// ISO-4217 currency code, lowercased as Stripe sends it (e.g. `"usd"`).
    pub currency: String,
    /// The dregg cell that should receive the mirrored USD-credit (from the
    /// payment object's `metadata.dregg_recipient`).
    pub recipient: CellId,
    /// The Stripe event type that produced this (`payment_intent.succeeded` or
    /// `charge.succeeded`).
    pub event_type: String,
}

// ============================================================================
// Webhook signature verification (the real Stripe scheme)
// ============================================================================

/// A raw inbound Stripe webhook: the EXACT request body bytes plus the value of
/// the `Stripe-Signature` header. The signature is computed over the raw body, so
/// these bytes must be the un-reserialized payload Stripe sent.
#[derive(Clone, Debug)]
pub struct StripeWebhookEvent {
    /// The raw HTTP request body, exactly as received.
    pub payload: Vec<u8>,
    /// The full `Stripe-Signature` header value, e.g.
    /// `t=1614288000,v1=5257a8...,v0=...`.
    pub signature_header: String,
}

/// Why a webhook / mint operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StripeMirrorError {
    /// The `Stripe-Signature` header was missing a `t=` timestamp or any `v1=`.
    MalformedSignatureHeader,
    /// No `v1` HMAC in the header matched the body under the signing secret.
    SignatureMismatch,
    /// The webhook timestamp is outside the allowed replay window.
    TimestampTooOld { age_secs: u64, tolerance_secs: u64 },
    /// The request body was not valid JSON / not a recognizable Stripe event.
    MalformedPayload,
    /// The event type is not one we mint against (we mint only on
    /// `payment_intent.succeeded` / `charge.succeeded`).
    UnhandledEventType(String),
    /// The payment object had no `metadata.dregg_recipient`, or it was not a
    /// 32-byte hex cell id.
    MissingOrBadRecipient,
    /// The payment currency is not the configured mirror currency.
    WrongCurrency { got: String, want: String },
    /// Amount is below the configured dust floor.
    BelowMin,
    /// Amount exceeds the configured per-payment maximum.
    AboveMax,
    /// This `payment_intent_id` was already mirrored (double-mint prevention —
    /// the webhook-retry / duplicate-event case).
    DuplicatePayment,
    /// Minting `amount` would push `live_supply` above `total_verified_payments`
    /// (the conservation invariant). A LIVE gate (red-team BR-3): the backing is
    /// raised ONLY by an independently-verified payment
    /// ([`StripeMirrorState::record_payment_backing`]); a mint draws against it
    /// ([`StripeMirrorState::draw_mint`]) and is refused here when it would exceed
    /// the backing — so a mint with no verified payment, or a draw beyond it, is
    /// rejected (not the old credit-both-sides-equally vacuity).
    InsufficientBacking {
        live: u64,
        backing: u64,
        amount: u64,
    },
    /// An accounting addition overflowed `u64`.
    Overflow,
}

impl std::fmt::Display for StripeMirrorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedSignatureHeader => write!(f, "malformed Stripe-Signature header"),
            Self::SignatureMismatch => write!(
                f,
                "no v1 signature matched the body (forged or wrong secret)"
            ),
            Self::TimestampTooOld {
                age_secs,
                tolerance_secs,
            } => write!(
                f,
                "webhook timestamp too old: {age_secs}s > tolerance {tolerance_secs}s"
            ),
            Self::MalformedPayload => write!(f, "webhook body is not a recognizable Stripe event"),
            Self::UnhandledEventType(t) => write!(f, "unhandled Stripe event type: {t}"),
            Self::MissingOrBadRecipient => {
                write!(
                    f,
                    "payment has no valid metadata.{RECIPIENT_METADATA_KEY} cell id"
                )
            }
            Self::WrongCurrency { got, want } => {
                write!(f, "payment currency {got} != mirror currency {want}")
            }
            Self::BelowMin => write!(f, "amount below the mirror minimum"),
            Self::AboveMax => write!(f, "amount above the per-payment maximum"),
            Self::DuplicatePayment => {
                write!(
                    f,
                    "payment_intent_id already mirrored (double-mint prevented)"
                )
            }
            Self::InsufficientBacking {
                live,
                backing,
                amount,
            } => write!(
                f,
                "mint of {amount} would break conservation: live {live} + {amount} > backing {backing}"
            ),
            Self::Overflow => write!(f, "supply accounting overflow"),
        }
    }
}

impl std::error::Error for StripeMirrorError {}

impl StripeWebhookEvent {
    /// Sign a payload body the way Stripe does and produce the header value — a
    /// test / oracle-side helper that is the inverse of [`Self::verify`].
    ///
    /// Builds `t=<timestamp>,v1=<hex(HMAC-SHA256(secret, "{t}.{body}"))>`.
    pub fn sign(payload: &[u8], secret: &[u8], timestamp: u64) -> Self {
        let sig = hex_lower(&Self::expected_sig(payload, secret, timestamp));
        StripeWebhookEvent {
            payload: payload.to_vec(),
            signature_header: format!("t={timestamp},v1={sig}"),
        }
    }

    /// The HMAC-SHA256 over Stripe's signed payload `"{timestamp}.{body}"`.
    fn expected_sig(payload: &[u8], secret: &[u8], timestamp: u64) -> [u8; 32] {
        let mut mac =
            <HmacSha256 as Mac>::new_from_slice(secret).expect("HMAC accepts any key length");
        mac.update(timestamp.to_string().as_bytes());
        mac.update(b".");
        mac.update(payload);
        mac.finalize().into_bytes().into()
    }

    /// **Verify the webhook signature and parse the payment, the real Stripe way.**
    ///
    /// 1. Parse `t=` and all `v1=` entries from the `Stripe-Signature` header.
    /// 2. Recompute `HMAC-SHA256(secret, "{t}.{body}")` and constant-time compare
    ///    it against each `v1` (multiple `v1`s occur during secret rotation).
    /// 3. If `now` is `Some`, reject a `t` older than `tolerance_secs` (the replay
    ///    window). Pass `None` to skip the time check (e.g. in deterministic tests).
    /// 4. Parse the body, require a handled event type, extract the
    ///    payment-intent id (the replay nonce), amount, currency, and the dregg
    ///    recipient from `metadata.dregg_recipient`.
    ///
    /// Returns a [`StripePaymentAttestation`] only when the signature is valid.
    pub fn verify(
        &self,
        secret: &[u8],
        now: Option<u64>,
        tolerance_secs: u64,
    ) -> Result<StripePaymentAttestation, StripeMirrorError> {
        let (timestamp, v1s) = parse_signature_header(&self.signature_header)?;

        // (2) Constant-time compare against every offered v1.
        let expected = Self::expected_sig(&self.payload, secret, timestamp);
        let matched = v1s.iter().any(|hexsig| {
            decode_hex32(hexsig)
                .map(|got| ct_eq32(&got, &expected))
                .unwrap_or(false)
        });
        if !matched {
            return Err(StripeMirrorError::SignatureMismatch);
        }

        // (3) Replay-window check (only when a clock is supplied).
        if let Some(now) = now {
            let age = now.saturating_sub(timestamp);
            if age > tolerance_secs {
                return Err(StripeMirrorError::TimestampTooOld {
                    age_secs: age,
                    tolerance_secs,
                });
            }
        }

        // (4) Parse the verified body.
        parse_payment_event(&self.payload)
    }
}

/// Parse `t=<int>` and the list of `v1=<hex>` from a `Stripe-Signature` header.
fn parse_signature_header(header: &str) -> Result<(u64, Vec<String>), StripeMirrorError> {
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
        _ => Err(StripeMirrorError::MalformedSignatureHeader),
    }
}

/// Parse a verified Stripe event body into a [`StripePaymentAttestation`].
///
/// Handles `payment_intent.succeeded` and `charge.succeeded`. The replay nonce
/// (`payment_intent_id`) is the payment-intent id common to both event kinds:
/// for a charge that is `data.object.payment_intent`; for a payment-intent that
/// is `data.object.id`.
fn parse_payment_event(body: &[u8]) -> Result<StripePaymentAttestation, StripeMirrorError> {
    let v: serde_json::Value =
        serde_json::from_slice(body).map_err(|_| StripeMirrorError::MalformedPayload)?;

    let event_type = v
        .get("type")
        .and_then(|t| t.as_str())
        .ok_or(StripeMirrorError::MalformedPayload)?
        .to_string();

    let obj = v
        .get("data")
        .and_then(|d| d.get("object"))
        .ok_or(StripeMirrorError::MalformedPayload)?;

    // Replay nonce: the underlying payment-intent id.
    let payment_intent_id = match event_type.as_str() {
        "payment_intent.succeeded" => obj.get("id").and_then(|i| i.as_str()).map(str::to_string),
        "charge.succeeded" => obj
            .get("payment_intent")
            .and_then(|i| i.as_str())
            .or_else(|| obj.get("id").and_then(|i| i.as_str()))
            .map(str::to_string),
        other => return Err(StripeMirrorError::UnhandledEventType(other.to_string())),
    }
    .ok_or(StripeMirrorError::MalformedPayload)?;

    // Amount: prefer `amount_received` (PI) when present, else `amount`.
    let amount_cents = obj
        .get("amount_received")
        .and_then(serde_json::Value::as_u64)
        .or_else(|| obj.get("amount").and_then(serde_json::Value::as_u64))
        .ok_or(StripeMirrorError::MalformedPayload)?;

    let currency = obj
        .get("currency")
        .and_then(|c| c.as_str())
        .ok_or(StripeMirrorError::MalformedPayload)?
        .to_string();

    let recipient_hex = obj
        .get("metadata")
        .and_then(|m| m.get(RECIPIENT_METADATA_KEY))
        .and_then(|r| r.as_str())
        .ok_or(StripeMirrorError::MissingOrBadRecipient)?;
    let recipient_bytes =
        decode_hex32(recipient_hex).ok_or(StripeMirrorError::MissingOrBadRecipient)?;
    let recipient = CellId::from_bytes(recipient_bytes);

    Ok(StripePaymentAttestation {
        payment_intent_id,
        amount_cents,
        currency,
        recipient,
        event_type,
    })
}

// ============================================================================
// The dregg-side mirror ledger
// ============================================================================

/// Configuration for the Stripe USD-credit mirror.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StripeMirrorConfig {
    /// The dregg `AssetId` of the USD-credit mirror (= the mirror issuer-well cell
    /// id; mirror holders denominate value in this `token_id`). 1 unit = 1 cent.
    pub asset: [u8; 32],
    /// The webhook endpoint's signing secret (`whsec_...`), the verifying key for
    /// every inbound webhook. Held opaque as bytes.
    pub webhook_secret: Vec<u8>,
    /// The ISO-4217 currency the mirror accepts (lowercase, e.g. `"usd"`).
    pub currency: String,
    /// Minimum mintable amount in cents (dust floor).
    pub min_cents: u64,
    /// Maximum per-payment amount in cents (above this, governance is required).
    pub max_cents: u64,
}

/// The dregg-side ledger of the Stripe USD-credit mirror.
///
/// - `total_verified_payments`: cumulative cents Stripe has attested as cleared.
/// - `live_supply`: USD-credit currently circulating inside dregg.
///
/// **Invariant (checked after every op):** `live_supply ≤ total_verified_payments`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StripeMirrorState {
    /// The mirror configuration (asset id, webhook secret, currency, bounds).
    pub config: StripeMirrorConfig,
    /// Cumulative cents attested as cleared by Stripe.
    pub total_verified_payments: u64,
    /// USD-credit currently circulating inside dregg.
    pub live_supply: u64,
    /// Payment-intent ids already mirrored — a per-relayer LOCAL fast-reject
    /// CACHE, NOT the global double-mint authority. The authoritative
    /// consume-once gate is the committed `note_nullifiers` set (see
    /// [`payment_nullifier`] + [`dregg_turn::executor::bridge_ledger`]): a second
    /// relayer with a fresh `seen_payments` is still refused by COMMITTED state.
    seen_payments: BTreeSet<String>,
}

/// The output of a successful mirror-mint: the kernel effect to submit plus a
/// record of who/what was credited.
///
/// (`Effect` is not `PartialEq`, so this struct is not either; inspect `effect`
/// by pattern match.)
#[derive(Clone, Debug)]
pub struct StripeMint {
    /// The REAL kernel mint effect: credits `recipient`, debits the mirror's
    /// issuer well as the conserving dual (`Effect::Mint` is `Generative`).
    pub effect: Effect,
    /// The recipient that was credited.
    pub recipient: CellId,
    /// The amount minted (cents).
    pub amount: u64,
}

impl StripeMirrorState {
    /// Create an empty mirror for `config` (nothing verified, nothing minted).
    pub fn new(config: StripeMirrorConfig) -> Self {
        Self {
            config,
            total_verified_payments: 0,
            live_supply: 0,
            seen_payments: BTreeSet::new(),
        }
    }

    /// The conservation invariant: circulating USD-credit never exceeds the cents
    /// Stripe has attested as cleared.
    pub fn invariant_holds(&self) -> bool {
        self.live_supply <= self.total_verified_payments
    }

    /// Whether `payment_intent_id` has already been mirrored.
    pub fn is_payment_seen(&self, payment_intent_id: &str) -> bool {
        self.seen_payments.contains(payment_intent_id)
    }

    /// **Record an independently-verified payment** as conservation backing,
    /// raising `total_verified_payments` by `amount`. Deduped by
    /// `payment_intent_id` so a webhook retry can never inflate the backing twice.
    /// The caller MUST have verified the webhook signature before calling. The
    /// mint draws against this backing separately ([`Self::draw_mint`]) so
    /// conservation is a real constraint (red-team BR-3).
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub(crate) fn record_payment_backing(
        &mut self,
        payment_intent_id: &str,
        amount: u64,
    ) -> Result<(), StripeMirrorError> {
        if self.seen_payments.contains(payment_intent_id) {
            return Err(StripeMirrorError::DuplicatePayment);
        }
        let new_backing = self
            .total_verified_payments
            .checked_add(amount)
            .ok_or(StripeMirrorError::Overflow)?;
        self.total_verified_payments = new_backing;
        self.seen_payments.insert(payment_intent_id.to_string());
        Ok(())
    }

    /// **Draw a mint against the recorded payment backing**, raising `live_supply`
    /// and emitting the REAL [`Effect::Mint`]. Conservation BITES here (red-team
    /// BR-3): a draw exceeding `total_verified_payments` — e.g. a mint with no
    /// verified payment — is refused with [`StripeMirrorError::InsufficientBacking`].
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub(crate) fn draw_mint(
        &mut self,
        amount: u64,
        recipient: CellId,
    ) -> Result<StripeMint, StripeMirrorError> {
        let new_live = self
            .live_supply
            .checked_add(amount)
            .ok_or(StripeMirrorError::Overflow)?;
        if new_live > self.total_verified_payments {
            return Err(StripeMirrorError::InsufficientBacking {
                live: self.live_supply,
                backing: self.total_verified_payments,
                amount,
            });
        }
        self.live_supply = new_live;
        debug_assert!(self.invariant_holds());

        Ok(StripeMint {
            effect: Effect::Mint {
                target: recipient,
                slot: 0,
                amount,
            },
            recipient,
            amount,
        })
    }

    /// **Verify a raw webhook AND mirror-mint against it in one step — RAM path,
    /// TEST/INTERNAL ONLY** (red-team BR-1).
    ///
    /// Convenience over [`StripeWebhookEvent::verify`] + [`Self::mint_against_payment`].
    /// Gated behind `#[cfg(any(test, feature = "test-utils"))]`: the production
    /// surface is [`Self::verify_payment`] → the committed `bridge_mint_against_lock`.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn mint_against_webhook(
        &mut self,
        webhook: &StripeWebhookEvent,
        now: Option<u64>,
        tolerance_secs: u64,
    ) -> Result<StripeMint, StripeMirrorError> {
        let att = webhook.verify(&self.config.webhook_secret, now, tolerance_secs)?;
        self.mint_against_payment(&att)
    }

    /// **Verify a payment for the COMMITTED bridge mint, mutating no per-relayer
    /// RAM.**
    ///
    /// Runs the same currency/amount checks as [`Self::mint_against_payment`] but
    /// does NOT touch `seen_payments` / `total_verified_payments` / `live_supply`.
    /// It returns the consume-once [`VerifiedPayment`] the caller feeds to
    /// [`dregg_turn::executor::bridge_ledger`]'s
    /// `TurnExecutor::bridge_mint_against_lock`, where the committed
    /// `note_nullifiers` set is the global double-mint authority. This is the
    /// SOUND multi-relayer path: any number of relayers (or webhook retries) may
    /// race the same payment and exactly one wins.
    ///
    /// The caller must already have verified the webhook signature (e.g. via
    /// [`StripeWebhookEvent::verify`]) to obtain `att`.
    pub fn verify_payment(
        &self,
        att: &StripePaymentAttestation,
    ) -> Result<VerifiedPayment, StripeMirrorError> {
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
        })
    }

    /// **Mirror-mint against a verified Stripe payment — RAM path, TEST/INTERNAL
    /// ONLY** (red-team BR-1).
    ///
    /// Enforces currency match, amount bounds, replay dedup, records the payment
    /// backing, and draws the mint against it. Backing and supply are now distinct
    /// accumulators, so [`StripeMirrorError::InsufficientBacking`] is genuinely
    /// reachable (red-team BR-3). Gated behind
    /// `#[cfg(any(test, feature = "test-utils"))]`; production uses
    /// [`Self::verify_payment`] → the committed `bridge_mint_against_lock`.
    ///
    /// On any error the state is left unchanged.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn mint_against_payment(
        &mut self,
        att: &StripePaymentAttestation,
    ) -> Result<StripeMint, StripeMirrorError> {
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

        // Record the verified-payment backing, then draw the mint against it. On a
        // draw failure, roll the backing back so the op is atomic.
        self.record_payment_backing(&att.payment_intent_id, att.amount_cents)?;
        match self.draw_mint(att.amount_cents, att.recipient) {
            Ok(mint) => Ok(mint),
            Err(e) => {
                self.total_verified_payments = self
                    .total_verified_payments
                    .saturating_sub(att.amount_cents);
                self.seen_payments.remove(&att.payment_intent_id);
                Err(e)
            }
        }
    }
}

// ============================================================================
// Small hex / constant-time helpers (no extra dep)
// ============================================================================

/// Lowercase-hex encode 32 bytes.
fn hex_lower(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

/// Decode exactly 64 hex chars into 32 bytes; `None` on any malformed input.
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.as_bytes();
    if s.len() != 64 {
        return None;
    }
    let nib = |c: u8| -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    };
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = nib(s[2 * i])?;
        let lo = nib(s[2 * i + 1])?;
        *byte = (hi << 4) | lo;
    }
    Some(out)
}

/// Constant-time equality over two 32-byte buffers.
fn ct_eq32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    use subtle::ConstantTimeEq;
    a.ct_eq(b).into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_payable::{InvokeAuthority, InvokeRefused, resolve_pay};

    const SECRET: &[u8] = b"whsec_test_dregg_hermes_hackathon";
    const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32]; // USD-credit issuer-well / token_id

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// The 64-char hex of a `cid(b)` cell, for the webhook `metadata.dregg_recipient`.
    fn recipient_hex(b: u8) -> String {
        hex_lower(&[b; 32])
    }

    fn config() -> StripeMirrorConfig {
        StripeMirrorConfig {
            asset: MIRROR_ASSET,
            webhook_secret: SECRET.to_vec(),
            currency: "usd".to_string(),
            min_cents: 50,           // Stripe's own $0.50 minimum
            max_cents: 1_000_000_00, // $1,000,000 governance ceiling
        }
    }

    /// A realistic `payment_intent.succeeded` event body crediting `recipient`.
    fn pi_body(id: &str, amount_cents: u64, recipient: u8) -> Vec<u8> {
        format!(
            r#"{{
              "id": "evt_{id}",
              "type": "payment_intent.succeeded",
              "data": {{
                "object": {{
                  "id": "{id}",
                  "object": "payment_intent",
                  "amount": {amount_cents},
                  "amount_received": {amount_cents},
                  "currency": "usd",
                  "status": "succeeded",
                  "metadata": {{ "{key}": "{rcpt}" }}
                }}
              }}
            }}"#,
            key = RECIPIENT_METADATA_KEY,
            rcpt = recipient_hex(recipient),
        )
        .into_bytes()
    }

    /// A `charge.succeeded` event whose `payment_intent` is `pi_id` (the dedup key
    /// shared with the corresponding `payment_intent.succeeded`).
    fn charge_body(charge_id: &str, pi_id: &str, amount_cents: u64, recipient: u8) -> Vec<u8> {
        format!(
            r#"{{
              "id": "evt_{charge_id}",
              "type": "charge.succeeded",
              "data": {{
                "object": {{
                  "id": "{charge_id}",
                  "object": "charge",
                  "payment_intent": "{pi_id}",
                  "amount": {amount_cents},
                  "currency": "usd",
                  "paid": true,
                  "metadata": {{ "{key}": "{rcpt}" }}
                }}
              }}
            }}"#,
            key = RECIPIENT_METADATA_KEY,
            rcpt = recipient_hex(recipient),
        )
        .into_bytes()
    }

    #[test]
    fn valid_signed_webhook_mints_the_right_credit() {
        let mut mirror = StripeMirrorState::new(config());
        let body = pi_body("pi_001", 2500, 1); // $25.00 → cell 1
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);

        let minted = mirror
            .mint_against_webhook(&hook, None, DEFAULT_TOLERANCE_SECS)
            .expect("a valid signed webhook mints");

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

    #[test]
    fn forged_signature_is_refused_and_state_unchanged() {
        let mut mirror = StripeMirrorState::new(config());
        let body = pi_body("pi_002", 5000, 1);

        // Signed under the WRONG secret (an attacker without the webhook secret).
        let forged = StripeWebhookEvent::sign(&body, b"whsec_attacker_guess", 1_700_000_000);
        assert_eq!(
            mirror
                .mint_against_webhook(&forged, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::SignatureMismatch
        );

        // A correctly-signed body whose payload was then tampered (amount bumped)
        // also fails: the HMAC is over the exact bytes.
        let good = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);
        let tampered = StripeWebhookEvent {
            payload: pi_body("pi_002", 9_999_999, 1),
            signature_header: good.signature_header,
        };
        assert_eq!(
            mirror
                .mint_against_webhook(&tampered, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::SignatureMismatch
        );

        assert_eq!(mirror.live_supply, 0);
        assert_eq!(mirror.total_verified_payments, 0);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn retried_webhook_does_not_double_mint() {
        // THE hackathon-critical case: Stripe retries webhooks (and fires both a
        // payment_intent.succeeded AND a charge.succeeded for one payment). The
        // payment-intent id dedups all of them to a single mint.
        let mut mirror = StripeMirrorState::new(config());

        let pi = pi_body("pi_777", 4000, 2);
        let hook = StripeWebhookEvent::sign(&pi, SECRET, 1_700_000_100);

        // First delivery mints.
        let first = mirror
            .mint_against_webhook(&hook, None, DEFAULT_TOLERANCE_SECS)
            .expect("first delivery mints");
        assert_eq!(first.amount, 4000);

        // Stripe re-delivers the identical event (a retry) — refused, no credit.
        assert_eq!(
            mirror
                .mint_against_webhook(&hook, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::DuplicatePayment
        );

        // And the sibling charge.succeeded for the SAME payment (pi_777) is also
        // deduped — both events share the payment-intent id.
        let charge = charge_body("ch_777", "pi_777", 4000, 2);
        let charge_hook = StripeWebhookEvent::sign(&charge, SECRET, 1_700_000_101);
        assert_eq!(
            mirror
                .mint_against_webhook(&charge_hook, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::DuplicatePayment
        );

        // Exactly one payment's worth of credit exists.
        assert_eq!(mirror.live_supply, 4000);
        assert_eq!(mirror.total_verified_payments, 4000);
        assert!(mirror.invariant_holds());
    }

    /// BR-3 (conservation NON-VACUOUS): a mint draw with no recorded payment
    /// backing is rejected, and a draw within the backing succeeds — the
    /// true-and-false coverage proving the gate bites (it was dead code when both
    /// sides moved by the same amount).
    #[test]
    fn draw_beyond_backing_breaks_conservation() {
        let mut mirror = StripeMirrorState::new(config());

        // No backing yet → any draw is over-mint.
        assert_eq!(
            mirror.draw_mint(2500, cid(1)).unwrap_err(),
            StripeMirrorError::InsufficientBacking {
                live: 0,
                backing: 0,
                amount: 2500,
            }
        );
        assert_eq!(mirror.live_supply, 0);

        // Record a verified payment of 2500; draw 2500 (within) → ok.
        mirror
            .record_payment_backing("pi_x", 2500)
            .expect("backing recorded");
        mirror.draw_mint(2500, cid(1)).expect("draw within backing");
        assert_eq!(mirror.live_supply, 2500);

        // A further draw exceeds the now-spent backing → rejected.
        assert_eq!(
            mirror.draw_mint(1, cid(2)).unwrap_err(),
            StripeMirrorError::InsufficientBacking {
                live: 2500,
                backing: 2500,
                amount: 1,
            }
        );
        assert_eq!(mirror.live_supply, 2500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn stale_webhook_is_refused_when_clock_supplied() {
        let mut mirror = StripeMirrorState::new(config());
        let body = pi_body("pi_old", 1000, 1);
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);

        // `now` is well past the tolerance window → replay-window reject.
        let now = 1_700_000_000 + DEFAULT_TOLERANCE_SECS + 1;
        assert!(matches!(
            mirror.mint_against_webhook(&hook, Some(now), DEFAULT_TOLERANCE_SECS),
            Err(StripeMirrorError::TimestampTooOld { .. })
        ));

        // Within the window it is accepted.
        let fresh = 1_700_000_000 + 10;
        assert!(
            mirror
                .mint_against_webhook(&hook, Some(fresh), DEFAULT_TOLERANCE_SECS)
                .is_ok()
        );
    }

    #[test]
    fn amount_bounds_and_currency_enforced() {
        let mut mirror = StripeMirrorState::new(config());

        let dust = StripeWebhookEvent::sign(&pi_body("pi_dust", 10, 1), SECRET, 1_700_000_000);
        assert_eq!(
            mirror
                .mint_against_webhook(&dust, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::BelowMin
        );

        let whale =
            StripeWebhookEvent::sign(&pi_body("pi_whale", 2_000_000_00, 1), SECRET, 1_700_000_000);
        assert_eq!(
            mirror
                .mint_against_webhook(&whale, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::AboveMax
        );

        // Wrong currency: a verified EUR payment against a USD mirror.
        let eur_body = pi_body("pi_eur", 5000, 1);
        let eur_body = String::from_utf8(eur_body)
            .unwrap()
            .replace("\"currency\": \"usd\"", "\"currency\": \"eur\"")
            .into_bytes();
        let eur = StripeWebhookEvent::sign(&eur_body, SECRET, 1_700_000_000);
        assert!(matches!(
            mirror.mint_against_webhook(&eur, None, DEFAULT_TOLERANCE_SECS),
            Err(StripeMirrorError::WrongCurrency { .. })
        ));
    }

    #[test]
    fn missing_recipient_metadata_is_refused() {
        let mut mirror = StripeMirrorState::new(config());
        let body = br#"{
          "type": "payment_intent.succeeded",
          "data": { "object": {
            "id": "pi_norcpt", "amount": 5000, "amount_received": 5000,
            "currency": "usd", "metadata": {}
          }}
        }"#
        .to_vec();
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);
        assert_eq!(
            mirror
                .mint_against_webhook(&hook, None, DEFAULT_TOLERANCE_SECS)
                .unwrap_err(),
            StripeMirrorError::MissingOrBadRecipient
        );
    }

    /// END-TO-END: a verified Stripe payment is mirror-minted into USD-credit,
    /// then that credit pays for a DreggNet execution-lease through the SAME
    /// `resolve_pay` rail $DREGG uses — desugaring to ONE conserving
    /// `Effect::Transfer`. This is the hackathon thesis: an agent's Stripe
    /// payment funds its durable execution on DreggNet.
    #[test]
    fn stripe_payment_funds_an_execution_lease() {
        let mut mirror = StripeMirrorState::new(config());

        let agent = cid(1); // the agent's dregg cell, set in payment metadata
        let lease_provider = cid(2); // the DreggNet execution-lease / service cell
        let lease_price = 1500u64; // $15.00 of lease

        // 1) The agent pays Stripe; Stripe webhooks; we verify + mint $50 credit.
        let body = pi_body("pi_lease", 5000, 1);
        let hook = StripeWebhookEvent::sign(&body, SECRET, 1_700_000_000);
        let minted = mirror
            .mint_against_webhook(&hook, None, DEFAULT_TOLERANCE_SECS)
            .expect("verified Stripe payment mirror-mints USD-credit");
        assert_eq!(minted.amount, 5000);
        assert_eq!(minted.recipient, agent);

        // 2) The agent pays the execution-lease with its mirrored USD-credit over
        //    the existing Payable rail (asset tag = the mirror's AssetId).
        let (action, sig) = resolve_pay(
            agent,
            mirror.config.asset, // USD-credit is an ordinary AssetId
            lease_price,
            lease_provider,
            InvokeAuthority::Signature,
        )
        .expect("USD-credit resolves a pay through the Payable interface");

        // The pay desugars to exactly ONE conserving Transfer (Σδ=0).
        assert_eq!(action.effects.len(), 1);
        match action.effects[0] {
            Effect::Transfer { from, to, amount } => {
                assert_eq!(from, agent);
                assert_eq!(to, lease_provider);
                assert_eq!(amount, lease_price);
            }
            ref other => panic!("execution-lease charge must be a Transfer, got {other:?}"),
        }
        assert_eq!(sig.semantics, dregg_cell::interface::Semantics::Replayable);

        // The mirror's conservation is intact through all of this.
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn unauthorized_lease_payment_is_refused() {
        // Defence: paying for a lease still requires the Signature cap gate —
        // funding via Stripe does not bypass authorization.
        let refused = resolve_pay(cid(1), MIRROR_ASSET, 100, cid(2), InvokeAuthority::None)
            .expect_err("an unauthorized lease payment must be refused");
        assert!(matches!(refused, InvokeRefused::Unauthorized { .. }));
    }
}
