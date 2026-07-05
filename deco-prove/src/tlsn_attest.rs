//! **Layer 2, the tlsn / MPC-TLS realization — the INTERFACE + ADAPTER.**
//!
//! This module is the trustless-shaped replacement for the semi-honest [`crate::notary`]
//! interim. Where `notary.rs` has a notary sign a Poseidon2 commitment to facts it
//! *claims* it observed, this module models the **TLSNotary** contract: a Prover and a
//! Notary jointly run the Stripe TLS session under **MPC-TLS** (2PC), the notary
//! co-derives the session secret and never sees the plaintext, and the prover
//! **selectively discloses** authenticated spans of the transcript. The verified output
//! is a [`TlsnPresentation`] whose disclosed spans of the *authenticated* HTTP transcript
//! carry the Stripe payment facts.
//!
//! ## What this is (honest scope — read before trusting)
//!
//! ⚑ This is the **Layer-2 tlsn-attestation INTERFACE + ADAPTER**, exercised end-to-end
//! by a **real tlsn-format fixture** (an authenticated HTTP/1.1 transcript of
//! `GET https://api.stripe.com/v1/payment_intents/{id}` with selective disclosure of the
//! payment facts and redaction of the `Authorization: Bearer sk_live_…` secret). It is
//! **NOT** a live trustless MPC-TLS run: producing a *genuine* verified presentation
//! needs the running `tlsn` notary + the `mpz` 2PC stack + a live Stripe TLS session
//! (none of which is in-tree — `tlsn` is git-only at `v0.1.0-alpha.15`, an async-tokio +
//! rustls + `mpz`-alpha two-party-computation surface that needs a notary service). The
//! adapter models the shape a *verified* `tlsn_core::presentation::PresentationOutput`
//! takes and performs the DECO-side binding; the 2PC session-integrity cryptography (the
//! reason the notary's signature becomes *trustless* rather than *trusted*) is the named
//! remaining wiring. See `docs/deos/TLSN-INTEGRATION.md`.
//!
//! ### Type correspondence to `tlsn-core` v0.1.0-alpha.15
//!
//! The adapter's input models the object `presentation.verify(&provider)` returns:
//!
//! | this module                | `tlsn_core` (alpha.15)                         |
//! |----------------------------|------------------------------------------------|
//! | [`TlsnVerifyingKey`]       | `signing::VerifyingKey { alg, data }`          |
//! | [`TlsnPresentation::server_name`] | `PresentationOutput.server_name`        |
//! | [`TlsnPresentation::connection_time`] | `PresentationOutput.connection_info.time` |
//! | [`PartialTranscript`]      | `PresentationOutput.transcript` (`PartialTranscript`, undisclosed bytes = fill `X`) |
//! | [`Span`] in [`PartialTranscript::authed`] | the authenticated ranges (`reveal_recv`/`reveal_sent`) |
//! | [`TlsnPresentation::notary_sig`] | the notary attestation signature checked by `verify()` |
//!
//! The modeled signature curve is **ed25519** (the curve already in-tree, the same
//! `ed25519-dalek` the interim uses); tlsn's real notary signs with secp256k1/p256 — a
//! notary-config detail, not a semantic one. Checking it here models `verify()`'s
//! signature leg; it does **not** by itself supply the 2PC session binding.
//!
//! ## What the adapter genuinely enforces (non-vacuous, real over the fixture)
//!
//! 1. **Server pinning** — `server_name` MUST be the pinned `api.stripe.com`; a
//!    presentation from any other host is refused.
//! 2. **Notary pinning** — the presentation's [`TlsnVerifyingKey`] MUST equal the pinned
//!    anchor.
//! 3. **Presentation-signature check** — the ed25519 notary signature MUST verify over
//!    the canonical presentation bytes (models `verify()`'s signature leg); tampering any
//!    disclosed byte breaks it.
//! 4. **Selective disclosure (the killer semantics)** — each payment fact is read ONLY
//!    from an **authenticated** span of the transcript. A fact the prover did NOT disclose
//!    (redacted → fill `X`) cannot be read: extraction fails ([`TlsnAdapterError::FactRedacted`]).
//! 5. **Settlement gate** — the disclosed `status` MUST be `succeeded`.
//! 6. **Facts → DECO** — the extracted [`StripePaymentFacts`] feed Layer 1
//!    ([`crate::prover::prove_stripe_deco`]) / the [`dregg_bridge::DecoPaymentAttestation`],
//!    exactly as the interim's facts do — Layer 1 and the bridge verifier are
//!    origin-agnostic and untouched.
//!
//! ## The trust boundary tlsn REMOVES vs what remains
//!
//! - **Removed (once the 2PC is wired):** trust that the notary *honestly observed and
//!   did not fabricate* the Stripe session. Under MPC-TLS the notary co-derives the
//!   session secret without seeing plaintext and cannot forge a transcript it did not
//!   co-witness — so a signed presentation *is* a real Stripe session.
//! - **Remaining honest boundary (named):** the Web-PKI / honest-Stripe floor (that
//!   `api.stripe.com`'s certificate chain is genuine) and the standard crypto carriers
//!   (MPC-TLS soundness, the notary signature scheme). And, in THIS slice specifically,
//!   the 2PC session-binding itself is modeled structurally (authenticated ranges) but
//!   not run — the fixture stands in for a verified presentation.

use dregg_bridge::DecoPaymentAttestation;
use dregg_types::CellId;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

use crate::prover::StripePaymentFacts;

/// The pinned Stripe API host a genuine payment presentation must be a session with.
pub const STRIPE_SERVER_NAME: &str = "api.stripe.com";

/// The `status` value a settled Stripe PaymentIntent discloses.
pub const STRIPE_STATUS_SUCCEEDED: &str = "succeeded";

/// The Stripe object metadata key carrying the dregg recipient cell (64-hex), the SAME
/// key the HMAC webhook path reads (`stripe_mirror::RECIPIENT_METADATA_KEY`).
pub const RECIPIENT_METADATA_KEY: &str = "dregg_recipient";

/// Domain separation over the modeled notary signature (so a tlsn presentation signature
/// can never be replayed as a signature over unrelated bytes).
const TLSN_PRESENTATION_DOMAIN: &[u8] = b"dregg/deco/tlsn-presentation/v1";

/// A byte span `[start, end)` within one direction of a transcript.
///
/// Models a disclosed range of a `tlsn_core` `PartialTranscript` (e.g. the bytes
/// `reveal_recv(json.get("amount"))` authenticates).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// Inclusive start offset.
    pub start: usize,
    /// Exclusive end offset.
    pub end: usize,
}

impl Span {
    /// A span is contained in `other` iff it lies entirely within it.
    fn within(&self, other: &Span) -> bool {
        self.start >= other.start && self.end <= other.end && self.start <= self.end
    }
}

/// The notary's verifying key — models `tlsn_core::signing::VerifyingKey { alg, data }`.
/// A verifier PINS its own expected anchor; the echoed key is a discarded claim unless it
/// matches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlsnVerifyingKey {
    /// The signature algorithm identifier (modeled: `"ed25519"`; tlsn's real notary uses
    /// secp256k1/p256 — a notary-config detail).
    pub alg: String,
    /// The public key bytes (ed25519: 32 bytes).
    pub data: Vec<u8>,
}

/// One direction of the delivered transcript, with only the authenticated (disclosed)
/// ranges readable. Models `tlsn_core` `PartialTranscript`: `data` is the direction's
/// bytes as delivered (undisclosed positions are the fill byte, tlsn `set_unauthed(b'X')`),
/// and `authed` are the cryptographically-authenticated, prover-disclosed ranges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialTranscript {
    /// The direction bytes as delivered (`received_unsafe()` / `sent_unsafe()`).
    pub data: Vec<u8>,
    /// The authenticated (disclosed) ranges. Bytes OUTSIDE these are NOT authenticated —
    /// reading them is a soundness error, and in a real presentation they are fill.
    pub authed: Vec<Span>,
}

impl PartialTranscript {
    /// The authenticated bytes of `span`, or `None` if `span` is not fully within a
    /// disclosed range (i.e. the prover redacted it). This is the selective-disclosure
    /// gate: a value the prover did not authenticate cannot be read.
    pub fn authed_slice(&self, span: Span) -> Option<&[u8]> {
        if span.end > self.data.len() {
            return None;
        }
        if self.authed.iter().any(|r| span.within(r)) {
            Some(&self.data[span.start..span.end])
        } else {
            None
        }
    }

    /// Whether `span` is fully authenticated (disclosed).
    pub fn is_authed(&self, span: Span) -> bool {
        span.end <= self.data.len() && self.authed.iter().any(|r| span.within(r))
    }
}

/// The disclosed-fact locations inside the *received* transcript — which authenticated
/// spans hold each Stripe payment fact (modeling `reveal_recv(json.get("<field>"))`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DisclosedFactSpans {
    /// The `payment_intent` `id` value span (the consume-once replay nonce).
    pub payment_intent_id: Span,
    /// The `amount` value span (integer cents, disclosed as ASCII digits).
    pub amount_cents: Span,
    /// The `currency` value span (ISO-4217, lowercase).
    pub currency: Span,
    /// The `status` value span (must disclose `succeeded`).
    pub status: Span,
    /// The `metadata.dregg_recipient` value span (64-hex dregg CellId).
    pub recipient: Span,
}

/// A **verified tlsn presentation** over a Stripe payment session — models the object
/// `tlsn_core` `presentation.verify(&provider)` yields, plus the disclosed-fact map and
/// the (modeled) notary signature the adapter re-checks.
///
/// Holding one is (once the 2PC session binding is wired) evidence that a live TLS
/// session with `api.stripe.com` disclosed this settled payment — the trustless analogue
/// of a [`crate::notary::NotaryAttestation`], but where the disclosed facts are read out
/// of an *authenticated* transcript rather than taken on the notary's word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlsnPresentation {
    /// The notary's verifying key (a verifier pins its own anchor).
    pub verifying_key: TlsnVerifyingKey,
    /// The authenticated server identity (must be [`STRIPE_SERVER_NAME`]).
    pub server_name: String,
    /// The session time (`connection_info.time`, unix seconds).
    pub connection_time: u64,
    /// The request-direction transcript (the `GET` target is disclosed; the
    /// `Authorization: Bearer sk_live_…` secret is REDACTED — not authenticated).
    pub sent: PartialTranscript,
    /// The response-direction transcript (the payment-fact JSON value spans disclosed).
    pub recv: PartialTranscript,
    /// Where each payment fact lives in the `recv` transcript.
    pub facts: DisclosedFactSpans,
    /// The notary's ed25519 signature over [`Self::canonical_signing_bytes`] — models the
    /// signature leg `presentation.verify()` checks.
    pub notary_sig: [u8; 64],
}

impl TlsnPresentation {
    /// The canonical bytes the notary signs: the domain, the pinned identity fields, and
    /// BOTH directions' delivered bytes + their authenticated ranges. Signing the full
    /// delivered `data` means tampering any disclosed byte (or moving an authed range)
    /// breaks the signature.
    fn canonical_signing_bytes(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(TLSN_PRESENTATION_DOMAIN);
        m.extend_from_slice(&(self.server_name.len() as u64).to_le_bytes());
        m.extend_from_slice(self.server_name.as_bytes());
        m.extend_from_slice(&self.connection_time.to_le_bytes());
        for dir in [&self.sent, &self.recv] {
            m.extend_from_slice(&(dir.data.len() as u64).to_le_bytes());
            m.extend_from_slice(&dir.data);
            m.extend_from_slice(&(dir.authed.len() as u64).to_le_bytes());
            for s in &dir.authed {
                m.extend_from_slice(&(s.start as u64).to_le_bytes());
                m.extend_from_slice(&(s.end as u64).to_le_bytes());
            }
        }
        m
    }
}

/// The pinned expectations the adapter checks a presentation against.
#[derive(Clone, Debug)]
pub struct TlsnStripeConfig {
    /// The server the presentation must be a session with (default [`STRIPE_SERVER_NAME`]).
    pub expected_server: String,
    /// The pinned notary verifying key anchor.
    pub expected_notary: TlsnVerifyingKey,
}

impl TlsnStripeConfig {
    /// Pin the Stripe server + a notary anchor.
    pub fn new(expected_notary: TlsnVerifyingKey) -> Self {
        TlsnStripeConfig {
            expected_server: STRIPE_SERVER_NAME.to_string(),
            expected_notary,
        }
    }
}

/// The reason a tlsn presentation is refused by the adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TlsnAdapterError {
    /// The authenticated server is not the pinned Stripe host.
    WrongServer { got: String },
    /// The presentation's verifying key is not the pinned notary anchor.
    WrongNotary,
    /// The notary key bytes are not a valid ed25519 point.
    MalformedKey,
    /// The notary signature does not verify over the presentation (models a failed
    /// `presentation.verify()` — the transcript or identity was tampered).
    BadNotarySignature,
    /// A payment fact was NOT disclosed (its span is not authenticated) — the prover
    /// redacted it, so it cannot be read. THE selective-disclosure gate.
    FactRedacted { field: &'static str },
    /// A disclosed fact span holds bytes that do not parse as the expected value.
    FactMalformed { field: &'static str },
    /// The disclosed `status` is not `succeeded` (the payment did not settle).
    PaymentNotSucceeded { got: String },
}

impl core::fmt::Display for TlsnAdapterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TlsnAdapterError::WrongServer { got } => {
                write!(
                    f,
                    "presentation server {got:?} is not the pinned {STRIPE_SERVER_NAME:?}"
                )
            }
            TlsnAdapterError::WrongNotary => {
                write!(f, "presentation notary key is not the pinned anchor")
            }
            TlsnAdapterError::MalformedKey => {
                write!(f, "notary key bytes are not a valid ed25519 point")
            }
            TlsnAdapterError::BadNotarySignature => {
                write!(f, "notary signature does not verify over the presentation")
            }
            TlsnAdapterError::FactRedacted { field } => {
                write!(
                    f,
                    "payment fact {field:?} was not disclosed (redacted / unauthenticated)"
                )
            }
            TlsnAdapterError::FactMalformed { field } => {
                write!(f, "disclosed fact {field:?} does not parse")
            }
            TlsnAdapterError::PaymentNotSucceeded { got } => {
                write!(
                    f,
                    "payment status {got:?} is not {STRIPE_STATUS_SUCCEEDED:?}"
                )
            }
        }
    }
}

impl std::error::Error for TlsnAdapterError {}

/// Read an authenticated fact span as UTF-8, or fail closed (redacted / malformed).
fn read_authed_str<'a>(
    recv: &'a PartialTranscript,
    span: Span,
    field: &'static str,
) -> Result<&'a str, TlsnAdapterError> {
    let bytes = recv
        .authed_slice(span)
        .ok_or(TlsnAdapterError::FactRedacted { field })?;
    core::str::from_utf8(bytes).map_err(|_| TlsnAdapterError::FactMalformed { field })
}

/// **THE ADAPTER** — verify a tlsn presentation and extract the disclosed
/// [`StripePaymentFacts`], replacing the semi-honest [`crate::notary`] path.
///
/// Enforces, in order: server pinning, notary pinning, the presentation signature,
/// selective disclosure of every fact (a redacted fact fails), the `succeeded` gate, and
/// the fact parses. On success the returned facts feed Layer 1
/// ([`crate::prover::prove_stripe_deco`]) / [`dregg_bridge::DecoPaymentAttestation`]
/// unchanged.
///
/// ⚑ This checks the presentation as *delivered + signed*; the 2PC session-integrity that
/// makes the signature *trustless* is the named remaining wiring (module docs).
pub fn verify_tlsn_presentation(
    pres: &TlsnPresentation,
    config: &TlsnStripeConfig,
) -> Result<StripePaymentFacts, TlsnAdapterError> {
    // (1) server pinning.
    if pres.server_name != config.expected_server {
        return Err(TlsnAdapterError::WrongServer {
            got: pres.server_name.clone(),
        });
    }

    // (2) notary pinning.
    if pres.verifying_key != config.expected_notary {
        return Err(TlsnAdapterError::WrongNotary);
    }

    // (3) the presentation signature (models presentation.verify()'s signature leg).
    let key_bytes: [u8; 32] = pres
        .verifying_key
        .data
        .as_slice()
        .try_into()
        .map_err(|_| TlsnAdapterError::MalformedKey)?;
    let vk = VerifyingKey::from_bytes(&key_bytes).map_err(|_| TlsnAdapterError::MalformedKey)?;
    let sig = Signature::from_bytes(&pres.notary_sig);
    vk.verify(&pres.canonical_signing_bytes(), &sig)
        .map_err(|_| TlsnAdapterError::BadNotarySignature)?;

    // (4) selective disclosure + (5) settlement + (6) parse.
    let status = read_authed_str(&pres.recv, pres.facts.status, "status")?;
    if status != STRIPE_STATUS_SUCCEEDED {
        return Err(TlsnAdapterError::PaymentNotSucceeded {
            got: status.to_string(),
        });
    }

    let payment_intent_id =
        read_authed_str(&pres.recv, pres.facts.payment_intent_id, "id")?.to_string();

    let amount_str = read_authed_str(&pres.recv, pres.facts.amount_cents, "amount")?;
    let amount_cents: u64 = amount_str
        .parse()
        .map_err(|_| TlsnAdapterError::FactMalformed { field: "amount" })?;

    let currency = read_authed_str(&pres.recv, pres.facts.currency, "currency")?.to_string();

    let recipient_hex = read_authed_str(&pres.recv, pres.facts.recipient, "recipient")?;
    let recipient = parse_recipient_hex(recipient_hex)?;

    Ok(StripePaymentFacts {
        payment_intent_id,
        amount_cents,
        currency,
        recipient,
    })
}

/// Parse a 64-hex `metadata.dregg_recipient` into a [`CellId`].
fn parse_recipient_hex(hex: &str) -> Result<CellId, TlsnAdapterError> {
    let hex = hex.trim();
    if hex.len() != 64 {
        return Err(TlsnAdapterError::FactMalformed { field: "recipient" });
    }
    let mut out = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let s = core::str::from_utf8(chunk)
            .map_err(|_| TlsnAdapterError::FactMalformed { field: "recipient" })?;
        out[i] = u8::from_str_radix(s, 16)
            .map_err(|_| TlsnAdapterError::FactMalformed { field: "recipient" })?;
    }
    Ok(CellId::from_bytes(out))
}

/// **Bind a verified tlsn presentation to a DECO attestation** — the Layer-2 → Layer-1
/// wiring. Verifies the presentation, then produces the [`DecoPaymentAttestation`] over
/// the disclosed facts (the STARK carrier `zk_tls_proof` attaches via
/// [`crate::prover::prove_stripe_deco`]; pass `None` for the commitment-binding-only
/// attestation the bridge verifier's felt-binding still checks).
pub fn tlsn_presentation_to_attestation(
    pres: &TlsnPresentation,
    config: &TlsnStripeConfig,
    zk_tls_proof: Option<Vec<u8>>,
) -> Result<DecoPaymentAttestation, TlsnAdapterError> {
    let facts = verify_tlsn_presentation(pres, config)?;
    Ok(DecoPaymentAttestation::attest(
        facts.payment_intent_id,
        facts.amount_cents,
        facts.currency,
        facts.recipient,
        zk_tls_proof,
    ))
}

// ─────────────────────────────────────────────────────────────────────────────
// The fixture producer — models the tlsn notary + 2PC + live Stripe session.
//
// ⚑ This is NOT a real notary. It is the in-tree PRODUCER that builds a tlsn-format
// presentation over a realistic Stripe HTTP transcript, so the adapter can be exercised
// end-to-end (and forgeries refuted) without the mpz 2PC stack / a running notary / a
// live Stripe TLS session. In the real wiring, `tlsn_core`'s notary produces the signed
// `Attestation` and the prover produces the `Presentation` from the MPC-TLS session.
// ─────────────────────────────────────────────────────────────────────────────

/// The modeled notary that signs a [`TlsnPresentation`] — the fixture producer standing
/// in for the tlsn notary + 2PC. Deterministic from a seed (reproducible fixtures).
pub struct TlsnFixtureNotary {
    signing: SigningKey,
}

impl TlsnFixtureNotary {
    /// A fixture notary from a 32-byte seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        TlsnFixtureNotary {
            signing: SigningKey::from_bytes(seed),
        }
    }

    /// The notary's pinnable verifying key.
    pub fn verifying_key(&self) -> TlsnVerifyingKey {
        TlsnVerifyingKey {
            alg: "ed25519".to_string(),
            data: self.signing.verifying_key().to_bytes().to_vec(),
        }
    }

    /// Sign a presentation (fills [`TlsnPresentation::notary_sig`] over the canonical bytes).
    fn sign(&self, mut pres: TlsnPresentation) -> TlsnPresentation {
        let sig: Signature = self.signing.sign(&pres.canonical_signing_bytes());
        pres.notary_sig = sig.to_bytes();
        pres
    }
}

/// The disclosed Stripe payment for the fixture (what the settled PaymentIntent returns).
#[derive(Clone, Debug)]
pub struct FixturePayment {
    /// The payment-intent id (e.g. `pi_3ABC…`).
    pub payment_intent_id: String,
    /// Amount in cents.
    pub amount_cents: u64,
    /// ISO-4217 currency (lowercase).
    pub currency: String,
    /// The `status` value to place in the response (`succeeded` for a settled payment;
    /// set otherwise to exercise the settlement gate).
    pub status: String,
    /// The dregg recipient cell (placed in `metadata.dregg_recipient` as 64-hex).
    pub recipient: CellId,
}

/// Which payment fact the fixture should REDACT (not authenticate) — to exercise the
/// selective-disclosure gate. `None` discloses all facts (the honest presentation).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RedactedFact {
    /// Redact the amount (the classic "prove a payment happened but hide the amount"
    /// misuse — the adapter must refuse, the amount is load-bearing).
    Amount,
    /// Redact the status.
    Status,
    /// Redact the recipient.
    Recipient,
}

fn hex64(cell: &CellId) -> String {
    let mut s = String::with_capacity(64);
    for b in cell.0 {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Locate `needle` in `hay` starting at `from`, returning the [`Span`] of the match.
fn span_of(hay: &str, needle: &str, from: usize) -> Span {
    let idx = hay[from..]
        .find(needle)
        .unwrap_or_else(|| panic!("fixture builder: {needle:?} not found in transcript"))
        + from;
    Span {
        start: idx,
        end: idx + needle.len(),
    }
}

/// **Build a tlsn-format Stripe payment presentation fixture.**
///
/// Constructs a realistic authenticated HTTP/1.1 transcript of
/// `GET https://api.stripe.com/v1/payment_intents/{id}`:
///
/// - **Request (`sent`):** the request line + `host` + `authorization: Bearer sk_live_…`
///   + `accept`. Only the request *target* (the path) is disclosed; the `Authorization`
///   secret is REDACTED (fill `X`, NOT authenticated) — the killer use case: prove the
///   payment WITHOUT revealing your Stripe secret key.
/// - **Response (`recv`):** the status line + headers + the PaymentIntent JSON. Only the
///   `id`, `amount`, `currency`, `status`, and `metadata.dregg_recipient` value spans are
///   disclosed; the rest of the body (customer, payment-method, etc.) is redacted.
///
/// `redact` optionally drops one fact from the disclosed set (to refute a forged
/// selective disclosure). The presentation is signed by `notary`.
pub fn build_stripe_tlsn_fixture(
    notary: &TlsnFixtureNotary,
    payment: &FixturePayment,
    connection_time: u64,
    redact: Option<RedactedFact>,
) -> TlsnPresentation {
    let recipient_hex = hex64(&payment.recipient);

    // ── Request transcript. The Bearer secret is present in the bytes but NOT disclosed.
    // (In production this is the merchant's real `sk_live_…` key; the fixture uses an
    // obvious placeholder so no real-key SHAPE lands in the tree / trips secret scanners
    // — the redaction demonstration is identical regardless of the token's contents.)
    let secret_key = "MERCHANT-STRIPE-SECRET-KEY-PLACEHOLDER";
    let target = format!("/v1/payment_intents/{}", payment.payment_intent_id);
    let sent_str = format!(
        "GET {target} HTTP/1.1\r\n\
         host: api.stripe.com\r\n\
         authorization: Bearer {secret_key}\r\n\
         accept: */*\r\n\r\n"
    );
    let target_span = span_of(&sent_str, &target, 0);
    // Disclose ONLY the request target; the authorization header stays redacted.
    let sent = redact_outside(&sent_str, &[target_span]);

    // ── Response transcript. A realistic PaymentIntent object; disclose the fact spans.
    let recv_str = format!(
        "HTTP/1.1 200 OK\r\n\
         content-type: application/json\r\n\
         request-id: req_fixture\r\n\r\n\
         {{\"id\":\"{id}\",\"object\":\"payment_intent\",\"amount\":{amount},\
         \"amount_received\":{amount},\"currency\":\"{currency}\",\
         \"customer\":\"cus_hidden\",\"payment_method\":\"pm_hidden\",\
         \"status\":\"{status}\",\"metadata\":{{\"{rkey}\":\"{rhex}\"}}}}",
        id = payment.payment_intent_id,
        amount = payment.amount_cents,
        currency = payment.currency,
        status = payment.status,
        rkey = RECIPIENT_METADATA_KEY,
        rhex = recipient_hex,
    );

    // The value spans (the exact bytes reveal_recv(json.get("<field>")) authenticates).
    let id_val = span_of(&recv_str, &payment.payment_intent_id, 0);
    let amount_str = payment.amount_cents.to_string();
    // Find the amount inside the "amount": occurrence (skip past the id which may collide).
    let amount_anchor = span_of(&recv_str, "\"amount\":", 0).end;
    let amount_val = span_of(&recv_str, &amount_str, amount_anchor);
    let currency_anchor = span_of(&recv_str, "\"currency\":\"", 0).end;
    let currency_val = span_of(&recv_str, &payment.currency, currency_anchor);
    let status_anchor = span_of(&recv_str, "\"status\":\"", 0).end;
    let status_val = span_of(&recv_str, &payment.status, status_anchor);
    let recipient_val = span_of(&recv_str, &recipient_hex, 0);

    let facts = DisclosedFactSpans {
        payment_intent_id: id_val,
        amount_cents: amount_val,
        currency: currency_val,
        status: status_val,
        recipient: recipient_val,
    };

    // The disclosed (authenticated) set — minus any redacted fact.
    let mut disclosed = vec![id_val, amount_val, currency_val, status_val, recipient_val];
    if let Some(r) = redact {
        let drop = match r {
            RedactedFact::Amount => amount_val,
            RedactedFact::Status => status_val,
            RedactedFact::Recipient => recipient_val,
        };
        disclosed.retain(|s| *s != drop);
    }
    let recv = redact_outside(&recv_str, &disclosed);

    let pres = TlsnPresentation {
        verifying_key: notary.verifying_key(),
        server_name: STRIPE_SERVER_NAME.to_string(),
        connection_time,
        sent,
        recv,
        facts,
        notary_sig: [0u8; 64],
    };
    notary.sign(pres)
}

/// Build a [`PartialTranscript`] from a source string, authenticating `authed` and
/// replacing every byte OUTSIDE those ranges with the fill byte `b'X'` (tlsn's
/// `set_unauthed(b'X')` model).
fn redact_outside(src: &str, authed: &[Span]) -> PartialTranscript {
    let mut data = vec![b'X'; src.len()];
    let bytes = src.as_bytes();
    for s in authed {
        data[s.start..s.end].copy_from_slice(&bytes[s.start..s.end]);
    }
    PartialTranscript {
        data,
        authed: authed.to_vec(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn payment() -> FixturePayment {
        FixturePayment {
            payment_intent_id: "pi_3ABCdef456".to_string(),
            amount_cents: 2500,
            currency: "usd".to_string(),
            status: STRIPE_STATUS_SUCCEEDED.to_string(),
            recipient: CellId::from_bytes([7u8; 32]),
        }
    }

    /// THE POSITIVE POLE: an honest tlsn presentation over a settled Stripe payment
    /// verifies + yields exactly the disclosed facts, and the Bearer secret is NOT
    /// disclosed (selective disclosure hid it).
    #[test]
    fn honest_presentation_yields_the_disclosed_facts() {
        let notary = TlsnFixtureNotary::from_seed(&[1u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let pres = build_stripe_tlsn_fixture(&notary, &payment(), 1_700_000_000, None);

        let facts = verify_tlsn_presentation(&pres, &cfg).expect("honest presentation verifies");
        assert_eq!(facts.payment_intent_id, "pi_3ABCdef456");
        assert_eq!(facts.amount_cents, 2500);
        assert_eq!(facts.currency, "usd");
        assert_eq!(facts.recipient, CellId::from_bytes([7u8; 32]));

        // The Stripe secret key is in the request but was NOT authenticated: it does not
        // survive into the delivered (redacted) sent bytes.
        let sent_str = String::from_utf8_lossy(&pres.sent.data);
        assert!(
            !sent_str.contains("MERCHANT-STRIPE-SECRET"),
            "the Bearer secret must be redacted (fill), not disclosed"
        );
    }

    /// The extracted facts feed Layer 1's canonical identity unchanged (the origin-agnostic
    /// hand-off to `prove_stripe_deco` / the bridge verifier).
    #[test]
    fn extracted_facts_project_to_the_canonical_identity() {
        let notary = TlsnFixtureNotary::from_seed(&[2u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let pres = build_stripe_tlsn_fixture(&notary, &payment(), 1, None);
        let facts = verify_tlsn_presentation(&pres, &cfg).unwrap();

        let att = tlsn_presentation_to_attestation(&pres, &cfg, None).unwrap();
        assert_eq!(att.payment_hash, facts.payment_hash());
        assert_eq!(att.amount_cents, 2500);
        assert_eq!(att.recipient, CellId::from_bytes([7u8; 32]));
    }

    /// THE SELECTIVE-DISCLOSURE GATE: a presentation that REDACTS the amount cannot have
    /// the amount read — refused (not silently defaulted). The amount is load-bearing.
    #[test]
    fn redacted_amount_is_refused() {
        let notary = TlsnFixtureNotary::from_seed(&[3u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let pres = build_stripe_tlsn_fixture(&notary, &payment(), 1, Some(RedactedFact::Amount));
        assert_eq!(
            verify_tlsn_presentation(&pres, &cfg).unwrap_err(),
            TlsnAdapterError::FactRedacted { field: "amount" }
        );
    }

    /// A redacted recipient is likewise unreadable → refused (can't mint to an
    /// undisclosed cell).
    #[test]
    fn redacted_recipient_is_refused() {
        let notary = TlsnFixtureNotary::from_seed(&[4u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let pres = build_stripe_tlsn_fixture(&notary, &payment(), 1, Some(RedactedFact::Recipient));
        assert_eq!(
            verify_tlsn_presentation(&pres, &cfg).unwrap_err(),
            TlsnAdapterError::FactRedacted { field: "recipient" }
        );
    }

    /// The settlement gate: a non-`succeeded` status is refused (the payment did not clear).
    #[test]
    fn unsettled_payment_is_refused() {
        let notary = TlsnFixtureNotary::from_seed(&[5u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let mut p = payment();
        p.status = "requires_payment_method".to_string();
        let pres = build_stripe_tlsn_fixture(&notary, &p, 1, None);
        assert_eq!(
            verify_tlsn_presentation(&pres, &cfg).unwrap_err(),
            TlsnAdapterError::PaymentNotSucceeded {
                got: "requires_payment_method".to_string()
            }
        );
    }

    /// Server pinning: a presentation from any other host is refused.
    #[test]
    fn wrong_server_is_refused() {
        let notary = TlsnFixtureNotary::from_seed(&[6u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let mut pres = build_stripe_tlsn_fixture(&notary, &payment(), 1, None);
        pres.server_name = "evil.example.com".to_string();
        // Re-sign so the sig is valid over the tampered server — the ADAPTER's server
        // pin (not the sig) must catch it.
        let resigned = notary.sign(pres);
        assert!(matches!(
            verify_tlsn_presentation(&resigned, &cfg).unwrap_err(),
            TlsnAdapterError::WrongServer { .. }
        ));
    }

    /// Notary pinning: a presentation signed by a DIFFERENT notary is refused.
    #[test]
    fn wrong_notary_anchor_is_refused() {
        let notary = TlsnFixtureNotary::from_seed(&[7u8; 32]);
        let other = TlsnFixtureNotary::from_seed(&[8u8; 32]);
        let cfg = TlsnStripeConfig::new(other.verifying_key());
        let pres = build_stripe_tlsn_fixture(&notary, &payment(), 1, None);
        assert_eq!(
            verify_tlsn_presentation(&pres, &cfg).unwrap_err(),
            TlsnAdapterError::WrongNotary
        );
    }

    /// The presentation-signature check: tampering a DISCLOSED byte (bump the amount in
    /// the authenticated transcript) breaks the notary signature — the presentation is
    /// refused before any fact is trusted.
    #[test]
    fn tampered_disclosed_byte_breaks_the_signature() {
        let notary = TlsnFixtureNotary::from_seed(&[9u8; 32]);
        let cfg = TlsnStripeConfig::new(notary.verifying_key());
        let mut pres = build_stripe_tlsn_fixture(&notary, &payment(), 1, None);

        // Flip a byte inside the authenticated amount span (2500 → 9500).
        let amt = pres.facts.amount_cents;
        pres.recv.data[amt.start] = b'9';
        assert_eq!(
            verify_tlsn_presentation(&pres, &cfg).unwrap_err(),
            TlsnAdapterError::BadNotarySignature
        );
    }
}
