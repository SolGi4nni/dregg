//! The metered-call seam: a backend-agnostic Converse request/response, the
//! [`ConverseBackend`] trait a hosted model implements, and [`metered_converse`] — the ONE
//! function that enforces the reservation → true-up ordering around any backend.
//!
//! The trait exists so the ordering can be tested WITHOUT the network: a test backend that
//! panics on call proves the reservation refuses an over-cap request BEFORE the backend is ever
//! reached, and a canned-usage backend proves the true-up records the exact cost.

use serde_json::Value;

use crate::ledger::BudgetLedger;
use crate::models::ModelRegistry;
use crate::NarratorError;

/// A conversation role in a Converse message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    User,
    Assistant,
}

/// One message in a Converse turn.
#[derive(Clone, Debug)]
pub struct ConverseMessage {
    pub role: Role,
    pub text: String,
}

impl ConverseMessage {
    pub fn user(text: impl Into<String>) -> ConverseMessage {
        ConverseMessage {
            role: Role::User,
            text: text.into(),
        }
    }
    pub fn assistant(text: impl Into<String>) -> ConverseMessage {
        ConverseMessage {
            role: Role::Assistant,
            text: text.into(),
        }
    }
}

/// A tool the model may call — the Converse `toolConfig` teeth. `input_schema` is a JSON-Schema
/// object describing the tool's arguments (Nova supports the Converse `toolConfig`).
#[derive(Clone, Debug)]
pub struct ToolDef {
    pub name: String,
    pub description: String,
    pub input_schema: Value,
}

/// A tool the model asked to call, parsed out of the response.
#[derive(Clone, Debug, PartialEq)]
pub struct ToolCall {
    pub id: String,
    pub name: String,
    pub input: Value,
}

/// A backend-agnostic Converse request. Carries its own model id so one client can serve several
/// models and the ledger can price/gate each call by the model it actually targets.
#[derive(Clone, Debug)]
pub struct ConverseRequest {
    /// The model id this call targets (must be priced in the registry, or it is refused).
    pub model: String,
    /// The system prompt (the DM's committed rules).
    pub system: String,
    /// The conversation so far.
    pub messages: Vec<ConverseMessage>,
    /// The output ceiling for this call — also what the reservation charges at the output rate.
    pub max_tokens: u32,
    /// Optional tools (the `toolConfig`); empty = plain narration.
    pub tools: Vec<ToolDef>,
}

impl ConverseRequest {
    /// A plain single-user-turn request with no tools.
    pub fn plain(
        model: impl Into<String>,
        system: impl Into<String>,
        user: impl Into<String>,
        max_tokens: u32,
    ) -> ConverseRequest {
        ConverseRequest {
            model: model.into(),
            system: system.into(),
            messages: vec![ConverseMessage::user(user)],
            max_tokens,
            tools: Vec::new(),
        }
    }

    /// The total prompt byte length — the reservation's conservative input estimate is
    /// `ceil(prompt_bytes / 3)`.
    pub fn prompt_bytes(&self) -> usize {
        self.system.len() + self.messages.iter().map(|m| m.text.len()).sum::<usize>()
    }
}

/// A LIGHT, provider-neutral receipt that a hosted call ran inside an ATTESTED enclave.
///
/// This crate does not verify anything — it only *names* the shape, so a backend that DOES
/// attest (today: `dregg-chutes-e2ee`'s `ChutesTeeBackend`, which DCAP-verifies an Intel TDX
/// quote before a byte is encrypted) can hand the outcome back through [`ConverseResponse`]
/// without dragging `tee-verify` → `dcap-qvl` → `pqcrypto` into every narrator consumer.
///
/// It is deliberately a SUMMARY: the full DER quote stays with the backend that verified it
/// (`ChutesTeeBackend::last_attestation`), so a receipt lane can commit the bytes without the
/// narration path carrying ~5 KB per turn. `quote_sha256` is the link between the two.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestationSummary {
    /// The enclave instance that served this call (pinned as `X-Instance-Id`).
    pub instance_id: String,
    /// The folded code-identity measurement (MRTD+RTMR0..2) that matched the pinned registry.
    pub measurement: [u8; 32],
    /// The DCAP TCB status the verifier accepted (e.g. `UpToDate`).
    pub tcb_status: String,
    /// SHA-256 of the raw attestation quote — the handle onto the full quote bytes.
    pub quote_sha256: [u8; 32],
    /// Length of the raw quote in bytes (a cheap sanity check against the full bytes).
    pub quote_len: usize,
}

impl AttestationSummary {
    /// The measurement as lowercase hex (for logs / embeds / receipts).
    pub fn measurement_hex(&self) -> String {
        hex32(&self.measurement)
    }

    /// The quote digest as lowercase hex.
    pub fn quote_sha256_hex(&self) -> String {
        hex32(&self.quote_sha256)
    }
}

/// **The FULL evidence behind an [`AttestationSummary`]** — everything an independent verifier
/// needs to re-run the check, rather than take our word for the summary.
///
/// [`AttestationSummary`] travels on every response because it is small; this does not, because
/// the quote is kilobytes. Splitting them lets the narration path stay light while a receipt lane
/// pulls the bytes exactly once, per turn, and archives them. `quote_sha256` of `quote_bytes` is
/// the link between the two halves, and a consumer that persists this MUST re-derive it rather
/// than trust the pairing (see [`AttestationEvidence::attestation_for`]).
///
/// `nonce_hex` and `e2e_pubkey_b64` are here for a specific reason: without them the quote alone
/// establishes only "some enclave with these measurements signed something". WITH them anyone can
/// recompute the provider's `report_data` binding and see that this quote was minted fresh for
/// this key — which is what makes an archived record checkable instead of decorative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestationQuote {
    /// The enclave instance that served the call.
    pub instance_id: String,
    /// The folded code-identity measurement that matched the pinned registry.
    pub measurement: [u8; 32],
    /// The TCB status the verifier accepted.
    pub tcb_status: String,
    /// The fresh attestation nonce this quote was requested with (provider-specific encoding;
    /// for Chutes, the 64-char hex string hashed into `report_data`).
    pub nonce_hex: String,
    /// The instance public key bound into the quote (for Chutes, the base64 ML-KEM-768 key the
    /// request was encapsulated to).
    pub e2e_pubkey_b64: String,
    /// The raw attestation quote — the bytes an independent DCAP verifier consumes.
    pub quote_bytes: Vec<u8>,
}

/// A backend that RETAINS the full evidence of the attestations it verified, keyed by quote
/// digest, so a receipt lane can archive the bytes behind a summary it was handed.
///
/// Keyed by digest and not "the last one" on purpose: a `converse` result and a later
/// `last_attestation()` are two reads with turns in between, and pairing a summary with whatever
/// record happened to be current is exactly how an archive acquires a quote that does not belong
/// to the response it is filed under.
pub trait AttestationEvidence: Send + Sync {
    /// The full evidence for the attestation whose quote hashes to `quote_sha256`, or `None` if
    /// this backend no longer retains it (it keeps a bounded window, not a history).
    ///
    /// Implementations MUST return only a record whose `quote_bytes` actually hash to
    /// `quote_sha256`.
    fn attestation_for(&self, quote_sha256: &[u8; 32]) -> Option<AttestationQuote>;
}

/// Lowercase hex of a 32-byte digest — a 6-line local encoder so naming an attestation costs
/// the light narrator crate no new dependency.
fn hex32(bytes: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(64);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

/// A backend-agnostic Converse response.
#[derive(Clone, Debug, Default)]
pub struct ConverseResponse {
    /// The concatenated text blocks (the narration).
    pub text: String,
    /// Any tool calls the model made this turn.
    pub tool_calls: Vec<ToolCall>,
    /// The model's stop reason (`end_turn`, `max_tokens`, `tool_use`, …).
    pub stop_reason: String,
    /// The REAL input-token count from the response usage — what the true-up prices.
    pub input_tokens: u32,
    /// The REAL output-token count from the response usage.
    pub output_tokens: u32,
    /// The TEE attestation that covered this call, when the backend attested one.
    ///
    /// `None` is the HONEST default and means exactly "this response carries no attestation" —
    /// never "attestation passed". Every non-attesting backend (Bedrock, the plain
    /// OpenAI-compatible client, every test double) leaves it `None`; only a backend that ran a
    /// real verification fills it in.
    pub attestation: Option<AttestationSummary>,
}

/// A hosted model that can run a Converse turn. Implemented by the real Bedrock client; a test
/// double implements it to exercise the ledger ordering offline.
pub trait ConverseBackend {
    /// Run one Converse turn, returning the usage-bearing response, or a human-readable error.
    fn converse(&self, req: &ConverseRequest) -> Result<ConverseResponse, String>;
}

/// Run `req` against `backend`, enforcing the hard ceiling. The order is the whole point:
///
/// 1. **Price the model** — look it up in `registry`. An UNPRICED model is refused
///    ([`NarratorError::UnpricedModel`]) here, BEFORE the backend is ever touched: we do not
///    enforce a budget on a cost we do not know.
/// 2. **Reserve** — an upper-bound cost is held against the cap; this may return
///    [`NarratorError::BudgetExhausted`], again BEFORE the backend is called (no network).
/// 3. **Call** the backend.
/// 4. **True up** the reservation with the response's REAL token usage (or **refund** on failure).
pub fn metered_converse(
    ledger: &BudgetLedger,
    registry: &ModelRegistry,
    backend: &(dyn ConverseBackend + Send + Sync),
    req: &ConverseRequest,
) -> Result<ConverseResponse, NarratorError> {
    // (1) PRICE — fail-closed on an unpriced model, before anything else.
    let pricing = registry
        .pricing_for(&req.model)
        .ok_or_else(|| NarratorError::UnpricedModel {
            model: req.model.clone(),
        })?;

    // (2) RESERVE — a refusal here short-circuits, so `backend.converse` is NEVER reached.
    let reservation = ledger.reserve(&req.model, req.prompt_bytes(), req.max_tokens, &pricing)?;

    // (3) CALL.
    match backend.converse(req) {
        Ok(resp) => {
            // (4) TRUE-UP — replace the reservation with the exact usage-priced cost.
            ledger.true_up(reservation, resp.input_tokens, resp.output_tokens, &pricing)?;
            Ok(resp)
        }
        Err(e) => {
            // The call never landed — release the reservation; it cost nothing.
            let _ = ledger.refund(reservation);
            Err(NarratorError::Backend(e))
        }
    }
}
