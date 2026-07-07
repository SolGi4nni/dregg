//! # commons-arbiter — the AI authority nobody owns, as a runnable core
//!
//! The **Commons Arbiter** (`docs/deos/UNCENSORABLE-UTILITY.md`) is a neutral service that
//! rules on cases against a community's published **rubric** — its "constitution" — where no
//! single operator can forge, bias, or halt a ruling. This crate is its **runnable core**.
//!
//! A member submits a [`Case`] (content + the rubric id it is judged under); the Arbiter's
//! **confined + attested brain** reads it against the [`Rubric`] and issues a [`Ruling`]; the
//! ruling lands as a **receipted attested turn** on a [`CaseLedger`], carrying a
//! [`dregg_zkoracle_prove::ZkOracleAttestation`] proving the turn was:
//!
//! ```text
//!   authentic     — from a real model (a genuine `/v1/messages` session), not forged;
//!   well-formed   — the response body lies in the JSON context-free language;
//!   injection-free — the bound ruling text carries no `{{` handlebars delimiter.
//! ```
//!
//! ## The killer property — an un-censorable authority
//!
//! A case whose content carries a **prompt-injection** (`{{`, or the handlebars injection
//! template) is **reflected into the ruling** — an arbiter states *what the case said* — and
//! there the **injection-free leg** catches it: the ruling over that input **cannot be
//! attested** ([`ArbiterError::Injection`]), so the ruling is **refused** and the ledger gains
//! nothing (the anti-ghost tooth). Nobody can inject a verdict into the Arbiter. This is the
//! same verified `neg`-complement matcher `verify_zkoracle` runs, so a forged attestation that
//! smuggled a `{{` field would ALSO be rejected at verify.
//!
//! ## Cap-bounded authority
//!
//! The Arbiter rules only under the rubric ids in its [`ArbiterCaps`] **jurisdiction** — its
//! authority is exactly the cap the community granted it (`UNCENSORABLE-UTILITY.md` §1). A
//! case under a rubric outside that jurisdiction is refused **fail-closed** ([`ArbiterError::
//! OutOfJurisdiction`]), ledger unchanged, before any attestation.
//!
//! ## No single operator owns it — the quorum
//!
//! A ruling is a record; it becomes **final** only when a committee of `n` genuinely
//! independent operators super-ratifies it, `⌊2n/3⌋+1` of them ([`quorum`]). A single
//! operator — or any `f = ⌊(n−1)/3⌋`-sized minority — cannot finalize it or forge one: a
//! ratification of a *different* (forged) commitment does not count toward the true ruling's
//! quorum. This is the `VoteEngine`-shaped stub of the real `collective-choice` / blocklace
//! finality; the live independent-operator federation deploy is the named operational
//! remainder (`UNCENSORABLE-UTILITY.md` §4).
//!
//! ## What is REAL vs modeled
//!
//! * **REAL — the attestation.** Produced by [`dregg_zkoracle_prove::prove_zkoracle`] and
//!   checked by [`dregg_zkoracle_prove::verify_zkoracle`] (authentic ∧ well-formed ∧
//!   injection-free). The SAME primitives `deos_hermes::attest::AttestationCarrier` wraps;
//!   composed here DIRECTLY so the Arbiter stays light (no HTTP/TLS). The real local MPC-TLS
//!   2PC roundtrip is behind the `tlsn-live` feature.
//! * **REAL — the case ledger.** Every landed ruling is appended to [`CaseLedger`] with a
//!   32-byte receipt commitment ([`attestation_commitment`]); [`CaseLedger::verify_ledger`]
//!   re-verifies the whole chain and a tampered / swapped / forged entry is distinguishable.
//! * **REAL — the cap bound + the quorum gate.** [`ArbiterCaps::authorize`] gates every case;
//!   [`quorum::QuorumCommittee`] finalizes only at `⌊2n/3⌋+1`.
//! * **MODELED — the brain.** A [`RulingBrain`] turns the rubric + case into a ruling; the
//!   default [`RecordedArbiter`] is a deterministic stand-in for a live LLM. The full OS-jailed
//!   confined body is `deos_hermes::DreggHost::run_hosted_agent_attested` (the crown).

use std::collections::BTreeSet;

use dregg_node_target::{NodeTarget, SubmittedTurn};
use dregg_zkoracle_prove::{
    build_anthropic_fixture, prove_zkoracle, verify_zkoracle, AnthropicConfig, FixtureNotary,
    ProveError, VerifiedZkOracle, ZkOracleAttestation, ZkOracleError,
};

pub mod quorum;

// ─────────────────────────────────────────────────────────────────────────────
// The attestation carrier — the real zkoracle-prove primitives, composed directly.
// ─────────────────────────────────────────────────────────────────────────────

/// Domain separator for [`attestation_commitment`] — the Arbiter ruling receipt-id domain.
const RECEIPT_COMMIT_DOMAIN: &[u8] = b"commons-arbiter-ruling-receipt-v1";

/// The modeled session time stamped on the carrier's presentation (unix seconds). The
/// attestation is about the ruling BODY; the exact timestamp is not load-bearing.
const ATTEST_CONNECTION_TIME: u64 = 1_700_000_000;

/// The default deterministic seed for the Arbiter's modeled notary carrier, so a session's
/// ruling attestations verify against a reproducible pinned anchor.
pub const DEFAULT_ARBITER_SEED: [u8; 32] = [0xA3; 32];

/// **The Arbiter's attestation carrier** — the modeled authentic anchor each ruling is
/// attested under. Holds the notary that signs the presentation carrier and the pinned
/// [`AnthropicConfig`] a verifier checks against. The direct composition of the real
/// [`dregg_zkoracle_prove`] primitives (`build_anthropic_fixture` + `prove_zkoracle`) — the
/// same ones `deos_hermes::attest::AttestationCarrier` wraps — kept here so the Arbiter needs
/// no HTTP/TLS / verified-Lean link for its default (modeled) path.
pub struct ArbiterAttestationCarrier {
    notary: FixtureNotary,
    config: AnthropicConfig,
}

impl Default for ArbiterAttestationCarrier {
    fn default() -> Self {
        ArbiterAttestationCarrier::from_seed(&DEFAULT_ARBITER_SEED)
    }
}

impl ArbiterAttestationCarrier {
    /// A carrier from a 32-byte notary seed. Its [`Self::config`] pins that notary's verifying
    /// key — the anchor `verify_zkoracle` checks the attestation against.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let notary = FixtureNotary::from_seed(seed);
        let config = AnthropicConfig::new(notary.verifying_key());
        ArbiterAttestationCarrier { notary, config }
    }

    /// The pinned config a verifier uses: `verify_zkoracle(&att, carrier.config())`.
    pub fn config(&self) -> &AnthropicConfig {
        &self.config
    }

    /// PRODUCE a zkOracle attestation over an Anthropic messages RESPONSE BODY, binding
    /// `field` (which MUST be a substring of `response_body`) injection-free. The modeled
    /// carrier signs the presentation; [`prove_zkoracle`] proves the CFG (well-formed) and
    /// injection-free legs and binds them to this one response. Refuses a malformed body, an
    /// injecting field, or a field absent from the body.
    pub fn attest_body(
        &self,
        response_body: &str,
        field: &[u8],
    ) -> Result<ZkOracleAttestation, ProveError> {
        let pres = build_anthropic_fixture(&self.notary, response_body, ATTEST_CONNECTION_TIME);
        prove_zkoracle(pres, field.to_vec(), self.config())
    }

    /// ATTEST A RULING. Shapes the ruling text into an Anthropic messages object and binds
    /// that text injection-free — so the attestation certifies the model's ACTUAL ruling this
    /// turn (authentic session + well-formed JSON + no `{{` in its own words). Returns the
    /// attestation and the exact field bound (the sanitized ruling text).
    pub fn attest_ruling(
        &self,
        ruling: &str,
    ) -> Result<(ZkOracleAttestation, Vec<u8>), ProveError> {
        let field = clean_field(ruling);
        let body = messages_body(&field);
        let att = self.attest_body(&body, field.as_bytes())?;
        Ok((att, field.into_bytes()))
    }

    /// THE CROWN, RUN REAL-LOCALLY. Attest `ruling` over a GENUINE local MPC-TLS 2PC roundtrip
    /// (server + notary + prover in-process; the notary sees no plaintext; a real
    /// `presentation.verify()`) against an Anthropic-shaped endpoint — so the certified bytes
    /// came from a real 2PC session, not a fixture literal. `ruling` must be JSON-string-safe
    /// and injection-free (no `{{`). The authentic *leg* is still the modeled carrier over the
    /// (now really-authenticated) body; fusing the real tlsn presentation into that leg is the
    /// named operational remainder (mirrors `deos_hermes::attest::attest_turn_live`).
    #[cfg(feature = "tlsn-live")]
    pub fn attest_ruling_live(
        &self,
        prompt: &str,
        ruling: &str,
    ) -> Result<ZkOracleAttestation, String> {
        use dregg_zkoracle_prove::tlsn_live::{run_local_roundtrip_blocking, LiveExchange};
        let exchange = LiveExchange::messages(prompt, ruling);
        let roundtrip = run_local_roundtrip_blocking(&exchange).map_err(|e| e.to_string())?;
        let body = String::from_utf8(roundtrip.verified.response_body.clone())
            .map_err(|e| format!("authenticated response body is not utf-8: {e}"))?;
        self.attest_body(&body, ruling.as_bytes())
            .map_err(|e| e.to_string())
    }
}

/// **The canonical 32-byte receipt id for a landed ruling turn** — a length-prefixed BLAKE3
/// over the attestation's load-bearing, verifier-visible fields (the pinned session identity +
/// signed transcripts, the cross-leg content commitment, and the injection-checked field
/// span). A total fingerprint: a tampered session, a spliced body, or a re-aimed field span
/// all change it. A light client holding the attestation recomputes this and checks it equals
/// the receipt on the landed turn. Mirrors `deos_hermes::attest::attestation_commitment`.
pub fn attestation_commitment(att: &ZkOracleAttestation) -> [u8; 32] {
    let pres = &att.presentation;
    let mut h = blake3::Hasher::new();
    h.update(RECEIPT_COMMIT_DOMAIN);
    h.update(&(pres.server_name.len() as u64).to_le_bytes());
    h.update(pres.server_name.as_bytes());
    h.update(&pres.connection_time.to_le_bytes());
    h.update(&(pres.sent.len() as u64).to_le_bytes());
    h.update(&pres.sent);
    h.update(&(pres.recv.len() as u64).to_le_bytes());
    h.update(&pres.recv);
    h.update(&pres.notary_sig);
    h.update(&att.content_commit.as_u32().to_le_bytes());
    h.update(&(att.field_span.offset as u64).to_le_bytes());
    h.update(&(att.field_span.len as u64).to_le_bytes());
    *h.finalize().as_bytes()
}

/// Shape a bound field into a well-formed Anthropic messages RESPONSE BODY (the shape
/// `/v1/messages` returns): the assistant `content[0].text` IS the field, so the field is a
/// verbatim, committed substring of the body.
fn messages_body(field: &str) -> String {
    format!(
        "{{\"id\":\"msg_arbiter\",\"type\":\"message\",\"role\":\"assistant\",\
         \"model\":\"claude-opus-4-8\",\
         \"content\":[{{\"type\":\"text\",\"text\":\"{field}\"}}],\
         \"stop_reason\":\"end_turn\",\"stop_sequence\":null,\
         \"usage\":{{\"input_tokens\":32,\"output_tokens\":16}}}}"
    )
}

/// Render `text` into a JSON-string-safe field that embeds verbatim (no escaping): drop the two
/// bytes JSON strings must escape (`"` and `\`) and the raw control chars, keeping everything
/// else — **crucially the `{` / `}` bytes**, so a genuine `{{` injection attempt reflected from
/// a case's content SURVIVES into the field and the injection-free leg still fires on it (the
/// load-bearing catch is preserved, not sanitized away). An empty result falls back to a
/// placeholder so the bound field is always a real substring.
fn clean_field(text: &str) -> String {
    let cleaned: String = text
        .chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control())
        .collect();
    let trimmed = cleaned.trim();
    if trimmed.is_empty() {
        "the arbiter withholds a ruling".to_string()
    } else {
        trimmed.to_string()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The case + the rubric + the ruling.
// ─────────────────────────────────────────────────────────────────────────────

/// **A community's published rubric** — the "constitution" the Arbiter must apply. A case is
/// judged under exactly one rubric (by [`Rubric::id`]); the ruling BINDS that id, so a ruling
/// is provably tied to the standard it applied.
#[derive(Clone, Debug)]
pub struct Rubric {
    /// The rubric id — the case names this, and the Arbiter's jurisdiction is a set of these.
    pub id: String,
    /// The rubric text (the published standard).
    pub text: String,
}

impl Rubric {
    /// A rubric with the given id and text.
    pub fn new(id: impl Into<String>, text: impl Into<String>) -> Rubric {
        Rubric {
            id: id.into(),
            text: text.into(),
        }
    }
}

/// **A case submitted to the Arbiter** — the content to be ruled on plus the rubric id it is
/// judged under. Its [`Case::content`] is reflected into the ruling (an arbiter states what the
/// case said), so a `{{`-bearing case reaches the injection-free leg — the un-censorable-
/// authority tooth.
#[derive(Clone, Debug)]
pub struct Case {
    /// Who submitted the case.
    pub submitter: String,
    /// The rubric id this case is to be judged under (must be in the Arbiter's jurisdiction).
    pub rubric_id: String,
    /// The raw case content (reflected verbatim into the ruling — this is how an injection
    /// reaches the attestation's injection-free leg).
    pub content: String,
}

impl Case {
    /// A case from `submitter`, judged under `rubric_id`, over `content`.
    pub fn new(
        submitter: impl Into<String>,
        rubric_id: impl Into<String>,
        content: impl Into<String>,
    ) -> Case {
        Case {
            submitter: submitter.into(),
            rubric_id: rubric_id.into(),
            content: content.into(),
        }
    }
}

/// The Arbiter's verdict on a case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The case complies with the rubric — no violation.
    Upholds,
    /// The case violates the rubric.
    Violates,
    /// The case cannot be decided on the record (needs more).
    Inconclusive,
}

impl Verdict {
    /// A short, brace-free label (safe to embed in an attested ruling field).
    pub fn label(self) -> &'static str {
        match self {
            Verdict::Upholds => "UPHOLDS",
            Verdict::Violates => "VIOLATES",
            Verdict::Inconclusive => "INCONCLUSIVE",
        }
    }
}

/// The Arbiter's ruling this turn — the verdict and its reasons. The ruling TEXT (see
/// [`Ruling::render`]) is what the attestation binds; it embeds the rubric id (so the ruling is
/// bound to the exact rubric it applied) and reflects the case content (so an injection is
/// caught).
#[derive(Clone, Debug)]
pub struct Ruling {
    /// The verdict.
    pub verdict: Verdict,
    /// The reasons the Arbiter gives (brace-free framing; the case content is appended raw).
    pub reasons: String,
}

impl Ruling {
    /// A ruling with the given verdict and reasons.
    pub fn new(verdict: Verdict, reasons: impl Into<String>) -> Ruling {
        Ruling {
            verdict,
            reasons: reasons.into(),
        }
    }

    /// **The exact ruling text bound by the attestation** — binds the rubric id, states the
    /// verdict + reasons, and REFLECTS the case content verbatim (NOT brace-sanitized, so a
    /// `{{` in the case reaches the injection-free leg). Any change to rubric / verdict /
    /// content changes this text, hence the attestation, hence its commitment.
    pub fn render(&self, rubric_id: &str, case: &Case) -> String {
        format!(
            "RULING under rubric {rubric_id}: {verdict} -- {reasons}. case by {who} says: {content}",
            verdict = self.verdict.label(),
            reasons = self.reasons,
            who = case.submitter,
            content = case.content,
        )
    }
}

/// How the Arbiter rules. A stand-in for a live LLM brain: the Arbiter's cap-bound,
/// attestation, and un-censorable teeth are real around whatever brain drives the ruling. The
/// full OS-jailed confined brain is `deos_hermes::DreggHost::run_hosted_agent_attested`.
pub trait RulingBrain {
    /// Rule on `case` against `rubric` and return the ruling. MUST NOT emit a `{{` handlebars
    /// sequence in its own framing (the case content it reflects may carry one — that is what
    /// the injection-free leg is for).
    fn rule(&self, rubric: &Rubric, case: &Case) -> Ruling;
}

/// The default modeled Arbiter brain: a deterministic, legible rule so a session is
/// reproducible. It reads the case content and returns a verdict — `Violates` when the content
/// signals a breach (`"violat"`), `Inconclusive` when it poses a question (`"?"`), else
/// `Upholds` — with reasons that cite the rubric. The case content is reflected by
/// [`Ruling::render`], not here, so it stays un-sanitized for the injection-free leg.
#[derive(Clone, Copy, Debug, Default)]
pub struct RecordedArbiter;

impl RulingBrain for RecordedArbiter {
    fn rule(&self, rubric: &Rubric, case: &Case) -> Ruling {
        let lower = case.content.to_lowercase();
        if lower.contains("violat") || lower.contains("harass") || lower.contains("spam") {
            Ruling::new(
                Verdict::Violates,
                format!("the submission breaches rubric {}", rubric.id),
            )
        } else if case.content.contains('?') {
            Ruling::new(
                Verdict::Inconclusive,
                format!("the record is insufficient under rubric {}", rubric.id),
            )
        } else {
            Ruling::new(
                Verdict::Upholds,
                format!("the submission conforms to rubric {}", rubric.id),
            )
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The Arbiter caps — cap-bounded authority (jurisdiction).
// ─────────────────────────────────────────────────────────────────────────────

/// **The Arbiter's granted authority.** The Arbiter rules only under the rubric ids in its
/// [`Self::jurisdiction`] — its authority is exactly the cap the community granted it. A case
/// under any other rubric is refused fail-closed ([`ArbiterError::OutOfJurisdiction`]). The
/// Arbiter cannot rule where it was not granted.
#[derive(Clone, Debug, Default)]
pub struct ArbiterCaps {
    /// The exact rubric ids the Arbiter is permitted to rule under.
    pub jurisdiction: BTreeSet<String>,
}

impl ArbiterCaps {
    /// An Arbiter granted jurisdiction over exactly the given rubric ids.
    pub fn over(rubric_ids: impl IntoIterator<Item = impl Into<String>>) -> ArbiterCaps {
        ArbiterCaps {
            jurisdiction: rubric_ids.into_iter().map(Into::into).collect(),
        }
    }

    /// **Authorize a case's rubric against this jurisdiction.** `Ok(())` iff the Arbiter may
    /// rule under `rubric_id`; `Err(OutOfJurisdiction)` otherwise. The fail-closed cap tooth.
    pub fn authorize(&self, rubric_id: &str) -> Result<(), OutOfJurisdiction> {
        if self.jurisdiction.contains(rubric_id) {
            Ok(())
        } else {
            Err(OutOfJurisdiction(rubric_id.to_string()))
        }
    }
}

/// The rubric a case named that lies outside the Arbiter's jurisdiction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutOfJurisdiction(pub String);

impl std::fmt::Display for OutOfJurisdiction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "the arbiter has no jurisdiction over rubric `{}`",
            self.0
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The case ledger — every ruling a receipted attested turn.
// ─────────────────────────────────────────────────────────────────────────────

/// **The case ledger** — the tamper-evident record of every landed ruling. A ruling advances
/// it and leaves a receipt; a refused ruling advances nothing and leaves no receipt (the
/// anti-ghost tooth). Locally defined from the Commons-Arbiter design; the live version is a
/// finalized turn on the community's shared ledger (`UNCENSORABLE-UTILITY.md` §3).
#[derive(Clone, Debug, Default)]
pub struct CaseLedger {
    /// The receipt ledger — every landed ruling, in order. Un-rewritable: a past ruling cannot
    /// be secretly changed ([`CaseLedger::verify_ledger`] catches it).
    pub ledger: Vec<LedgerEntry>,
}

/// One landed, attested, receipted ruling turn on the ledger.
#[derive(Clone, Debug)]
pub struct LedgerEntry {
    /// The sequence number (the ruling's index in the ledger).
    pub seq: u64,
    /// The rubric id the ruling was made under.
    pub rubric_id: String,
    /// The verdict.
    pub verdict: Verdict,
    /// The ruling text the Arbiter produced this turn (the exact bound field — a committed
    /// substring of the authenticated response body).
    pub ruling_text: String,
    /// THE ATTESTATION — a `verify_zkoracle`-checkable proof this ruling was authentic (from a
    /// real model) ∧ well-formed ∧ injection-free.
    pub attestation: ZkOracleAttestation,
    /// The 32-byte receipt id ([`attestation_commitment`]) — the fingerprint a light client
    /// recomputes.
    pub receipt: [u8; 32],
}

impl CaseLedger {
    /// A fresh, empty case ledger.
    pub fn new() -> CaseLedger {
        CaseLedger::default()
    }

    /// The receipt id of every landed ruling (the tamper-proof chain).
    pub fn receipts(&self) -> Vec<[u8; 32]> {
        self.ledger.iter().map(|e| e.receipt).collect()
    }

    /// **Re-verify the whole ledger** against `config`: every entry's attestation
    /// `verify_zkoracle`-accepts (authentic ∧ well-formed ∧ injection-free), its displayed
    /// ruling text is the committed attested text (a swapped ruling is caught), and its receipt
    /// commitment recomputes. A tampered / forged entry is distinguishable — [`LedgerError`]
    /// names which turn and why.
    pub fn verify_ledger(&self, config: &AnthropicConfig) -> Result<(), LedgerError> {
        for (i, entry) in self.ledger.iter().enumerate() {
            verify_turn(entry, config).map_err(|reason| LedgerError {
                seq: i as u64,
                reason,
            })?;
        }
        Ok(())
    }
}

/// **Verify one landed ruling is authentic + un-forged.** Checks: (1) `verify_zkoracle` accepts
/// the attestation (authentic ∧ well-formed ∧ injection-free); (2) the displayed ruling text is
/// a committed substring of the authenticated response body (a swapped-out ruling over a real
/// attestation is caught); (3) the receipt id recomputes ([`attestation_commitment`]). A
/// fabricated ruling without a valid attestation, or a tampered session / re-aimed field span,
/// fails one of these — the forged-ruling-distinguishable tooth.
pub fn verify_turn(
    entry: &LedgerEntry,
    config: &AnthropicConfig,
) -> Result<VerifiedZkOracle, RulingForgery> {
    let out = verify_zkoracle(&entry.attestation, config).map_err(RulingForgery::Attestation)?;
    let field = clean_field(&entry.ruling_text);
    if !contains(&out.session.response_body, field.as_bytes()) {
        return Err(RulingForgery::RulingNotAttested);
    }
    if attestation_commitment(&entry.attestation) != entry.receipt {
        return Err(RulingForgery::ReceiptMismatch);
    }
    Ok(out)
}

/// Why a landed ruling failed re-verification — a forged / tampered ruling is distinguishable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RulingForgery {
    /// The attestation itself does not verify (forged / tampered session, malformed body, or a
    /// smuggled `{{` field caught at verify).
    Attestation(ZkOracleError),
    /// The displayed ruling is not the attested text — a ruling swapped onto a real attestation
    /// (the verdict a reader would see differs from what was certified).
    RulingNotAttested,
    /// The receipt id does not recompute from the attestation — a fabricated receipt.
    ReceiptMismatch,
}

impl std::fmt::Display for RulingForgery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RulingForgery::Attestation(e) => write!(f, "attestation does not verify: {e:?}"),
            RulingForgery::RulingNotAttested => {
                write!(f, "displayed ruling is not the attested text")
            }
            RulingForgery::ReceiptMismatch => write!(f, "receipt id does not recompute"),
        }
    }
}

impl std::error::Error for RulingForgery {}

/// A ledger re-verification failure, naming the offending ruling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LedgerError {
    /// The sequence number of the ruling that failed.
    pub seq: u64,
    /// Why it failed.
    pub reason: RulingForgery,
}

impl std::fmt::Display for LedgerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ledger ruling #{} is not authentic: {}",
            self.seq, self.reason
        )
    }
}

impl std::error::Error for LedgerError {}

// ─────────────────────────────────────────────────────────────────────────────
// The Arbiter — attested + cap-bounded neutral authority.
// ─────────────────────────────────────────────────────────────────────────────

/// **The Commons Arbiter.** Reads a case against a rubric, rules via its [`RulingBrain`], and
/// fires a **receipted attested turn** onto the case ledger — each ruling carrying a
/// [`ZkOracleAttestation`] (authentic ∧ well-formed ∧ injection-free). Its authority is
/// cap-bounded by [`ArbiterCaps`] (jurisdiction). A case that carries a prompt-injection is
/// refused by the injection-free leg (un-censorable); an out-of-jurisdiction case is refused
/// fail-closed.
pub struct Arbiter<B: RulingBrain = RecordedArbiter> {
    carrier: ArbiterAttestationCarrier,
    caps: ArbiterCaps,
    brain: B,
    /// Where a landed ruling routes. [`NodeTarget::Local`] (default) keeps it on the
    /// in-process [`CaseLedger`]; [`NodeTarget::Federation`] additionally submits the
    /// ruling's receipt commitment to a real `DREGG_NODE_URL` node + confirms it landed.
    node_target: NodeTarget,
}

impl<B: RulingBrain> Arbiter<B> {
    /// An Arbiter with the given attestation carrier, jurisdiction, and brain.
    pub fn new(carrier: ArbiterAttestationCarrier, caps: ArbiterCaps, brain: B) -> Arbiter<B> {
        Arbiter {
            carrier,
            caps,
            brain,
            node_target: NodeTarget::Local,
        }
    }

    /// **Make this Arbiter federation-capable.** By default it runs `Local` (rulings land
    /// only on the in-process [`CaseLedger`]). Pass a [`NodeTarget::Federation`] (e.g. from
    /// [`NodeTarget::from_env`], reading `DREGG_NODE_URL`) to additionally submit each
    /// landed ruling's receipt commitment to a real independent-operator federation node
    /// and confirm it landed — one flip from the live federation deploy.
    pub fn with_node_target(mut self, target: NodeTarget) -> Arbiter<B> {
        self.node_target = target;
        self
    }

    /// The pinned config a verifier checks this Arbiter's rulings against.
    pub fn config(&self) -> &AnthropicConfig {
        self.carrier.config()
    }

    /// The Arbiter's jurisdiction.
    pub fn caps(&self) -> &ArbiterCaps {
        &self.caps
    }

    /// **RULE ON A CASE.** Cap-check the case's rubric (fail-closed); rule via the brain; attest
    /// the ruling (injection-free tooth); append the receipted attested turn to `ledger`.
    ///
    /// REFUSED — ledger unchanged (anti-ghost) — when:
    /// * the case's rubric is outside the Arbiter's jurisdiction ([`ArbiterError::
    ///   OutOfJurisdiction`]) — the cap tooth, fail-closed before any attestation;
    /// * the ruling text carries a `{{` injection reflected from the case content
    ///   ([`ArbiterError::Injection`]) — the **un-censorable tooth**.
    ///
    /// On success returns the landed ruling's [`Receipt`].
    pub fn rule_case(
        &self,
        ledger: &mut CaseLedger,
        rubric: &Rubric,
        case: &Case,
    ) -> Result<Receipt, ArbiterError> {
        // (1) CAP-BOUND the case's rubric FIRST, fail-closed — an out-of-jurisdiction case
        //     never produces a ruling and never touches the ledger.
        self.caps
            .authorize(&case.rubric_id)
            .map_err(ArbiterError::OutOfJurisdiction)?;
        // (2) RULE via the brain (against the rubric the case named).
        let ruling = self.brain.rule(rubric, case);
        let ruling_text = ruling.render(&rubric.id, case);
        // (3) ATTEST the ruling: authentic ∧ well-formed ∧ injection-free. A `{{` reflected from
        //     the case content is REFUSED here (the un-censorable tooth) — no attestation.
        let (attestation, field) = self
            .carrier
            .attest_ruling(&ruling_text)
            .map_err(ArbiterError::from_prove)?;
        // (4) LAND the turn: append the receipted attested ruling.
        let seq = ledger.ledger.len() as u64;
        let receipt = attestation_commitment(&attestation);
        // FEDERATION SEAM: in `Local` mode a no-op; in `Federation` mode the ruling's
        // receipt commitment is submitted to the real node + confirmed landed FIRST — a
        // rejected / unreachable / non-landing submit refuses the ruling fail-closed, so
        // the ledger never records a ruling that did not replicate to the federation.
        self.node_target
            .route(&SubmittedTurn::new(rubric.id.clone(), receipt))
            .map_err(|e| ArbiterError::Federation(e.to_string()))?;
        ledger.ledger.push(LedgerEntry {
            seq,
            rubric_id: rubric.id.clone(),
            verdict: ruling.verdict,
            ruling_text: String::from_utf8_lossy(&field).into_owned(),
            attestation,
            receipt,
        });
        Ok(Receipt {
            seq,
            id: receipt,
            verdict: ruling.verdict,
        })
    }
}

impl Arbiter<RecordedArbiter> {
    /// A default modeled Arbiter: the deterministic [`RecordedArbiter`] brain, the default
    /// attestation carrier, and the given jurisdiction.
    pub fn recorded(caps: ArbiterCaps) -> Arbiter<RecordedArbiter> {
        Arbiter::new(ArbiterAttestationCarrier::default(), caps, RecordedArbiter)
    }
}

/// The receipt of a landed ruling turn — its ledger sequence, its 32-byte id, and the verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receipt {
    /// The ruling's sequence number in the ledger.
    pub seq: u64,
    /// The 32-byte receipt id ([`attestation_commitment`]) — the ruling's commitment, put to
    /// the quorum for finality.
    pub id: [u8; 32],
    /// The verdict this ruling reached.
    pub verdict: Verdict,
}

/// Why a ruling was refused — the ledger advanced not at all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArbiterError {
    /// **The un-censorable tooth.** The ruling text carries a `{{` handlebars injection
    /// (reflected from the case content); the injection-free leg refuses to attest it, so the
    /// ruling over that input is refused. Nobody can inject a verdict into the Arbiter.
    Injection,
    /// The case's rubric is outside the Arbiter's jurisdiction; refused fail-closed.
    OutOfJurisdiction(OutOfJurisdiction),
    /// The ruling could not be shaped into a well-formed attestable body (a modeling fault —
    /// should not arise from an ordinary ruling).
    NotAttestable(String),
    /// The ruling attested cleanly but a configured [`NodeTarget::Federation`] node refused
    /// it or could not confirm it landed (a rejected / unreachable / non-landing submit).
    /// Refused fail-closed: the ledger records no ruling that did not replicate.
    Federation(String),
}

impl ArbiterError {
    fn from_prove(e: ProveError) -> ArbiterError {
        match e {
            ProveError::Injection => ArbiterError::Injection,
            other => ArbiterError::NotAttestable(format!("{other:?}")),
        }
    }
}

impl std::fmt::Display for ArbiterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArbiterError::Injection => write!(
                f,
                "REFUSED (un-censorable): the case carries a `{{{{` prompt-injection"
            ),
            ArbiterError::OutOfJurisdiction(o) => write!(f, "REFUSED (out of jurisdiction): {o}"),
            ArbiterError::NotAttestable(m) => write!(f, "ruling not attestable: {m}"),
            ArbiterError::Federation(m) => write!(f, "REFUSED (federation routing failed): {m}"),
        }
    }
}

impl std::error::Error for ArbiterError {}

/// A byte-substring search (the displayed ruling inside the authenticated body).
fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || needle.len() > haystack.len() {
        return needle.is_empty();
    }
    haystack.windows(needle.len()).any(|w| w == needle)
}

#[cfg(test)]
mod tests;
