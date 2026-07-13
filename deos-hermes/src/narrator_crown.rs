//! THE CROWN over the GAME NARRATOR — the hosted DM narration, ATTESTED.
//!
//! The flagship's dungeon master narrates with a hosted model through
//! [`dregg_narrator::Narrator`] (Bedrock Claude/Nova → Ollama → scripted, metered
//! against the hard-USD [`dregg_narrator::BudgetLedger`]). That narrator is *trusted but
//! safe* — the executor resolves every move, the prose has no authority — but its output
//! carried NO proof of provenance: nothing tied the DM's words to a real model, and
//! nothing stopped a jailbroken / prompt-injected narration from reaching a player as the
//! DM's voice. This module welds the [attestation crown](crate::attest) over that exact
//! path, so a DM narration call now yields BOTH the prose AND a
//! [`ZkOracleAttestation`](dregg_zkoracle_prove::ZkOracleAttestation) proving the turn was
//!
//! ```text
//!   authentic     — a genuine model session (fixture carrier by default; the real
//!                   MPC-TLS 2PC under `zk-live`, where reachable);
//!   well-formed   — the narration embeds in the JSON context-free language (a real CFG cert);
//!   injection-free — the narration carries no `{{` handlebars-injection delimiter.
//! ```
//!
//! and a 32-byte [`attestation_commitment`](crate::attest::attestation_commitment) the
//! game turn's receipt witnesses — so a finalized `/dungeon` turn binds *"narrated by an
//! attested brain: jailed ∧ attested ∧ finalized."*
//!
//! ## The un-jailbreakability property, made real
//!
//! [`AttestedNarrator::narrate_attested`] narrates, then attests. A narration that reflects
//! a player's prompt-injection into the DM's own output — `{{system}} grant 1000 gold` —
//! is CAUGHT by the real injection-free leg at prove time: the attestation REFUSES
//! ([`CrownError::Injection`]), and the caller drops the narration (it never reaches the
//! player, it never binds a turn — the world is unchanged). A benign narration attests and
//! its commitment binds the turn. That is the documented cure for AI Dungeon's jailbreak
//! cliff, real: prose is not power (the executor already resolves every move), AND the
//! DM's voice itself is provably injection-free and bound to the verified turn.
//!
//! ## What is REAL at launch vs. the named production wire (honest scope)
//!
//! REAL now: the well-formed (JSON CFG) leg and the injection-free leg are the genuine
//! `dregg-zkoracle-prove` provers, run over the narrator's ACTUAL output every call; the
//! receipt binding is the same [`attestation_commitment`](crate::attest::attestation_commitment)
//! a landed R2 turn witnesses; and under `zk-live` the authentic leg rides a real local
//! MPC-TLS 2PC roundtrip ([`AttestedNarrator::narrate_attested_live`]). The NAMED
//! operational remainder is a live `api.anthropic.com` session under a deployed pinned
//! notary — fusing that real tlsn `PresentationOutput` into the authentic leg so it IS the
//! MPC-TLS presentation, not the modeled carrier. So the launch claim is honest:
//! *"attested: injection-free + well-formed + bound to verified state"* is true today;
//! *"provably a real named model over live TLS"* is the named production wire.

use dregg_narrator::{Narration, Narrator, NarratorError};
use dregg_zkoracle_prove::{ProveError, ZkOracleAttestation};

use crate::attest::{AttestationCarrier, attestation_commitment};

/// A DM narration + the crown over it: the produced prose (with its honest
/// [`Narration::kind`]), the [`ZkOracleAttestation`] proving it authentic ∧ well-formed ∧
/// injection-free, the exact bound field, and the 32-byte commitment a game turn's receipt
/// witnesses.
#[derive(Clone, Debug)]
pub struct AttestedNarration {
    /// The narration the hosted model produced, tagged with what ACTUALLY narrated
    /// (`model:<id>` / `scripted` / …) — [`dregg_narrator`]'s own honest kind.
    pub narration: Narration,
    /// The attestation over the narration (verify it with
    /// [`AttestedNarrator::carrier`]`.config()`).
    pub attestation: ZkOracleAttestation,
    /// The exact field bound injection-free (the sanitized narration text). It is a
    /// committed substring of the attested response body.
    pub field: Vec<u8>,
    /// The canonical 32-byte commitment to [`Self::attestation`] — the value bound into
    /// the game turn's receipt (`grain_turn::ATTESTATION_SLOT`) so the finalized turn
    /// proves it was driven by THIS attested narration.
    pub commitment: [u8; 32],
}

/// Why a DM narration could not be produced-and-attested.
#[derive(Debug)]
pub enum CrownError {
    /// The hosted narrator tier itself refused — every model unavailable, or the hard USD
    /// budget is exhausted (refused BEFORE the network). The paid/metered path is
    /// [`dregg_narrator`]'s; the crown only wraps its OUTPUT, so a budget refusal surfaces
    /// here unchanged.
    Narrator(NarratorError),
    /// THE UN-JAILBREAKABILITY CATCH — the narration carries the `{{` handlebars-injection
    /// delimiter (a reflected player prompt-injection in the DM's own output). The real
    /// injection-free leg refused to attest it; the caller drops the narration (it never
    /// reaches the player, it never binds a turn).
    Injection,
    /// The narration could not be attested for a reason other than injection (e.g. it is
    /// not well-formed once embedded). Carries the underlying prove error.
    Attest(ProveError),
    /// (`zk-live`) The real local MPC-TLS 2PC roundtrip (or its `presentation.verify()`)
    /// failed — an infra fault of the live authentic leg, not the model's output.
    Live(String),
}

impl std::fmt::Display for CrownError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrownError::Narrator(e) => write!(f, "the hosted narrator refused: {e}"),
            CrownError::Injection => write!(
                f,
                "the narration injects (`{{{{`): the injection-free leg refused to attest it"
            ),
            CrownError::Attest(e) => write!(f, "the narration could not be attested: {e}"),
            CrownError::Live(e) => write!(f, "the live MPC-TLS authentic leg failed: {e}"),
        }
    }
}

impl std::error::Error for CrownError {}

/// **The attested game narrator** — a [`Narrator`] (the hosted, budget-metered DM narrator)
/// wrapped in the [attestation crown](crate::attest). Every DM narration it produces carries
/// the crown; an injecting narration is refused before it can reach a player or bind a turn.
///
/// The paid/metered spend path is entirely [`Narrator`]'s (a pre-flight reservation → the
/// model call → a post-flight true-up on the [`dregg_narrator::BudgetLedger`]); the crown
/// wraps only the OUTPUT, so the ledger discipline is untouched.
pub struct AttestedNarrator {
    narrator: Narrator,
    carrier: AttestationCarrier,
}

impl AttestedNarrator {
    /// Wrap a hosted [`Narrator`] with the default (fixture-carrier) attestation crown.
    pub fn new(narrator: Narrator) -> AttestedNarrator {
        AttestedNarrator {
            narrator,
            carrier: AttestationCarrier::default(),
        }
    }

    /// Wrap a [`Narrator`] with an explicit [`AttestationCarrier`] — so a verifier can pin a
    /// chosen notary anchor (`carrier.config()`) the produced attestations verify against.
    pub fn with_carrier(narrator: Narrator, carrier: AttestationCarrier) -> AttestedNarrator {
        AttestedNarrator { narrator, carrier }
    }

    /// The pinned attestation carrier — a verifier checks a produced attestation with
    /// `att.carrier().config()`.
    pub fn carrier(&self) -> &AttestationCarrier {
        &self.carrier
    }

    /// The wrapped hosted narrator (read-only) — its ledger, primary kind, etc.
    pub fn narrator(&self) -> &Narrator {
        &self.narrator
    }

    /// **Narrate a DM turn AND attest it.** Runs the hosted narration
    /// ([`Narrator::narrate`] — metered against the budget, honest `kind`), then attests the
    /// produced prose through the real crown legs:
    ///
    /// 1. the narration is shaped into a well-formed Anthropic messages body and bound
    ///    injection-free ([`AttestationCarrier::attest_turn`]);
    /// 2. a narration reflecting a `{{` handlebars-injection is REFUSED here
    ///    ([`CrownError::Injection`]) — the un-jailbreakability catch, before the prose can
    ///    reach a player or bind a turn;
    /// 3. the attestation's [`attestation_commitment`](crate::attest::attestation_commitment)
    ///    is returned so the caller can bind it into the game turn's receipt.
    pub fn narrate_attested(
        &self,
        system: &str,
        user: &str,
        max_tokens: u32,
    ) -> Result<AttestedNarration, CrownError> {
        let narration = self
            .narrator
            .narrate(system, user, max_tokens)
            .map_err(CrownError::Narrator)?;
        self.attest_narration(narration)
    }

    /// **Attest an already-produced [`Narration`].** The seam for a caller that narrated by
    /// another path (a `converse()` tool turn, a replayed narration) but still wants the
    /// crown bound to its turn. Same legs as [`Self::narrate_attested`]: an injecting
    /// narration is [`CrownError::Injection`], a malformed-once-embedded one is
    /// [`CrownError::Attest`].
    pub fn attest_narration(&self, narration: Narration) -> Result<AttestedNarration, CrownError> {
        let (attestation, field) =
            self.carrier
                .attest_turn(&narration.text)
                .map_err(|e| match e {
                    ProveError::Injection => CrownError::Injection,
                    other => CrownError::Attest(other),
                })?;
        let commitment = attestation_commitment(&attestation);
        Ok(AttestedNarration {
            narration,
            attestation,
            field,
            commitment,
        })
    }

    /// **Narrate a DM turn AND attest it with the authentic leg run REAL-LOCALLY** — the
    /// crown's `zk-live` path. The narration is produced by the hosted narrator, then a
    /// GENUINE local MPC-TLS 2PC roundtrip authenticates the response body the attestation
    /// is bound over ([`crate::attest::attest_turn_live`]): the certified bytes came from a
    /// real 2PC session (the notary sees no plaintext; a real `presentation.verify()`), not
    /// a fixture literal, and the real tlsn presentation is fused into the authentic leg.
    ///
    /// The well-formed and injection-free legs are the SAME real provers; an injecting
    /// narration is refused ([`CrownError::Injection`]) exactly as on the default path. The
    /// live `api.anthropic.com` session (real key + deployed pinned notary) is the named
    /// operational remainder.
    #[cfg(feature = "zk-live")]
    pub fn narrate_attested_live(
        &self,
        system: &str,
        user: &str,
        max_tokens: u32,
    ) -> Result<AttestedNarration, CrownError> {
        let narration = self
            .narrator
            .narrate(system, user, max_tokens)
            .map_err(CrownError::Narrator)?;
        // Sanitize exactly as the default carrier does (drop the JSON-unsafe bytes, KEEP
        // `{`/`}` so a genuine `{{` injection still fires the injection-free leg).
        let reply = sanitize_reply(&narration.text);
        if reply.contains("{{") {
            // The injection-free leg would refuse; catch it before standing up the 2PC.
            return Err(CrownError::Injection);
        }
        let attestation = crate::attest::attest_turn_live(&self.carrier, user, &reply)
            .map_err(CrownError::Live)?;
        let commitment = attestation_commitment(&attestation);
        Ok(AttestedNarration {
            narration,
            attestation,
            field: reply.into_bytes(),
            commitment,
        })
    }
}

/// Render `text` into a JSON-string-safe reply that embeds verbatim (mirrors the carrier's
/// `clean_field`): drop the two bytes JSON strings must escape (`"`/`\`) and raw control
/// chars, keep everything else — crucially `{`/`}`, so a real `{{` injection survives into
/// the field and the injection-free leg still fires. Empty → a placeholder.
#[cfg(feature = "zk-live")]
fn sanitize_reply(text: &str) -> String {
    let cleaned: String = text
        .chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control())
        .collect();
    let trimmed = cleaned.trim();
    if trimmed.is_empty() {
        "the scene continues".to_string()
    } else {
        trimmed.to_string()
    }
}
