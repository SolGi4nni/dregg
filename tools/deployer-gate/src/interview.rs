//! # The interview harness — the marquee attestation arm
//!
//! *"Convince a skeptical Opus your project is real, prove you did it in
//! zero-knowledge, then you may deploy."*
//!
//! The compelling deployer-gate is not a whitelist and not a token-gate — it is
//! a **structured interview with a hard-to-convince Claude Opus 4.8**, briefed
//! to probe a project for scam-signals, rug-intent, and vaporware and to refuse
//! to be moved by hype. Passing it issues the deploy capability. It is strictly
//! better than a whitelist because a scammer cannot fake their way past a
//! skeptic asking real questions, and it does not doxx: it interrogates the
//! *project*, not the person.
//!
//! ## The real runs (not a mock)
//!
//! `interview/interviewer-prompt.md` is the briefing (skeptical stance +
//! scam-signal checklist + a strict machine-readable verdict format). It was run
//! by Claude Opus 4.8 against two project specs:
//!
//! - `interview/spec-legit.md` ("Meridian Grid": live pilots, disclosed capped
//!   supply, published audit hash, a 50 ETH slashable bond) →
//!   **`interview/runs/verdict-legit.txt`: VERDICT PASS (confidence 0.85)**.
//! - `interview/spec-rug.md` ("QuantumYield AI": retained mint function, 40%
//!   insider unlock, guaranteed-2%-daily Ponzi yield, anonymous + no product) →
//!   **`interview/runs/verdict-rug.txt`: VERDICT FAIL (confidence 0.99)**.
//!
//! The skeptic passed the real project and failed the rug. [`InterviewVerdict::parse`]
//! parses exactly that verdict block; the tests feed it the captured runs.
//!
//! ## Honest scope: the transcripts are FROZEN — the interview arm is not live
//!
//! The two runs above were produced by a real Opus 4.8 **once, offline** and
//! captured verbatim. This crate contains **no LLM client and no HTTP** — the
//! automated path is [`InterviewVerdict::parse`] replaying those two frozen
//! transcripts forever. A *live* interview (a real model call per applicant,
//! behind grain-jail or a hosted provider) is the named wire-later; until it is
//! wired, "the deployer sits an interview" describes the DESIGN, and what runs
//! is the parser + the captured evidence. The zkTLS attestation of a live
//! session is likewise design + type-shape ([`crate::private::zktls`]).

use crate::private::{self, VerdictCommitment};

/// The structured outcome of a deployer interview.
#[derive(Clone, Debug, PartialEq)]
pub struct InterviewVerdict {
    pub pass: bool,
    pub confidence: f64,
    pub reasons: Vec<String>,
    pub scam_signals: Vec<String>,
}

impl InterviewVerdict {
    /// Parse the machine-readable verdict block the briefed interviewer emits
    /// (see `interviewer-prompt.md`). Tolerant of the `# comment` header lines
    /// the captured runs carry.
    pub fn parse(block: &str) -> Option<InterviewVerdict> {
        let mut pass: Option<bool> = None;
        let mut confidence = 0.0f64;
        let mut reasons = Vec::new();
        let mut signals = Vec::new();
        let mut in_reasons = false;

        for raw in block.lines() {
            let line = raw.trim();
            if line.starts_with('#') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("VERDICT:") {
                // First VERDICT line wins (a run may repeat it); do not overwrite.
                if pass.is_none() {
                    let v = rest.trim().to_ascii_uppercase();
                    pass = Some(v.starts_with("PASS"));
                }
                in_reasons = false;
            } else if let Some(rest) = line.strip_prefix("CONFIDENCE:") {
                confidence = rest.trim().parse().unwrap_or(0.0);
                in_reasons = false;
            } else if line.starts_with("REASONS:") {
                in_reasons = true;
            } else if let Some(rest) = line.strip_prefix("SCAM_SIGNALS_FOUND:") {
                in_reasons = false;
                let s = rest.trim();
                if !s.is_empty() && !s.eq_ignore_ascii_case("NONE") {
                    signals = s.split(',').map(|x| x.trim().to_string()).collect();
                }
            } else if in_reasons {
                if let Some(r) = line.strip_prefix("- ") {
                    reasons.push(r.to_string());
                }
            }
        }

        pass.map(|pass| InterviewVerdict {
            pass,
            confidence,
            reasons,
            scam_signals: signals,
        })
    }

    /// Turn a verdict into the hiding [`VerdictCommitment`] the operator admits
    /// to the trusted set (only if `pass`). Returns `None` for a FAIL — a failed
    /// interview yields no admissible commitment, so no capability can issue.
    pub fn to_commitment(
        &self,
        session_nonce: &[u8; 32],
        endpoint_binding: &[u8],
    ) -> Option<VerdictCommitment> {
        if !self.pass {
            return None;
        }
        Some(private::verdict_commitment(
            true,
            session_nonce,
            endpoint_binding,
        ))
    }
}
