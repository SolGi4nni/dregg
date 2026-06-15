//! Captured-turn-forest analysis — conservation & non-amplification, attested
//! against the REAL `dregg_userspace_verify` static-assurance checks.
//!
//! ## Input format ([`ForestCapture`])
//!
//! A captured `dregg_turn::CallForest` (the turn artifact a node executed or a
//! receipt-graph references) plus a flag for whether to treat it as a settlement
//! ring. This is the forest-shaped half of the "surface conservation across a
//! turn history" goal: where [`crate::receipts`] surfaces the per-turn `was_burn`
//! disclosure, this re-runs the actual conservation/non-amplification verifier
//! over a captured forest so the analyzer ATTESTS the turn conserved (rather than
//! trusting the receipt's self-disclosure).
//!
//! ## What is ATTESTED (real verifier reused)
//!
//!   * conservation (guarantee B), non-amplification (guarantee A),
//!     well-formedness, and ring balance — ALL via the real
//!     [`dregg_userspace_verify::analyze`]. We do not re-implement the
//!     conservation sum; we run the same `check_conservation` the SDK pre-flight
//!     and the executor's law agree on.

use serde::{Deserialize, Serialize};

use dregg_turn::CallForest;
use dregg_userspace_verify::{Verdict, analyze as uverify};

use crate::findings::{AnalysisReport, Finding, Severity};

/// A captured turn forest to attest.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ForestCapture {
    /// The captured turn forest (the executed/referenced artifact).
    pub forest: CallForest,
    /// Treat as a settlement ring (run ring-balance over its transfer legs).
    #[serde(default)]
    pub treat_as_ring: bool,
}

/// Analyze a captured forest, attesting conservation/non-amplification against
/// the real `dregg_userspace_verify` checks.
pub fn analyze(capture: &ForestCapture) -> AnalysisReport {
    let mut report = AnalysisReport::new("forest");
    let assurance = uverify(&capture.forest, capture.treat_as_ring);

    report.summarize("roots", capture.forest.roots.len());
    report.summarize("treated_as_ring", capture.treat_as_ring);
    report.summarize("assurance_pass", assurance.pass());

    for (name, by, verdict) in [
        (
            "conservation (B)",
            "dregg_userspace_verify::check_conservation",
            &assurance.conservation,
        ),
        (
            "non-amplification (A)",
            "dregg_userspace_verify::check_no_amplification",
            &assurance.no_amplification,
        ),
        (
            "well-formedness",
            "dregg_userspace_verify::check_wellformed",
            &assurance.wellformed,
        ),
        (
            "ring-balance",
            "dregg_userspace_verify::check_ring_balance",
            &assurance.ring_balance,
        ),
    ] {
        match verdict {
            Verdict::Pass => report.push(Finding::verified(
                Severity::Info,
                by,
                "forest.check_pass",
                format!("{name} VERIFIED: the captured forest passes the real check"),
            )),
            Verdict::Fail(findings) => {
                for f in findings {
                    report.push(Finding::verified(
                        Severity::Critical,
                        by,
                        "forest.check_fail",
                        format!("{name} VIOLATED at {}: {}", f.locus, f.message),
                    ));
                }
            }
        }
    }

    if assurance.pass() {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_userspace_verify::analyze",
            "forest.assured",
            "the captured forest passes EVERY static-assurance check (conservation, \
             non-amplification, well-formedness, ring) — attested by the same \
             verifier the SDK pre-flight and executor law use",
        ));
    }

    report
}
