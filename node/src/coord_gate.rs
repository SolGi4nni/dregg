//! Verified 2PC COORDINATOR-DECISION GATE — make the Lean-exported `evaluate_votes` the
//! AUTHORITATIVE Commit/Abort/Pending verdict, with the Rust `Coordinator::evaluate_votes` demoted
//! to the DIFFERENTIAL sibling.
//!
//! # What this is
//!
//! `api.rs::atomic_vote` feeds each vote to `dregg_coord::Coordinator::receive_vote`, which internally
//! calls `evaluate_votes` (`coord/src/atomic.rs`) and returns a `Decision`. That decision gates the
//! whole atomic turn: `Commit` runs the forest against the ledger, `Abort` tears the proposal down,
//! `Pending` waits. It is exactly the 2PC SAFETY content — and `Dregg2.Coord.TwoPhaseCommit` proves
//! the verified `evaluate` never yields a conflicting Commit+Abort (`evaluate_not_commit_and_abort`),
//! that Commit implies the threshold was met, and that Abort is sound/irreversible.
//!
//! This module makes the node CALL the verified rule at the live decision point. The coordinator
//! exposes its tally as a wire (`Coordinator::decision_wire`); we feed that to the VERIFIED Lean
//! `dregg_coord_2pc_decide` export (`Dregg2.Exec.DistributedExports`), whose
//! `coord_2pc_decide_eq` theorem proves the verdict IS `TwoPhaseCommit.evaluate`. So the
//! commit/abort/pending the node acts on is decided BY THE VERIFIED RULE.
//!
//! The Rust `Coordinator`'s own `Decision` (already computed by `receive_vote`) is kept as the
//! DIFFERENTIAL sibling: on every gated decision we compare the two and log LOUDLY on divergence (a
//! Lean-vs-Rust drift is a real bug in one of them). The template is the consensus tau-order swap
//! (`node::finality_gate` makes `dregg_tau_order` authoritative, Rust `tau` differential).
//!
//! # Flag + fail-safety
//!
//! Gated by [`coord_decision_gate_enabled`] (`DREGG_COORD_DECISION_GATE`, **default ON**). When the
//! Lean archive lacks the export (stale/marshal-only build), or the wire fails to round-trip, the gate
//! FALLS BACK to the Rust `Decision` so the coordinator is never broken — only un-verified — with a
//! once-warning. The verified gate is fail-SAFE: a malformed tally decodes to `Pending` (never a
//! terminal Commit/Abort on garbage), matching `twoPCGate`'s fail-safe sentinel.

use std::sync::Once;

use dregg_coord::Decision;

/// One-shot guard so the verified/fallback diagnostic is logged at most once per process.
static GATE_BACKEND_ANNOUNCED: Once = Once::new();

/// Whether the live 2PC-decision gate is enabled. **Default ON**. `DREGG_COORD_DECISION_GATE=0`/
/// `false`/`off` opts OUT (keeps the raw Rust `Decision`).
pub fn coord_decision_gate_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_COORD_DECISION_GATE").ok().as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    )
}

/// Whether the verified Lean distributed exports are linked (so the gate decides via the VERIFIED
/// `dregg_coord_2pc_decide` rather than the Rust fallback).
pub fn lean_backed() -> bool {
    dregg_lean_ffi::distributed_exports_available()
}

/// Map the verified Lean verdict to a `dregg_coord::Decision`.
fn decision_of(verdict: dregg_lean_ffi::Decision2pc) -> Decision {
    match verdict {
        dregg_lean_ffi::Decision2pc::Commit => Decision::Commit,
        dregg_lean_ffi::Decision2pc::Abort => Decision::Abort,
        dregg_lean_ffi::Decision2pc::Pending => Decision::Pending,
    }
}

/// The AUTHORITATIVE 2PC decision for the current coordinator tally.
///
/// `rust_decision` is the verdict the Rust `Coordinator::receive_vote` just produced (the DIFFERENTIAL
/// sibling); `wire` is the coordinator's `decision_wire()` (the tally encoded for the Lean gate), or
/// `None` when not Proposing (terminal/idle — then the Rust decision stands).
///
/// When the gate is enabled AND the Lean export is linked, this runs the VERIFIED
/// `dregg_coord_2pc_decide` over `wire`, COMPARES it to `rust_decision` (logging on drift), and
/// returns the VERIFIED verdict — the node acts on the proved rule. Otherwise it returns
/// `rust_decision` unchanged (fall back to the Rust coordinator, with a once-warning when un-verified).
pub fn authoritative_decision(rust_decision: Decision, wire: Option<&str>) -> Decision {
    if !coord_decision_gate_enabled() {
        return rust_decision;
    }
    let Some(wire) = wire else {
        // Terminal/idle coordinator: the Rust decision (Pending by construction off the Proposing
        // path) stands; there is no tally to verify.
        return rust_decision;
    };

    GATE_BACKEND_ANNOUNCED.call_once(|| {
        if lean_backed() {
            tracing::info!(
                "2PC coordinator decision is LEAN-BACKED: commit/abort/pending is decided by the \
                 VERIFIED dregg_coord_2pc_decide (TwoPhaseCommit.evaluate); the Rust \
                 Coordinator::evaluate_votes is the differential sibling."
            );
        } else {
            tracing::warn!(
                "2PC coordinator decision is running on the Rust FALLBACK (Lean distributed \
                 exports not linked). Rebuild the closure-complete archive \
                 (scripts/seed-dregg2-closure.sh) to gate the decision on the VERIFIED rule."
            );
        }
    });

    match dregg_lean_ffi::verified_2pc_decide(wire) {
        Ok(verdict) => {
            let lean_decision = decision_of(verdict);
            if lean_decision != rust_decision {
                // A Lean-vs-Rust drift on the SAME tally is a real bug in one of the two engines.
                // We trust the VERIFIED Lean rule (it carries the proved no-conflicting-decision
                // safety) and log the divergence LOUDLY for investigation.
                tracing::error!(
                    wire = %wire,
                    rust = ?rust_decision,
                    lean = ?lean_decision,
                    "2PC DECISION DIVERGENCE: Rust Coordinator and verified Lean gate disagree on \
                     the same tally — acting on the VERIFIED verdict. Investigate the Rust path."
                );
            }
            lean_decision
        }
        Err(e) => {
            // The export is unavailable / wire error: fall back to the Rust decision (never break
            // the coordinator). Logged at debug to avoid spamming a fallback build.
            tracing::debug!(error = %e, "2PC gate fell back to the Rust decision");
            rust_decision
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// On a fallback build (or with the gate off), the authoritative decision is just the Rust one.
    #[test]
    fn falls_back_to_rust_when_no_wire() {
        assert_eq!(
            authoritative_decision(Decision::Commit, None),
            Decision::Commit
        );
        assert_eq!(
            authoritative_decision(Decision::Abort, None),
            Decision::Abort
        );
        assert_eq!(
            authoritative_decision(Decision::Pending, None),
            Decision::Pending
        );
    }

    /// THE LIVE 2PC GATE DIFFERENTIAL — when the Lean export is linked, the authoritative verdict for
    /// a unanimous-yes tally is Commit, for a too-many-no tally is Abort, and they AGREE with the Rust
    /// coordinator on the well-formed scenarios. Self-skips when the archive lacks the export.
    #[test]
    fn lean_gate_decides_unanimous_scenarios() {
        if !lean_backed() {
            eprintln!("SKIP: Lean distributed exports not linked (lean_backed()==false)");
            return;
        }
        // 3-of-3 all yes ⇒ Commit (the Rust coordinator would also reach Commit here).
        assert_eq!(
            authoritative_decision(Decision::Commit, Some("y=3;n=0;N=3;t=3")),
            Decision::Commit
        );
        // 3-of-3, 2 yes 1 no ⇒ Abort (threshold unreachable).
        assert_eq!(
            authoritative_decision(Decision::Abort, Some("y=2;n=1;N=3;t=3")),
            Decision::Abort
        );
        // 3-of-3, 2 yes 0 no ⇒ Pending.
        assert_eq!(
            authoritative_decision(Decision::Pending, Some("y=2;n=0;N=3;t=3")),
            Decision::Pending
        );
    }
}
