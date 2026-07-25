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
//! # ⚑ FAIL-CLOSED — the THIRD confirmed member of the fail-OPEN class
//!
//! This site used to end its gate-absent arm with a bare `rust_decision`, logged at `debug!`. It was
//! fail-closed only **TRANSITIVELY**: `rust_decision` comes from `receive_vote -> evaluate_votes ->
//! evaluate_votes_no_gate`, and *that callee* returns `Decision::Abort` for a `Proposing`
//! coordinator. The safety therefore lived in a callee, UNDECLARED here — one refactor of
//! `evaluate_votes_no_gate` silently reopened it — and it was NOT EVEN UNIFORM: under `dregg-coord`'s
//! own `cfg(test)` that callee was the native sibling, which CAN RETURN `Commit`. Both halves are now
//! closed: the disposition is stated AT THIS SITE by the named, sliceable
//! [`coord_decision_disposition`] (registered in `scripts/ci-invariants/gate-dataflow.tsv` as
//! twin#3b), and `evaluate_votes_no_gate` has ONE body for every cfg (its test-only native path is
//! now a DECLARED thread-local fault injector the differential arms explicitly).
//!
//! POLICY: when the verified gate CANNOT ANSWER and no bypass is declared, this site returns
//! [`Decision::Abort`] — REFUSE TO COMMIT. It does not inherit a callee's verdict. `Abort` (not
//! `Pending`) is chosen to match twin#3's own declared disposition in `coord/src/atomic.rs`, which
//! `coord/tests/twin_fail_closed.rs` pins; a `Pending` would also be non-admitting but would leave
//! the shape of the refusal to the proposal timeout. The liveness cost is real and bounded: a
//! transient FFI miss on a tally that could otherwise DECIDE tears that proposal down and the
//! proposer must re-propose. The vacuity short-circuit below is what keeps that from happening on
//! every early vote.
//!
//! TWO DECLARED BYPASSES ([`coord_gate_bypass_allowed`], the shape twin#8's
//! `rust_tau_fallback_allowed` / twin#8b's `belt_gate_bypass_allowed` already use), and nothing else:
//! there is no `dregg_coord_2pc_decide` export linked AT ALL (an archive-less build — every test
//! binary, the wasm/zkVM guest, a marshal-only dev box), or the operator explicitly disabled this
//! gate (`DREGG_COORD_DECISION_GATE=0`). `DREGG_REQUIRE_LEAN=1` REVOKES BOTH. Both are named in
//! `gate-dataflow.tsv`'s `allow` column so they print in every CI log instead of hiding in a `match`
//! arm.
//!
//! Deliberately NOT a bypass — and this is the hole that was closed: the export IS linked and this
//! vote still got no answer out of it (`ensure_lean_init` failed, or the FFI returned an unusable
//! buffer / non-UTF-8). Note that a MALFORMED WIRE is not that state: `verified_2pc_decide` decodes
//! garbage to `Ok(Pending)`, a fail-safe sentinel, so it never reaches the refusal.
//!
//! ⚑ HOW WIDE THE HOLE WAS, at its real resolution. On a fully Lean-linked node
//! `verified_2pc_decide` returns `Ok(..)` and the refusal never arms; on an archive-less node the
//! miss is a DECLARED bypass. What the refusal newly closes is (a) an export-present node whose Lean
//! runtime init or FFI call fails at the moment of a decision, (b) `DREGG_REQUIRE_LEAN=1`, which
//! previously had NO EFFECT ON THIS PATH AT ALL and now yields a hard refusal instead of a `debug!`
//! line, and (c) the durable half — the disposition is a REGISTERED decision site, so a
//! warn-and-continue cannot regrow silently and it no longer depends on what a callee in another
//! crate happens to return.
//!
//! ⚑ AND THE PRECISION THAT KEEPS THE FIX FROM BEING OVER-READ: on a Lean-linked node this tally is
//! decided by the verified rule TWICE. `Coordinator::evaluate_votes` already routes its own
//! `verified_decision` through the `dregg_coord::verified_gate` seam that `lib.rs::run` installs
//! (`register_distributed_gates()`), which is twin#3's registered row; this module is the SECOND,
//! node-level application of the SAME `dregg_coord_2pc_decide` over the SAME tally. So `rust_decision`
//! on a live node is not "the un-verified Rust twin's answer" — it is usually the verified answer
//! arriving by the other path. What was genuinely wrong here was the SHAPE, not a live inflation
//! bug: an `Err` arm that named no disposition, at `debug!`, unregistered, and NOT UNIFORM across
//! cfgs. Both callers of `receive_vote` (`api.rs::atomic_vote` and
//! `blocklace_sync.rs::tally_returned_vote`) therefore already had a verified decider; only THIS one
//! also has an explicit, registered disposition for when it cannot answer.

use std::sync::Once;

use dregg_coord::Decision;

/// One-shot guard so the verified/fallback diagnostic is logged at most once per process.
static GATE_BACKEND_ANNOUNCED: Once = Once::new();

/// Whether the live 2PC-decision gate is enabled. **Default ON**. `DREGG_COORD_DECISION_GATE=0`/
/// `false`/`off` opts OUT (keeps the raw Rust `Decision`) — a DECLARED bypass that
/// `DREGG_REQUIRE_LEAN=1` revokes.
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

/// `DREGG_REQUIRE_LEAN=1` — "I demand the verified artifact". The tree-wide signal (the
/// `dregg-lean-ffi` build gate; `turn`'s `require_verified_conservation_gate`; twin#8b's
/// `require_verified_lean_gate`) that a build must not take ANY declared bypass around a verified
/// gate. It promotes both of [`coord_gate_bypass_allowed`]'s bypasses to the hard refusal, which is
/// how an archive-less build — a test binary, a dev box — can drive the fail-closed pole that an
/// export-present node reaches on its own.
fn require_verified_lean_gate() -> bool {
    std::env::var_os("DREGG_REQUIRE_LEAN")
        .is_some_and(|v| matches!(v.to_string_lossy().trim(), "1" | "true" | "on" | "yes"))
}

/// Map the verified Lean verdict to a `dregg_coord::Decision`.
fn decision_of(verdict: dregg_lean_ffi::Decision2pc) -> Decision {
    match verdict {
        dregg_lean_ffi::Decision2pc::Commit => Decision::Commit,
        dregg_lean_ffi::Decision2pc::Abort => Decision::Abort,
        dregg_lean_ffi::Decision2pc::Pending => Decision::Pending,
    }
}

/// Decode `Coordinator::decision_wire()`'s `"y=<yes>;n=<no>;N=<participants>;t=<threshold>"` back to
/// the tally, or `None` when the wire is not that shape.
///
/// This is a wire READER, not a decider: its only consumer is [`wire_is_decision_actionable`], which
/// decides whether there is a decision in existence for a missing gate to have made.
fn parse_decision_wire(wire: &str) -> Option<(usize, usize, usize, usize)> {
    let mut yes = None;
    let mut no = None;
    let mut n = None;
    let mut thr = None;
    for field in wire.split(';') {
        let (key, val) = field.split_once('=')?;
        let val: usize = val.trim().parse().ok()?;
        match key.trim() {
            "y" => yes = Some(val),
            "n" => no = Some(val),
            "N" => n = Some(val),
            "t" => thr = Some(val),
            _ => return None,
        }
    }
    Some((yes?, no?, n?, thr?))
}

/// Whether a tally is DECISION-ACTIONABLE — i.e. a TERMINAL verdict (Commit or Abort) is reachable
/// from it, so the verified 2PC rule is entitled to have an opinion worth refusing over.
///
/// This is the coord analogue of twin#8b's `is_consensus_actionable`. It is a NECESSARY-CONDITION
/// FILTER on whether to refuse, never a decider — the verdict itself is always the verified rule's.
/// Both of its error directions are non-admitting, which is why a filter is safe here: too
/// PERMISSIVE and we refuse where `Pending` was the right answer (a liveness cost, no `Commit`); too
/// RESTRICTIVE and we fall through to the coordinator's own verdict, which on the live path is
/// itself fail-closed (`evaluate_votes_no_gate` ⇒ `Abort` while `Proposing`).
fn tally_is_decision_actionable(yes: usize, no: usize, n: usize, threshold: usize) -> bool {
    yes >= threshold || no > n.saturating_sub(threshold)
}

/// [`tally_is_decision_actionable`] over the raw wire. A wire we cannot parse is treated as
/// ACTIONABLE (fail-closed): "I cannot tell whether a decision exists" must never be the thing that
/// silences the refusal.
fn wire_is_decision_actionable(wire: &str) -> bool {
    parse_decision_wire(wire)
        .is_none_or(|(yes, no, n, thr)| tally_is_decision_actionable(yes, no, n, thr))
}

/// FAIL-CLOSED CLASS (twin#3b, the coord sibling of `rust_tau_fallback_allowed` /
/// `quorum_rust_fallback_allowed` / `belt_gate_bypass_allowed`): whether the verified 2PC decision
/// gate — the `dregg_coord_2pc_decide` export of `TwoPhaseCommit.evaluate` — may be BYPASSED when it
/// could not answer.
///
/// Two DECLARED bypasses, and nothing else:
///   * `!export_linked` — the archive contains no `dregg_coord_2pc_decide` at all, so there is no
///     verified rule in this binary to route to. The coordinator's own live-path disposition is then
///     the decider, and `coord/src/atomic.rs::evaluate_votes_no_gate` refuses to commit there.
///   * `gate_disabled_by_operator` — `DREGG_COORD_DECISION_GATE=0`, the operator's explicit opt-out
///     of this gate. They kept the Rust coordinator's verdict deliberately.
///
/// `require_lean` (`DREGG_REQUIRE_LEAN=1`) revokes BOTH.
///
/// ⚑ ONE BOOLEAN EXPRESSION, DELIBERATELY — this shape MEASURABLY WIDENS what invariant 6 can catch
/// at this site. `gate-dataflow.py` short-circuits on the first region line naming a declared
/// discriminator and then looks for a refusal in the region PLUS the inlined bodies of the helpers it
/// calls (depth ≤ 2). The sibling predicates (`belt_gate_bypass_allowed`,
/// `rust_tau_fallback_allowed`) open with `if require_lean { return false; }`, and that `return false`
/// is itself a REFUSAL token the checker finds — so the caller's real refusal arm never gets read.
/// MEASURED on this site: with the early `return false`, a mutant that reverts
/// [`coord_decision_disposition`]'s refusal arm to `Ok(())` stays **GREEN** under invariant 6; written
/// as one expression, that mutant goes **RED** ("the declaration is decoration"). Do not reintroduce
/// the early return.
fn coord_gate_bypass_allowed(
    export_linked: bool,
    gate_disabled_by_operator: bool,
    require_lean: bool,
) -> bool {
    !require_lean && (!export_linked || gate_disabled_by_operator)
}

/// Why a vote's authoritative verdict REFUSED. Distinct from every "the verified rule said Abort"
/// outcome on purpose: mirroring twin#1's `ConservationGateUnavailable` and twin#8b's
/// `FinalityGateUnavailable`, a VERIFIER's missing archive is not a PROPOSER's fault. No vote is
/// invalid here and none was rejected — the gate could not answer, so the proposal declines to
/// commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoordDecisionRefusal {
    /// The verified `dregg_coord_2pc_decide` gate was ARMED (the export is linked, this tally can
    /// reach a terminal verdict) and could not answer, with no declared bypass. The proposal does
    /// not commit.
    CoordDecisionGateUnavailable,
}

impl std::fmt::Display for CoordDecisionRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CoordDecisionGateUnavailable => write!(
                f,
                "CoordDecisionGateUnavailable: the verified 2PC coordinator gate \
                 (dregg_coord_2pc_decide = TwoPhaseCommit.evaluate) was armed and could not answer \
                 — the proposal REFUSES to commit (this is a MISSING GATE, not a verdict about any \
                 vote)"
            ),
        }
    }
}

/// THE FAIL-CLOSED DISPOSITION for the verified 2PC decision gate. Called by
/// [`authoritative_decision`] on every vote where the gate is armed.
///
/// `Ok(())` ⇒ the caller may hand back the Rust coordinator's own verdict (a declared bypass, or a
/// tally with no decision in it). `Err(CoordDecisionGateUnavailable)` ⇒ REFUSE: the caller returns
/// [`Decision::Abort`] and no commit happens.
///
/// ## The vacuity short-circuit, and why it is REQUIRED
///
/// A refusal that fires where it means nothing is not a gate. `authoritative_decision` runs on EVERY
/// vote, and most votes cannot decide anything: with threshold 3 of 3, the first Yes has one
/// verdict available and it is `Pending`. Refusing there would tear a healthy proposal down on a
/// verdict that DOES NOT EXIST — the same over-refusal the conservation fix hit when a `set_state`
/// with no value delta tripped its gate, and the one twin#8b hit on an ack/heartbeat-only poll. So a
/// tally that cannot reach a terminal verdict ([`tally_is_decision_actionable`]) short-circuits
/// BEFORE the gate's answer is consulted. (The other two vacuous states are handled at the call
/// site: a `wire` of `None` — a terminal/idle coordinator has no tally at all — and the gate having
/// ANSWERED, where there is no missing gate to dispose of.)
fn coord_decision_disposition(
    verified_verdict: Option<&Decision>,
    tally_is_actionable: bool,
    export_linked: bool,
    gate_disabled_by_operator: bool,
    require_lean: bool,
) -> Result<(), CoordDecisionRefusal> {
    // VACUOUS TALLY — no terminal verdict is reachable from it, so there is no decision in
    // existence for the verified rule to have made. Short-circuited BEFORE the gate's answer is
    // consulted, so the refusal below can never fire where it would mean nothing.
    if !tally_is_actionable {
        return Ok(());
    }
    let Some(_verdict) = verified_verdict else {
        if coord_gate_bypass_allowed(export_linked, gate_disabled_by_operator, require_lean) {
            return Ok(());
        }
        return Err(CoordDecisionRefusal::CoordDecisionGateUnavailable);
    };
    Ok(())
}

// TEST-ONLY fault injection for the 2PC gate's ARMED-BUT-UNANSWERABLE state — the export linked and
// no answer out of the FFI (`ensure_lean_init` failed, or `run()` got an unusable buffer /
// non-UTF-8 back).
//
// It exists because that state is not producible in-process on EITHER build. With the archive
// present, `verified_2pc_decide` returns `Ok(..)` (it even decodes garbage to `Ok(Pending)`); with
// the archive absent, `lean_backed()` is false, so the miss is a DECLARED bypass. So without this,
// the refusal could only be asserted on a box where the Lean runtime is broken — i.e. it would pass
// VACUOUSLY on ember's laptop and in CI alike.
//
// `#[cfg(test)]`: it does not exist in any non-test build, and `scripts/ci-invariants/
// gate-dataflow.py` strips `cfg(test)` definitions before slicing.
//
// THREAD-LOCAL, not a static: `dregg-node`'s test binary runs its tests concurrently and a
// process-wide flag would turn unrelated `authoritative_decision` tests flakily red.
//
// (Plain `//` comments, not `///`: a doc comment on a macro invocation is an
// `unused_doc_comments` warning — the macro would have to emit the docs itself.)
#[cfg(test)]
thread_local! {
    static FORCE_COORD_GATE_UNANSWERABLE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
fn coord_gate_fault_injected() -> bool {
    FORCE_COORD_GATE_UNANSWERABLE.with(|c| c.get())
}

/// TEST-ONLY: arm/disarm the 2PC-gate fault injector for THIS thread. See
/// [`FORCE_COORD_GATE_UNANSWERABLE`].
#[cfg(test)]
fn set_coord_gate_fault_injected(on: bool) {
    FORCE_COORD_GATE_UNANSWERABLE.with(|c| c.set(on));
}

#[cfg(not(test))]
#[inline]
fn coord_gate_fault_injected() -> bool {
    false
}

/// The AUTHORITATIVE 2PC decision for the current coordinator tally.
///
/// `rust_decision` is the verdict the Rust `Coordinator::receive_vote` just produced (the DIFFERENTIAL
/// sibling); `wire` is the coordinator's `decision_wire()` (the tally encoded for the Lean gate), or
/// `None` when not Proposing (terminal/idle — then the Rust decision stands).
///
/// When the gate is enabled AND the Lean export answers, this runs the VERIFIED
/// `dregg_coord_2pc_decide` over `wire`, COMPARES it to `rust_decision` (logging on drift), and
/// returns the VERIFIED verdict — the node acts on the proved rule. When it CANNOT answer, the
/// disposition is [`coord_decision_disposition`]: `Decision::Abort` unless a DECLARED bypass holds.
pub fn authoritative_decision(rust_decision: Decision, wire: Option<&str>) -> Decision {
    let Some(wire) = wire else {
        // VACUOUS: a terminal/idle coordinator. The Rust decision (Pending by construction off the
        // Proposing path) stands; there is no tally to verify and nothing for a missing gate to
        // have decided.
        return rust_decision;
    };

    // The operator opt-out is a DECLARED bypass, and `DREGG_REQUIRE_LEAN=1` revokes it — an
    // operator who demands the verified artifact must not be silently opted out of it by a second
    // env var. Both booleans flow into `coord_decision_disposition` so the disposition, not this
    // early return, owns the decision when the gate is armed.
    let gate_disabled_by_operator = !coord_decision_gate_enabled();
    let require_lean = require_verified_lean_gate();
    if gate_disabled_by_operator && !require_lean {
        return rust_decision;
    }

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

    let gate_answer = if coord_gate_fault_injected() {
        Err(
            "TEST-ONLY fault injection: the verified 2PC gate is armed and unanswerable"
                .to_string(),
        )
    } else {
        dregg_lean_ffi::verified_2pc_decide(wire)
    };
    let verified_verdict = match &gate_answer {
        Ok(v) => Some(decision_of(*v)),
        Err(_) => None,
    };
    // Whether the verified 2PC export is linked AT ALL. This is what distinguishes "there is no
    // verified rule in this binary" (a DECLARED bypass — an archive-less build) from "the export IS
    // here and this vote could not get an answer out of it" (the undeclared fall-through this site
    // shipped with).
    let export_linked = lean_backed() || coord_gate_fault_injected();

    if let Err(refusal) = coord_decision_disposition(
        verified_verdict.as_ref(),
        wire_is_decision_actionable(wire),
        export_linked,
        gate_disabled_by_operator,
        require_lean,
    ) {
        crate::metrics::inc_coord_decision_gate_unavailable_refusals();
        tracing::warn!(
            refusal = %refusal,
            wire = %wire,
            error = gate_answer.as_ref().err().map(String::as_str).unwrap_or("-"),
            export_linked,
            rust_sibling = ?rust_decision,
            "verified 2PC coordinator gate MISSING — FAILING CLOSED: this atomic proposal REFUSES \
             to commit rather than acting on the un-verified Rust Coordinator verdict. This is NOT \
             a verdict about any vote (no vote was rejected; the gate could not answer). Rebuild \
             the node against the verified archive (it splices Dregg2.Exec.DistributedExports), or \
             set DREGG_COORD_DECISION_GATE=0 to deliberately accept the un-verified coordinator."
        );
        return Decision::Abort;
    }

    match verified_verdict {
        Some(lean_decision) => {
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
        None => {
            // The gate could not answer AND the disposition permitted it: either a DECLARED bypass
            // (`coord_gate_bypass_allowed`) or a tally with no terminal verdict in it. The Rust
            // coordinator's verdict stands — which on the live path is itself fail-closed.
            tracing::debug!(
                error = gate_answer
                    .as_ref()
                    .err()
                    .map(String::as_str)
                    .unwrap_or("-"),
                export_linked,
                "verified 2PC gate gave no answer and the disposition PERMITTED it (declared bypass \
                 or a tally with no terminal verdict) — the Rust Coordinator verdict stands"
            );
            rust_decision
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE HONEST POLE — when the Lean export is linked, the verified verdict for each well-formed
    /// tally is the one the Rust coordinator also reaches. Asserted FIRST, because without it the
    /// override tooth below could pass against a gate that returns a constant.
    ///
    /// This pole is deliberately weak ON ITS OWN, and saying so is the point: it is exactly the shape
    /// that made the old `lean_gate_decides_unanimous_scenarios` vacuous. On a build where the gate
    /// cannot answer, `authoritative_decision` either refuses or hands back `rust_decision`, and here
    /// every `rust_decision` IS the expected answer — so this test is green whether
    /// `verified_2pc_decide` works, is broken, returns garbage, or is absent. It carries no assurance
    /// alone. `lean_verdict_overrides_a_wrong_rust_decision` is the tooth; this is only its
    /// non-vacuity companion.
    #[test]
    fn lean_gate_agrees_with_rust_on_wellformed_tallies() {
        if !dregg_lean_ffi::demand_lean(
            lean_backed(),
            "the Lean distributed exports (lean_backed()==false)",
        ) {
            return;
        }
        // 3-of-3 all yes ⇒ Commit; 2 yes 1 no ⇒ Abort (threshold unreachable); 2 yes 0 no ⇒ Pending.
        for (wire, expected) in [
            ("y=3;n=0;N=3;t=3", Decision::Commit),
            ("y=2;n=1;N=3;t=3", Decision::Abort),
            ("y=2;n=0;N=3;t=3", Decision::Pending),
        ] {
            assert_eq!(
                authoritative_decision(expected.clone(), Some(wire)),
                expected,
                "the verified 2PC gate must agree with the Rust coordinator on the well-formed tally \
                 {wire} — a disagreement is a real bug in one of the two engines"
            );
        }
    }

    /// **THE TOOTH, and POLE B of the fail-closed pair — the VERIFIED verdict OVERRIDES the Rust
    /// one, so an honest quorum STILL COMMITS and a bad one STILL ABORTS with the gate installed.**
    /// This module's whole claim is that `dregg_coord_2pc_decide`, not
    /// `Coordinator::evaluate_votes`, decides commit/abort/pending. The only way to witness that is
    /// to hand the gate a `rust_decision` that is DELIBERATELY WRONG for the tally and require the
    /// Lean verdict to win. Every expected value below is one the no-answer path CANNOT produce,
    /// because that path either refuses (`Abort`) or returns `rust_decision` verbatim — so a bypass,
    /// a stuck export, or a deleted `verified_2pc_decide` all turn this test RED.
    ///
    /// That is precisely what the deleted `lean_gate_decides_unanimous_scenarios` could not do, and
    /// what the deleted `falls_back_to_rust_when_no_wire` was not even trying to do: the latter
    /// asserted `f(x, None) == x` against a body whose first statement is
    /// `let Some(wire) = wire else { return rust_decision; }` — literally P → P.
    ///
    /// On an archive-less build this test does not run: `demand_lean` skips it honestly, or PANICS
    /// under `DREGG_TEST_REQUIRE_LEAN=1`. That the verified gate is unassertable without the archive
    /// is the finding, not a defect of the test.
    #[test]
    fn lean_verdict_overrides_a_wrong_rust_decision() {
        if !dregg_lean_ffi::demand_lean(
            lean_backed(),
            "the Lean distributed exports (lean_backed()==false)",
        ) {
            return;
        }
        set_coord_gate_fault_injected(false);
        // (tally wire, a WRONG rust_decision, the verified verdict that must override it).
        for (wire, wrong_rust, verified) in [
            // Unanimous yes: Lean says Commit though Rust handed us Abort. THE HONEST QUORUM STILL
            // COMMITS with the gate installed — without this half, "refuses when the gate is
            // missing" is satisfied by a node that never commits anything.
            ("y=3;n=0;N=3;t=3", Decision::Abort, Decision::Commit),
            ("y=3;n=0;N=3;t=3", Decision::Pending, Decision::Commit),
            // Threshold unreachable: Lean says Abort though Rust handed us Commit. A BAD QUORUM
            // STILL ABORTS.
            ("y=2;n=1;N=3;t=3", Decision::Commit, Decision::Abort),
            // Undecided: Lean says Pending though Rust handed us a TERMINAL verdict — the
            // safety-relevant direction (a premature Commit must not survive the gate).
            ("y=2;n=0;N=3;t=3", Decision::Commit, Decision::Pending),
            ("y=2;n=0;N=3;t=3", Decision::Abort, Decision::Pending),
        ] {
            let got = authoritative_decision(wrong_rust.clone(), Some(wire));
            assert_eq!(
                got, verified,
                "the VERIFIED 2PC gate must OVERRIDE the Rust coordinator: on tally {wire} the Rust \
                 sibling said {wrong_rust:?} and the verified rule says {verified:?}, but the gate \
                 returned {got:?}. Returning {wrong_rust:?} means the gate took the no-answer path — \
                 the verified rule is not deciding and this module's central claim is false on this \
                 build."
            );
        }
    }

    /// ⚑ POLE A (the DISPOSITION, exhaustively): the verified 2PC decision gate is UNAVAILABLE and
    /// the proposal REFUSES TO COMMIT. This is the THIRD confirmed member of the conservation twin's
    /// fail-OPEN class — `authoritative_decision` used to end its no-answer arm with a bare
    /// `rust_decision` at `debug!` level, fail-closed only because a callee in ANOTHER CRATE happened
    /// to return `Abort` (and, under that crate's own `cfg(test)`, did not).
    ///
    /// The test asserts THE NEGATIVE the way conservation's and twin#8b's Pole A do: an `Ok(())` in
    /// the no-bypass quadrant PANICS with a FAIL-OPEN message, because `Ok(())` there means the site
    /// went on to act on an un-verified coordinator verdict — the exact defect.
    ///
    /// It also pins the two DECLARED bypasses (and that `DREGG_REQUIRE_LEAN=1` revokes both), the
    /// VACUITY short-circuit (a tally with no terminal verdict in it is not refused — a refusal that
    /// fires where it means nothing is a bust nobody can land), and the bypass predicate's own
    /// quadrants, because invariant 6 checks that the region REACHES a refusal past a declared
    /// discriminator and does NOT evaluate the discriminator: a mutation of `coord_gate_bypass_allowed`
    /// to a bare `true` stays GREEN there and must redden HERE.
    #[test]
    fn coord_decision_fails_closed_when_the_verified_gate_is_unavailable() {
        // ── THE HOLE, CLOSED. Export linked, operator did not opt out, the tally CAN decide, and
        //    the gate returned no answer ⇒ REFUSE.
        match coord_decision_disposition(None, true, true, false, false) {
            Err(CoordDecisionRefusal::CoordDecisionGateUnavailable) => { /* fail-closed */ }
            Ok(()) => panic!(
                "FAIL-OPEN: the verified `dregg_coord_2pc_decide` export IS linked, the operator did \
                 NOT disable the gate, the tally CAN reach a terminal verdict, and the gate returned \
                 NO ANSWER — yet the disposition permits the site to act on the UN-VERIFIED Rust \
                 Coordinator verdict. That is the defect this gate exists to prevent: a 2PC \
                 commit/abort decision taken with no verified rule having decided it."
            ),
        }

        // ── VACUITY SHORT-CIRCUIT: the tally cannot reach a terminal verdict (an early vote). There
        //    is no decision in existence, so refusing would tear a healthy proposal down over a
        //    verdict that does not exist — the over-refusal the conservation fix had to fix.
        assert!(
            coord_decision_disposition(None, false, true, false, false).is_ok(),
            "a tally with NO terminal verdict reachable must NOT be refused — the verified rule's \
             only available answer there is Pending, so there is nothing for a missing gate to have \
             decided. A refusal here would abort every proposal on its first vote."
        );

        // ── THE GATE ANSWERED: there is no missing gate to dispose of, whatever the verdict is.
        for verdict in [Decision::Commit, Decision::Abort, Decision::Pending] {
            assert!(
                coord_decision_disposition(Some(&verdict), true, true, false, false).is_ok(),
                "an ANSWERING gate must never be refused — {verdict:?} is the verified rule's own \
                 verdict, not a missing gate"
            );
        }

        // ── DECLARED BYPASS 1: no `dregg_coord_2pc_decide` export in this binary at all. Nothing to
        //    route to (an archive-less build / the guest / every test binary).
        assert!(
            coord_decision_disposition(None, true, false, false, false).is_ok(),
            "with NO verified 2PC export linked there is no gate to be unavailable — this is the \
             DECLARED bypass (gate-dataflow.tsv), not a silent fall-open"
        );
        // ── DECLARED BYPASS 2: the operator explicitly disabled this gate.
        assert!(
            coord_decision_disposition(None, true, true, true, false).is_ok(),
            "DREGG_COORD_DECISION_GATE=0 is the operator's declared opt-out of this gate (the same \
             shape twin#8 and twin#11 use)"
        );
        // ── `DREGG_REQUIRE_LEAN=1` REVOKES BOTH — this is what lets an archive-less build drive the
        //    same hard refusal an export-present node reaches on its own.
        assert!(
            coord_decision_disposition(None, true, false, false, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must revoke the no-export bypass"
        );
        assert!(
            coord_decision_disposition(None, true, true, true, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must revoke the operator opt-out bypass too"
        );

        // The bypass predicate itself, so a future widening is a visible diff and not a quiet
        // boolean flip. Invariant 6 CANNOT see this (it does not evaluate the discriminator) — these
        // four lines are the complement that catches a `coord_gate_bypass_allowed -> true` mutant.
        assert!(!coord_gate_bypass_allowed(true, false, false));
        assert!(coord_gate_bypass_allowed(false, false, false));
        assert!(coord_gate_bypass_allowed(true, true, false));
        assert!(!coord_gate_bypass_allowed(false, true, true));

        // The actionability filter, since it is what decides whether the refusal is even consulted.
        // A tally that can COMMIT and a tally that can ABORT are both actionable; an undecided one
        // is not; and an unparseable wire fails CLOSED to actionable.
        assert!(wire_is_decision_actionable("y=3;n=0;N=3;t=3"));
        assert!(wire_is_decision_actionable("y=2;n=1;N=3;t=3"));
        assert!(!wire_is_decision_actionable("y=2;n=0;N=3;t=3"));
        assert!(!wire_is_decision_actionable("y=0;n=0;N=3;t=3"));
        assert!(
            wire_is_decision_actionable("not-a-wire"),
            "an unparseable wire must fail CLOSED to ACTIONABLE — 'I cannot tell whether a decision \
             exists' must never be the thing that silences the refusal"
        );
        assert_eq!(parse_decision_wire("y=3;n=0;N=3;t=3"), Some((3, 0, 3, 3)));
        assert_eq!(parse_decision_wire("y=3;n=0;N=3"), None);
    }

    /// ⚑ POLE A AT THE SITE, and its NON-OVER-FIRE companion beside it: the SAME wire, the SAME Rust
    /// sibling verdict — the ONLY thing that changes is whether the verified gate can answer.
    ///
    /// * GATE ANSWERS (or is bypassed) ⇒ an honest unanimous tally still yields `Commit`. Without
    ///   this half, "refuses when the gate is missing" is satisfied by a site that returns `Abort`
    ///   unconditionally.
    /// * GATE ARMED AND CANNOT ANSWER ⇒ `Decision::Abort`, and a `Commit` observed here PANICS with
    ///   a FAIL-OPEN message: it would mean an atomic forest ran against the ledger with no verified
    ///   2PC rule having decided it.
    /// * THE VACUITY SHORT-CIRCUIT AT THE SITE: with the fault still injected, a tally that cannot
    ///   decide is NOT refused.
    ///
    /// The fault injector is needed because the armed-and-unanswerable state is not producible
    /// in-process on either build (see `FORCE_COORD_GATE_UNANSWERABLE`) — without it this pole would
    /// pass VACUOUSLY everywhere.
    #[test]
    fn authoritative_decision_refuses_when_the_verified_2pc_gate_cannot_answer() {
        // A UNANIMOUS tally: the verified rule's answer here is Commit, so the refusal below is
        // refusing a decision that genuinely exists.
        const HONEST_QUORUM: &str = "y=3;n=0;N=3;t=3";
        // ≥1 ACTIONABLE VOTE, or the pole is vacuous: the refusal must fire where a TERMINAL verdict
        // was reachable, not on an early vote the vacuity short-circuit swallows.
        let (yes, _no, _n, thr) = parse_decision_wire(HONEST_QUORUM).expect("the pole's own wire");
        assert!(
            yes >= 1 && yes >= thr && wire_is_decision_actionable(HONEST_QUORUM),
            "the refusal pole needs a DECISION-ACTIONABLE tally with at least one actionable vote \
             (got yes={yes}, threshold={thr}) — on a tally the vacuity short-circuit swallows this \
             pole would assert nothing at all"
        );

        // ── NON-OVER-FIRE: no fault ⇒ the honest unanimous tally COMMITS. (Skipped only when the
        //    environment has REVOKED the bypasses on an archive-less build, where refusing IS the
        //    correct answer and this half would be asserting the wrong thing.)
        set_coord_gate_fault_injected(false);
        if lean_backed() || !require_verified_lean_gate() {
            assert_eq!(
                authoritative_decision(Decision::Commit, Some(HONEST_QUORUM)),
                Decision::Commit,
                "with the gate answering (or bypassed) an honest unanimous tally must still COMMIT — \
                 otherwise the refusal pole below is satisfied by a site that aborts everything and \
                 asserts nothing"
            );
            assert_eq!(
                authoritative_decision(Decision::Abort, Some("y=2;n=1;N=3;t=3")),
                Decision::Abort,
                "and a tally whose threshold is unreachable must still ABORT"
            );
        }

        // ── POLE A: hold EVERYTHING fixed and change ONLY the gate's ability to answer.
        set_coord_gate_fault_injected(true);
        let refused = authoritative_decision(Decision::Commit, Some(HONEST_QUORUM));
        // The vacuity short-circuit, at the SITE and with the fault still armed.
        let vacuous = authoritative_decision(Decision::Pending, Some("y=1;n=0;N=3;t=3"));
        set_coord_gate_fault_injected(false);

        if refused == Decision::Commit {
            panic!(
                "FAIL-OPEN: the verified 2PC gate was ARMED and could NOT answer on the unanimous \
                 tally {HONEST_QUORUM}, and `authoritative_decision` STILL returned Commit — so \
                 `api.rs::atomic_vote` would run the atomic forest against the ledger with NO \
                 verified 2PC rule having decided it, on the strength of the un-verified Rust \
                 Coordinator sibling alone. That is exactly the transitive fall-through this site \
                 shipped with."
            );
        }
        assert_eq!(
            refused,
            Decision::Abort,
            "the armed-and-unanswerable 2PC gate must yield the EXPLICIT refusal Decision::Abort at \
             THIS site, not whatever the Rust Coordinator sibling happened to hand in"
        );
        assert_eq!(
            vacuous,
            Decision::Pending,
            "the refusal must NOT fire on a tally with no terminal verdict in it (1 yes of 3 needed) \
             even with the gate unanswerable — the Rust sibling's Pending stands. A refusal here \
             would abort every healthy proposal on its first vote."
        );

        // ── AND IT RECOVERS. This site is stateless, so the refusal is per-vote and poisons
        //    nothing: with the gate able to answer again the SAME tally decides again. A fail-closed
        //    path that never recovers is not a fix. (Recovery of the PROPOSAL itself is a level up —
        //    `api.rs::atomic_vote` tears a refused proposal down and the proposer re-proposes; that
        //    liveness cost is stated in this module's header, not hidden.)
        if lean_backed() || !require_verified_lean_gate() {
            assert_eq!(
                authoritative_decision(Decision::Commit, Some(HONEST_QUORUM)),
                Decision::Commit,
                "once the gate can answer again the same tally must decide again — the refusal is \
                 per-vote, it does not latch"
            );
        }
    }
}
