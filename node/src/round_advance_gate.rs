//! Verified ES ROUND-ADVANCE GATE — Cordial Miners Alg. 4 lines 67–75, consulted by the round
//! producer before it honors a `RoundPlan::Advance`.
//!
//! # The defect this closes (READING-DAG-BFT-2026-08-08 §5.3)
//!
//! Cordial Miners' two instances pair leader election with a round-advance rule ON PURPOSE
//! (CM §6.2): the asynchrony instance (retrospective coin leader) advances as soon as a round is
//! cordial (Alg. 4:59); the eventual-synchrony instance (prospective round-robin leader — what we
//! run, `blocklace/src/ordering.rs::wave_leader`) advances only when the leader block is
//! present / ratified / super-ratified **or a timeout fires** (Alg. 4:67–75), *"to prevent the
//! adversary from ordering the messages after GST … as the leader is known in advance."*
//! `blocklace_sync::plan_round_block` implemented line 59's rule under line 67's leader schedule:
//! cordiality alone, no leader clause, no timer. That is a liveness hole — free for an adversary
//! controlling delivery order, and a standing `1/n` wave tax on any persistently slow member
//! (SH §5.2 says the same about its even-round timeout).
//!
//! # The substrate
//!
//! The RULE is authored in Lean — `metatheory/Dregg2/Distributed/RoundAdvanceGate.lean`
//! (`advanceGate`, over the SAME `BlocklaceFinality` vocabulary the verified finalizer uses), with
//! the spec theorems `leader_advances_promptly` / `no_early_advance` / `timeout_advances` /
//! `timeout_does_not_bypass_cordiality`, exported as `@[export] dregg_round_advance`
//! (`round_advance_eq_gate` proves the wire verdict IS the verified predicate). This module is
//! only the CLOCK and the WIRE: it measures the timeout (time is I/O), encodes the lace with the
//! SAME encoder the finality gate uses ([`crate::finality_gate::VerifiedFinality::build_wire`] —
//! one grammar for every consensus gate), and routes the verdict. No advance-rule logic lives here.
//!
//! # The timeout, and the ∆ it must exceed (CM Prop. 38)
//!
//! CM Prop. 38 (ES leader-liveness with probability 1) holds **only if `timeout > ∆`**, ∆ the
//! post-GST message-delay bound; the timeout is measured *"from when round r is cordial"*
//! (Alg. 4:75). [`RoundAdvanceTimer`] implements exactly that: the clock for round `r` starts at
//! the first production attempt where `r` was observed cordial (the first `RoundPlan::Advance`
//! for `r`), and `timeout_fired` is `elapsed ≥ round_advance_timeout_ms`.
//!
//! **The ∆ assumption, stated:** we assume post-GST one-way block delivery (gossip publish →
//! peer's lace insert, including persist) completes within **∆ ≤ 1 s** for the deployments this
//! tree targets (a single-digit-validator federation on commodity cloud WAN; worst measured
//! inter-region RTTs are ≲ 300 ms and blocks are far below bandwidth-relevant size). The default
//! timeout is **5 000 ms = 5× that envelope**. The choice is asymmetric on purpose: a timeout
//! below the true ∆ voids Prop. 38's hypothesis (the round can advance past a merely-slow honest
//! leader — the exact tax the gate removes), while a timeout above it costs ONLY absent-leader
//! latency (the leader-present fast path never consults the clock — Lean
//! `leader_advances_promptly`). So the default is deliberately generous, and ∆ here is an
//! ENVELOPE CLAIM, not a fleet measurement — measuring the live gossip-delay distribution and
//! tightening the default is real follow-up work, and shrinking it is safe to defer because only
//! latency, never safety or liveness, is on the table above ∆. At n=1 (the live Path-of-Angels
//! shape) the solo validator is every wave's leader and the gate passes without the timer at all
//! (Lean `solo_advances_promptly`).
//!
//! # Fail-safety (the `finality_belt_disposition` shape)
//!
//! * Export linked, gate answers `"1"`/`"0"` — the verdict decides (the normal path).
//! * Export linked, gate answers `ERR`/garbage — **HOLD, always** ([`EsAdvanceConsult::GateError`]
//!   never advances; an `ERR` is OUR encoder bug and a refusal under a false diagnosis is still a
//!   refusal — fix it, never route around it).
//! * Export ABSENT — the two DECLARED bypasses of [`es_gate_bypass_allowed`], mirroring
//!   `belt_gate_bypass_allowed`: a genuinely archive-less build, or the operator's explicit
//!   `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`; `DREGG_REQUIRE_LEAN=1` revokes both. Under a bypass the
//!   producer advances on cordiality alone (the pre-gate behavior), loudly.

use dregg_blocklace::finality::Blocklace;

/// Default `round_advance_timeout_ms`: 5 s, ≥ 5× the assumed post-GST ∆ ≤ 1 s (module docstring).
pub(crate) const DEFAULT_ROUND_ADVANCE_TIMEOUT_MS: u64 = 5_000;

/// The configured ES round-advance timeout (`DREGG_ROUND_ADVANCE_TIMEOUT_MS`, default
/// [`DEFAULT_ROUND_ADVANCE_TIMEOUT_MS`]).
///
/// ⚑ REFUSES `0` and garbage rather than defaulting: `0` makes `timeout_fired` constantly true,
/// which reduces the gate to `cordialRound` alone — the EXACT asynchrony-advance defect this gate
/// exists to close, reintroduced by a config knob. A node with that setting must not run.
/// (⚠ This is deliberately NOT `blocklace_wave_timeout_ms` — that is GOVERNANCE PROPOSAL EXPIRY,
/// threaded to `ConstitutionManager`; the name collision is how the missing consensus timer stayed
/// missing.)
pub(crate) fn round_advance_timeout_ms() -> u64 {
    match std::env::var("DREGG_ROUND_ADVANCE_TIMEOUT_MS") {
        Err(_) => DEFAULT_ROUND_ADVANCE_TIMEOUT_MS,
        Ok(raw) => match raw.trim().parse::<u64>() {
            Ok(ms) if ms > 0 => ms,
            _ => panic!(
                "DREGG_ROUND_ADVANCE_TIMEOUT_MS={raw:?} is not a positive integer. `0` would \
                 reintroduce the asynchrony round-advance rule under a prospective leader (the \
                 defect the ES gate closes) and is refused; set a value strictly greater than the \
                 assumed post-GST delay bound ∆ (CM Prop. 38 needs timeout > ∆), or unset it for \
                 the {DEFAULT_ROUND_ADVANCE_TIMEOUT_MS} ms default."
            ),
        },
    }
}

/// CM Alg. 4:75's clock: *"timeout is measured from when round r is cordial."* One slot suffices —
/// the producer only ever completes ONE round at a time, and advancing (or falling back to an
/// earlier round view) re-arms the slot for the new round.
#[derive(Debug, Default)]
pub(crate) struct RoundAdvanceTimer(Option<(u64, std::time::Instant)>);

impl RoundAdvanceTimer {
    /// Whether the timeout has fired for `completing_round`. First observation of a round arms the
    /// clock and reports `false` (the leader clause gets its prompt-path chance); later
    /// observations of the SAME round compare elapsed time against `timeout_ms`. A DIFFERENT round
    /// re-arms.
    pub(crate) fn timeout_fired(&mut self, completing_round: u64, timeout_ms: u64) -> bool {
        match &self.0 {
            Some((round, since)) if *round == completing_round => {
                since.elapsed().as_millis() >= u128::from(timeout_ms)
            }
            _ => {
                self.0 = Some((completing_round, std::time::Instant::now()));
                false
            }
        }
    }

    /// Milliseconds this round has been waiting (0 if the clock is not armed for it) — diagnostics
    /// for the HOLD log line, so a stalled producer can SAY WHY (the `RoundPlan::Wait` ethos).
    pub(crate) fn waiting_ms(&self, completing_round: u64) -> u128 {
        match &self.0 {
            Some((round, since)) if *round == completing_round => since.elapsed().as_millis(),
            _ => 0,
        }
    }
}

/// What one consult of the verified gate produced. `GateError` (export linked, no usable verdict)
/// is deliberately DISTINCT from `ExportUnavailable` (nothing linked): the first is a bug that must
/// HOLD unconditionally, the second is the declared-bypass state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EsAdvanceConsult {
    /// The verified rule says the round may advance (leader clause or timeout, on a cordial round).
    Advance,
    /// The verified rule says HOLD — cordial, but the leader clause is unmet and the timeout has
    /// not fired.
    Hold,
    /// The export answered, but not with a verdict (`ERR` — malformed wire — or garbage). HOLD.
    GateError(String),
    /// The linked archive has no `dregg_round_advance` export at all.
    ExportUnavailable(String),
}

/// Encode the advance-gate wire: `r=<round>;t=<0|1>;` + the finality gate's
/// `(wavelength, participants, lace)` grammar (`RoundAdvanceGate.decodeAdvanceWire` mirrors this
/// byte-for-byte; the Lean side re-derives rounds/cordiality/leader from the lace — the round and
/// the timeout BIT are the only inputs Rust adds).
pub(crate) fn advance_wire(
    lace: &Blocklace,
    participants: &[[u8; 32]],
    completing_round: u64,
    timeout_fired: bool,
) -> String {
    let lace_wire = crate::finality_gate::VerifiedFinality::lace_wire(lace, participants);
    format!(
        "r={completing_round};t={};{lace_wire}",
        if timeout_fired { "1" } else { "0" }
    )
}

/// Consult the VERIFIED gate once. Pure routing — every decision is the Lean rule's or the
/// disposition's, never this function's.
pub(crate) fn consult(
    lace: &Blocklace,
    participants: &[[u8; 32]],
    completing_round: u64,
    timeout_fired: bool,
) -> EsAdvanceConsult {
    let wire = advance_wire(lace, participants, completing_round, timeout_fired);
    match dregg_lean_ffi::shadow_round_advance(&wire) {
        Ok(v) if v == "1" => EsAdvanceConsult::Advance,
        Ok(v) if v == "0" => EsAdvanceConsult::Hold,
        Ok(other) => EsAdvanceConsult::GateError(format!(
            "dregg_round_advance answered {other:?} (an ERR wire is an encoder bug — HOLDING)"
        )),
        Err(e) => EsAdvanceConsult::ExportUnavailable(e),
    }
}

/// FAIL-CLOSED CLASS (the round-advance twin of `belt_gate_bypass_allowed`, and the same ONE
/// BOOLEAN EXPRESSION shape — the early-return form blinded ci-invariant 6 once already; see that
/// function's docstring). Whether an ABSENT export may be bypassed (advance on cordiality alone,
/// the pre-gate behavior): only on a genuinely archive-less build or under the operator's explicit
/// `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, and `DREGG_REQUIRE_LEAN=1` revokes both. A linked-but-
/// erroring gate is NOT in this function's vocabulary on purpose — `GateError` HOLDS
/// unconditionally at the call site.
pub(crate) fn es_gate_bypass_allowed(
    export_linked: bool,
    allow_unverified: bool,
    require_lean: bool,
) -> bool {
    !require_lean && (!export_linked || allow_unverified)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::finality::{Block, BlockId, Payload};
    use ed25519_dalek::SigningKey;

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// A fully cross-linked `rounds`-deep lace over `creators` — every round-(k+1) block
    /// references ALL of round k (the `finality_gate::tests::cross_linked_lace` shape).
    fn cross_linked_lace(creators: &[SigningKey], rounds: u64) -> Blocklace {
        let mut lace = Blocklace::new(creators[0].clone(), 3);
        let mut round_prev: Vec<BlockId> = Vec::new();
        for round in 0..rounds {
            let mut this_round = Vec::new();
            for (i, k) in creators.iter().enumerate() {
                let b = Block::new(
                    k,
                    round,
                    Payload::Turn(vec![(round * 10) as u8 + i as u8]),
                    round_prev.clone(),
                );
                this_round.push(b.id());
                lace.receive_block(b).expect("block insert");
            }
            round_prev = this_round;
        }
        lace
    }

    /// The timer implements Alg. 4:75's clock: arms on first observation (false), fires only after
    /// `timeout_ms`, and re-arms on a different round.
    #[test]
    fn timer_arms_fires_and_rearms() {
        let mut t = RoundAdvanceTimer::default();
        assert!(
            !t.timeout_fired(7, 25),
            "first observation arms, never fires"
        );
        assert!(
            !t.timeout_fired(7, 25),
            "immediately after arming: not fired"
        );
        std::thread::sleep(std::time::Duration::from_millis(30));
        assert!(t.timeout_fired(7, 25), "after timeout_ms elapsed: fired");
        assert!(t.waiting_ms(7) >= 30);
        // A different round re-arms rather than inheriting the stale clock.
        assert!(!t.timeout_fired(8, 25), "new round re-arms");
        assert_eq!(t.waiting_ms(7), 0, "the old round's clock is gone");
    }

    /// `0`/garbage timeout config REFUSES to run (it would reintroduce the async advance rule).
    #[test]
    fn zero_timeout_is_refused() {
        // Env mutation is process-global; this test runs the parse path via a child-free check of
        // the panic message shape instead of poisoning sibling tests' environment.
        // SAFETY: test-local env mutation; the variable is removed before the test returns and
        // no sibling test in this crate reads it concurrently.
        unsafe {
            std::env::set_var("DREGG_ROUND_ADVANCE_TIMEOUT_MS", "0");
        }
        let result = std::panic::catch_unwind(|| {
            // The parse arm: `round_advance_timeout_ms` panics on 0.
            let _ = round_advance_timeout_ms();
        });
        // SAFETY: as above.
        unsafe {
            std::env::remove_var("DREGG_ROUND_ADVANCE_TIMEOUT_MS");
        }
        assert!(result.is_err(), "a zero timeout must refuse to run");
    }

    /// The bypass predicate is the belt's exact truth table (and stays ONE expression).
    #[test]
    fn bypass_truth_table() {
        // archive-less build: bypass unless required.
        assert!(es_gate_bypass_allowed(false, false, false));
        // linked + no escape: NO bypass.
        assert!(!es_gate_bypass_allowed(true, false, false));
        // linked + operator escape: bypass.
        assert!(es_gate_bypass_allowed(true, true, false));
        // DREGG_REQUIRE_LEAN revokes everything.
        assert!(!es_gate_bypass_allowed(false, false, true));
        assert!(!es_gate_bypass_allowed(true, true, true));
    }

    /// **POLE 1 (prompt).** Leader present at the wave-start round ⇒ the VERIFIED gate advances
    /// with NO timeout — and the call's wall-clock cost (the good-case latency the gate adds to
    /// the producer) is measured and printed, not asserted by vibes. Self-skips without the
    /// archive (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).
    #[test]
    fn leader_present_advances_promptly_and_costs_little() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::round_advance_available(),
            "the Lean round-advance export (round_advance_available()==false)",
        ) {
            return;
        }

        for &n in &[3usize, 5] {
            let keys: Vec<SigningKey> = (1..=n as u8).map(key).collect();
            let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();
            // Completing round 1 (wave-start): the wave-0 leader `participants[0]` has a block.
            let lace = cross_linked_lace(&keys, 1);

            let t0 = std::time::Instant::now();
            let verdict = consult(&lace, &participants, 1, false);
            let first_call = t0.elapsed();
            assert_eq!(
                verdict,
                EsAdvanceConsult::Advance,
                "n={n}: leader block present at the wave start must advance PROMPTLY (no timeout)"
            );

            // Steady-state cost: median of repeated calls (first call may amortize Lean init).
            let mut samples: Vec<u128> = (0..20)
                .map(|_| {
                    let t = std::time::Instant::now();
                    let v = consult(&lace, &participants, 1, false);
                    assert_eq!(v, EsAdvanceConsult::Advance);
                    t.elapsed().as_micros()
                })
                .collect();
            samples.sort_unstable();
            eprintln!(
                "ES-GATE GOOD-CASE LATENCY n={n}: first call {first_call:?}, median of 20 = \
                 {} µs, p90 = {} µs (⚠ read alongside the box load — a loaded box prices the \
                 fleet, not the code)",
                samples[samples.len() / 2],
                samples[(samples.len() * 9) / 10],
            );
        }
    }

    /// **THE DEPTH SWEEP — the measurement the good-case latency above CANNOT make.**
    ///
    /// `leader_present_advances_promptly_and_costs_little` consults at **round 1**, and round 1 is
    /// the single depth at which a cost exponential *in round depth* is invisible: the BFS under
    /// `mkPastCache` does one layer. That instrument reported a healthy 23–36 µs for as long as the
    /// gate took **half an hour per consult at round 11** — four nodes at 100% CPU on an idle box,
    /// `/status` timing out, `dag_height` frozen. The instrument was not wrong; it was pointed at
    /// the one place the wound could not appear.
    ///
    /// So this sweeps the completing round and prints cost against lace size. It asserts nothing
    /// about wall-clock (that prices the box); it is `#[ignore]`d and read as a table. What it makes
    /// impossible is a repeat of the blind spot — the curve is now on the bench at the depth the
    /// federation actually runs at.
    ///
    /// ```text
    /// cargo test -p dregg-node --lib -- --ignored --nocapture es_gate_cost_against_round_depth
    /// ```
    #[test]
    #[ignore = "measurement instrument, not a gate — run explicitly on a quiet box"]
    fn es_gate_cost_against_round_depth() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::round_advance_available(),
            "the Lean round-advance export (round_advance_available()==false)",
        ) {
            return;
        }
        let n = 4usize; // the observed federation
        let keys: Vec<SigningKey> = (1..=n as u8).map(key).collect();
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();

        eprintln!("ES-GATE COST vs ROUND DEPTH (n={n}) — rounds, lace blocks, median µs of 5");
        for rounds in [1u64, 4, 8, 10, 11, 12, 16, 24, 32, 48] {
            let lace = cross_linked_lace(&keys, rounds);
            let blocks = lace.iter().count();
            let mut samples: Vec<u128> = (0..5)
                .map(|_| {
                    let t = std::time::Instant::now();
                    let v = consult(&lace, &participants, rounds, false);
                    // A gate ERROR would make the timing meaningless — never read a cost off a
                    // call that did not actually decide.
                    assert!(
                        matches!(v, EsAdvanceConsult::Advance | EsAdvanceConsult::Hold),
                        "rounds={rounds}: the gate did not decide ({v:?}) — the timing below would \
                         be priced off a failed call"
                    );
                    t.elapsed().as_micros()
                })
                .collect();
            samples.sort_unstable();
            eprintln!(
                "  rounds={rounds:<3} lace={blocks:<4} median={:>10} µs",
                samples[samples.len() / 2]
            );
        }
        eprintln!(
            "⚠ absolute µs price the box and its load; the SHAPE of the curve is the result."
        );
    }

    /// **POLE 2 (no early advance + timeout escape).** n=4, round 1 filled by creators 2..4 —
    /// cordial (3 ≥ supermajority(4) = 3) with the wave-0 leader ABSENT: the verified gate HOLDS
    /// on a mere creator supermajority, and the SAME lace advances once the timeout bit fires.
    /// The Lean twins are `noLeader_r1_refuses` / `noLeader_r1_timeout_advances`; this exercises
    /// them through the REAL wire on REAL hybrid-id blocks.
    #[test]
    fn absent_leader_holds_then_advances_on_timeout() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::round_advance_available(),
            "the Lean round-advance export (round_advance_available()==false)",
        ) {
            return;
        }

        let keys: Vec<SigningKey> = (1..=4u8).map(key).collect();
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();
        assert_eq!(
            dregg_blocklace::ordering::supermajority_threshold(participants.len()),
            3,
            "n=4 supermajority is 3 — the leaderless round below IS cordial"
        );

        // Round 1 by creators 2,3,4 only. The wave-0 round-robin leader is participants[0] —
        // absent. (The lace's signing key is keys[1]; the leader's key authors NOTHING.)
        let mut lace = Blocklace::new(keys[1].clone(), 3);
        for (i, k) in keys.iter().enumerate().skip(1) {
            let b = Block::new(k, 0, Payload::Turn(vec![i as u8]), vec![]);
            lace.receive_block(b).expect("block insert");
        }

        // Anti-vacuity: the leader really is enrolled and really is absent from the lace.
        assert!(
            !lace.iter().any(|(_, b)| b.creator == participants[0]),
            "the wave-0 leader must have NO block — else this test has no absent leader"
        );

        assert_eq!(
            consult(&lace, &participants, 1, false),
            EsAdvanceConsult::Hold,
            "a creator supermajority WITHOUT the leader must NOT advance before the timeout — \
             this is the line-67 clause the async rule was missing"
        );
        assert_eq!(
            consult(&lace, &participants, 1, true),
            EsAdvanceConsult::Advance,
            "the timeout must un-stick the leaderless round (Prop. 38's liveness arm)"
        );
    }

    /// A malformed wire is a GateError (HOLD), never an Advance — the fail-closed pole of the
    /// wire itself.
    #[test]
    fn malformed_wire_is_gate_error() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::round_advance_available(),
            "the Lean round-advance export (round_advance_available()==false)",
        ) {
            return;
        }
        match dregg_lean_ffi::shadow_round_advance("r=1;t=2;w=3;P=1;B=") {
            Ok(v) => assert_eq!(
                v, "ERR",
                "a bad timeout bit must be the fail-closed sentinel"
            ),
            Err(e) => panic!("export vanished mid-test: {e}"),
        }
    }
}
