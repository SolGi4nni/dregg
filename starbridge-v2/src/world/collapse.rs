//! **SYMBOLIC EXECUTION** — the deferred-witness fast path and its collapse orchestrator.
//!
//! Extracted verbatim from `world/mod.rs` so the witness/cost track owns a file rather than
//! a line-range. No behaviour change. A CHILD module, so it keeps private access to
//! `World`'s fields (`symbolic_turns`, `witness_mode`, `history`, `record_exec`,
//! `record_ledger`, `receipts`, `engine`) exactly as it had inline.
//!
//! The thesis is sound and proved: the witness layer is what a REMOTE light client needs to
//! be convinced, not what the local state transition needs to happen
//! (`turn/src/collapse.rs`, grounded in `metatheory/Dregg2/Spec/ExecRefinement.lean`).
//! Admission gates are mode-independent — a turn rejected in Full is rejected in Symbolic.
//!
//! ⚑ THREE UNSOUNDNESSES BLOCK MAKING SYMBOLIC THE DEFAULT. All three are repairs owed
//! before any flip, and all three fail QUIETLY:
//!   1. Durable recovery replays through `commit_turn`; under a symbolic default it buffers
//!      instead of recording the tape, and the fail-closed root check still PASSES because
//!      it compares ABSTRACT state, which Symbolic preserves exactly. You reopen into an
//!      empty `History` with every receipt a sentinel, and no error.
//!   2. `collapse` overwrites the provenance log with the RECORDER's receipts but never
//!      re-syncs the ENGINE's per-agent receipt head, so the next live turn links to a hash
//!      no receipt carries. (`turn/src/collapse.rs`'s own `collapse_with` DOES call
//!      `set_last_receipt_hash`; this path takes `History::record_commit` and skips it.)
//!   3. `DEFERRED_STATE_HASH` is all-zeros, a receipt carrying it is VALIDLY SIGNED, and
//!      nothing refuses it: `is_deferred` has zero callers in `turn/src/verify.rs`, and its
//!      only non-test callers tree-wide are two `debug_assert!`s — compiled out in release.

use super::*;

impl World {
    // --- SYMBOLIC EXECUTION (the deferred-witness fast path + collapse) ------
    //
    // ⚠ EXPERIMENTAL / SHELVED — NOT YET WIRED (backlog #2). This is the
    // partial-turn / promises symbolic-witness path. Nothing in the shipped
    // cockpit calls it — its ONLY callers are the self-tests below. It is kept
    // (not deleted) because it IS the partial-turn vision, but it is
    // `#[doc(hidden)]` so it stops PRESENTING as live API, and it carries a
    // cluster of KNOWN LATENT BUGS in the collapse protocol (backlog #3/#5/#6:
    // a receipt-index desync when Full receipts land at the tail, a non-atomic
    // `mem::take` that tears state on mid-collapse failure, and a durability
    // drift where buffered turns are lost on reopen). Those are MOOT while the
    // feature is gated (no live caller). DO NOT wire any of these into a live
    // path until the collapse protocol is repaired — see
    // docs/STARBRIDGE-V2-IMPROVEMENT-BACKLOG-2026-07-24.md.

    /// The current [`WitnessMode`] (Full by default).
    ///
    /// ⚠ EXPERIMENTAL / not yet wired — part of the shelved symbolic-witness
    /// path (backlog #2). See the section banner above.
    #[doc(hidden)]
    pub fn witness_mode(&self) -> WitnessMode {
        self.witness_mode
    }

    /// `true` iff the live commit path is currently deferring witnesses
    /// ([`WitnessMode::Symbolic`]).
    ///
    /// ⚠ EXPERIMENTAL / not yet wired — part of the shelved symbolic-witness
    /// path (backlog #2). See the section banner above.
    #[doc(hidden)]
    pub fn is_symbolic(&self) -> bool {
        self.witness_mode.is_symbolic()
    }

    /// How many symbolic (deferred-witness) turns are buffered, awaiting
    /// [`World::collapse`]. `0` in Full mode or after a collapse.
    ///
    /// ⚠ EXPERIMENTAL / not yet wired — part of the shelved symbolic-witness
    /// path (backlog #2). See the section banner above.
    #[doc(hidden)]
    pub fn symbolic_pending(&self) -> usize {
        self.symbolic_turns.len()
    }

    /// **Enter / leave SYMBOLIC mode** — the local deferred-witness fast path.
    ///
    /// ⚠ EXPERIMENTAL / not yet wired — the partial-turn symbolic-witness path
    /// (backlog #2); no live caller. See the section banner above.
    ///
    /// In [`WitnessMode::Symbolic`] the engine applies each turn's FULL state
    /// transition (balances / caps / nonces — the abstract progress) but DEFERS
    /// the per-turn Merkle witness: the engine executor skips `Ledger::root()`
    /// (the receipt carries the deferred sentinel state-hash), and `commit_turn`
    /// skips the replay-tape double-execution, buffering the turn for later
    /// [`World::collapse`]. This is the cost the mode saves: zero per-turn
    /// hashing on the live path AND no second full execution on the recorder.
    ///
    /// SOUNDNESS: this selects ONLY whether witnesses materialize; it NEVER
    /// changes which turns are admitted (every legality gate — authority,
    /// conservation, the `NoteSpend` STARK, sovereign-witness, nonce/fee — runs
    /// identically in both modes). A symbolic receipt is local/unpublishable
    /// until collapsed; the witness is deferred, never the decision.
    ///
    /// Switching back to `Full` does NOT auto-collapse the already-buffered
    /// symbolic turns (call [`World::collapse`] for that); it only makes
    /// SUBSEQUENT turns witness eagerly again. The engine executor's mode is
    /// flipped here so the live receipts reflect the new mode immediately.
    #[doc(hidden)]
    pub fn set_witness_mode(&mut self, mode: WitnessMode) {
        self.witness_mode = mode;
        self.engine.executor().set_witness_mode(mode);
    }

    /// **COLLAPSE** — materialize the deferred witnesses of every buffered
    /// symbolic turn by re-running them through FULL execution on the replay
    /// recorder, reproducing EXACTLY what a Full run would have witnessed.
    ///
    /// For each buffered symbolic turn, this drives the SKIPPED replay-tape
    /// commit (`History::record_commit` against the recorder's Full executor +
    /// ledger), which re-executes the turn and captures the real post-state root
    /// tooth — then replaces that turn's DEFERRED receipt in the provenance log
    /// with the re-derived REAL one. Determinism is already discharged (the
    /// pinned timestamp + cost model + the recorder's chain-head lock-step), so
    /// each collapsed receipt is byte-identical to the Full-mode receipt.
    ///
    /// After collapse the live commit path returns to [`WitnessMode::Full`] and
    /// the symbolic buffer is empty. FAIL-CLOSED: if a buffered turn does NOT
    /// re-commit under Full, or the materialized recorder root diverges from the
    /// live engine's post-state, this returns `Err` (an integrity event — a
    /// symbolic run that admitted a turn Full execution refuses, which the
    /// shared admission gate makes impossible barring corruption).
    ///
    /// Returns the count of turns collapsed.
    ///
    /// ⚠ EXPERIMENTAL / not yet wired (backlog #2) — no live caller. The collapse
    /// protocol carries KNOWN LATENT BUGS #3/#5/#6 (receipt-index desync when Full
    /// receipts land at the tail, non-atomic `mem::take` on mid-collapse failure,
    /// and buffered turns lost on reopen). MOOT while gated; DO NOT use in a live
    /// path until repaired. See the section banner above.
    #[doc(hidden)]
    pub fn collapse(&mut self) -> Result<usize, String> {
        // Defensive (#7): materialize any deferred replay-tape clone before the
        // Full re-execution reads/writes it. A fork is always Full (never symbolic),
        // so it never reaches collapse deferred; a live symbolic world is never
        // deferred — so this is a no-op today, keeping the invariant robust if the
        // deferral surface ever widens.
        self.ensure_record_ledger();
        let buffered = std::mem::take(&mut self.symbolic_turns);
        let n = buffered.len();

        // The provenance index of the FIRST symbolic receipt: the symbolic turns
        // are the LAST `n` entries in `receipts` (they were pushed in order,
        // after any prior Full commits). Re-derive each and overwrite in place.
        let first = self.receipts.len().checked_sub(n).ok_or_else(|| {
            "collapse: fewer receipts than buffered symbolic turns (provenance desync)".to_string()
        })?;

        for (offset, turn) in buffered.into_iter().enumerate() {
            // Drive the SKIPPED Full replay-tape commit — re-executes the turn
            // against the recorder's Full executor + ledger and captures the real
            // post-root tooth. The recorder's chain head advances in lock-step.
            let receipt = self
                .history
                .record_commit(&self.record_exec, &mut self.record_ledger, turn.clone())
                .ok_or_else(|| {
                    format!(
                        "collapse: buffered symbolic turn (agent {}) did NOT re-commit under \
                         Full execution — integrity event (symbolic admitted a Full-illegal turn)",
                        short(&turn.agent)
                    )
                })?;
            debug_assert!(
                !is_deferred(&receipt),
                "a collapsed receipt must carry a real (non-deferred) witness"
            );
            // Replace the deferred receipt in the provenance log with the real one.
            self.receipts[first + offset] = receipt;
        }

        // FAIL-CLOSED convergence: the recorder ledger (Full-replayed) MUST now
        // commit to the SAME canonical root as the live engine ledger (which
        // applied the identical state transitions, just witness-deferred). A
        // divergence means the deferred path drifted from Full — refuse.
        let engine_root = crate::persistence::canonical_ledger_root(self.engine.ledger());
        let record_root = crate::persistence::canonical_ledger_root(&self.record_ledger);
        if engine_root != record_root {
            return Err(format!(
                "collapse: post-collapse ledger divergence — engine root {:?} != \
                 collapsed recorder root {:?} (the symbolic state transition drifted from Full)",
                engine_root, record_root
            ));
        }

        // The live path returns to Full (subsequent turns witness eagerly).
        self.set_witness_mode(WitnessMode::Full);
        Ok(n)
    }
}
