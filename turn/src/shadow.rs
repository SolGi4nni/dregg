//! The post-commit observer SEAM — dependency inversion that keeps `dregg-turn` FFI-free.
//!
//! The verified-Lean executor cluster lives in the native-only `dregg-exec-lean` crate, which
//! links `libdregg_lean.a`. `dregg-turn` itself must NOT link the Lean archive (it is the crate
//! a wasm / no-FFI build composes), so the executor's production path reaches it through this
//! trait rather than the FFI directly.
//!
//! [`TurnExecutor`](crate::executor::TurnExecutor) holds an
//! `Arc<dyn ShadowObserver>`. A native node injects `dregg_exec_lean::LeanShadowObserver`;
//! every other construction defaults to [`NoOpShadowObserver`], which does nothing.
//!
//! ⚑ **THE DIFFERENTIAL IS NO LONGER HERE — 2026-07-30.** Until this date the trait also carried
//! `enabled()` and `capture_pre_state()`, driving a Lean↔Rust differential gated on
//! `DREGG_LEAN_SHADOW=1`. That variable was set by NOTHING in the tree outside one test (swept
//! four ways), so the differential never ran on a deployed node; and its verdict was discarded at
//! the single call site (`let _ = maybe_shadow_turn(..)`), so it could not decide anything even
//! armed. Its one genuine strength — a CELL-BY-CELL Lean↔Rust post-state comparison — was moved
//! onto the seam that IS armed (`dregg_exec_lean::lean_apply::produce_via_lean`, default-ON via
//! `DREGG_LEAN_PRODUCER`), where it now decides `ProducerOutcome`'s `divergence` field, and the
//! dark path was deleted rather than kept alongside it.
//!
//! What survives here is what the observer actually *does* on a live node: advance
//! observer-owned cross-turn accumulators after a committed turn (the durable nullifier
//! frontier). That is a real side effect on the production path, not a diagnostic.
//!
//! [`ShadowHostCtx`] is pure data (only `CellId`, no FFI), so it lives here in `dregg-turn`;
//! the verified producer reads it (via `TurnExecutor::build_shadow_host_ctx`) to drive the
//! verified gate.

use dregg_cell::CellId;

use crate::turn::{Turn, TurnResult};
use dregg_cell::Ledger;

/// The HOST/NODE-fed admission context (boundary-P1 bug-1). These come from the EXECUTOR's own
/// state — NOT the turn — so the verified gate's clock / freeze-set / chain-head / budget legs are
/// decided by the node, exactly as `admissible` reads `AdmCtx`. The production node (and the
/// in-process executor) builds this from `self.block_height` / `self.cell_migrations` (frozen) /
/// `self.get_last_receipt_hash(agent)` (stored head) / `self.budget_gate.remaining()` (budget).
///
/// Defaults (via [`ShadowHostCtx::diag`]) are the DIAGNOSTIC values that never spuriously reject
/// (clock 0, no frozen cells, genesis head, large budget) — used by tests/round-trips. The
/// security of bug-1 is that the EXECUTOR overrides every field from its own state.
///
/// # The host obligation (Lean: `Dregg2.Exec.HostCorrespondence`, AssuranceCase seam §2)
///
/// The verified gate's conditional soundness lemma `admissible_sound_of_reflects` proves: IF this
/// context FAITHFULLY REFLECTS the node's true runtime facts (`HostFacts`: true clock / freeze-set /
/// stored head / budget) THEN the gate decides EXACTLY as the node's own state would. The teeth
/// (`{stored_head,budget,freeze,clock}_obligation_teeth`) show each field is load-bearing: an unsafe
/// under-report (omit a truly-frozen referenced cell, advance the head to a forked turn's `prev`,
/// inflate the budget, retard the clock) ADMITS a turn the true-facts gate REJECTS. So the production
/// executor MUST override every field below from its own `self` state — never `diag()`. The only
/// residual is producer-coverage: every cell the freeze gate reads (agent + write-set) must get a
/// wire id; the `frozen` projection here is faithful on exactly those read cells
/// (`marshalled_admission_sound`).
#[derive(Clone, Debug)]
pub struct ShadowHostCtx {
    /// The executor's current chain block height (`self.block_height`).
    pub block_height: u64,
    /// The migration freeze-set as raw `CellId`s (`self.cell_migrations` frozen cells). Only the
    /// subset referenced by the turn (and thus in the wire id map) crosses; a frozen agent /
    /// write-set cell then trips the verified `admissible` frozen leg, matching apply.rs.
    pub frozen: Vec<CellId>,
    /// The agent's stored receipt-chain head (`self.get_last_receipt_hash(agent)`), or `None` =
    /// genesis. The verified `admissible` ChainHead leg requires the turn's claimed `prev` to
    /// EQUAL this — a forked / replayed turn (`prev ≠ stored_head`) is rejected.
    pub stored_head: Option<[u8; 32]>,
    /// The Stingray silo budget slice the fee must fit (`self.budget_gate.remaining()`). The
    /// verified `admissible` Budget leg rejects `fee > budget`.
    pub budget: u64,
    /// The executor's `max_introduction_lifetime` (`self.max_introduction_lifetime`). An
    /// `Introduce` stamps the granted cap's `expires_at = block_height + max_introduction_lifetime`;
    /// the cap-fidelity reconstitution (`collect_cap_ops`) needs the SAME value to rebuild the
    /// introduced cap's leaf byte-exactly. Defaults to the executor default (1000).
    pub intro_lifetime: u64,
    /// The executor's wall-clock (`self.current_timestamp`, as `u64`). `apply_refresh_delegation`
    /// stamps the re-armed delegation snapshot's `refreshed_at` with this value, and `refreshed_at`
    /// FOLDS INTO the cell commitment (`hash_delegation_into`), so the refresh reconstitution
    /// (`StateOp::RefreshDelegation`) must stamp the SAME value for the reconstituted `.root()` to
    /// match Rust. Defaults to `0` (the test/round-trip clock).
    pub current_timestamp: u64,
    /// The executor's local federation id (`self.local_federation_id`). The `Authorization::Signature`
    /// WHO leg binds the ed25519 signing message to THIS federation
    /// (`compute_signing_message`/`compute_partial_signing_message`), so the producer marshaller must
    /// recompute the SAME message the executor's `verify_ed25519_signature` checks. A genuine sig is
    /// then folded into the wire as a self-echoing `(statement, proof)` pair (admits); a forged /
    /// cross-federation / tampered one fails the recomputed `verify_strict` and the wire DOES NOT echo
    /// (the gate's WHO leg fail-closes). Defaults to the all-zero id (the test/round-trip federation).
    pub federation_id: [u8; 32],
    /// The HOST fee-distribution cells (`self.proposer_cell` / `self.treasury_cell` /
    /// `self.fee_well_cell`). THE EPOCH §5 ("fees as moves"): after a committing turn the Rust
    /// executor MOVES the fee — `proposer_cell` += fee/2, `treasury_cell` += fee*3/10, and the
    /// remainder to `fee_well_cell` (`distribute_fee_shares`) — so the committed value delta is zero.
    ///
    /// These are HOST/CONSENSUS config, NOT kernel-turn-body state: the verified kernel's
    /// `distributeFee` runs against FIXED PLACEHOLDER cells (`admCtxOfHost`'s `hostProposerCell` /
    /// `hostTreasuryCell` = 0xF00 / 0xF01) and burns the residue, precisely because the real
    /// distribution targets are node config the wire grammar does not carry. The placeholder credits
    /// land on synthetic cells absent from the deployed ledger (dropped by the `WireState → Ledger`
    /// extractor), so the verified producer's reconstituted ledger reflects ONLY the agent's
    /// prologue fee debit, never the real fee-well credit. The Rust executor, in contrast, applies
    /// the REAL distribution to real cells — so a fee-bearing turn diverged on `.root()` (the n=5
    /// dogfood faucet bug). Threading the real cells here lets the producer apply the IDENTICAL host
    /// fee distribution to the reconstituted ledger (`lean_apply::apply_fee_distribution`), so both
    /// producers reflect the same host fee policy and agree on `.root()` WITHOUT changing the
    /// verified spec. Defaults to all-`None` (the test/round-trip path: no fee distribution).
    pub proposer_cell: Option<CellId>,
    /// See [`Self::proposer_cell`] — the treasury share recipient (`self.treasury_cell`).
    pub treasury_cell: Option<CellId>,
    /// See [`Self::proposer_cell`] — the fee-well remainder recipient (`self.fee_well_cell`).
    pub fee_well_cell: Option<CellId>,
}

impl ShadowHostCtx {
    /// The DIAGNOSTIC host context — never spuriously rejects. The PRODUCTION executor MUST
    /// override every field from its own state (that override is what makes bug-1 real).
    pub fn diag() -> Self {
        ShadowHostCtx {
            block_height: 0,
            frozen: vec![],
            stored_head: None,
            budget: 1_000_000_000,
            intro_lifetime: 1000,
            current_timestamp: 0,
            federation_id: [0u8; 32],
            proposer_cell: None,
            treasury_cell: None,
            fee_well_cell: None,
        }
    }
}

/// The dependency-inversion seam for the native post-commit observer.
///
/// The production execute path ([`TurnExecutor::execute`](crate::executor::TurnExecutor::execute))
/// calls [`observe`](ShadowObserver::observe) once, after the turn's result is final, so
/// `dregg-turn` never links the FFI directly.
///
/// ⚑ **THIS SEAM DECIDES NOTHING, AND NO LONGER PRETENDS TO OBSERVE ANYTHING EITHER.** `observe`
/// is side-effect-free with respect to the `TurnResult`; the executor does not consult it to
/// commit or reject. The verified Lean executor is the AUTHORITATIVE decision-maker on the *other*
/// seam — `dregg_exec_lean::lean_apply::produce_via_lean` (THE SWAP authority inversion, default-ON
/// via `DREGG_LEAN_PRODUCER`), which installs the verified post-state and verdict, owns the
/// reject-side rollback of executor side state (`checkpoint_producer_reference` /
/// `rollback_producer_reference`), and — since 2026-07-30 — carries the cell-by-cell Lean↔Rust
/// post-state comparison that used to live behind `DREGG_LEAN_SHADOW`.
///
/// Two decisionless mechanisms have now been deleted from this seam rather than left alongside the
/// armed one:
///
/// * `strict_veto_enabled` / `lean_vetoes` (2026-07-28) — armed by nothing, dominated by the
///   producer inversion, and its rollback restored the ledger while leaving the agent's
///   receipt-chain head advanced to a receipt that was never issued, bricking the agent.
/// * `enabled` / `capture_pre_state` and the `DREGG_LEAN_SHADOW` differential (2026-07-30) —
///   the variable was set by nothing, and the verdict was dropped at the call site.
///
/// The native node injects `dregg_exec_lean::LeanShadowObserver`; everyone else gets
/// [`NoOpShadowObserver`].
pub trait ShadowObserver: Send + Sync {
    /// Advance observer-owned CROSS-TURN state from a finished turn. Called once at the end of
    /// [`TurnExecutor::execute`](crate::executor::TurnExecutor::execute) with the final `result`.
    ///
    /// It must never change `result` — the turn is already decided. `dregg_exec_lean` uses it to
    /// advance its durable nullifier frontier on a committed `NoteSpend`; that is the only live
    /// consumer, and it is a real production side effect rather than a diagnostic.
    fn observe(&self, turn: &Turn, ledger: &Ledger, result: &TurnResult, block_height: u64);
}

/// The default observer for every executor that is NOT a native Lean-linked node: it advances
/// nothing. The wasm / no-FFI path gets this, making the absence a visible platform fact rather
/// than a silent omission.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoOpShadowObserver;

impl ShadowObserver for NoOpShadowObserver {
    fn observe(&self, _turn: &Turn, _ledger: &Ledger, _result: &TurnResult, _block_height: u64) {}
}
