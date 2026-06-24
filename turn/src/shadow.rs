//! The shadow-observer SEAM — dependency inversion that keeps `dregg-turn` FFI-free.
//!
//! The verified-Lean shadow/gate executor (the differential observer + the strict-veto
//! rejection authority) lives in the native-only `dregg-exec-lean` crate, which links
//! `libdregg_lean.a`. `dregg-turn` itself must NOT link the Lean archive (it is the crate
//! a wasm / no-FFI build composes), so the executor's production path calls the shadow
//! through this trait rather than the FFI directly.
//!
//! [`TurnExecutor`](crate::executor::TurnExecutor) holds an
//! `Arc<dyn ShadowObserver>`. A native node injects `dregg_exec_lean::LeanShadowObserver`
//! (the real differential + veto authority); every other construction defaults to
//! [`NoOpShadowObserver`], which compares nothing and never vetoes. "No shadow" is then a
//! visible platform fact (the wasm / no-FFI path), never an accident — the native node's
//! executor builders inject the Lean observer explicitly.
//!
//! [`ShadowHostCtx`] is pure data (only `CellId`, no FFI), so it lives here in `dregg-turn`
//! and the trait can name it; the Lean observer reads it to drive the verified gate.

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
        }
    }
}

/// The dependency-inversion seam for the verified-Lean shadow/gate executor.
///
/// The production execute path ([`TurnExecutor::execute`](crate::executor::TurnExecutor::execute))
/// drives the 5-step shadow flow through this trait so `dregg-turn` never links the FFI directly:
///
/// 1. [`enabled`](ShadowObserver::enabled) — is the shadow on (`DREGG_LEAN_SHADOW=1`)?
/// 2. [`capture_pre_state`](ShadowObserver::capture_pre_state) — snapshot the pre-state + host ctx.
/// 3. [`strict_veto_enabled`](ShadowObserver::strict_veto_enabled) — is the binding-reject gate on?
/// 4. [`observe`](ShadowObserver::observe) — run the verified Lean executor; return its commit bit.
/// 5. [`lean_vetoes`](ShadowObserver::lean_vetoes) — does the verified verdict VETO the Rust commit?
///
/// The native node injects `dregg_exec_lean::LeanShadowObserver`; everyone else gets
/// [`NoOpShadowObserver`].
pub trait ShadowObserver: Send + Sync {
    /// Whether shadow execution is enabled (`DREGG_LEAN_SHADOW=1`). The executor uses this to AVOID
    /// building the host-fed admission context (which locks the migration / budget mutexes) on the
    /// hot path when the shadow is off.
    fn enabled(&self) -> bool;

    /// Capture a minimal pre-state snapshot when shadow mode may run later. Called at the start of
    /// [`TurnExecutor::execute`](crate::executor::TurnExecutor::execute) before any ledger mutation
    /// so the Lean oracle sees the same admission inputs as Rust. `host` carries the NODE-fed
    /// admission context (clock / freeze-set / stored head / budget) — the bug-1 seam.
    fn capture_pre_state(&self, turn: &Turn, ledger: &Ledger, host: ShadowHostCtx);

    /// Whether strict mode is on — the verified Lean executor is a binding REJECTION authority.
    fn strict_veto_enabled(&self) -> bool;

    /// Run the verified Lean executor against the just-produced Rust `result` and return the Lean
    /// commit bit (`Some(committed)`), or `None` when the turn was not comparable (FFI off / GAP /
    /// marshal failure). Side-effecting diagnostics only — never changes `result`.
    fn observe(
        &self,
        turn: &Turn,
        ledger: &Ledger,
        result: &TurnResult,
        block_height: u64,
    ) -> Option<bool>;

    /// Decide whether the verified Lean verdict VETOES a Rust commit. Returns `true` ONLY when strict
    /// mode is on, the turn was COMPARABLE (`lean_verdict = Some(_)`), the Rust executor COMMITTED, and
    /// the verified Lean executor REJECTED. A `None` verdict (GAP / FFI off) NEVER vetoes (we cannot
    /// veto what we did not compare). The veto is one-directional: `lean=false ∧ rust=true` only.
    fn lean_vetoes(&self, rust_committed: bool, lean_verdict: Option<bool>) -> bool;

    /// The theorem-backed admission REASON the verified executor reported for the last
    /// [`observe`](Self::observe)d turn, if the verified wire carried one (the legible "why" of a
    /// refusal). `None` when there is no reason to surface — the turn was not comparable
    /// (FFI off / GAP / marshal failure), the legacy no-`reason` wire was decoded, or the turn was
    /// admitted (the body's success/rollback is then the relevant outcome, not admission). The
    /// default (no-op observer) returns `None` — "no reason" is then a visible platform fact.
    fn admission_reason(&self) -> Option<crate::AdmissionReason> {
        None
    }
}

/// The default shadow observer for every executor that is NOT a native Lean-linked node: it
/// compares nothing, captures nothing, and never vetoes. The wasm / no-FFI path gets this, making
/// "no shadow" a visible platform fact rather than a silent omission.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoOpShadowObserver;

impl ShadowObserver for NoOpShadowObserver {
    fn enabled(&self) -> bool {
        false
    }

    fn capture_pre_state(&self, _turn: &Turn, _ledger: &Ledger, _host: ShadowHostCtx) {}

    fn strict_veto_enabled(&self) -> bool {
        false
    }

    fn observe(
        &self,
        _turn: &Turn,
        _ledger: &Ledger,
        _result: &TurnResult,
        _block_height: u64,
    ) -> Option<bool> {
        None
    }

    fn lean_vetoes(&self, _rust_committed: bool, _lean_verdict: Option<bool>) -> bool {
        false
    }
}
