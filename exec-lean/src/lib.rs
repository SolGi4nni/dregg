//! `dregg-exec-lean`: the verified-Lean-FFI executor cluster.
//!
//! This native-only crate holds ALL the Lean-FFI executor code that `dregg-turn` used to carry
//! behind the (now-deleted) `no-lean-link` feature:
//!
//! - [`lean_shadow`] — the differential OBSERVER: it marshals a turn through the verified Lean
//!   kernel and compares its commit decision (and, on the swap-safe root-agreeing set, its full
//!   reconstituted post-state root) against the legacy Rust executor, WITHOUT affecting the
//!   `TurnResult`. It is also the binding strict-veto REJECTION authority (`DREGG_LEAN_SHADOW_STRICT`).
//! - [`lean_apply`] — the authoritative state PRODUCER: `produce_via_lean` installs the verified
//!   Lean post-state and commit verdict UNCONDITIONALLY (the authority inversion), demoting the
//!   Rust executor to a checked reference.
//!
//! # The seam
//!
//! `dregg-turn` defines [`dregg_turn::ShadowObserver`] (a `Send + Sync` trait) and holds an
//! `Arc<dyn ShadowObserver>` in its `TurnExecutor`, defaulting to `NoOpShadowObserver`. This crate
//! provides [`LeanShadowObserver`], which implements that trait by delegating to the moved
//! `lean_shadow` free functions. A native node injects it via
//! `TurnExecutor::with_shadow_observer(Arc::new(LeanShadowObserver))`; a wasm / no-FFI build simply
//! does not depend on this crate and keeps the no-op default. That dependency choice — not a feature
//! flag — is what selects the verified shadow/gate executor.

pub mod distributed_gates;
pub mod lean_apply;
pub mod lean_shadow;
pub mod spec_audit;

use std::sync::Arc;

use dregg_cell::Ledger;
use dregg_turn::shadow::{ShadowHostCtx, ShadowObserver};
use dregg_turn::turn::{Turn, TurnResult};

pub use distributed_gates::{LeanDistributedGate, register_distributed_gates};
pub use lean_apply::{
    ProducerOutcome, execute_via_lean, produce_via_lean, prof_outer_dump, profile_lean_phases,
};
pub use lean_shadow::{ShadowAgreement, ShadowReport, maybe_shadow_turn, shadow_report};
pub use spec_audit::{
    AuditEntry, AuditOutcome, AuditWorker, DivergenceKind, DivergenceReport, DivergenceSink,
    SpeculativeAudit, WorkerStop,
};

/// The verified-Lean shadow/gate observer — the real implementation of
/// [`dregg_turn::ShadowObserver`] that `dregg-turn`'s executor drives through the seam.
///
/// Inject it on a native node:
///
/// ```ignore
/// use std::sync::Arc;
/// let executor = TurnExecutor::new(costs)
///     .with_shadow_observer(Arc::new(dregg_exec_lean::LeanShadowObserver));
/// ```
///
/// All five trait methods delegate to the moved `lean_shadow` free functions (which carry the
/// thread-local pre-state / host-context the differential needs).
#[derive(Clone, Copy, Debug, Default)]
pub struct LeanShadowObserver;

impl LeanShadowObserver {
    /// Construct the observer (wrapped in an `Arc` for `TurnExecutor::with_shadow_observer`).
    pub fn arc() -> Arc<dyn ShadowObserver> {
        Arc::new(LeanShadowObserver)
    }
}

impl ShadowObserver for LeanShadowObserver {
    fn enabled(&self) -> bool {
        lean_shadow::shadow_enabled()
    }

    fn capture_pre_state(&self, turn: &Turn, ledger: &Ledger, host: ShadowHostCtx) {
        lean_shadow::capture_pre_state_if_eligible(turn, ledger, host);
    }

    fn strict_veto_enabled(&self) -> bool {
        lean_shadow::strict_veto_enabled()
    }

    fn observe(
        &self,
        turn: &Turn,
        ledger: &Ledger,
        result: &TurnResult,
        block_height: u64,
    ) -> Option<bool> {
        lean_shadow::maybe_shadow_turn(turn, ledger, result, block_height)
    }

    fn lean_vetoes(&self, rust_committed: bool, lean_verdict: Option<bool>) -> bool {
        lean_shadow::lean_vetoes(rust_committed, lean_verdict)
    }

    fn admission_reason(&self) -> Option<dregg_turn::AdmissionReason> {
        lean_shadow::last_admission_reason()
    }
}
