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

pub mod conservation_oracle;
pub mod constraint_oracle;
pub mod distributed_gates;
pub mod lean_apply;
pub mod lean_shadow;
pub mod nullifier;
pub mod spec_audit;

use std::sync::{Arc, Mutex};

use dregg_cell::Ledger;
use dregg_turn::action::Effect;
use dregg_turn::forest::CallTree;
use dregg_turn::shadow::{ShadowHostCtx, ShadowObserver};
use dregg_turn::turn::{Turn, TurnResult};

pub use nullifier::{NullifierDoubleSpend, ShadowNullifierAccumulator};

pub use conservation_oracle::{LeanConservationOracle, register_conservation_oracle};
pub use constraint_oracle::{LeanConstraintOracle, register_constraint_oracle};
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
/// ```
/// use dregg_turn::{ComputronCosts, TurnExecutor};
///
/// # let costs = ComputronCosts::default();
/// let executor = TurnExecutor::new(costs)
///     .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
/// # let _ = executor;
/// ```
///
/// The differential trait methods delegate to the moved `lean_shadow` free functions (which carry
/// the thread-local pre-state / host-context the differential needs). The observer additionally
/// holds the DURABLE nullifier accumulator ([`ShadowNullifierAccumulator`], VK-epoch stage E2 Path
/// B): a per-executor cumulative double-spend frontier advanced on every committed `NoteSpend`.
/// This is the cross-turn executor state — the observer lives for the node's lifetime inside the
/// `TurnExecutor`'s `Arc<dyn ShadowObserver>`, so the frontier persists across turns. The advanced
/// root is exposed via [`Self::nullifier_root`] / [`Self::nullifier_root_faithful`] — the seam the
/// item-3 wire-codec feed (ember-gated VK-epoch flip) plugs into. It does NOT gate the commit
/// decision yet (that is the gated flip).
#[derive(Clone, Debug, Default)]
pub struct LeanShadowObserver {
    /// The cumulative nullifier accumulator (the double-spend frontier). Interior-mutable behind an
    /// `Arc<Mutex<…>>` because the `ShadowObserver` methods take `&self` and the observer is shared
    /// as `Arc<dyn ShadowObserver>`.
    nullifier_acc: Arc<Mutex<ShadowNullifierAccumulator>>,
}

impl LeanShadowObserver {
    /// Construct the observer (wrapped in an `Arc` for `TurnExecutor::with_shadow_observer`).
    pub fn arc() -> Arc<dyn ShadowObserver> {
        Arc::new(LeanShadowObserver::default())
    }

    /// The current advanced 8-felt `nullifier_root` (the circuit limb-26 candidate) held by this
    /// observer's accumulator. For inspection / the item-3 wire-codec feed.
    pub fn nullifier_root(&self) -> [dregg_circuit::field::BabyBear; 8] {
        self.nullifier_acc.lock().unwrap().nullifier_root()
    }

    /// The current advanced nullifier root as a [`dregg_circuit::Faithful8`] — the value threaded
    /// into `V9RotationContext.nullifier_root` / `rotation_witness::produce` at the proof-context
    /// construction site so the rotated commitment's limb-26 ‖ 67..73 group binds the LIVE frontier
    /// (the item-3 wire-codec feed, ember-gated).
    pub fn nullifier_root_faithful(&self) -> dregg_circuit::Faithful8 {
        self.nullifier_acc.lock().unwrap().nullifier_root_faithful()
    }

    /// Advance the durable accumulator by every `NoteSpend` nullifier in a COMMITTED turn (the Path
    /// B fast root advance). A refused advance (an already-present nullifier — the fail-closed
    /// `present_no_witness` face) is logged as an anomaly but does NOT veto here: the commit
    /// decision does not yet turn on this root (that is item 3, the wire-codec fork). The legacy
    /// `dregg_cell` `NullifierSet::insert` already refuses a genuine double-spend at the executor
    /// entry point, so a refusal here signals the two frontiers disagreed.
    fn advance_committed_nullifiers(&self, turn: &Turn) {
        fn collect(tree: &CallTree, out: &mut Vec<[u8; 32]>) {
            for eff in &tree.action.effects {
                if let Effect::NoteSpend { nullifier, .. } = eff {
                    out.push(nullifier.0);
                }
            }
            for c in &tree.children {
                collect(c, out);
            }
        }
        let mut nfs = Vec::new();
        for r in &turn.call_forest.roots {
            collect(r, &mut nfs);
        }
        if nfs.is_empty() {
            return;
        }
        let mut acc = self.nullifier_acc.lock().unwrap();
        for nf in &nfs {
            match acc.spend(nf) {
                Ok(_) => {}
                Err(e) => {
                    tracing::warn!(
                        target: "dregg::lean_shadow::nullifier",
                        addr = e.addr,
                        "Path-B nullifier accumulator refused an advance for a COMMITTED NoteSpend \
                         (already-present key) — the fail-closed present_no_witness face; the shadow \
                         frontier and the committed turn disagree"
                    );
                }
            }
        }
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
        let verdict = lean_shadow::maybe_shadow_turn(turn, ledger, result, block_height);
        // Path B: advance the durable nullifier root on a committed NoteSpend (the fast O(depth)
        // Rust advance; the verified Lean `advanceRoot8Exec` is the proven spec + offline KAT tie).
        if result.is_committed() {
            self.advance_committed_nullifiers(turn);
        }
        verdict
    }

    fn lean_vetoes(&self, rust_committed: bool, lean_verdict: Option<bool>) -> bool {
        lean_shadow::lean_vetoes(rust_committed, lean_verdict)
    }

    fn admission_reason(&self) -> Option<dregg_turn::AdmissionReason> {
        lean_shadow::last_admission_reason()
    }
}
