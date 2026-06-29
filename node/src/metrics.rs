//! Prometheus metrics for operational observability.
//!
//! Installs a Prometheus recorder and exposes a `/metrics` HTTP handler
//! that renders the exposition format.

use std::sync::OnceLock;

use metrics::{counter, gauge, histogram};
use metrics_exporter_prometheus::{PrometheusBuilder, PrometheusHandle};

/// The process-global Prometheus handle. The recorder may only be installed ONCE per
/// process (a second `install_recorder()` errors — the global recorder is already set),
/// so we install on first call and hand back a clone of the same handle thereafter. This
/// makes `install_recorder()` idempotent, which matters when several in-process tests (or
/// a re-entrant boot) each ask for the recorder.
static RECORDER: OnceLock<PrometheusHandle> = OnceLock::new();

/// Install the Prometheus metrics recorder (idempotent). Returns the handle used to
/// render the exposition-format output from the `/metrics` endpoint.
pub fn install_recorder() -> PrometheusHandle {
    RECORDER
        .get_or_init(|| {
            PrometheusBuilder::new()
                .install_recorder()
                .expect("failed to install Prometheus metrics recorder")
        })
        .clone()
}

/// Axum handler for GET /metrics.
pub async fn metrics_handler(
    axum::extract::State(handle): axum::extract::State<PrometheusHandle>,
) -> String {
    handle.render()
}

// ─── Counters ────────────────────────────────────────────────────────────────

/// Increment the turns-submitted counter.
pub fn inc_turns_submitted() {
    counter!("dregg_turns_submitted_total").increment(1);
}

/// Increment the turns-executed counter with a status label.
pub fn inc_turns_executed(status: &'static str) {
    counter!("dregg_turns_executed_total", "status" => status).increment(1);
}

/// Increment proof verification outcomes.
pub fn inc_proofs_verified(result: &'static str) {
    counter!("dregg_proofs_verified_total", "result" => result).increment(1);
}

/// Increment revocations processed.
pub fn inc_revocations() {
    counter!("dregg_revocations_total").increment(1);
}

/// Increment gossip message counter.
pub fn inc_gossip(direction: &'static str) {
    counter!("dregg_gossip_messages_total", "direction" => direction).increment(1);
}

/// Increment the consensus-wide-attested counter: a block reached a quorum
/// (2f+1) of distinct signed finalization votes, the cross-node AGREEMENT step
/// beyond the per-node `tau` order. See `crate::finalization_votes`.
pub fn inc_consensus_attested() {
    counter!("dregg_consensus_attested_total").increment(1);
}

/// Increment the tau finalized-order prefix-shift counter: the previously
/// computed finalized order was NOT a prefix of the newly computed one — a
/// reorg-by-catchup (an honest late block sorted into the already-executed
/// region), the live occurrence of the machine-checked counterexample in
/// `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean`. The identity execution
/// cursor absorbs it correctly; this counter makes it visible to operators.
pub fn inc_tau_prefix_shift() {
    counter!("dregg_tau_prefix_shifts_total").increment(1);
}

/// Increment the consensus rust↔lean DIFFERENTIAL DIVERGENCE counter: on a
/// Lean-shadowed node, the verified Lean `dregg_tau_order` and the Rust
/// `ordering::tau` finalized DIFFERENT `(creator, seq)` sets for a poll. This is
/// how a mixed rust/lean federation surfaces a real implementation divergence to
/// monitoring continuously (every finalization), not only in a log line — a
/// non-zero rate means the two finality implementations disagree and must be
/// investigated (a Rust-side bug or a stale/mismatched archive). The verified
/// Lean order is authoritative for that poll; this counter makes the divergence
/// observable so the mixed-network differential is a SAFETY NET, not a silent drop.
pub fn inc_consensus_differential_divergence() {
    counter!("dregg_consensus_differential_divergence_total").increment(1);
}

// ─── Histograms ──────────────────────────────────────────────────────────────

/// Record turn execution duration.
pub fn record_turn_execution_duration(seconds: f64) {
    histogram!("dregg_turn_execution_duration_seconds").record(seconds);
}

/// Record proof verification duration.
pub fn record_proof_verification_duration(seconds: f64) {
    histogram!("dregg_proof_verification_duration_seconds").record(seconds);
}

// ─── Async prove pool (F-DOS-1: proving OFF the commit/request path) ──────────

/// An async proof-attestation job completed (proof attached to a committed
/// receipt off the request path).
pub fn inc_async_proofs_completed() {
    counter!("dregg_async_proofs_total", "result" => "completed").increment(1);
}

/// An async proof job failed (proving error / panic). The receipt stays
/// committed-but-unattested; this is a liveness degradation of the attestation
/// layer, never a safety problem (the commit was witness-revalidated).
pub fn inc_async_proofs_failed() {
    counter!("dregg_async_proofs_total", "result" => "failed").increment(1);
}

/// An async proof job was dropped because the bounded queue was full (back-
/// pressure under a proving flood — bounds CPU/memory instead of wedging).
pub fn inc_async_proofs_dropped() {
    counter!("dregg_async_proofs_total", "result" => "dropped").increment(1);
}

/// Record wall-clock duration of an async proof generation (off the lock).
pub fn record_async_proof_duration(seconds: f64) {
    histogram!("dregg_async_proof_duration_seconds").record(seconds);
}

// ─── Gauges ──────────────────────────────────────────────────────────────────

/// Set the current peer count.
pub fn set_federation_peers_connected(count: f64) {
    gauge!("dregg_federation_peers_connected").set(count);
}

/// Set the current ledger cell count.
pub fn set_ledger_cell_count(count: f64) {
    gauge!("dregg_ledger_cell_count").set(count);
}

/// Set the current block height.
pub fn set_block_height(height: f64) {
    gauge!("dregg_block_height").set(height);
}

/// Set time since the last root update (seconds).
pub fn set_federation_root_age(seconds: f64) {
    gauge!("dregg_federation_root_age_seconds").set(seconds);
}
