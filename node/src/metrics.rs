//! Prometheus metrics for operational observability.
//!
//! Installs a Prometheus recorder and exposes a `/metrics` HTTP handler
//! that renders the exposition format.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

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
            let handle = PrometheusBuilder::new()
                .install_recorder()
                .expect("failed to install Prometheus metrics recorder");
            // Pre-register the flat security series at 0 so the Security dashboard
            // renders "0" (a live, healthy detector) from boot rather than "No
            // data" until the first refusal. The Prometheus recorder only creates
            // a series on first touch, so an `increment(0)` here materializes it.
            counter!("dregg_auth_failures_total").increment(0);
            counter!("dregg_cap_refusals_total").increment(0);
            counter!("dregg_turns_rejected_total").increment(0);
            counter!("dregg_sandbox_denials_total").increment(0);
            // Pre-seed the protocol-activity series the same way so the protocol
            // dashboard renders "0" from boot rather than "No data" on an idle
            // node. The label shapes MATCH the real emit sites: `inc_turns_submitted`
            // is unlabelled, `inc_proofs_verified` carries `result` (seeded with the
            // representative "valid" value it emits on a passing verification).
            counter!("dregg_turns_submitted_total").increment(0);
            counter!("dregg_proofs_verified_total", "result" => "valid").increment(0);
            gauge!("dregg_block_height").set(0.0);
            // Pre-seed the gossip stream-rejection series at 0 so the federation
            // dashboard's gossip-rejection panel renders a healthy "0" from boot
            // (a flat green line) and lights up as a RATE spike during a gossip
            // storm, rather than reading "No data" until the first rejection. The
            // real, labelled emissions come from `dregg-net`'s inbound
            // stream-rejection sites (`net/src/gossip.rs::note_gossip_stream_rejected`,
            // peer/reason labelled) onto this same process-global recorder; the
            // sentinel label set below is the boot floor under those series.
            counter!(
                "dregg_gossip_stream_rejected_total",
                "peer" => "none",
                "reason" => "none",
            )
            .increment(0);
            // Pre-seed the bridge conservation gauge at 1 (CONSERVING) so the
            // series exists on /metrics from boot — a healthy flat line — and the
            // `BridgeConservationBreach` page (deploy/observability/prometheus/rules/
            // dregg.rules.yml, `min(dregg_bridge_conservation_ok) == 0`) is ARMED
            // rather than matching no series (inert, cannot fire). The gauge means:
            // 1 when the bridge's circulating mirror value never exceeds the value
            // locked/burned on the source chain (`live_supply <= currently_locked`,
            // `dregg_bridge::solana_mirror::MirrorState::invariant_holds`), 0 the
            // instant a mint outruns its backing.
            //
            // SEAM (do not read this as a live breach detector yet): the
            // AUTHORITATIVE conservation decision is the COMMITTED bridge ledger in
            // `dregg_turn::executor::bridge_ledger::bridge_mint_against_lock`
            // (it computes `new_live <= locked` against committed cell state); a
            // breach can only arise when that mint path runs. Today NO in-process
            // caller drives it on the node — the relayer mint/escrow loop is
            // exercised only in `bridge/tests/` — so this series holds the boot
            // floor. Full coverage = the node hosts the relayer loop (or the
            // relayer process exports its own /metrics) and calls
            // `set_bridge_conservation_ok(receipt.live_supply <= receipt.currently_locked)`
            // at every `bridge_mint_against_lock` / `record_escrow` receipt. This is
            // the same "registered here, wired when its plane exports" posture as
            // `dregg_sandbox_denials_total` below.
            gauge!("dregg_bridge_conservation_ok").set(1.0);
            handle
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

/// Publish the bridge conservation state: `true` (→ gauge 1) when the bridge's
/// circulating mirror value is fully backed (`live_supply <= currently_locked`),
/// `false` (→ gauge 0) the instant a mint outran its lock/burn backing.
///
/// This is the single most important bridge safety signal — a 0 means the bridge
/// released more value on the destination chain than was locked/burned on the
/// source (an unbacked-value emission: double-mint or forged lock attestation),
/// and pages via `BridgeConservationBreach`.
///
/// Call this at every committed bridge accounting outcome — i.e. from the
/// `dregg_turn::executor::bridge_ledger::bridge_mint_against_lock` /
/// `record_escrow` receipt path (`BridgeMintReceipt` / `BridgeEscrowReceipt`
/// carry the committed `currently_locked` + `live_supply`) — with
/// `receipt.live_supply <= receipt.currently_locked`. See the boot-seed note in
/// `install_recorder` for why the node does not yet drive this in-process (no
/// hosted relayer loop) and what full coverage requires.
pub fn set_bridge_conservation_ok(ok: bool) {
    gauge!("dregg_bridge_conservation_ok").set(if ok { 1.0 } else { 0.0 });
}

// ─── Protocol structure gauges (receipt chain · blocklace DAG · mempool) ──────

/// Set the current length of this node's receipt chain (the append-only
/// per-turn receipt log). Emitted after each successful `append_receipt`.
pub fn set_receipt_chain_length(n: f64) {
    gauge!("dregg_receipt_chain_length").set(n);
}

/// Set the blocklace DAG depth: the maximum round across the current per-creator
/// tips (how far the lace has advanced).
pub fn set_blocklace_depth(d: f64) {
    gauge!("dregg_blocklace_depth").set(d);
}

/// Set the blocklace frontier width: the number of current per-creator tip
/// blocks (the DAG heads), bounded by committee size.
pub fn set_blocklace_frontier(w: f64) {
    gauge!("dregg_blocklace_frontier").set(w);
}

/// Set the mempool depth: turns/payloads queued but not yet drained into a
/// produced block (the `pending_payloads` backlog awaiting inclusion).
pub fn set_mempool_pending(n: f64) {
    gauge!("dregg_mempool_pending").set(n);
}

/// Increment a per-validator finalization-vote counter. Bumped at the same site
/// as `set_validator_last_seen`, so a dashboard derives each validator's
/// vote-share as `votes / sum(votes)`. `voter` is the short hex key tag; label
/// cardinality is bounded by committee size.
pub fn inc_validator_votes(voter: &str) {
    counter!("dregg_validator_votes_total", "voter" => voter.to_owned()).increment(1);
}

// ─── Security counters (the Security dashboard's exploitation-attempt detector) ─
//
// `dregg_turns_rejected_total` counts turns the executor REFUSED
// (`TurnResult::Rejected`). `dregg_auth_failures_total` and
// `dregg_cap_refusals_total` are the subset of those refusals that were a
// credential/authorization-gate refusal or a capability-gate (CAP path) refusal
// respectively — classified from the `TurnError` via
// `dregg_turn::TurnError::refusal_class`. A rising rate (especially post
// red-team) is a live signal that something is probing the gates.

/// A credential / authorization-gate refusal was raised.
pub fn inc_auth_failure() {
    counter!("dregg_auth_failures_total").increment(1);
}

/// A capability-gate refusal (the CAP path) was raised.
pub fn inc_cap_refusal() {
    counter!("dregg_cap_refusals_total").increment(1);
}

/// A sandbox/exec deny-by-default refusal was raised.
///
/// NOTE: the default-deny sandbox lives in the DreggNet `exec` crate (a separate
/// process with no Prometheus surface), so on the node this series stays at 0
/// today — it is registered here so the Security dashboard panel renders, and so
/// the helper exists for the day the exec plane exports its own metrics.
pub fn inc_sandbox_denial() {
    counter!("dregg_sandbox_denials_total").increment(1);
}

/// Record a refused turn for the Security dashboard: always bumps
/// `dregg_turns_rejected_total`, then bumps the auth / cap sub-counter the
/// `TurnError` classifies into. Call this at every `TurnResult::Rejected` site.
pub fn note_turn_rejected(reason: &dregg_turn::TurnError) {
    counter!("dregg_turns_rejected_total").increment(1);
    match reason.refusal_class() {
        dregg_turn::RefusalClass::Auth => inc_auth_failure(),
        dregg_turn::RefusalClass::Capability => inc_cap_refusal(),
        dregg_turn::RefusalClass::Other => {}
    }
}

// ─── Consensus signals (per-validator health + finality latency) ──────────────
//
// Finality latency is the wall-clock from the moment this node FIRST records a
// finalization vote for a block (it begins gathering the quorum) to the moment a
// quorum of distinct signed votes is reached (consensus-wide Attested). The
// per-block start instant is held in a small bounded map; an entry that never
// reaches quorum is dropped when the map is trimmed.

/// Per-block first-vote instant, keyed by block id. Bounded; trimmed wholesale
/// if it grows past the cap (stale, never-finalized entries).
static FINALITY_T0: OnceLock<Mutex<HashMap<[u8; 32], Instant>>> = OnceLock::new();

fn finality_t0() -> &'static Mutex<HashMap<[u8; 32], Instant>> {
    FINALITY_T0.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Mark the start of the local quorum-gathering window for `block_id` (the first
/// finalization vote this node recorded for it). Idempotent per block.
pub fn mark_block_voting_started(block_id: [u8; 32]) {
    let mut m = finality_t0().lock().unwrap_or_else(|p| p.into_inner());
    // Trim if a flood of never-finalized blocks accumulates (bounded memory).
    if m.len() > 8192 {
        m.clear();
    }
    m.entry(block_id).or_insert_with(Instant::now);
}

/// Record the finality latency for `block_id` (first vote → quorum) into the
/// `dregg_consensus_finality_latency_seconds` histogram. No-op if no start was
/// marked (e.g. a single-vote quorum where this node never opened a window).
pub fn record_finality_latency(block_id: &[u8; 32]) {
    let t0 = finality_t0()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .remove(block_id);
    if let Some(t0) = t0 {
        histogram!("dregg_consensus_finality_latency_seconds").record(t0.elapsed().as_secs_f64());
    }
}

/// Set the last-seen unix timestamp (seconds) for a finalization-vote signer.
/// `voter` is a short hex tag of the validator key; the label cardinality is
/// bounded by the committee size. Feeds the Consensus dashboard's per-validator
/// liveness.
pub fn set_validator_last_seen(voter: &str) {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs_f64())
        .unwrap_or(0.0);
    gauge!("dregg_validator_last_seen_timestamp_seconds", "voter" => voter.to_owned()).set(now);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `BridgeConservationBreach` page fires on
    /// `min(dregg_bridge_conservation_ok) == 0`, so the series MUST exist on
    /// `/metrics` (the wound: it did not) and MUST render 0 on a breach. This
    /// exercises the exposition surface end-to-end: install the recorder (which
    /// boot-seeds the healthy 1), drive the setter to a breach and back, and read
    /// it out of the rendered text the `/metrics` handler serves. Only this test
    /// writes this gauge, so its value is stable across the shared process-global
    /// recorder.
    #[test]
    fn bridge_conservation_gauge_renders_and_flips() {
        let handle = install_recorder();

        // Boot seed materialized the series at the healthy value.
        assert!(
            handle.render().contains("dregg_bridge_conservation_ok"),
            "conservation series must exist on /metrics from boot"
        );

        // A breach renders as 0 — the value the page keys on.
        set_bridge_conservation_ok(false);
        assert!(
            handle
                .render()
                .lines()
                .any(|l| l.trim() == "dregg_bridge_conservation_ok 0"),
            "breach must render dregg_bridge_conservation_ok 0"
        );

        // Recovery renders as 1 (conserving).
        set_bridge_conservation_ok(true);
        assert!(
            handle
                .render()
                .lines()
                .any(|l| l.trim() == "dregg_bridge_conservation_ok 1"),
            "conserving must render dregg_bridge_conservation_ok 1"
        );
    }
}
