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
            // The post-finalization rejection breakdown. Seeded with the
            // sentinel label so `dregg_finalized_turns_rejected_total` EXISTS at
            // boot: an alert on it is then ARMED rather than matching no series,
            // which is the difference between a detector and a wish. Label shape
            // MATCHES the real emit site (`note_finalized_payload_rejected`).
            counter!("dregg_finalized_turns_rejected_total", "reason" => "none").increment(0);
            // Pre-seed the protocol-activity series the same way so the protocol
            // dashboard renders "0" from boot rather than "No data" on an idle
            // node. The label shapes MATCH the real emit sites: `inc_turns_submitted`
            // is unlabelled, `inc_proofs_verified` carries `result` (seeded with the
            // representative "valid" value it emits on a passing verification).
            counter!("dregg_turns_submitted_total").increment(0);
            counter!("dregg_proofs_verified_total", "result" => "valid").increment(0);
            gauge!("dregg_block_height").set(0.0);
            // Pre-seed the CONSENSUS-ORDER PROVENANCE series at 0, one per source, so an alert
            // on "a poll finalized over an UN-VERIFIED order" (or on a budget miss) is ARMED
            // from boot rather than matching no series. This is the whole point of the tally:
            // the degrade it watches for is one that used to announce itself in a single WARN
            // line and then be served silently from cache forever. Label shape MATCHES the real
            // emit site (`record_consensus_order_source`).
            for source in ORDER_SOURCE_LABELS {
                counter!("dregg_consensus_order_polls_total", "source" => source).increment(0);
            }
            counter!("dregg_consensus_order_over_budget_total").increment(0);
            // Pre-seed the ROOT-DISAGREEMENT series at 0 so a ledger fork is a
            // detector going RED from a visible green, not a series appearing out
            // of "No data" — the 2026-08 3-vs-1 root fork ran 27 h with every
            // instrument reading healthy precisely because no armed series
            // existed for it. `verified_total > 0` is the real alarm (both sides
            // hybrid-signed); `unverified_claim_total` is attacker-inflatable
            // noise that names nobody and must never page anyone by itself.
            counter!("dregg_finalization_root_disagreement_verified_total").increment(0);
            counter!("dregg_finalization_root_disagreement_unverified_claim_total").increment(0);
            gauge!("dregg_finalization_root_split_blocks").set(0.0);
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
            // Pre-seed the PQ-PROVENANCE series for all six post-quantum directions so the
            // panel renders a live "0 unaudited answers" from boot rather than "No data",
            // and so `dregg_pq_unaudited_crate_answers_total > 0` is an ARMED alert rather
            // than one matching no series. See `publish_pq_provenance`.
            for site in dregg_pq::PqSite::ALL {
                gauge!("dregg_pq_verified_core_answers_total", "site" => site.label()).set(0.0);
                gauge!("dregg_pq_unaudited_crate_answers_total", "site" => site.label()).set(0.0);
                gauge!("dregg_pq_verified_core_faults_total", "site" => site.label()).set(0.0);
            }
            handle
        })
        .clone()
}

/// PUBLISH THE PQ PROVENANCE: for each of the six post-quantum directions, how many operations
/// were answered by the Lean-VERIFIED core, how many by the UNAUDITED `fips204`/`ml-kem` crate,
/// and how many refused because an installed core FAULTED.
///
/// ⚑ WHY THIS EXISTS. Until now the only signal that unaudited PQ was live in a process was ONE
/// `warn!` at boot per install site (`lib.rs`, the `ExportAbsent` arms) plus one process-global
/// stderr line from `dregg_pq::audit`. That tells an operator that an export was missing at
/// startup; it does NOT tell them which implementation answered a given verification, or that
/// the answer changed, or how many times. A non-zero
/// `dregg_pq_unaudited_crate_answers_total{site="ml_dsa_verify"}` means the ACCEPT/REJECT
/// AUTHORITY behind ~10 surfaces (token/revocation, lightclient, cell-crypto, wire,
/// turn/authorize, captp, blocklace/pq) is the third-party crate RIGHT NOW — a SAFETY alarm, not
/// a liveness one, and the only site of the six for which that is true
/// (`PqSite::is_accept_reject_gate`). The other five are provenance: a keygen has no verdict to
/// fail open on.
///
/// GAUGES, not counters, deliberately: the authoritative totals live in `dregg-pq`'s own atomics
/// (it is a LIGHT leaf and cannot depend on a metrics recorder), so this mirrors an absolute
/// value rather than emitting deltas that would double-count on every scrape.
pub fn publish_pq_provenance() {
    for (site, verified, unaudited, faults) in dregg_pq::pq_provenance() {
        gauge!("dregg_pq_verified_core_answers_total", "site" => site.label()).set(verified as f64);
        gauge!("dregg_pq_unaudited_crate_answers_total", "site" => site.label())
            .set(unaudited as f64);
        gauge!("dregg_pq_verified_core_faults_total", "site" => site.label()).set(faults as f64);
    }
}

/// Axum handler for GET /metrics.
pub async fn metrics_handler(
    axum::extract::State(handle): axum::extract::State<PrometheusHandle>,
) -> String {
    // Refresh the pull-time mirrors before rendering, so a scrape always reflects the CURRENT
    // PQ provenance rather than whatever it was at the last push.
    publish_pq_provenance();
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

// ─── Finalization-root disagreement — DETECTION, NOT ATTRIBUTION ─────────────
//
// The 2026-08 ledger fork was a 3-vs-1 disagreement between HONEST nodes about
// what was COMPUTED (the finalized `merkle_root`), not about what was said; no
// component compared the two roots and nothing fired
// (`docs/reference/READING-ACCOUNTABILITY-2026-08-08.md`). These series make
// that state loud. They deliberately carry NO member label: a verified split
// does not identify a culprit (a diverging executor is not Byzantine under
// `byz(B)` — correctly), and an unverified claim must never turn into an
// accusation. The WARN log line names the verified signers on each side; the
// metric only counts.

/// A hybrid-VERIFIED finalization vote attests a different
/// `(merkle_root, receipt_stream_root)` pair than another hybrid-verified
/// committee vote for the same block. Emitted only after `verify_hybrid`
/// (ed25519 ∧ ML-DSA) in `finalization_votes::VoteCollector::record`, so both
/// sides of every counted disagreement are cryptographically signed — forging
/// this signal requires forging a hybrid signature. Non-zero means two
/// committee members REALLY computed/attested different finalized states:
/// serious, and exactly what the 3-vs-1 fork looked like.
pub fn inc_finalization_root_disagreement_verified() {
    counter!("dregg_finalization_root_disagreement_verified_total").increment(1);
}

/// Vote BYTES whose claimed pair disagrees with a counted verified vote, where
/// the claim's signature was NOT checked (the inert-repeat fast path) or FAILED
/// (`verify_hybrid` refused). This is a claim, not evidence: any on-path
/// adversary can mint these from chosen bytes at zero cost, so the rate is
/// attacker-controllable noise, it names no member, and nothing is retained.
/// It exists so "somebody is injecting conflicting-vote bytes" is visible
/// without ever becoming an accusation.
pub fn inc_finalization_root_disagreement_unverified_claim() {
    counter!("dregg_finalization_root_disagreement_unverified_claim_total").increment(1);
}

/// Gauge: the number of blocks whose VERIFIED vote tally currently holds
/// conflicting attested pairs (`VoteCollector::verified_root_split_count`).
/// Sticky per block for the collector's lifetime — a real divergence stays
/// visible even after a majority root reaches quorum (the fork DID finalize
/// 3-vs-1; the dissent must not vanish into the quorum).
pub fn set_finalization_root_split_blocks(n: f64) {
    gauge!("dregg_finalization_root_split_blocks").set(n);
}

// ─── THE VERIFIED-ORDER BUDGET — WHICH order decided each finality poll ──────────────────────
//
// The node's claim is that it "finalizes over the VERIFIED ordering". That claim is CONDITIONAL
// ON A WALL-CLOCK BUDGET: `blocklace_sync::verified_order_ffi_timeout()` (default 2500 ms) bounds
// the verified `dregg_tau_order` FFI, and a poll that misses it does NOT finalize over the
// verified order — it runs the un-verified Rust `ordering::tau` twin (only under
// `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`) or finalizes nothing.
//
// Until now the ONLY trace of that degrade was a WARN line, which (a) is not countable, (b) is
// lost on a node whose log level is above WARN or whose logs nobody reads, and — the reason this
// exists — (c) fires ONCE and then goes quiet, because the poll STORES its order in the cross-poll
// cache and every later fingerprint-matching poll takes the silent "cache HIT" path. A degrade
// that announces itself once and is then served silently forever is not a detected degrade.
//
// So provenance is now a first-class, countable property of every poll, it RIDES THE CACHE (a
// cached un-verified order stays un-verified on every hit), and `/status` reports it.

/// WHICH order decided one finality poll. Recorded on EVERY poll that selects an order, so
/// `verified + unverified + failed_closed` is the total poll count and the ratio is readable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConsensusOrderSource {
    /// The verified Lean `dregg_tau_order` FFI ran WITHIN the per-poll budget and its order
    /// decided this poll. **This is the only value under which "this poll finalized over the
    /// verified ordering" is true without qualification.**
    VerifiedFfi,
    /// A cross-poll cache HIT whose cached order was itself produced by the verified FFI. The
    /// order is the verified one (the cache is keyed on the finalized order, so a hit means the
    /// finalized order did not change), so this still counts as verified.
    VerifiedCached,
    /// The verified FFI EXCEEDED THE PER-POLL BUDGET and the un-verified Rust `ordering::tau`
    /// twin decided this poll. Reachable only under `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` (or a
    /// build with no verified archive at all).
    UnverifiedOverBudget,
    /// The verified export was unavailable / returned ERR / the blocking task died, and the
    /// un-verified Rust twin decided this poll.
    UnverifiedUnavailable,
    /// A cache HIT whose cached order was an UN-VERIFIED Rust order, stored by an earlier
    /// over-budget or unavailable poll. **Verified-ness does not come back on a cache hit** —
    /// this is the silent-forever path the WARN line could not see.
    UnverifiedCached,
    /// No verified order this poll and the Rust twin is FORBIDDEN (a Lean-linked node without
    /// the escape): the poll FINALIZED NOTHING. A liveness alarm, not a safety one.
    FailedClosed,
}

impl ConsensusOrderSource {
    /// The Prometheus label / `/status` string for this source. Stable wire spelling.
    pub fn label(self) -> &'static str {
        match self {
            Self::VerifiedFfi => "verified_ffi",
            Self::VerifiedCached => "verified_cached",
            Self::UnverifiedOverBudget => "unverified_over_budget",
            Self::UnverifiedUnavailable => "unverified_unavailable",
            Self::UnverifiedCached => "unverified_cached",
            Self::FailedClosed => "failed_closed",
        }
    }

    /// Whether a poll decided by this source finalized over the VERIFIED Lean order. This is the
    /// predicate the honesty of the whole claim rests on; it is written once, here.
    pub fn is_verified(self) -> bool {
        matches!(self, Self::VerifiedFfi | Self::VerifiedCached)
    }
}

static ORDER_POLLS_VERIFIED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static ORDER_POLLS_UNVERIFIED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static ORDER_POLLS_FAILED_CLOSED: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
static ORDER_POLLS_OVER_BUDGET: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// The `label()` of the most recent poll's source, as a discriminant index into
/// [`ORDER_SOURCE_LABELS`]. `u8::MAX` = no poll has selected an order yet.
static ORDER_LAST_SOURCE: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(u8::MAX);

const ORDER_SOURCE_LABELS: [&str; 6] = [
    "verified_ffi",
    "verified_cached",
    "unverified_over_budget",
    "unverified_unavailable",
    "unverified_cached",
    "failed_closed",
];

fn order_source_index(src: ConsensusOrderSource) -> u8 {
    match src {
        ConsensusOrderSource::VerifiedFfi => 0,
        ConsensusOrderSource::VerifiedCached => 1,
        ConsensusOrderSource::UnverifiedOverBudget => 2,
        ConsensusOrderSource::UnverifiedUnavailable => 3,
        ConsensusOrderSource::UnverifiedCached => 4,
        ConsensusOrderSource::FailedClosed => 5,
    }
}

/// The consensus-order provenance tally, readable back for `/status` (the Prometheus recorder is
/// write-only, so the same facts are kept in process-global atomics).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConsensusOrderTally {
    /// Polls decided by the VERIFIED Lean order (fresh FFI or a verified-provenance cache hit).
    pub verified_polls: u64,
    /// Polls decided by the UN-VERIFIED Rust `ordering::tau` twin, for any reason.
    pub unverified_polls: u64,
    /// Polls that finalized NOTHING because no verified order was available and the twin was
    /// forbidden.
    pub failed_closed_polls: u64,
    /// Of all polls, how many ran the verified FFI and BLEW THE PER-POLL BUDGET. This is the
    /// number that says whether the budget is a real constraint on this node.
    pub over_budget_polls: u64,
    /// The source of the most recent poll, or `"none"` before the first.
    pub last_source: &'static str,
}

impl ConsensusOrderTally {
    /// Whether EVERY poll so far finalized over the verified order — i.e. whether the unqualified
    /// claim "this node finalizes over the verified ordering" is currently true of this process.
    pub fn fully_verified(self) -> bool {
        self.unverified_polls == 0 && self.failed_closed_polls == 0
    }
}

/// Record WHICH order decided one finality poll. Called on EVERY order selection in
/// `poll_finalized_blocks` — including the cache-hit paths, which is the point: a cached
/// un-verified order is recorded as un-verified on every hit it serves.
///
/// `over_budget` is passed separately because it is orthogonal to the source: a poll can blow the
/// budget and STILL end up `FailedClosed` (a Lean-linked node without the escape), and that node
/// needs the budget-miss visible even though no un-verified order ever ran on it.
pub fn record_consensus_order_source(src: ConsensusOrderSource, over_budget: bool) {
    use std::sync::atomic::Ordering::Relaxed;
    counter!("dregg_consensus_order_polls_total", "source" => src.label()).increment(1);
    if src.is_verified() {
        ORDER_POLLS_VERIFIED.fetch_add(1, Relaxed);
    } else if src == ConsensusOrderSource::FailedClosed {
        ORDER_POLLS_FAILED_CLOSED.fetch_add(1, Relaxed);
    } else {
        ORDER_POLLS_UNVERIFIED.fetch_add(1, Relaxed);
    }
    if over_budget {
        counter!("dregg_consensus_order_over_budget_total").increment(1);
        ORDER_POLLS_OVER_BUDGET.fetch_add(1, Relaxed);
    }
    ORDER_LAST_SOURCE.store(order_source_index(src), Relaxed);
}

/// Read back the consensus-order provenance tally for `/status`.
pub fn consensus_order_tally() -> ConsensusOrderTally {
    use std::sync::atomic::Ordering::Relaxed;
    let last = ORDER_LAST_SOURCE.load(Relaxed);
    ConsensusOrderTally {
        verified_polls: ORDER_POLLS_VERIFIED.load(Relaxed),
        unverified_polls: ORDER_POLLS_UNVERIFIED.load(Relaxed),
        failed_closed_polls: ORDER_POLLS_FAILED_CLOSED.load(Relaxed),
        over_budget_polls: ORDER_POLLS_OVER_BUDGET.load(Relaxed),
        last_source: ORDER_SOURCE_LABELS
            .get(last as usize)
            .copied()
            .unwrap_or("none"),
    }
}

/// Increment the FINALITY-GATE-UNAVAILABLE REFUSAL counter: a poll declined to advance finality
/// because the verified `dregg_blocklace_finalize` belt projection was ARMED (the poll was about to
/// advance over an order the verified Lean rule did not produce) and could not answer, with no
/// declared bypass. This is the fail-CLOSED disposition that replaced this site's fail-OPEN, and it
/// is deliberately a SEPARATE series from `dregg_consensus_differential_divergence_total` and from
/// any per-block refusal: no block was judged invalid here — the gate could not answer. A non-zero
/// rate means finality is HALTED pending a verified archive (or a deliberate
/// `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`), which is a liveness alarm, not a safety one.
pub fn inc_finality_gate_unavailable_refusals() {
    counter!("dregg_finality_gate_unavailable_refusals_total").increment(1);
}

/// Increment the 2PC-COORDINATOR-DECISION-GATE-UNAVAILABLE REFUSAL counter: a vote's authoritative
/// verdict was forced to `Decision::Abort` because the verified `dregg_coord_2pc_decide` gate
/// (`TwoPhaseCommit.evaluate`) was ARMED — the export is linked and the tally could reach a terminal
/// verdict — and could not answer, with no declared bypass. This is the fail-CLOSED disposition that
/// replaced this site's transitive fall-through to the un-verified Rust `Coordinator` sibling, and it
/// is deliberately a SEPARATE series from every "the verified rule said Abort" outcome: no vote was
/// rejected here — the gate could not answer. A non-zero rate means atomic proposals are being torn
/// down pending a verified archive (or a deliberate `DREGG_COORD_DECISION_GATE=0`), which is a
/// liveness alarm, not a safety one. See `crate::coord_gate::coord_decision_disposition`.
pub fn inc_coord_decision_gate_unavailable_refusals() {
    counter!("dregg_coord_decision_gate_unavailable_refusals_total").increment(1);
}

/// Increment the STRAND-ADMISSION-GATE-UNAVAILABLE REFUSAL counter: a participant projection refused
/// to hand `tau` the raw candidate list because no F-4 admission rule decided it — the operator set
/// `DREGG_STRAND_ADMISSION_GATE=0` and `DREGG_REQUIRE_LEAN=1` REVOKED that bypass. This is the
/// fail-CLOSED disposition that replaced this site's unregistered, unlogged `return candidates.to_vec()`,
/// and it is deliberately a SEPARATE series from every "the F-4 rule dropped this strand" outcome: no
/// strand was rejected here — no rule had decided the set. A non-zero rate means a node is running
/// with two contradictory environment variables and the gate is winning, which is a CONFIGURATION
/// alarm, not a safety one. See `crate::strand_admission_gate::strand_admission_disposition`.
pub fn inc_strand_admission_gate_unavailable_refusals() {
    counter!("dregg_strand_admission_gate_unavailable_refusals_total").increment(1);
}

/// Increment the BEARER-AUTHORITY-LEG REFUSAL counter: a finalized bearer-delegated turn published NO
/// full-turn proof because its delegator's pre-state capability root could not be resolved, so the
/// AUTHORITY leg could not be bound and the site refused to attach a v1 proof that silently omits it.
/// Deliberately a SEPARATE series from `Prove`/`Verify` failures: nothing was rejected and no proof
/// failed to verify — the authority binding was unbuildable, so the attestation is withheld rather
/// than under-claimed. The turn itself still COMMITS (the executor enforced the delegation
/// independently); a non-zero rate is an ATTESTATION-COVERAGE alarm, not a safety one. See
/// `crate::blocklace_sync::bearer_authority_disposition`.
pub fn inc_bearer_authority_leg_refusals() {
    counter!("dregg_bearer_authority_leg_refusals_total").increment(1);
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

/// The label value used for a rejection whose reason code is not canonical.
///
/// Reason codes are `&'static str` constants and error `code()`s today, and
/// `FinalizedPayloadRejectionRecord::decode_authenticated` already refuses a row
/// whose code is not `[a-z0-9-]{1,128}`. This is the metric-side twin of that
/// refusal: a label is unbounded-cardinality-sensitive in a way a durable row is
/// not, so anything off-shape collapses to one bucket instead of minting a
/// series per distinct string.
const NON_CANONICAL_REASON_LABEL: &str = "non-canonical";

/// Clamp a rejection reason code to a safe Prometheus label value.
fn rejection_reason_label(reason_code: &str) -> String {
    let canonical = !reason_code.is_empty()
        && reason_code.len() <= 64
        && reason_code
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-');
    if canonical {
        reason_code.to_owned()
    } else {
        NON_CANONICAL_REASON_LABEL.to_owned()
    }
}

/// Record a DETERMINISTIC POST-FINALIZATION rejection: consensus finalized a
/// payload and the application predicate refused it before any mutation.
///
/// ⚑ WHY THIS EXISTS. `note_turn_rejected` is reachable only where a
/// `dregg_turn::TurnError` exists — i.e. from the *executor*, on the ingress
/// paths in `api.rs`. The post-finalization refusals funnel through
/// `blocklace_sync::persist_finalized_payload_rejection` instead, which carries a
/// stable reason CODE and no `TurnError`, and so bumped NOTHING. Measured on a
/// live 4-node federation: two faucet turns each returned
/// `{"success":true,"turn_hash":…}`, were unanimously and CORRECTLY refused by all
/// four nodes for `receipt-chain-mismatch`, were durably recorded on all four —
/// and `dregg_turns_rejected_total` read 0 everywhere. The metric named for
/// exactly this did not count the path.
///
/// The consensus behaviour is right; this is the reporting. Both series move:
/// `dregg_turns_rejected_total` so the flat total finally includes the
/// post-finalization refusals, and `dregg_finalized_turns_rejected_total` with a
/// `reason` label for the breakdown. They are separate NAMES on purpose — one
/// metric family must not carry both a bare and a labelled series, or a naive
/// `sum()` double counts.
///
/// Call this exactly ONCE per newly persisted rejection row. The idempotent
/// re-observation of an already-recorded rejection (crash replay, duplicate
/// delivery) must NOT bump it: a counter that climbs on restart is a counter of
/// restarts.
pub fn note_finalized_payload_rejected(reason_code: &str) {
    counter!("dregg_turns_rejected_total").increment(1);
    counter!(
        "dregg_finalized_turns_rejected_total",
        "reason" => rejection_reason_label(reason_code),
    )
    .increment(1);
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
