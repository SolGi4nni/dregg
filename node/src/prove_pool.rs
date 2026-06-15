//! Async STARK-proving task pool — moves full-turn proof generation OFF the
//! request/commit path (red-team finding F-DOS-1, task #109).
//!
//! ## The problem this closes
//!
//! The submit/commit handlers used to run the full `p3-batch-stark` prover
//! (`stark::try_prove`, ~750 ms per turn — see
//! `circuit/tests/turn_revalidation_vs_prove.rs`) **inline, while holding the
//! global `state.write()` lock**. A single submitted turn therefore pinned a
//! worker in proving and froze the whole runtime behind the write lock: on the
//! public devnet the node stopped producing blocks for ~5 minutes and served 0
//! bytes until a `systemctl restart` (red-team `MULTINODE-BYZANTINE-FINDINGS`
//! F-DOS-1). The STARK proof was a **per-turn commit gate** it never needed to
//! be.
//!
//! ## The fix (soundness-preserving)
//!
//! Proofs are *additive attestation*, not a per-step soundness gate. The commit
//! path's job is to make sure the committed state is *correct*; the authoritative
//! executor (`execute_via_producer → Committed`) already validated the turn and
//! committed the new state BEFORE this pool ever runs. The commit therefore needs
//! no inline STARK proving or FRI-free re-check — the executor IS the soundness
//! boundary. The full STARK proof — the attestation layer light-clients and
//! cross-trust peers consume — is generated **asynchronously** by this pool,
//! OFF the write lock, and attached to the receipt when it lands.
//!
//! ## The ROTATED leg (PATH-PRESERVE Phase 5b cutover)
//!
//! This pool no longer proves a bespoke v1 hand-AIR STARK over a trace re-derived
//! from pre-state. It proves the SAME composed `FullTurnProof` the finalized
//! commit path proves (`turn_proving::prove_and_verify_finalized_turn`): the
//! effect-vm leg goes through the LEAN-emitted ROTATED descriptor (a multi-table
//! `Ir2BatchProof`) when the caller threaded the per-turn rotation witness from
//! the REAL before/after `dregg_cell::Cell`s, and self-verifies before it is
//! attached. Under `not(recursion)` (or when the cell is not a rotatable cohort
//! member) the byte-identical v1 leg runs INSIDE `prove_and_verify_finalized_turn`
//! — this pool never touches the v1 effect-vm hand-AIR.
//!
//! Soundness is preserved because the executor already validated and committed
//! the state; the async proof only enriches the receipt with the succinct,
//! self-verified attestation.
//!
//! ## Pool shape
//!
//! A bounded MPSC queue feeds a fixed set of `spawn_blocking` workers (proving
//! is CPU-bound, so it must run on the blocking pool, never an async worker).
//! When the queue is full the job is dropped with a logged warning — the commit
//! has ALREADY happened and is sound; a dropped attestation is a *liveness*
//! degradation of the proof-enrichment layer, never a *safety* problem, and is
//! self-healing (a later finalized-turn prove pass / verifier re-request can
//! regenerate it). This bounds memory and CPU under a proving flood instead of
//! letting it wedge the node — the exact failure mode F-DOS-1 described.

use std::sync::Arc;

use dregg_types::CellId;
use tokio::sync::mpsc;

use crate::state::NodeState;

/// A single async proving job: everything `prove_and_verify_finalized_turn` needs
/// to (re-)build + self-verify the committed turn's composed `FullTurnProof` off
/// the lock, plus the receipt hash to attach the resulting `WitnessedReceipt` to
/// once proving completes. The executor already validated + committed this turn;
/// the proof is additive attestation (see module docs).
pub struct ProveJob {
    /// The actor cell whose whole-turn transition is proven.
    pub agent: CellId,
    /// The actor cell's balance captured BEFORE the executor mutated the ledger
    /// (the pre-state the proof's `old_commit` binds to).
    pub pre_balance: u64,
    /// The actor cell's nonce captured before execution.
    pub pre_nonce: u64,
    /// The turn's effects (the same `turn.call_forest.total_effects()` the
    /// executor ran), marshalled onto the actor inside the prover.
    pub effects: Vec<dregg_turn::Effect>,
    /// The turn hash the proof is bound to (replay binding).
    pub turn_hash: [u8; 32],
    /// The per-turn ROTATION producer witness built from the REAL before/after
    /// actor cells. `Some` ⇒ the effect-vm leg proves through the rotated
    /// descriptor; `None` ⇒ the byte-identical v1 leg runs inside the prover
    /// (a non-cohort cell, or `not(recursion)`).
    pub rotation: Option<dregg_sdk::RotationTurnWitness>,
    /// The committed receipt the proof attests (moved into the WitnessedReceipt).
    pub receipt: dregg_turn::TurnReceipt,
    /// Receipt hash key under which to store the proven WitnessedReceipt.
    pub receipt_hash: [u8; 32],
    /// Hex turn hash, for log correlation only.
    pub turn_hash_hex: String,
}

/// Handle to the async prove pool. Cheaply cloneable (wraps an mpsc sender).
#[derive(Clone)]
pub struct ProvePool {
    tx: mpsc::Sender<ProveJob>,
}

/// Default number of concurrent proving workers. Proving is CPU-bound; we keep
/// this small so a proving flood cannot starve the async runtime's blocking
/// pool of threads needed for other I/O. Override with `DREGG_PROVE_WORKERS`.
const DEFAULT_PROVE_WORKERS: usize = 2;

/// Bounded job-queue depth. Past this, new jobs are dropped (the commit already
/// succeeded — see module docs). Override with `DREGG_PROVE_QUEUE_DEPTH`.
const DEFAULT_QUEUE_DEPTH: usize = 256;

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(default)
}

impl ProvePool {
    /// Spawn the worker set and return a handle. `state` is captured so a
    /// completed proof can be stored back under its receipt hash (a brief lock
    /// acquisition for the `push_witnessed_receipt` write only — never held
    /// across the proving itself).
    pub fn spawn(state: NodeState) -> Self {
        let workers = env_usize("DREGG_PROVE_WORKERS", DEFAULT_PROVE_WORKERS);
        let depth = env_usize("DREGG_PROVE_QUEUE_DEPTH", DEFAULT_QUEUE_DEPTH);
        let (tx, rx) = mpsc::channel::<ProveJob>(depth);
        let rx = Arc::new(tokio::sync::Mutex::new(rx));

        for worker_id in 0..workers {
            let rx = rx.clone();
            let state = state.clone();
            tokio::spawn(async move {
                loop {
                    // Take the next job. The receiver mutex is held only across
                    // the `recv().await`, never across proving.
                    let job = {
                        let mut guard = rx.lock().await;
                        guard.recv().await
                    };
                    let Some(job) = job else {
                        tracing::debug!(worker_id, "prove pool channel closed; worker exiting");
                        return;
                    };
                    run_job(worker_id, job, &state).await;
                }
            });
        }

        tracing::info!(
            workers,
            queue_depth = depth,
            "async STARK prove pool started (proving moved OFF the commit/request path)"
        );
        Self { tx }
    }

    /// Enqueue a proving job. Returns `true` if the job was accepted into the
    /// queue, `false` if the queue is full (job dropped — the commit is already
    /// sound; see module docs). Never blocks the caller.
    pub fn enqueue(&self, job: ProveJob) -> bool {
        let turn_hash = job.turn_hash_hex.clone();
        match self.tx.try_send(job) {
            Ok(()) => {
                // Loud (info-level) job-lifecycle line: the pool's only other
                // success logs were debug-level, so a healthy pipeline looked
                // identical to a dead one at the default RUST_LOG=info.
                tracing::info!(
                    turn_hash = %turn_hash,
                    "async prove job ENQUEUED (proof attaches to the receipt when it lands)"
                );
                true
            }
            Err(mpsc::error::TrySendError::Full(job)) => {
                crate::metrics::inc_async_proofs_dropped();
                tracing::warn!(
                    turn_hash = %job.turn_hash_hex,
                    "async prove queue full; dropping proof-attestation job (commit already \
                     succeeded + was witness-revalidated — proof can be regenerated later)"
                );
                false
            }
            Err(mpsc::error::TrySendError::Closed(_)) => {
                tracing::error!("async prove pool channel closed; cannot enqueue proof job");
                false
            }
        }
    }
}

/// Run one proving job on the blocking pool, then attach the resulting
/// `WitnessedReceipt` back into state under a brief write-lock acquisition.
async fn run_job(worker_id: usize, job: ProveJob, state: &NodeState) {
    let ProveJob {
        agent,
        pre_balance,
        pre_nonce,
        effects,
        turn_hash,
        rotation,
        receipt,
        receipt_hash,
        turn_hash_hex,
    } = job;

    let started = std::time::Instant::now();

    // Proving is CPU-bound: run it on the blocking pool so it never stalls the
    // async runtime's I/O workers. CRUCIALLY, no state lock is held here.
    //
    // The composed `FullTurnProof` is generated + self-verified by the SAME
    // helper the finalized commit path uses; its effect-vm leg proves through the
    // LEAN-emitted ROTATED descriptor when a rotation witness was threaded (else
    // the byte-identical v1 leg runs inside the helper). The resulting
    // `WitnessedReceipt` is a scope-1 attestation (proof + composed PI): the
    // executor already committed the state, and the inline-trace replay bundle is
    // a v1-only Silver-Vision artifact the rotated leg does not carry.
    let prove_result = tokio::task::spawn_blocking(move || {
        let proven = crate::turn_proving::prove_and_verify_finalized_turn(
            &agent,
            pre_balance,
            pre_nonce,
            &effects,
            turn_hash,
            rotation,
        )
        .map_err(|e| format!("async full-turn proof generation failed: {e}"))?;
        let proof_bytes = proven.proof_bytes().to_vec();
        let public_inputs_u32: Vec<u32> = proven
            .proof
            .composed
            .public_inputs
            .iter()
            .map(|f| f.as_u32())
            .collect();
        let witnessed = dregg_turn::WitnessedReceipt::from_components(
            receipt,
            proof_bytes,
            public_inputs_u32,
            None,
        );
        Ok::<_, String>(witnessed)
    })
    .await;

    let witnessed = match prove_result {
        Ok(Ok(w)) => w,
        Ok(Err(e)) => {
            crate::metrics::inc_async_proofs_failed();
            tracing::warn!(
                worker_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "async proof generation failed; receipt stays committed-but-unattested"
            );
            return;
        }
        Err(join_err) => {
            crate::metrics::inc_async_proofs_failed();
            tracing::warn!(
                worker_id,
                turn_hash = %turn_hash_hex,
                error = %join_err,
                "async proving task panicked/cancelled; receipt stays committed-but-unattested"
            );
            return;
        }
    };

    // Brief write-lock ONLY to store the finished attestation + clear pending.
    {
        let mut s = state.write().await;
        s.push_witnessed_receipt(receipt_hash, witnessed);
        s.clear_proof_pending(&receipt_hash);
    }
    crate::metrics::inc_async_proofs_completed();
    crate::metrics::record_async_proof_duration(started.elapsed().as_secs_f64());

    // Notify subscribers that the attestation for this receipt is now available.
    state.emit(crate::state::NodeEvent::Receipt {
        hash: turn_hash_hex.clone(),
    });

    // Info-level so the live pipeline is visibly healthy: this is the line
    // operators (and the quickstart) watch for after submitting a turn.
    tracing::info!(
        worker_id,
        turn_hash = %turn_hash_hex,
        elapsed_ms = started.elapsed().as_millis(),
        "async proof attached to committed receipt (has_proof flips true)"
    );
}
