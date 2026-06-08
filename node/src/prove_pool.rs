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
//! path's job is to make sure the committed state is *correct*; it does that by
//! DIRECTLY revalidating the witness (re-executing the verified executor and/or
//! FRI-free constraint-checking the trace via
//! `effect_vm_p3_full_air::bespoke_air_accepts` — sub-millisecond, see the
//! bench), then committing and returning a fast `Tentative` / "proof pending"
//! ack. The full STARK proof — the attestation layer light-clients and
//! cross-trust peers consume — is generated **asynchronously** by this pool,
//! OFF the write lock, and attached to the receipt when it lands.
//!
//! Soundness is preserved because the witness is directly CHECKED at commit
//! time (no trust): the trace satisfies the AIR constraints (or the verified
//! executor re-derives the identical post-state) before the state mutation is
//! kept. The async proof never gates the commit; it only enriches the receipt
//! with the succinct attestation.
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

use dregg_circuit::field::BabyBear;
use tokio::sync::mpsc;

use crate::state::NodeState;

/// A single async proving job: the FRI-free-revalidated witness + the receipt
/// hash to attach the resulting `WitnessedReceipt` to once proving completes.
pub struct ProveJob {
    /// Base Effect-VM trace (already FRI-free revalidated on the commit path).
    pub trace: Vec<Vec<BabyBear>>,
    /// Public inputs the prover binds (turn-hash / commitment PIs already set).
    pub public_inputs: Vec<BabyBear>,
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
        match self.tx.try_send(job) {
            Ok(()) => true,
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
        trace,
        public_inputs,
        receipt,
        receipt_hash,
        turn_hash_hex,
    } = job;

    let started = std::time::Instant::now();

    // Proving is CPU-bound: run it on the blocking pool so it never stalls the
    // async runtime's I/O workers. CRUCIALLY, no state lock is held here.
    let prove_result = tokio::task::spawn_blocking(move || {
        let air = dregg_circuit::effect_vm::EffectVmAir::new(trace.len());
        let proof = dregg_circuit::stark::try_prove(&air, &trace, &public_inputs)
            .map_err(|e| format!("async Effect VM proof generation failed: {e}"))?;
        let proof_bytes = dregg_circuit::stark::proof_to_bytes(&proof);
        let public_inputs_u32: Vec<u32> = public_inputs.iter().map(|f| f.as_u32()).collect();
        let witnessed = dregg_turn::WitnessedReceipt::from_components(
            receipt,
            proof_bytes,
            public_inputs_u32,
            Some(trace.as_slice()),
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

    tracing::debug!(
        worker_id,
        turn_hash = %turn_hash_hex,
        elapsed_ms = started.elapsed().as_millis(),
        "async proof attached to committed receipt"
    );
}
