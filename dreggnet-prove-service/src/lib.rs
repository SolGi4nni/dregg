//! # The async match-fold proving service — deploy-plan Phase 3.
//!
//! **The whole-match STARK fold runs OFF the player's critical path.** Play is
//! interactive-fast; the fold ([`dreggnet_game_board::prove_match`] →
//! `prove_turn_chain_recursive`) is minutes-to-hours. So a finished match is
//! [`enqueue`](ProveService::enqueue)d — returning a [`JobId`] IMMEDIATELY — and
//! folded on a BACKGROUND WORKER POOL. The player polls
//! [`status`](ProveService::status) (or blocks on [`wait`](ProveService::wait))
//! and, when the job is [`JobStatus::Done`], submits the succinct proof to the
//! proof-carrying board. The UX is:
//!
//! ```text
//!   play (fast) ──▶ enqueue ──▶ [ fold on a worker, GPU-dispatched ] ──▶ rank when Done
//!        │             │                     │                              │
//!    interactive   a JobId,             the ~45-min fold,               a MatchProof
//!    (no fold)     instantly            off the play path            (submit, never moves)
//! ```
//!
//! ## This is the PRODUCTION pool — the per-turn pattern, extended to the match
//!
//! `node/src/prove_pool.rs` moved the ~0.75 s per-TURN attestation off the
//! commit/write-lock path onto a bounded MPSC + a fixed worker set (off-lock,
//! `DREGG_PROVE_WORKERS`/`DREGG_PROVE_QUEUE_DEPTH`, metric-counted). This service
//! is that same shape, lifted to the whole `WholeChainProof` match fold:
//!
//! | `prove_pool.rs` (per turn)              | this service (per match)                 |
//! | --------------------------------------- | ---------------------------------------- |
//! | bounded `tokio::mpsc` queue             | bounded `std::sync::mpsc::sync_channel`  |
//! | N `spawn_blocking` workers, off-lock    | N OS-thread workers, off-lock            |
//! | `DREGG_PROVE_WORKERS` / `_QUEUE_DEPTH`  | `DREGG_MATCH_PROVE_WORKERS` / `_QUEUE_DEPTH` |
//! | drop-on-full (commit already sound)     | drop-on-full (the play already happened) |
//! | `metrics::inc_async_proofs_*`           | [`Metrics`] atomics                      |
//!
//! Bounding both the concurrency (N workers) and the queue (a depth cap, past
//! which [`enqueue`](ProveService::enqueue) returns `None` rather than blocking)
//! is what keeps a proving flood from wedging the host — the play path is never
//! blocked, and a dropped job is a *liveness* degradation of the enrichment
//! layer (the match can be re-enqueued), never a safety problem.
//!
//! [`ProveService`] is generic over the job input `I` and the proof output `O`
//! so the pool mechanics (bounded concurrency, status, metrics, off-lock) are
//! driven fast with stub backends, while the concrete
//! [`MatchProveService`] = `ProveService<`[`PlayedMatch`]`, `[`MatchProof`]`>`
//! runs the real deployed fold ([`fold_played_match`]).
//!
//! ## GPU dispatch on the fold path (honest scope)
//!
//! The fold reaches the GPU through the same runtime dispatch the rest of the
//! prover uses: [`dregg_circuit_prove::gpu_backend`]'s `GpuDft` / `GpuBn254Mmcs`
//! select the GPU kernels when an adapter is present and fall back to the CPU
//! path (identical types, identical output) when it is not — [`gpu::available`]
//! reports which. The GPU speedup is realized on a GPU box; the correctness of a
//! folded proof is identical either way (bit-exact roots), so the CPU box is the
//! correctness gate and the GPU box is the speed win.
//!
//! **What is REAL here:** the async service — proving is OFF the play path,
//! bounded and metered, the proof correctness-identical to the foreground fold.
//!
//! **NAMED (not built here), per the deploy plan:**
//! * **GPU-ing the whole-match fold's inner apex aggregation.** Today
//!   [`dreggnet_game_board::prove_match`] → `prove_turn_chain_recursive` folds
//!   through the CPU recursion config (`create_recursion_backend`,
//!   `Radix2DitParallel` DFT + `MerkleTreeMmcs`). The GPU recursion variant
//!   (`gpu_backend::create_gpu_recursion_config` / `prove_recursion_layer_gpu`,
//!   `GpuDft` + `GpuFoldValMmcs`) EXISTS and is runtime-dispatched, but routing
//!   the per-layer aggregation through it is a `circuit-prove` change this
//!   additive crate does not make. This is the ~241 s inner-MMCS lever — the
//!   order-of-magnitude (~45 min → ~20 min) needs it.
//! * **On-device (wasm) proving.** The fold runs wherever this service runs — a
//!   server-side worker. "The moves never leave the device" needs the prover
//!   compiled to the client, a separate workstream.
//! * **The service→board submit wire.** [`MatchProof`] is handed to
//!   [`dreggnet_game_board::GameBoard`] by the caller; this crate stops at
//!   `Done{proof}`.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, SyncSender, TrySendError, sync_channel};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;
use std::time::Instant;

pub use dreggnet_game_board::{
    AutomataflMatch, Game, LeafBundle, MatchError, MatchProof, MultiRoundTurn, ProveError,
    TugMatch, TugWin,
};

// ═══════════════════════════════════════════════════════════════════════════
// The GENERIC bounded worker pool (the prove_pool.rs shape, lifted off tokio).
// ═══════════════════════════════════════════════════════════════════════════

/// A queued job's handle — poll [`ProveService::status`] / [`ProveService::wait`]
/// with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JobId(pub u64);

/// Where a proving job is. The player's client polls this; nothing downstream is
/// involved until [`JobStatus::Done`].
#[derive(Clone, Debug)]
pub enum JobStatus<O> {
    /// Accepted into the bounded queue, not yet picked up by a worker.
    Queued,
    /// A worker is folding the match (the slow, off-path step).
    Proving,
    /// The fold is done (and, for the match backend, self-attested) — this proof
    /// can be submitted to the board.
    Done(Box<O>),
    /// The fold refused the match (a forged / unsatisfiable chain) or the prover
    /// errored. Nothing to submit.
    Failed(String),
    /// No such job (never enqueued, or dropped on a full queue).
    Unknown,
}

impl<O> JobStatus<O> {
    /// The finished proof, if this job is [`JobStatus::Done`].
    pub fn done(&self) -> Option<&O> {
        match self {
            JobStatus::Done(o) => Some(o),
            _ => None,
        }
    }
    /// Whether the job has settled (done or failed).
    pub fn is_settled(&self) -> bool {
        matches!(self, JobStatus::Done(_) | JobStatus::Failed(_))
    }
}

/// The proving backend a [`ProveService`] runs: one job input → one proof output,
/// or a failure string. Runs on a worker thread, off the caller's path.
pub type Backend<I, O> = Arc<dyn Fn(I) -> Result<O, String> + Send + Sync>;

/// A snapshot of the pool's lifetime counters (mirrors `prove_pool`'s
/// `metrics::inc_async_proofs_*`).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Metrics {
    /// Jobs accepted into the queue.
    pub enqueued: u64,
    /// Jobs refused because the bounded queue was full (dropped, not blocked).
    pub dropped: u64,
    /// Jobs that folded to a proof.
    pub completed: u64,
    /// Jobs whose fold failed (refused/forged match, or prover error).
    pub failed: u64,
    /// Jobs currently being folded on a worker (a gauge).
    pub in_flight: u64,
    /// Total wall time spent inside the backend across all settled jobs.
    pub total_prove_secs: f64,
}

#[derive(Default)]
struct Counters {
    enqueued: AtomicU64,
    dropped: AtomicU64,
    completed: AtomicU64,
    failed: AtomicU64,
    in_flight: AtomicU64,
    prove_nanos: AtomicU64,
}

type StatusMap<O> = Arc<(Mutex<HashMap<u64, JobStatus<O>>>, Condvar)>;

/// **THE ASYNC PROVING SERVICE.** A bounded MPSC queue feeds a fixed set of
/// worker threads; [`enqueue`](Self::enqueue) never blocks the caller and
/// returns a [`JobId`] immediately. Cheap to construct; folds happen entirely on
/// the workers, off the caller's path.
pub struct ProveService<I, O> {
    tx: Option<SyncSender<(u64, I)>>,
    status: StatusMap<O>,
    counters: Arc<Counters>,
    next: AtomicU64,
    workers: Vec<JoinHandle<()>>,
    n_workers: usize,
    queue_depth: usize,
}

/// Default worker count. Folds are heavy (RAM + CPU); keep this small so a flood
/// cannot exhaust the host. Override with `DREGG_MATCH_PROVE_WORKERS`.
pub const DEFAULT_WORKERS: usize = 2;

/// Default bounded-queue depth. Past this, [`ProveService::enqueue`] returns
/// `None` (the play already happened — a dropped fold is re-enqueueable). Override
/// with `DREGG_MATCH_PROVE_QUEUE_DEPTH`.
pub const DEFAULT_QUEUE_DEPTH: usize = 64;

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(default)
}

impl<I, O> ProveService<I, O>
where
    I: Send + 'static,
    O: Clone + Send + 'static,
{
    /// Spawn the worker set for a `backend`. Reads `DREGG_MATCH_PROVE_WORKERS`
    /// and `DREGG_MATCH_PROVE_QUEUE_DEPTH` (mirroring `prove_pool`'s knobs).
    pub fn spawn(backend: Backend<I, O>) -> Self {
        let n_workers = env_usize("DREGG_MATCH_PROVE_WORKERS", DEFAULT_WORKERS);
        let queue_depth = env_usize("DREGG_MATCH_PROVE_QUEUE_DEPTH", DEFAULT_QUEUE_DEPTH);
        Self::spawn_with(backend, n_workers, queue_depth)
    }

    /// Spawn with explicit knobs (env is bypassed) — used by the pool-mechanics
    /// tests to pin an exact worker count and depth.
    pub fn spawn_with(backend: Backend<I, O>, n_workers: usize, queue_depth: usize) -> Self {
        let n_workers = n_workers.max(1);
        let queue_depth = queue_depth.max(1);
        let (tx, rx) = sync_channel::<(u64, I)>(queue_depth);
        let rx = Arc::new(Mutex::new(rx));
        let status: StatusMap<O> = Arc::new((Mutex::new(HashMap::new()), Condvar::new()));
        let counters = Arc::new(Counters::default());

        let mut workers = Vec::with_capacity(n_workers);
        for wid in 0..n_workers {
            let rx: Arc<Mutex<Receiver<(u64, I)>>> = rx.clone();
            let status = status.clone();
            let counters = counters.clone();
            let backend = backend.clone();
            let handle = std::thread::Builder::new()
                .name(format!("match-prover-{wid}"))
                .spawn(move || worker_loop(wid, rx, status, counters, backend))
                .expect("the match-prover worker thread spawns");
            workers.push(handle);
        }

        tracing::info!(
            workers = n_workers,
            queue_depth,
            "async match-fold prove service started (proving moved OFF the play path)"
        );

        ProveService {
            tx: Some(tx),
            status,
            counters,
            next: AtomicU64::new(1),
            workers,
            n_workers,
            queue_depth,
        }
    }

    /// **ENQUEUE a job.** Returns a [`JobId`] immediately (`Some`) if the job was
    /// accepted into the bounded queue, or `None` if the queue is full (dropped —
    /// the play already happened; re-enqueue later). NEVER blocks the caller: the
    /// whole point is that play stays interactive-fast.
    pub fn enqueue(&self, input: I) -> Option<JobId> {
        let id = self.next.fetch_add(1, Ordering::Relaxed);
        // Register `Queued` BEFORE the send so a status poll can never observe a
        // spurious `Unknown` for an accepted job, and a fast worker that finishes
        // before we return only ever OVERWRITES this with `Done`.
        set_status(&self.status, id, JobStatus::Queued);
        let tx = self.tx.as_ref().expect("service running");
        match tx.try_send((id, input)) {
            Ok(()) => {
                self.counters.enqueued.fetch_add(1, Ordering::Relaxed);
                tracing::info!(
                    job = id,
                    "match-fold job ENQUEUED (fold runs off the play path)"
                );
                Some(JobId(id))
            }
            Err(TrySendError::Full(_)) => {
                self.counters.dropped.fetch_add(1, Ordering::Relaxed);
                remove_status(&self.status, id);
                tracing::warn!(
                    job = id,
                    "match-fold queue full; dropping job (the play already happened — re-enqueue)"
                );
                None
            }
            Err(TrySendError::Disconnected(_)) => {
                remove_status(&self.status, id);
                tracing::error!(
                    job = id,
                    "match-fold service channel closed; cannot enqueue"
                );
                None
            }
        }
    }

    /// Poll a job's [`JobStatus`]. Cheap: a brief lock on the status map only.
    pub fn status(&self, id: JobId) -> JobStatus<O> {
        let (m, _) = &*self.status;
        m.lock()
            .expect("status map")
            .get(&id.0)
            .cloned()
            .unwrap_or(JobStatus::Unknown)
    }

    /// Block until the job settles, then hand back the proof (or the fold's
    /// refusal). Convenience for callers that want to await one job.
    pub fn wait(&self, id: JobId) -> Result<O, String> {
        let (m, cv) = &*self.status;
        let mut guard = m.lock().expect("status map");
        loop {
            match guard.get(&id.0) {
                Some(JobStatus::Done(o)) => return Ok((**o).clone()),
                Some(JobStatus::Failed(e)) => return Err(e.clone()),
                Some(_) => {}
                None => return Err(format!("unknown job {}", id.0)),
            }
            guard = cv.wait(guard).expect("status condvar");
        }
    }

    /// A snapshot of the lifetime counters.
    pub fn metrics(&self) -> Metrics {
        Metrics {
            enqueued: self.counters.enqueued.load(Ordering::Relaxed),
            dropped: self.counters.dropped.load(Ordering::Relaxed),
            completed: self.counters.completed.load(Ordering::Relaxed),
            failed: self.counters.failed.load(Ordering::Relaxed),
            in_flight: self.counters.in_flight.load(Ordering::Relaxed),
            total_prove_secs: self.counters.prove_nanos.load(Ordering::Relaxed) as f64 / 1e9,
        }
    }

    /// The number of worker threads folding in parallel.
    pub fn workers(&self) -> usize {
        self.n_workers
    }
    /// The bounded-queue depth (jobs past this are dropped by `enqueue`).
    pub fn queue_depth(&self) -> usize {
        self.queue_depth
    }
}

fn worker_loop<I, O>(
    wid: usize,
    rx: Arc<Mutex<Receiver<(u64, I)>>>,
    status: StatusMap<O>,
    counters: Arc<Counters>,
    backend: Backend<I, O>,
) where
    O: Clone + Send + 'static,
{
    loop {
        // Hold the receiver mutex ONLY across `recv()` — never across the fold —
        // so all N workers can fold concurrently (exactly `prove_pool`'s pattern:
        // the lock guards job pickup, not proving).
        let job = {
            let guard = rx.lock().expect("worker receiver");
            guard.recv()
        };
        let Ok((id, input)) = job else {
            tracing::debug!(worker = wid, "match-fold channel closed; worker exiting");
            return;
        };

        set_status(&status, id, JobStatus::Proving);
        counters.in_flight.fetch_add(1, Ordering::Relaxed);
        let started = Instant::now();

        let outcome = match backend(input) {
            Ok(o) => {
                counters.completed.fetch_add(1, Ordering::Relaxed);
                JobStatus::Done(Box::new(o))
            }
            Err(e) => {
                counters.failed.fetch_add(1, Ordering::Relaxed);
                tracing::warn!(worker = wid, job = id, error = %e, "match fold failed");
                JobStatus::Failed(e)
            }
        };

        counters
            .prove_nanos
            .fetch_add(started.elapsed().as_nanos() as u64, Ordering::Relaxed);
        counters.in_flight.fetch_sub(1, Ordering::Relaxed);
        tracing::info!(
            worker = wid,
            job = id,
            elapsed_ms = started.elapsed().as_millis(),
            "match fold settled"
        );
        set_status(&status, id, outcome);
    }
}

fn set_status<O>(status: &StatusMap<O>, id: u64, s: JobStatus<O>) {
    let (m, cv) = &**status;
    m.lock().expect("status map").insert(id, s);
    cv.notify_all();
}

fn remove_status<O>(status: &StatusMap<O>, id: u64) {
    let (m, _) = &**status;
    m.lock().expect("status map").remove(&id);
}

impl<I, O> Drop for ProveService<I, O> {
    fn drop(&mut self) {
        // Close the queue so each worker's blocking `recv()` returns `Err` and the
        // loop ends, then join every worker.
        drop(self.tx.take());
        for w in self.workers.drain(..) {
            let _ = w.join();
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// The CONCRETE match service: a played match -> ONE MatchProof.
// ═══════════════════════════════════════════════════════════════════════════

/// A played match of a portfolio game, ready to fold. The play is over — this is
/// the job the service takes.
#[derive(Clone, Debug)]
pub enum PlayedMatch {
    /// A played multiway-tug match (ranks with the HAND never revealed).
    Tug(TugMatch),
    /// A played automatafl match (ranks with the MOVES never posted). CLEAN rounds only — the
    /// plain two-leg chain has no marks lane, so a turn that RE-ENTERED belongs in
    /// [`PlayedMatch::AutomataflTurn`].
    Automatafl(AutomataflMatch),
    /// ⚑ **ONE automatafl TURN that went through the ruleset's CONFLICT re-submission loop** — `k`
    /// conflict rounds (the Leg C braid on the 32-lane RoundState window, accumulating the marks)
    /// welded to the terminating clean round (the marks-aware Leg RM + the marks-carrying Leg A),
    /// folded by [`MultiRoundTurn::prove`] into ONE `WholeChainProof`.
    ///
    /// A separate variant rather than a field on [`AutomataflMatch`] because it is a genuinely
    /// different fold SHAPE: the clean-handoff root has exactly one width change (32 → 20), which is
    /// what the deployed mixed-width verifier accepts, and chaining a second turn onto it is not
    /// built. So this variant carries a SINGLE turn, and the crown says so.
    AutomataflTurn(MultiRoundTurn),
}

impl PlayedMatch {
    /// Which game this match was played in.
    pub fn game(&self) -> Game {
        match self {
            PlayedMatch::Tug(_) => Game::MultiwayTug,
            PlayedMatch::Automatafl(_) | PlayedMatch::AutomataflTurn(_) => Game::Automatafl,
        }
    }
}

impl From<TugMatch> for PlayedMatch {
    fn from(m: TugMatch) -> Self {
        PlayedMatch::Tug(m)
    }
}
impl From<AutomataflMatch> for PlayedMatch {
    fn from(m: AutomataflMatch) -> Self {
        PlayedMatch::Automatafl(m)
    }
}

/// **THE FOLD BACKEND** — lower a played match to its foldable leaves and fold
/// them, through the game-board bridge, into ONE self-attested [`MatchProof`].
/// SLOW (minutes-to-hours); this is what a worker runs. A forged / unsatisfiable
/// match returns `Err` (the job settles [`JobStatus::Failed`]) — the fold's teeth
/// bite here, off the play path.
pub fn fold_played_match(m: PlayedMatch) -> Result<MatchProof, String> {
    match m {
        PlayedMatch::Tug(t) => {
            dreggnet_game_board::prove_tug_match(&t).map_err(|e: ProveError| e.to_string())
        }
        PlayedMatch::Automatafl(a) => {
            dreggnet_game_board::prove_automatafl_match(&a).map_err(|e: ProveError| e.to_string())
        }
        // ⚑ THE CONFLICT BRAID. `MultiRoundTurn::prove` lowers the `k` Leg C conflict rounds and the
        // terminating Leg RM + Leg A, folds them across the one clean-handoff width change, and
        // self-attests the mixed-width root through the SAME verifier the board runs.
        PlayedMatch::AutomataflTurn(t) => t.prove().map_err(|e: ProveError| e.to_string()),
    }
}

/// The concrete async match-fold service: a [`PlayedMatch`] job → a
/// [`MatchProof`] output.
pub type MatchProveService = ProveService<PlayedMatch, MatchProof>;

/// Spawn the production match-fold service — the bounded worker pool running the
/// REAL deployed fold ([`fold_played_match`]), tuned by
/// `DREGG_MATCH_PROVE_WORKERS` / `DREGG_MATCH_PROVE_QUEUE_DEPTH`.
pub fn match_prove_service() -> MatchProveService {
    ProveService::spawn(Arc::new(fold_played_match))
}

// ═══════════════════════════════════════════════════════════════════════════
// The GPU dispatch on the fold path (runtime-dispatched; CPU fallback).
// ═══════════════════════════════════════════════════════════════════════════

/// The runtime GPU dispatch the prover backend takes on the fold path. The
/// `gpu_backend` selects its GPU kernels when an adapter is present and falls
/// back to the identical-output CPU path when it is not — so a folded proof is
/// correctness-identical on either, and the speedup is realized on a GPU box.
pub mod gpu {
    use dregg_circuit_prove::gpu_backend::{GpuBn254Mmcs, GpuDft};

    /// Whether a GPU adapter is available to the prover (the dominant BN254
    /// Merkle-tree hash seam). `false` ⇒ permanent CPU fallback (the correctness
    /// gate runs here); `true` ⇒ the GPU path is taken where a commit qualifies.
    pub fn available() -> bool {
        GpuBn254Mmcs::new(0).adapter_available()
    }

    /// The GPU adapter's name, or `None` under CPU fallback. Reads the DFT seam's
    /// adapter (same shared device as the hash seam).
    pub fn adapter_name() -> Option<String> {
        GpuDft::default().adapter_name()
    }

    /// A one-line human summary of the dispatch state, for logs / a health probe.
    pub fn describe() -> String {
        match adapter_name() {
            Some(name) => format!("GPU dispatch ACTIVE on adapter: {name}"),
            None => "GPU dispatch fallback: CPU (no adapter) — proofs correctness-identical".into(),
        }
    }
}
