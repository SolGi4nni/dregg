//! The TREE-SCAN-STATE aggregation infra — the merge-pool + the frontier/driver that make proof
//! AGGREGATION parallelize (throughput ∝ worker count, farmable to a GPU / machine pool).
//!
//! ## The serial cap this closes
//!
//! [`ivc_turn_chain::aggregate_tree`](crate::ivc_turn_chain) folds K segment-carrying descriptor
//! leaves to one root through a balanced binary tree, but it runs as a single-threaded
//! `while proofs.len() > 1` loop: every internal node is proven sequentially, so a prover POOL
//! cannot help — the bottleneck is the `while`, not a shortage of provers. Yet a balanced tree's
//! internal nodes at the same depth are INDEPENDENT: node `(2i, 2i+1)` and node `(2j, 2j+1)` share
//! no inputs and can be proven on different cores / GPUs / machines at the same time. Each merge is
//! also a PURE, side-effect-free function ([`merge_two_segment_proofs`]) whose inputs and
//! result-of-interest are the `Send`, serde [`BatchStarkProof`] (NOT the `!Send`
//! `Rc<CircuitProverData>`, which no downstream merge or verifier ever reads — exactly the
//! verify-sufficient subset [`WholeChainProofBytes`](crate::ivc_turn_chain::WholeChainProofBytes)
//! ships over a wire). So the merge is the natural FARM-ABLE unit.
//!
//! ## The two atoms
//!
//!   1. **[`MergePool`]** — the merge worker-pool: `N` workers pull [`MergeJob`]s (each = two child
//!      proofs + the tree-node id they produce) from a bounded queue, prove the merge with their own
//!      thread-local config + backend, and ship back the parent [`BatchStarkProof`]. It mirrors the
//!      base per-turn [`prove_pool`](../../node/src/prove_pool.rs) pattern (an `Arc<Mutex<Receiver>>`
//!      pulled by a fixed worker set), tunable via `DREGG_MERGE_WORKERS` /
//!      `DREGG_MERGE_QUEUE_DEPTH`. Because each job is independent and `Send`, throughput scales with
//!      the worker/machine count — a from-scratch GPU farm drains the same queue.
//!
//!   2. **[`aggregate_tree_scan_state`]** — the scan-state DRIVER: instead of a one-shot level loop,
//!      it builds the SAME balanced-tree DAG `aggregate_tree` walks (identical pairing, identical odd
//!      promotion), holds a FRONTIER of ready merge-pairs, feeds the merge-pool as nodes become
//!      ready, and consumes completed root-ward proofs — enqueuing the constant new work each
//!      completion unlocks ("base-leaf completions enqueue `(left,right)` pairs; the pool drains
//!      them; the chain consumes completed work"). Because every node delegates to the SAME
//!      [`merge_two_segment_proofs`] the serial tree uses, the parallel root is BYTE-IDENTICAL to the
//!      serial root (witness: the `scan_state_root_equals_serial_root` test) — same answer, parallel
//!      path.
//!
//! ## Depth-4-anchored NOW; uniform-unbounded once the canonical seed lands
//!
//! This driver works over the CURRENT depth-4-anchored form (the running-VK fixed point reached at
//! depth 4; see [`accumulator`](crate::accumulator)). It is a pure DRIVER/QUEUE change — the
//! per-node math (continuity `connect` + count-add + ordered Poseidon digest) is untouched. Once the
//! canonical-seed lane lands the uniform unbounded-depth VK, the same merge-pool/driver farm over the
//! fully-uniform tree with no change to this file's structure.

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, mpsc};
use std::thread::JoinHandle;

use p3_circuit_prover::BatchStarkProof;
use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::ivc_turn_chain::{TurnChainError, merge_two_segment_proofs};
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// A tree-node identifier in the aggregation DAG. Leaves are `0..num_leaves`; every internal node
/// (a merge output) gets the next id, in the SAME order [`aggregate_tree`](crate::ivc_turn_chain)
/// would produce them.
pub type NodeId = usize;

/// Default number of concurrent merge workers. Proving is CPU-bound (and p3 already uses rayon
/// inside one merge), so the real throughput win is across MACHINES / GPUs draining the same queue;
/// on one box this defaults small to avoid core oversubscription. Override with `DREGG_MERGE_WORKERS`.
pub const DEFAULT_MERGE_WORKERS: usize = 2;

/// Default bounded merge-queue depth. The driver applies backpressure (re-queues a pair) when the
/// queue is full, so this only bounds in-flight memory. Override with `DREGG_MERGE_QUEUE_DEPTH`.
pub const DEFAULT_MERGE_QUEUE_DEPTH: usize = 256;

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(default)
}

/// The number of merge workers the driver will spawn (`DREGG_MERGE_WORKERS`, default
/// [`DEFAULT_MERGE_WORKERS`]).
pub fn configured_merge_workers() -> usize {
    env_usize("DREGG_MERGE_WORKERS", DEFAULT_MERGE_WORKERS)
}

/// Whether the parallel scan-state driver is opted in (`DREGG_MERGE_WORKERS` is set, to any value).
/// When unset, callers keep the byte-identical serial [`aggregate_tree`](crate::ivc_turn_chain) — so
/// the default proving path is UNCHANGED and the parallel path is an operator throughput knob.
pub fn parallel_aggregation_enabled() -> bool {
    std::env::var_os("DREGG_MERGE_WORKERS").is_some()
}

/// One farmable merge: aggregate two child [`BatchStarkProof`]s into the parent tree node `out`.
///
/// Both children and the result are the `Send`, serde [`BatchStarkProof`] — never the `!Send`
/// `Rc<CircuitProverData>` — so a `MergeJob` crosses a thread / GPU / machine boundary unchanged.
pub struct MergeJob {
    /// The DAG node id this merge PRODUCES (so the driver can place the result in the frontier).
    pub out: NodeId,
    /// The left child proof (the lower-index subtree).
    pub left: BatchStarkProof<DreggRecursionConfig>,
    /// The right child proof (the higher-index subtree).
    pub right: BatchStarkProof<DreggRecursionConfig>,
}

/// The result of one merge: the produced node id + either its parent proof or the failure reason.
pub struct MergeResult {
    /// The DAG node id whose proof this is.
    pub out: NodeId,
    /// The parent [`BatchStarkProof`] (the merge output's `.0`, the `Rc` dropped on the worker), or
    /// the merge failure rendered to a string (re-wrapped to a [`TurnChainError`] by the driver).
    pub result: Result<BatchStarkProof<DreggRecursionConfig>, String>,
}

/// The merge worker-pool: a fixed set of OS-thread workers pulling [`MergeJob`]s from a bounded
/// queue and returning [`MergeResult`]s. Mirrors the base per-turn prove-pool (`node/src/prove_pool`):
/// an `Arc<Mutex<Receiver>>` pulled by every worker, so jobs are claimed first-come.
///
/// A merge job is independent and `Send`, so the SAME queue is drainable by more workers (more cores
/// today, more GPUs/machines tomorrow): throughput is ∝ the worker count, with no serial `while`.
pub struct MergePool {
    jobs_tx: Option<mpsc::SyncSender<MergeJob>>,
    results_rx: mpsc::Receiver<MergeResult>,
    handles: Vec<JoinHandle<()>>,
    workers: usize,
}

impl MergePool {
    /// Spawn `workers` merge workers behind a bounded queue of `queue_depth`. Each worker builds its
    /// OWN thread-local recursion config + backend (both are `thread_local`-cached — see
    /// [`ir2_leaf_wrap_config`](crate::ivc_turn_chain::ir2_leaf_wrap_config) /
    /// [`create_recursion_backend`](crate::plonky3_recursion_impl::recursive::create_recursion_backend)),
    /// so nothing `!Sync` is shared across the pool.
    pub fn spawn(workers: usize, queue_depth: usize) -> Self {
        let workers = workers.max(1);
        let queue_depth = queue_depth.max(1);
        let (jobs_tx, jobs_rx) = mpsc::sync_channel::<MergeJob>(queue_depth);
        let (results_tx, results_rx) = mpsc::channel::<MergeResult>();
        let jobs_rx = Arc::new(Mutex::new(jobs_rx));

        let mut handles = Vec::with_capacity(workers);
        for worker_id in 0..workers {
            let jobs_rx = jobs_rx.clone();
            let results_tx = results_tx.clone();
            let handle = std::thread::Builder::new()
                .name(format!("dregg-merge-{worker_id}"))
                .spawn(move || merge_worker_loop(worker_id, jobs_rx, results_tx))
                .expect("merge worker thread spawns");
            handles.push(handle);
        }
        // The pool's own `jobs_tx` is the LAST live sender; when it (and the pool) drops, every
        // worker's `recv()` returns `Err` and the worker exits. `results_tx` is moved into the
        // workers (the clones above); this original is dropped here so `results_rx` closes once all
        // workers are gone.
        drop(results_tx);

        Self {
            jobs_tx: Some(jobs_tx),
            results_rx,
            handles,
            workers,
        }
    }

    /// The configured worker count.
    pub fn workers(&self) -> usize {
        self.workers
    }

    /// Try to dispatch a job without blocking. Returns the job back on `Err` if the bounded queue is
    /// full (the driver then drains a result and retries — backpressure, never a drop: an aggregation
    /// merge is load-bearing, unlike a per-turn attestation).
    pub fn try_dispatch(&self, job: MergeJob) -> Result<(), MergeJob> {
        match self.jobs_tx.as_ref().expect("pool live").try_send(job) {
            Ok(()) => Ok(()),
            Err(mpsc::TrySendError::Full(job)) => Err(job),
            Err(mpsc::TrySendError::Disconnected(job)) => Err(job),
        }
    }

    /// Block until the next merge result is available. `Err` once all workers have exited (the queue
    /// drained + pool senders dropped).
    pub fn recv_result(&self) -> Result<MergeResult, mpsc::RecvError> {
        self.results_rx.recv()
    }
}

impl Drop for MergePool {
    fn drop(&mut self) {
        // Close the queue so idle workers (blocked on `recv`) exit, then join — a clean shutdown.
        // By the time the driver drops the pool the tree is folded, so workers are idle and the join
        // returns promptly.
        self.jobs_tx.take();
        for handle in self.handles.drain(..) {
            let _ = handle.join();
        }
    }
}

/// The per-worker loop: pull a job (the receiver mutex held ONLY across `recv`, never across the
/// merge), prove the merge with thread-local config/backend, ship back the parent proof.
fn merge_worker_loop(
    _worker_id: usize,
    jobs_rx: Arc<Mutex<mpsc::Receiver<MergeJob>>>,
    results_tx: mpsc::Sender<MergeResult>,
) {
    // ⚑ A MERGE IS A FOLD, SO IT RUNS AT THE FOLD ENGINE. `ir2_leaf_wrap_config()` is the engine
    // the leaves' CHILD (the IR-v2 descriptor batch) is minted at — no proof this pool ever sees
    // carries it. Taking it here would verify every child at an engine it was not minted at, and
    // this driver is the one that has to stay byte-identical to serial `aggregate_tree`.
    let config = crate::ivc_turn_chain::turn_chain_root_config();
    let backend = crate::plonky3_recursion_impl::recursive::create_recursion_backend();
    let params = ProveNextLayerParams::default();
    loop {
        let job = {
            let guard = jobs_rx.lock().expect("merge job queue mutex not poisoned");
            guard.recv()
        };
        let Ok(job) = job else {
            return; // queue closed: pool dropped.
        };
        let result = merge_two_segment_proofs(&job.left, &job.right, &config, &backend, &params)
            .map(|out| out.0) // keep ONLY the Send BatchStarkProof; the prover-only Rc is unread.
            .map_err(|e| e.to_string());
        if results_tx
            .send(MergeResult {
                out: job.out,
                result,
            })
            .is_err()
        {
            return; // driver gone.
        }
    }
}

/// One merge task in the aggregation DAG: prove `out := merge(left, right)`.
struct MergeTask {
    left: NodeId,
    right: NodeId,
    out: NodeId,
}

/// Build the aggregation DAG that EXACTLY mirrors
/// [`aggregate_tree`](crate::ivc_turn_chain)'s balanced binary fold: at each level pair adjacent
/// nodes left-to-right, and promote the lone leftover (the `proofs.pop()` tail) unchanged to the next
/// level. Returns the ordered task list (parents after their children) and the root node id.
fn build_dag(num_leaves: usize) -> (Vec<MergeTask>, NodeId) {
    debug_assert!(num_leaves >= 1);
    let mut tasks = Vec::new();
    let mut next_node = num_leaves;
    let mut level: Vec<NodeId> = (0..num_leaves).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            let out = next_node;
            next_node += 1;
            tasks.push(MergeTask {
                left: level[i],
                right: level[i + 1],
                out,
            });
            next.push(out);
            i += 2;
        }
        if i < level.len() {
            // The odd leftover — `aggregate_tree`'s `next_level.push(proofs.pop())` — promoted to
            // the END of the next level, unchanged.
            next.push(level[i]);
        }
        level = next;
    }
    (tasks, level[0])
}

/// **THE FARM-ABLE SHAPE (inspection / structural witness).** Return the aggregation DAG that
/// [`aggregate_tree_scan_state`] (and the serial [`aggregate_tree`](crate::ivc_turn_chain)) walk for
/// `num_leaves` leaves: an ordered list of `(left, right, out)` merge nodes (parents after children)
/// plus the root node id. Leaves are `0..num_leaves`. Independent merges (disjoint `out`s at the same
/// depth) are the unit a worker/GPU pool farms — this is what makes throughput ∝ worker count.
pub fn aggregation_dag(num_leaves: usize) -> (Vec<(NodeId, NodeId, NodeId)>, NodeId) {
    let (tasks, root) = build_dag(num_leaves.max(1));
    (
        tasks
            .into_iter()
            .map(|t| (t.left, t.right, t.out))
            .collect(),
        root,
    )
}

/// **THE SCAN-STATE DRIVER — the parallel dual of [`aggregate_tree`](crate::ivc_turn_chain).**
///
/// Fold `leaves` (the per-turn segment-carrying descriptor leaves) to ONE root via the merge-pool,
/// producing a root BYTE-IDENTICAL to the serial `aggregate_tree` (same DAG, same per-node
/// [`merge_two_segment_proofs`]). Independent merges run concurrently on the pool; the FRONTIER
/// (ready merge-pairs) is fed as nodes complete and consumed root-ward.
///
/// The ROOT node is proven inline by the driver (not on the pool) so its result is a full
/// [`RecursionOutput`] — every NON-root node ships back only its `Send` [`BatchStarkProof`] (its
/// prover-only `Rc<CircuitProverData>` is never read downstream). Each leaf's proof is likewise moved
/// out of its [`RecursionOutput`] as the `Send` currency; the leaf `Rc` is dropped.
///
/// `workers` is the merge-pool size (use [`configured_merge_workers`]); `queue_depth` bounds the
/// in-flight job queue.
pub fn aggregate_tree_scan_state(
    leaves: Vec<RecursionOutput<DreggRecursionConfig>>,
    workers: usize,
    queue_depth: usize,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if leaves.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "no leaves to aggregate".to_string(),
        });
    }
    if leaves.len() == 1 {
        // Degenerate: the single leaf IS the root (matches `aggregate_tree`'s `proofs.pop()` exit).
        return Ok(leaves.into_iter().next().unwrap());
    }

    let num_leaves = leaves.len();
    let (tasks, root_node) = build_dag(num_leaves);
    debug_assert!(!tasks.is_empty());
    let root_task_idx = tasks.len() - 1;
    debug_assert_eq!(tasks[root_task_idx].out, root_node);

    // ── Dependency bookkeeping. A task input that is itself a task OUTPUT (`>= num_leaves`) must
    //    wait for that task; a leaf input is available from the start. `pending[t]` counts the
    //    not-yet-ready inputs; `dependents[node]` are the tasks waiting on `node`.
    let is_internal = |node: NodeId| node >= num_leaves;
    let mut pending: Vec<usize> = vec![0; tasks.len()];
    let mut dependents: HashMap<NodeId, Vec<usize>> = HashMap::new();
    for (tidx, t) in tasks.iter().enumerate() {
        for input in [t.left, t.right] {
            if is_internal(input) {
                pending[tidx] += 1;
                dependents.entry(input).or_default().push(tidx);
            }
        }
    }

    // ── The available proofs (the `Send` currency), keyed by node id. Leaves move in up front.
    let mut available: HashMap<NodeId, BatchStarkProof<DreggRecursionConfig>> =
        HashMap::with_capacity(num_leaves * 2);
    for (i, out) in leaves.into_iter().enumerate() {
        // Move the leaf's BatchStarkProof out, dropping the prover-only Rc — the Send currency.
        let RecursionOutput(proof, _prover_data) = out;
        available.insert(i, proof);
    }

    // ── The frontier: ready NON-root tasks (root is run inline). A task is ready when `pending == 0`.
    let mut frontier: VecDeque<usize> = (0..tasks.len())
        .filter(|&tidx| pending[tidx] == 0 && tidx != root_task_idx)
        .collect();

    let pool = MergePool::spawn(workers, queue_depth);
    let mut outstanding = 0usize;

    loop {
        // (a) the root is the terminal node: once both its children are available, fold it inline.
        let root = &tasks[root_task_idx];
        if available.contains_key(&root.left) && available.contains_key(&root.right) {
            break;
        }

        // (b) dispatch every ready non-root task, honoring queue backpressure.
        while let Some(&tidx) = frontier.front() {
            let t = &tasks[tidx];
            // Both inputs are present (the readiness invariant). Move them into the job; on a full
            // queue, put them back and go drain a result instead (backpressure, never a drop).
            let left = available
                .remove(&t.left)
                .expect("ready merge task: left input available");
            let right = available
                .remove(&t.right)
                .expect("ready merge task: right input available");
            match pool.try_dispatch(MergeJob {
                out: t.out,
                left,
                right,
            }) {
                Ok(()) => {
                    frontier.pop_front();
                    outstanding += 1;
                }
                Err(job) => {
                    available.insert(t.left, job.left);
                    available.insert(t.right, job.right);
                    break;
                }
            }
        }

        if outstanding == 0 {
            // Nothing in flight and the root is not ready. Either the frontier still has work (we
            // just dispatched some this iteration → loop and dispatch more / it was full), or the
            // DAG is malformed. In a connected balanced tree this cannot deadlock.
            if frontier.is_empty() {
                return Err(TurnChainError::RecursionFailed {
                    reason: "scan-state driver stalled: no in-flight merge, empty frontier, root \
                             not ready (malformed aggregation DAG)"
                        .to_string(),
                });
            }
            continue;
        }

        // (c) consume one completed proof; place it and wake its dependents.
        let res = self_recv(&pool)?;
        outstanding -= 1;
        let proof = res
            .result
            .map_err(|reason| TurnChainError::RecursionFailed {
                reason: format!("parallel merge node {} failed: {reason}", res.out),
            })?;
        available.insert(res.out, proof);
        if let Some(deps) = dependents.get(&res.out) {
            for &dtidx in deps {
                pending[dtidx] -= 1;
                if pending[dtidx] == 0 && dtidx != root_task_idx {
                    frontier.push_back(dtidx);
                }
            }
        }
    }

    // ── The root fold, inline, so the artifact is a full RecursionOutput (its Rc is fresh but, like
    //    every node's, never read by verification — the root is consumed via `root.0`).
    let root = &tasks[root_task_idx];
    let left = available
        .remove(&root.left)
        .expect("root left input available");
    let right = available
        .remove(&root.right)
        .expect("root right input available");
    // ⚑ A MERGE IS A FOLD, SO IT RUNS AT THE FOLD ENGINE. `ir2_leaf_wrap_config()` is the engine
    // the leaves' CHILD (the IR-v2 descriptor batch) is minted at — no proof this pool ever sees
    // carries it. Taking it here would verify every child at an engine it was not minted at, and
    // this driver is the one that has to stay byte-identical to serial `aggregate_tree`.
    let config = crate::ivc_turn_chain::turn_chain_root_config();
    let backend = crate::plonky3_recursion_impl::recursive::create_recursion_backend();
    let params = ProveNextLayerParams::default();
    let root_out = merge_two_segment_proofs(&left, &right, &config, &backend, &params)?;
    Ok(root_out)
}

/// Receive the next result, mapping the channel-closed error to a [`TurnChainError`] (a worker
/// panicked or the pool died mid-fold).
fn self_recv(pool: &MergePool) -> Result<MergeResult, TurnChainError> {
    pool.recv_result()
        .map_err(|_| TurnChainError::RecursionFailed {
            reason: "merge pool closed before the aggregation completed (a worker panicked?)"
                .to_string(),
        })
}

/// Convenience: drive the scan-state aggregation with the configured worker count
/// ([`configured_merge_workers`]) and the configured queue depth.
pub fn aggregate_tree_scan_state_configured(
    leaves: Vec<RecursionOutput<DreggRecursionConfig>>,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    let workers = configured_merge_workers();
    let queue_depth = env_usize("DREGG_MERGE_QUEUE_DEPTH", DEFAULT_MERGE_QUEUE_DEPTH);
    aggregate_tree_scan_state(leaves, workers, queue_depth)
}
