//! F-DOS-1 — proof of defence: a submitted turn must NOT wedge the node.
//!
//! ## The break this test pins down
//!
//! Red-team finding **F-DOS-1** (`redteam/MULTINODE-BYZANTINE-FINDINGS.md`,
//! task #116/#109): the public devnet's HTTP submit handler ran the full
//! `p3-batch-stark` prover (~750 ms / turn) **inline while holding the global
//! `state.write()` lock**. One submitted turn pinned a tokio worker in proving;
//! every other task that needs the write lock — block production, gossip, HTTP —
//! starved behind it. Observed live: the node stopped producing blocks for **5+
//! minutes** and served 0 bytes until a `systemctl restart`.
//!
//! ## What this test proves
//!
//! It reproduces the *exact architectural mechanism* (a `tokio::sync::RwLock`
//! standing in for the node's `state` lock, a "block producer" heartbeat task
//! that must take `state.write()` each tick to advance height, and a submit
//! that touches the same lock) and contrasts the two designs over the SAME
//! honest transfer turn, using the SAME real components the node uses:
//!
//!   * OLD path — `submit_old_inline_prove`: take `state.write()`, run the real
//!     STARK prover (`stark::try_prove` over `EffectVmAir`) under the lock,
//!     return only after proving. → the heartbeat is STARVED: zero (or near-zero)
//!     blocks produced while the submit holds the lock for the whole proof; the
//!     commit ack takes the full prove time (hundreds of ms). This is the wedge.
//!
//!   * NEW path — `submit_new_revalidate_then_async_prove`: take `state.write()`,
//!     DIRECTLY revalidate the witness FRI-free (`bespoke_air_accepts` — the same
//!     predicate `api.rs::revalidate_http_witness` calls), commit `Tentative`,
//!     DROP the lock, hand proving to an async pool off the lock (the
//!     `node::prove_pool` shape). → the heartbeat KEEPS PRODUCING blocks
//!     throughout, the commit ack returns in single-digit ms, and the proof
//!     attaches asynchronously LATER (Proven).
//!
//! ## The soundness bar (l4v / soundness-preserving)
//!
//! The fast commit is sound because it **directly CHECKS the witness, it does
//! not trust it**: `bespoke_air_accepts` re-evaluates every AIR constraint
//! (the exact predicate the audited verifier enforces). A test below feeds a
//! TAMPERED trace and asserts the NEW path REJECTS it before committing — so the
//! async-proof move cannot launder a bad witness. Proofs are *additive
//! attestation* for light-clients / cross-trust, not a per-step commit gate.
//!
//! Run (offload the build via persvati):
//!   scripts/pbuild async cargo test -p dregg-node --test f_dos_1_request_path_liveness \
//!     -- --nocapture --ignored

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use dregg_circuit::BabyBear;
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect, EffectVmAir, generate_effect_vm_trace};
use dregg_circuit::effect_vm_p3_full_air::bespoke_air_accepts;
use tokio::sync::RwLock;

/// Probe alphas for the FRI-free multi-alpha constraint fold — mirrors
/// `node/src/api.rs::revalidation_alphas` (fixed, non-zero, distinct).
fn revalidation_alphas() -> [BabyBear; 4] {
    [
        BabyBear::new(0x1234_5678),
        BabyBear::new(0x9abc_def1),
        BabyBear::new(0x2468_ace0),
        BabyBear::new(0x7777_7777),
    ]
}

/// The honest turn under test: a single transfer (the verifiable-execution
/// beachhead). Returns the (trace, public_inputs) the node's commit path
/// derives from the actor's pre-state.
fn honest_transfer_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let st = CellState::new(100_000, 0);
    let effects = vec![VmEffect::Transfer { amount: 50, direction: 1 }];
    let (trace, mut pis) = generate_effect_vm_trace(&st, &effects);
    // The agent-cell tag the verifier's single-proof replay binding requires
    // (matches `revalidate_http_witness`).
    pis[dregg_circuit::effect_vm::pi::IS_AGENT_CELL] = BabyBear::ONE;
    (trace, pis)
}

/// A minimal stand-in for the node's `state` — what every handler and the block
/// producer contend on via `state.write().await`. `height` is the consensus
/// block height the producer heartbeat advances; `committed` is the count of
/// turns that reached a Tentative commit.
#[derive(Default)]
struct NodeStateStub {
    height: u64,
    committed: u64,
}

/// The block-producer heartbeat: every `tick`, take the WRITE lock and advance
/// height by one (exactly what `blocklace_sync`'s self-block producer does — it
/// needs the same `state.write()` the submit handler takes). Runs until
/// `stop` flips. Returns nothing; progress is observed via `state.height`.
async fn run_block_producer(
    state: Arc<RwLock<NodeStateStub>>,
    tick: Duration,
    stop: Arc<std::sync::atomic::AtomicBool>,
) {
    while !stop.load(Ordering::Relaxed) {
        {
            let mut s = state.write().await;
            s.height += 1;
        }
        tokio::time::sleep(tick).await;
    }
}

// ===========================================================================
// OLD path — prove INLINE under the state-write lock (the F-DOS-1 wedge).
// ===========================================================================

/// Reproduces the pre-fix commit handler: hold `state.write()` across the full
/// CPU-bound STARK proof. Returns the wall-clock the caller waited for its ack.
async fn submit_old_inline_prove(
    state: Arc<RwLock<NodeStateStub>>,
    trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
) -> Duration {
    let t0 = Instant::now();
    // The lock is held for the ENTIRE proof — this is the bug. Any other task
    // (block producer, gossip, other HTTP) that wants `state.write()` blocks
    // for the whole prove time.
    let mut s = state.write().await;
    let air = EffectVmAir::new(trace.len());
    let _proof = dregg_circuit::stark::try_prove(&air, &trace, &pis)
        .expect("honest transfer proves");
    s.committed += 1;
    drop(s);
    t0.elapsed()
}

// ===========================================================================
// NEW path — revalidate FRI-free under the lock, prove ASYNC off the lock.
// ===========================================================================

/// The committed-but-pending receipt the fast ack returns. The proof lands
/// asynchronously into `proven` later.
struct CommitAck {
    /// Wall-clock the caller waited for the (Tentative) commit ack.
    ack_latency: Duration,
    /// Set true once the async pool attaches the STARK proof (Proven).
    proven: Arc<std::sync::atomic::AtomicBool>,
}

/// Reproduces the fixed commit handler (`api.rs::post_submit_turn` +
/// `prove_pool`): under the write lock, DIRECTLY revalidate the witness
/// (FRI-free), commit Tentative, DROP the lock, then spawn the real STARK proof
/// off the lock and flip `proven` when it lands. Returns immediately with a
/// fast Tentative ack. `Err` if the witness fails revalidation (rejected before
/// commit — the soundness tooth).
async fn submit_new_revalidate_then_async_prove(
    state: Arc<RwLock<NodeStateStub>>,
    trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
) -> Result<CommitAck, String> {
    let t0 = Instant::now();

    // --- Under the lock: FRI-free DIRECT witness revalidation (no proving). ---
    // This is sub-millisecond (see circuit/tests/turn_revalidation_vs_prove.rs);
    // the lock is held only for this cheap check + the state mutation.
    let proven = {
        let mut s = state.write().await;
        let accepted = bespoke_air_accepts(&trace, &pis, &revalidation_alphas());
        if !accepted {
            // Reject BEFORE committing — the witness is checked, not trusted.
            return Err("witness failed direct constraint revalidation".to_string());
        }
        s.committed += 1; // Tentative commit.
        let proven = Arc::new(std::sync::atomic::AtomicBool::new(false));
        proven
        // lock dropped here ↑↓ (end of block) — proving runs OFF the lock.
    };

    let ack_latency = t0.elapsed();

    // --- Off the lock: hand the real STARK proof to the async pool. ---
    // `spawn_blocking` because proving is CPU-bound (exactly `prove_pool::run_job`).
    let proven_for_task = proven.clone();
    let trace_for_task = trace;
    let pis_for_task = pis;
    tokio::spawn(async move {
        let res = tokio::task::spawn_blocking(move || {
            let air = EffectVmAir::new(trace_for_task.len());
            dregg_circuit::stark::try_prove(&air, &trace_for_task, &pis_for_task)
                .expect("async honest transfer proves")
        })
        .await;
        if res.is_ok() {
            proven_for_task.store(true, Ordering::Relaxed);
        }
    });

    Ok(CommitAck { ack_latency, proven })
}

// ===========================================================================
// TEST 1 — the OLD path WEDGES the producer; the NEW path keeps it LIVE.
// ===========================================================================

/// Multi-worker so the producer and the submit run on different threads — the
/// real node is multi-threaded; the wedge is about LOCK contention, not a
/// single-thread executor.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "runs the real STARK prover (~750 ms); run with --ignored --nocapture"]
async fn f_dos_1_old_path_wedges_new_path_stays_live() {
    let (trace, pis) = honest_transfer_witness();

    // The producer ticks every 2 ms — a fast heartbeat so a few-hundred-ms wedge
    // is unmistakable (a healthy producer makes ~100 blocks in 200 ms).
    let tick = Duration::from_millis(2);

    // -------- OLD PATH: prove under the lock --------
    let state_old = Arc::new(RwLock::new(NodeStateStub::default()));
    let stop_old = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let producer_old = tokio::spawn(run_block_producer(
        state_old.clone(),
        tick,
        stop_old.clone(),
    ));
    // Let the producer warm up and establish it IS producing.
    tokio::time::sleep(Duration::from_millis(40)).await;
    let height_before_old = state_old.read().await.height;
    assert!(
        height_before_old > 0,
        "sanity: the producer must be live before the submit"
    );

    let old_ack = submit_old_inline_prove(state_old.clone(), trace.clone(), pis.clone()).await;
    let height_after_old = state_old.read().await.height;
    let blocks_during_old_submit = height_after_old - height_before_old;

    stop_old.store(true, Ordering::Relaxed);
    let _ = producer_old.await;

    // -------- NEW PATH: revalidate fast, prove async off-lock --------
    let state_new = Arc::new(RwLock::new(NodeStateStub::default()));
    let stop_new = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let producer_new = tokio::spawn(run_block_producer(
        state_new.clone(),
        tick,
        stop_new.clone(),
    ));
    tokio::time::sleep(Duration::from_millis(40)).await;
    let height_before_new = state_new.read().await.height;
    assert!(height_before_new > 0, "sanity: producer live before NEW submit");

    let ack = submit_new_revalidate_then_async_prove(state_new.clone(), trace.clone(), pis.clone())
        .await
        .expect("honest turn commits Tentative on the NEW path");

    // The producer MUST keep advancing while the async proof is in flight. Wait
    // out (more than) one full prove time and watch the heartbeat the whole way.
    let height_at_ack_new = state_new.read().await.height;
    tokio::time::sleep(old_ack + Duration::from_millis(100)).await;
    let height_after_proof_new = state_new.read().await.height;
    let blocks_during_new_window = height_after_proof_new - height_before_new;
    let proven_eventually = ack.proven.load(Ordering::Relaxed);

    stop_new.store(true, Ordering::Relaxed);
    let _ = producer_new.await;

    // -------- Report (the before/after the task asks for) --------
    eprintln!("\n==================== F-DOS-1 defence ====================");
    eprintln!("  OLD path (prove under the state-write lock — the wedge):");
    eprintln!("    commit-ack latency        : {:>8.1} ms", old_ack.as_secs_f64() * 1e3);
    eprintln!("    blocks produced DURING submit: {blocks_during_old_submit}  (producer STARVED)");
    eprintln!("  NEW path (revalidate fast, prove async off-lock):");
    eprintln!("    Tentative commit-ack latency : {:>8.3} ms", ack.ack_latency.as_secs_f64() * 1e3);
    eprintln!("    blocks during {:.0} ms window  : {blocks_during_new_window}  (producer LIVE)",
        (old_ack + Duration::from_millis(100)).as_secs_f64() * 1e3);
    eprintln!("    height advanced even by ack-time: {} -> {}", height_before_new, height_at_ack_new);
    eprintln!("    async STARK proof attached (Proven): {proven_eventually}");
    eprintln!("=========================================================\n");

    // -------- Assertions: the wedge, and its defence --------

    // (a) OLD path: the producer is STARVED for the whole proof. A healthy 2ms
    //     producer would make tens-to-hundreds of blocks in a few hundred ms;
    //     under the lock it makes at most a tiny handful (whatever squeaked
    //     through before the submit grabbed the lock). Use a generous ceiling so
    //     this is not flaky, but far below a live producer's rate.
    let old_proof_ms = old_ack.as_secs_f64() * 1e3;
    assert!(
        old_proof_ms > 50.0,
        "sanity: the real prover should take tens-to-hundreds of ms (got {old_proof_ms:.1} ms); \
         if proving got trivially fast this contrast is meaningless"
    );
    let healthy_blocks_estimate = (old_proof_ms / tick.as_secs_f64() / 1e3) as u64;
    assert!(
        blocks_during_old_submit < healthy_blocks_estimate / 4 + 2,
        "F-DOS-1 reproduction: under inline proving the producer is starved — \
         it made {blocks_during_old_submit} blocks during a {old_proof_ms:.0} ms submit, \
         where a live 2ms producer would make ~{healthy_blocks_estimate}"
    );

    // (b) NEW path: the Tentative commit ack returns FAST — single-digit ms, NOT
    //     the hundreds-of-ms proof time. Allow a comfortable ceiling for CI noise
    //     but assert it is a small fraction of the OLD ack.
    let new_ack_ms = ack.ack_latency.as_secs_f64() * 1e3;
    assert!(
        new_ack_ms < old_proof_ms / 4.0,
        "NEW path commit ack ({new_ack_ms:.3} ms) must be far faster than inline-prove \
         ({old_proof_ms:.1} ms) — proving is off the request path"
    );

    // (c) NEW path: the producer KEEPS PRODUCING throughout the proof window —
    //     no freeze. Over a window ≥ one prove time at a 2ms tick it should make
    //     many blocks; require it to clearly out-produce the starved OLD path.
    assert!(
        blocks_during_new_window > blocks_during_old_submit * 4 + 10,
        "NEW path: producer must stay LIVE during async proving — made \
         {blocks_during_new_window} blocks vs {blocks_during_old_submit} starved on OLD path"
    );

    // (d) NEW path: the async STARK proof DID attach (Proven later) — the
    //     attestation layer still happens, just off the critical path.
    assert!(
        proven_eventually,
        "NEW path: the async STARK proof must attach to the committed receipt (Proven later)"
    );
}

// ===========================================================================
// TEST 2 — soundness tooth: the fast commit CHECKS the witness (no trust).
// ===========================================================================

/// The async-prove move is only sound because the commit path DIRECTLY
/// revalidates the witness. A tampered trace must be REJECTED before the
/// Tentative commit — proving it later cannot save (or launder) a bad witness.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn f_dos_1_new_path_rejects_tampered_witness_before_commit() {
    let (mut trace, pis) = honest_transfer_witness();

    // Honest witness commits.
    let state = Arc::new(RwLock::new(NodeStateStub::default()));
    let ok = submit_new_revalidate_then_async_prove(state.clone(), trace.clone(), pis.clone()).await;
    assert!(ok.is_ok(), "honest witness must pass direct revalidation and commit");
    assert_eq!(state.read().await.committed, 1, "honest turn is committed");

    // Tamper an interior trace cell — the forged witness violates the AIR.
    trace[0][0] = trace[0][0] + BabyBear::new(1);
    let state2 = Arc::new(RwLock::new(NodeStateStub::default()));
    let rejected =
        submit_new_revalidate_then_async_prove(state2.clone(), trace, pis).await;
    assert!(
        rejected.is_err(),
        "F-DOS-1 soundness: a tampered witness MUST be rejected by direct revalidation \
         BEFORE the (fast) commit — the witness is CHECKED, not trusted"
    );
    assert_eq!(
        state2.read().await.committed,
        0,
        "a rejected witness must leave the state byte-identical (nothing committed)"
    );
}

// ===========================================================================
// TEST 3 — many concurrent submits do not wedge the producer (the multi-node /
// burst amplification F-DOS-1 warned about: one HTTP request ⇒ one frozen
// runtime). On the NEW path a BURST commits fast and the producer stays live.
// ===========================================================================

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "runs the real STARK prover under a burst; run with --ignored --nocapture"]
async fn f_dos_1_burst_does_not_wedge_producer() {
    let (trace, pis) = honest_transfer_witness();
    let tick = Duration::from_millis(2);

    let state = Arc::new(RwLock::new(NodeStateStub::default()));
    let stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let producer = tokio::spawn(run_block_producer(state.clone(), tick, stop.clone()));
    tokio::time::sleep(Duration::from_millis(40)).await;
    let height_before = state.read().await.height;

    // Fire a burst of submits. Each commits Tentative fast; proofs run async on
    // the (bounded) blocking pool. The producer must keep advancing throughout.
    let burst = 16u64;
    let committed = Arc::new(AtomicU64::new(0));
    let mut acks = Vec::new();
    let t0 = Instant::now();
    for _ in 0..burst {
        let ack = submit_new_revalidate_then_async_prove(state.clone(), trace.clone(), pis.clone())
            .await
            .expect("burst turn commits Tentative");
        committed.fetch_add(1, Ordering::Relaxed);
        acks.push(ack);
    }
    let burst_commit_time = t0.elapsed();
    let height_after_burst_commits = state.read().await.height;

    // The whole BURST of fast commits should take well under a single inline
    // proof time — it never touches proving on the request path.
    eprintln!(
        "\n  F-DOS-1 burst: {burst} Tentative commits in {:.1} ms ({:.3} ms/commit); \
         producer height {height_before} -> {height_after_burst_commits} during the burst",
        burst_commit_time.as_secs_f64() * 1e3,
        burst_commit_time.as_secs_f64() * 1e3 / burst as f64,
    );

    assert_eq!(
        committed.load(Ordering::Relaxed),
        burst,
        "every burst turn must commit Tentative (no commit blocked on proving)"
    );
    assert!(
        height_after_burst_commits > height_before,
        "producer must keep producing blocks DURING a submit burst (no wedge)"
    );

    // Wait for the async proofs to drain and confirm the attestation layer ran.
    tokio::time::sleep(Duration::from_secs(8)).await;
    let proven_count = acks
        .iter()
        .filter(|a| a.proven.load(Ordering::Relaxed))
        .count();
    let height_after_drain = state.read().await.height;
    eprintln!(
        "  F-DOS-1 burst: {proven_count}/{burst} async proofs attached; \
         producer reached height {height_after_drain} (stayed live throughout)\n"
    );

    stop.store(true, Ordering::Relaxed);
    let _ = producer.await;

    assert!(
        height_after_drain > height_after_burst_commits,
        "producer must keep advancing while async proofs drain (never frozen)"
    );
    assert!(
        proven_count > 0,
        "at least some async proofs must attach (attestation layer runs off the critical path)"
    );
}
