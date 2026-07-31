//! The node-side submit-queue DRAINER — the READ side of pg-dregg's write loop
//! (`.docs-history-noclaude/PG-DREGG.md` §11.4, M3), symmetric to the WRITE side in
//! [`crate::pg_mirror`].
//!
//! # The one gap this closes
//!
//! The §11 write outbox (`pg_dregg::mirror::ddl::write_outbox`) already ships the
//! *enqueue* half: a pg role calls `dregg_submit_turn(signed_turn, agent)` and a
//! row lands in `dregg.submit_queue` with `status='pending'`, RLS-gated so a role
//! enqueues only the turns its capability admits `submit` on. What was missing was
//! the half that closes the loop: a row's `status` never walked
//! `pending → executed | refused`, because nothing *drained* the queue. This
//! module is that drainer. It is the node-side tail that:
//!
//! 1. `LISTEN`s on the `dregg_submit_queue` notify channel (low latency) AND
//!    periodically sweeps the `submit_queue_pending` partial index (a safety net
//!    so a notification lost across a reconnect, or a row enqueued while the
//!    drainer was down, is still drained — a node restart resumes from the
//!    `pending` rows, losing nothing);
//! 2. for each pending row, `postcard`-decodes the `signed_turn` bytes into a
//!    [`dregg_sdk::SignedTurn`] and runs the SAME admission gates the node's
//!    `POST /turns/submit` handler runs (signature over the turn hash,
//!    agent-derivation, receipt-chain), staging it through THE ONE executor gate
//!    ([`crate::executor_setup::execute_via_producer`], #171) — the verified Lean
//!    producer is authoritative exactly as for an HTTP-submitted turn — and then
//!    rolling that staging run back and submitting the envelope to the blocklace;
//! 3. writes the outcome back in one `UPDATE`:
//!    `status='executed', receipt_hash=…, resolved_at=now()` once the turn is
//!    DURABLY FINALIZED, or `status='refused', error=…` on rejection. A turn that
//!    is admitted but not yet finalized leaves the row `pending`.
//!
//! # The spine invariant (preserved)
//!
//! > **Reads are free SQL; state mutates ONLY through verified turns.**
//!
//! Postgres never executes — `dregg_submit_turn` only *records an intent*. The
//! drainer hands that intent to the REAL verified executor (the same one every
//! ingress uses), so the executor stays the sole trust boundary; the drainer is
//! plumbing, not a second semantics. A queued turn the executor rejects is
//! recorded `refused` and changes no state. The post-state cell projection into
//! the `dregg.*` mirror tables is NOT this module's job: it rides the existing
//! commit-path mirror ([`crate::state::NodeStateInner::mirror_committed_record`])
//! when the executed turn reaches finality, exactly as a locally-submitted turn's
//! post-state does — duplicating it here would fight the M2 [`crate::pg_mirror`]
//! `RootChain` ordinal discipline.
//!
//! ⚑ That paragraph WAS FALSE for the drainer until 2026-07-30, and the sentence
//! it was false about is the one right above: the drained turn never reached
//! finality, because the drainer committed the in-place execution itself and
//! submitted nothing to the blocklace. It was the only ingress that mutated
//! authoritative state outside consensus (HTTP `/turns/submit` has been
//! staging-only at every committee size since `5f0999ab9`). Reported as the
//! second half of issue #65 finding 6. The drainer's load-bearing contract is now
//! "admit the queued intent on the shared predicate, hand it to consensus, and
//! resolve the row from the durable commit log."
//!
//! # Opt-in, off by default
//!
//! The drainer connects ONLY when `pg-mirror-live` is built AND
//! `DREGG_PG_MIRROR_URL` is set — the same on/off switch the [`crate::pg_mirror`]
//! WRITE side uses ([`crate::pg_mirror::PgMirrorConfig::from_env`]). With the flag
//! unset the node behaves byte-identically: [`spawn`] returns `None` and no task
//! runs. The drainer reads the queue as the `dregg_kernel` role (the role the §11
//! DDL grants `SELECT, UPDATE` on `dregg.submit_queue`, and which must hold
//! BYPASSRLS to read every pending row regardless of submitter) — the connection
//! URL is expected to authenticate as that role.

#![cfg(feature = "pg-mirror-live")]

use std::time::Duration;

use dregg_sdk::SignedTurn;
use tokio::task::JoinHandle;
use tokio_postgres::{AsyncMessage, Client, NoTls};

// NOTE on the `id` column: `dregg.submit_queue.id` is a pg `uuid`, but the
// node's `tokio-postgres` is built WITHOUT the `with-uuid-1` feature (the WRITE
// side never needed it). Rather than add the feature, the drainer reads the id
// as `id::text` and binds it back with `$1::uuid`, so it never needs a Rust uuid
// type to cross the wire. The id is opaque to the drainer — it only ever
// round-trips it to address the row.

use crate::pg_mirror::PgMirrorConfig;
use crate::state::NodeState;

/// The postgres `LISTEN` channel the drainer wakes on. `dregg_submit_turn` does
/// not itself `NOTIFY` today (the §11 DDL is notify-free), so the drainer does
/// not RELY on a notification to make progress — the periodic sweep is the
/// source of liveness and the LISTEN is a latency optimisation for deployments
/// that add a `NOTIFY '<this channel>'` trigger on `submit_queue` inserts. The
/// name is fixed so such a trigger and the drainer agree.
const NOTIFY_CHANNEL: &str = "dregg_submit_queue";

/// The safety-net sweep cadence: even with no NOTIFY trigger installed, the
/// drainer re-scans the `pending` partial index this often, so a row enqueued
/// while no notification fired (the default DDL) is drained within one interval.
/// Short enough to feel responsive, long enough to be negligible load against
/// the `submit_queue_pending` partial index (which is empty in steady state).
const SWEEP_INTERVAL: Duration = Duration::from_millis(1000);

/// Reconnect backoff after a dropped pg connection. The drainer is a durable
/// tail: a transient pg outage must not kill it — it backs off and reconnects,
/// and the next sweep drains whatever accumulated while it was away.
const RECONNECT_BACKOFF: Duration = Duration::from_secs(5);

/// One pending submission read from `dregg.submit_queue`. `id` is the row's uuid
/// rendered as text (see the module-level note) — opaque, only round-tripped to
/// address the row in the resolving `UPDATE`.
struct PendingSubmission {
    id: String,
    signed_turn: Vec<u8>,
}

/// The outcome of draining one queued turn — what gets written back to the row.
enum DrainOutcome {
    /// The turn is DURABLY FINALIZED: a commit record exists for its turn hash in
    /// this node's own log. Carry the finalized receipt hash back to the
    /// submitter. This is the only outcome that reports state changed, and it is
    /// read from the commit log — never from a local execution result.
    Executed { receipt_hash: [u8; 32] },
    /// Admitted and submitted to consensus, but not yet finalized within this
    /// drain pass. The row stays `pending` and the next sweep re-checks; a
    /// re-drain short-circuits on the commit log rather than re-executing.
    Deferred,
    /// The turn was refused (bad bytes, bad signature, agent mismatch, receipt
    /// chain mismatch, or the executor rejected it). The reason is recorded so a
    /// submitter polling `submit_queue.error` learns why.
    Refused { error: String },
}

/// How long one drain pass waits for a submitted turn to appear in the durable
/// commit log before leaving the row `pending` for the next sweep. Solo cadence
/// is 50 ms blocks plus a 150 ms finality debounce, so this is generous; the
/// sweep interval above bounds how long a `Deferred` row waits to be re-checked.
const FINALITY_WAIT: Duration = Duration::from_secs(5);

/// Poll cadence inside [`FINALITY_WAIT`].
const FINALITY_POLL: Duration = Duration::from_millis(50);

/// Spawn the drainer task IF mirroring is configured (`DREGG_PG_MIRROR_URL` set;
/// the `pg-mirror-live` feature gates the whole module). Returns the task handle,
/// or `None` when mirroring is off (the node then runs exactly as before — no
/// task, no pg connection). Mirror of the lifecycle that [`crate::pg_mirror`]'s
/// `NodeMirror::from_env` follows for the WRITE side; spawned alongside the HTTP
/// server in `main.rs`, sharing the same [`NodeState`] handle (like the prove
/// pool). The task ends on its own when the shared runtime shuts down.
pub fn spawn(state: NodeState) -> Option<JoinHandle<()>> {
    let cfg = PgMirrorConfig::from_env()?;
    tracing::info!(
        url = %cfg.url,
        channel = NOTIFY_CHANNEL,
        sweep_ms = SWEEP_INTERVAL.as_millis() as u64,
        "pg-drainer: starting the submit-queue drainer (the §11.4 write-loop READ side)"
    );
    Some(tokio::spawn(run(cfg, state)))
}

/// The drainer's outer loop: (re)connect, drain forever, and on any connection
/// loss back off and reconnect. Never returns under normal operation (it ends
/// only when the runtime is torn down).
async fn run(cfg: PgMirrorConfig, state: NodeState) {
    loop {
        match connect_and_drain(&cfg, &state).await {
            Ok(()) => {
                // `connect_and_drain` only returns Ok on a clean connection
                // close (the connection task ended); reconnect after a beat.
                tracing::warn!(
                    "pg-drainer: postgres connection closed; reconnecting after backoff"
                );
            }
            Err(e) => {
                tracing::error!(
                    error = %e,
                    "pg-drainer: connection error; reconnecting after backoff \
                     (pending rows drain on the next successful connect — nothing lost)"
                );
            }
        }
        tokio::time::sleep(RECONNECT_BACKOFF).await;
    }
}

/// Connect to postgres as the kernel role, `LISTEN`, run an initial sweep, then
/// alternate between notification wake-ups and periodic sweeps until the
/// connection drops. Returns `Ok(())` on a clean connection close, `Err` on a
/// connection or setup error (the outer loop reconnects either way).
async fn connect_and_drain(cfg: &PgMirrorConfig, state: &NodeState) -> Result<(), String> {
    // Connect, and take the connection object so we can poll it for async
    // notifications (`AsyncMessage::Notification`) ourselves — unlike the
    // PgSink WRITE side, which only needs the client and spawns the connection
    // to drive completed queries, the drainer wants the LISTEN notification
    // stream, which arrives via the connection's poll_message.
    let (client, mut connection) = tokio_postgres::connect(&cfg.url, NoTls)
        .await
        .map_err(|e| format!("pg connect: {e}"))?;

    // The notification wake-up signal: the connection-driver task pings this
    // whenever a NOTIFY on our channel arrives (or when the connection ends).
    let (notify_tx, mut notify_rx) = tokio::sync::mpsc::channel::<()>(8);
    let conn_task = tokio::spawn(async move {
        use futures_util::StreamExt;
        use futures_util::stream::poll_fn;
        // Drive the connection AND surface notifications. `poll_message`
        // advances the protocol and yields `AsyncMessage::Notification` for
        // each NOTIFY; we collapse them to a single "wake the drainer" ping
        // (the drainer always re-scans the whole pending set, so we never need
        // the payload — coalescing many notifications into one sweep is correct
        // and cheap).
        let mut messages = poll_fn(move |cx| connection.poll_message(cx));
        while let Some(msg) = messages.next().await {
            match msg {
                Ok(AsyncMessage::Notification(n)) => {
                    tracing::debug!(
                        channel = n.channel(),
                        "pg-drainer: NOTIFY received — waking the drainer"
                    );
                    // Best-effort wake; a full buffer already means a sweep is
                    // imminent, so dropping the extra ping is fine.
                    let _ = notify_tx.try_send(());
                }
                Ok(_) => {}
                Err(e) => {
                    tracing::error!(error = %e, "pg-drainer: connection error in driver");
                    break;
                }
            }
        }
        // Connection ended — wake the drainer so it notices and reconnects.
        let _ = notify_tx.try_send(());
    });

    // LISTEN on our channel (a no-op for liveness when no NOTIFY trigger is
    // installed, but harmless and ready for one).
    if let Err(e) = client
        .batch_execute(&format!("LISTEN {NOTIFY_CHANNEL}"))
        .await
    {
        conn_task.abort();
        return Err(format!("LISTEN {NOTIFY_CHANNEL}: {e}"));
    }
    tracing::info!(
        channel = NOTIFY_CHANNEL,
        "pg-drainer: connected + LISTENing"
    );

    // Initial sweep: drain everything already pending (resume after a restart).
    drain_all_pending(&client, state).await?;

    // Steady state: wake on a notification OR the sweep timer, then drain.
    loop {
        let woke = tokio::time::timeout(SWEEP_INTERVAL, notify_rx.recv()).await;
        match woke {
            // A notification arrived: but `None` means the channel closed (the
            // connection driver ended) — treat that as a clean close so we
            // reconnect.
            Ok(Some(())) => {}
            Ok(None) => {
                conn_task.abort();
                return Ok(());
            }
            // Timed out — the periodic safety-net sweep.
            Err(_) => {}
        }
        // Whatever woke us, re-scan the whole pending set (idempotent: rows we
        // already resolved are no longer `pending`, so a coalesced wake never
        // double-executes). A drain error means the connection is suspect —
        // bubble up so the outer loop reconnects.
        if let Err(e) = drain_all_pending(&client, state).await {
            conn_task.abort();
            return Err(e);
        }
    }
}

/// Drain every currently-`pending` row, oldest first (the `uuidv7` key /
/// `submitted_at` order). Each row is executed and resolved in turn; one bad row
/// never blocks the rest. Returns `Err` only on a postgres I/O error (the SELECT
/// or an UPDATE failing) — a *turn* rejection is a normal `refused` resolution,
/// not an error.
async fn drain_all_pending(client: &Client, state: &NodeState) -> Result<(), String> {
    let pending = fetch_pending(client).await?;
    if pending.is_empty() {
        return Ok(());
    }
    tracing::info!(
        count = pending.len(),
        "pg-drainer: draining pending submissions"
    );
    for sub in pending {
        let outcome = execute_submission(state, &sub.signed_turn).await;
        resolve_row(client, &sub.id, outcome).await?;
    }
    Ok(())
}

/// Read all pending submissions, oldest first. Uses the `submit_queue_pending`
/// partial index (the `WHERE status='pending'` predicate matches it), so this is
/// cheap — empty in steady state.
async fn fetch_pending(client: &Client) -> Result<Vec<PendingSubmission>, String> {
    let rows = client
        .query(
            "SELECT id::text, signed_turn FROM dregg.submit_queue \
             WHERE status = 'pending' ORDER BY submitted_at",
            &[],
        )
        .await
        .map_err(|e| format!("select pending: {e}"))?;
    Ok(rows
        .into_iter()
        .map(|row| PendingSubmission {
            id: row.get(0),
            signed_turn: row.get(1),
        })
        .collect())
}

/// Admit one queued signed turn and hand it to CONSENSUS, returning the outcome
/// to write back.
///
/// This mirrors `api::post_submit_signed_turn` (the remote-ingress HTTP handler)
/// exactly, in both halves:
///
/// * the same admission gates — complete shared outer authorization (Ed25519,
///   signer→agent binding, and the enrolled/required ML-DSA half), receipt-chain
///   continuity, then [`crate::executor_setup::execute_via_producer`], the ONE
///   executor gate (#171) routing through the verified Lean producer; and
/// * the same FATE for the mutation: the in-place run is ADMISSION STAGING, its
///   journal is rolled back UNCONDITIONALLY, and the envelope is submitted to the
///   blocklace so `execute_finalized_turn` is the sole authoritative application.
///
/// ⚑ WHAT THIS USED TO DO, AND WHY IT IS THE BUG A READER SHOULD LOOK FOR.
/// The drainer used to `commit_restore_point()` the in-place execution and
/// `append_receipt` on the spot, with no blocklace submission anywhere in the
/// function — while its own module docs said the post-state "rides the existing
/// commit-path mirror when the executed turn reaches finality." It never reached
/// finality. That made this the ONLY ingress that mutated authoritative state
/// outside consensus: a pg-drained turn advanced one node's nonce/balance and no
/// peer ever saw it, and the same turn arriving over consensus later would then
/// meet a bumped nonce and be refused `NonceReplay`. Reported as the second half
/// of issue #65 finding 6 ("a separate admission predicate and state-mutation
/// path"); the predicate half was closed on 2026-07-21, this half was not.
///
/// A row therefore resolves `executed` ONLY against this node's durable commit
/// log ([`dregg_persist::PersistentStore::lookup_turn`]), never against a local
/// execution result. A turn that has not finalized inside [`FINALITY_WAIT`]
/// leaves the row `pending` and the next sweep re-checks it; the commit-log
/// short-circuit at the top makes that re-drain safe, since re-executing an
/// already-finalized turn would meet its own bumped nonce and be misreported as
/// `refused`.
async fn execute_submission(state: &NodeState, signed_turn: &[u8]) -> DrainOutcome {
    // Decode the postcard SignedTurn bytes the pg-user enqueued.
    let signed: SignedTurn = match crate::signed_turn_validation::decode_signed_turn(signed_turn) {
        Ok(s) => s,
        Err(e) => {
            return DrainOutcome::Refused {
                error: e.to_string(),
            };
        }
    };

    let turn_hash = signed.turn.hash();

    // Take the write lock before validation and hold it through execution.  The
    // enrolled identity and live cell epoch used by validation therefore cannot
    // rotate between check and mutation.
    let mut s = state.write().await;
    if !s.unlocked {
        return DrainOutcome::Refused {
            error: "node cipherclerk is locked".to_string(),
        };
    }

    // COMMIT-LOG SHORT-CIRCUIT, before anything is staged. A row left `pending`
    // by an earlier pass (submitted, not yet finalized) is re-drained by the
    // sweep; if consensus has since applied it, re-executing here would meet the
    // actor's own bumped nonce and resolve the row `refused` for a turn that
    // succeeded.
    match s.store.lookup_turn(&turn_hash) {
        Ok(Some(record)) => {
            return DrainOutcome::Executed {
                receipt_hash: record.receipt_hash,
            };
        }
        Ok(None) => {}
        Err(error) => {
            return DrainOutcome::Refused {
                error: format!("could not read the durable commit log: {error}"),
            };
        }
    }

    // The same complete application-payload predicate as HTTP admission and
    // consensus finalization.  In required/native mode a self-carried key is
    // never an authority: it must equal the independently enrolled key.
    let executor = crate::executor_setup::new_submit_executor(&s);
    // Admission staging is O(touched)-reversible: arm the undo journal BEFORE the
    // first-turn claim so a refused turn — and an admitted one, which consensus
    // applies authoritatively — leaves the ledger exactly as it found it.
    s.ledger.begin_restore_point();
    // THE FIRST-TURN CLAIM, before the predicate reads the actor cell — the same
    // ordering every other ingress uses. A queued first turn from a fresh client
    // otherwise refuses `pq-identity-not-enrolled` / `live-agent-signer-mismatch`
    // here while finalization would have accepted it.
    crate::signed_turn_validation::claim_signer_actor_cell(
        &mut s.ledger,
        &signed,
        executor.require_pq(),
    );
    if let Err(error) = crate::signed_turn_validation::validate_signed_turn(
        &signed,
        &executor,
        s.ledger.get(&signed.turn.agent),
    ) {
        s.ledger.rollback_restore_point();
        return DrainOutcome::Refused {
            error: error.to_string(),
        };
    }

    // Agent-scoped receipt continuity. Compare exact Options: `None` is valid
    // only for this agent's genesis turn, never as an omitted-link reset.
    let expected_prev = s.cclerk.agent_receipt_head_hash(&signed.turn.agent);
    if signed.turn.previous_receipt_hash != expected_prev {
        s.ledger.rollback_restore_point();
        return DrainOutcome::Refused {
            error: "receipt chain mismatch".to_string(),
        };
    }

    // THE ONE executor gate (#171): execute through the producer-aware path —
    // the verified Lean producer is authoritative for the covered set, exactly
    // as for a locally- or HTTP-submitted turn. No new execution path.
    let lean_producer_enabled = s.lean_producer_enabled;
    let exec_result = crate::executor_setup::execute_via_producer(
        &executor,
        &signed.turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

    // EVERY arm rolls the journal back, admitted or refused: this run exists to
    // decide admissibility and nothing else. The executor restores its own
    // mutations on rejection, but the first-turn claim above is not the
    // executor's, and an ADMITTED turn's mutation belongs to finalization.
    let admitted = match exec_result {
        dregg_turn::TurnResult::Committed { .. } => Ok(()),
        dregg_turn::TurnResult::Rejected { reason, .. } => Err(format!("turn rejected: {reason}")),
        dregg_turn::TurnResult::Expired => Err("turn expired".to_string()),
        dregg_turn::TurnResult::Pending => {
            Err("turn pending (conditional turns are not queue-drainable)".to_string())
        }
    };
    s.ledger.rollback_restore_point();
    if let Err(error) = admitted {
        return DrainOutcome::Refused { error };
    }
    drop(s);

    // Hand the admitted envelope to consensus. A node with no blocklace can never
    // finalize it, so say that rather than reporting a success nothing applied.
    let Some(blocklace) = state.blocklace().await else {
        return DrainOutcome::Refused {
            error: "node has no blocklace handle; a queued turn cannot reach finality".to_string(),
        };
    };
    blocklace.submit_turn(state, signed_turn.to_vec()).await;

    // Resolve against the DURABLE COMMIT LOG, never against the staging run.
    let deadline = tokio::time::Instant::now() + FINALITY_WAIT;
    loop {
        match state.read().await.store.lookup_turn(&turn_hash) {
            Ok(Some(record)) => {
                let receipt_hash = record.receipt_hash;
                tracing::info!(
                    receipt_hash = %crate::trustline_service::hex_encode(&receipt_hash),
                    "pg-drainer: queued turn FINALIZED through consensus"
                );
                return DrainOutcome::Executed { receipt_hash };
            }
            Ok(None) => {}
            Err(error) => {
                return DrainOutcome::Refused {
                    error: format!("could not read the durable commit log: {error}"),
                };
            }
        }
        if tokio::time::Instant::now() >= deadline {
            tracing::info!(
                turn_hash = %crate::trustline_service::hex_encode(&turn_hash),
                "pg-drainer: queued turn admitted and submitted; awaiting finality (row stays pending)"
            );
            return DrainOutcome::Deferred;
        }
        tokio::time::sleep(FINALITY_POLL).await;
    }
}

/// Write the outcome back to the row in ONE `UPDATE`, flipping `status` away from
/// `pending` and stamping `resolved_at`. On durable finality: `status='executed'`
/// + `receipt_hash`. On refusal: `status='refused'` + `error`. On
/// [`DrainOutcome::Deferred`] the row is deliberately LEFT `pending` — the turn is
/// in consensus but not yet applied, and `executed` must never precede the commit
/// record. The `WHERE status='pending'` guard makes a re-drain idempotent — a row
/// another pass already resolved is skipped (0 rows updated), so a coalesced wake
/// or a restart mid-drain never double-resolves.
async fn resolve_row(client: &Client, id: &str, outcome: DrainOutcome) -> Result<(), String> {
    match outcome {
        // Not terminal: no UPDATE at all, so the next sweep re-reads this row and
        // short-circuits on the commit log.
        DrainOutcome::Deferred => {}
        DrainOutcome::Executed { receipt_hash } => {
            client
                .execute(
                    // Compare the uuid column AS TEXT against a text param, so
                    // tokio-postgres (built without `with-uuid-1`) binds `$1` as
                    // text cleanly — `$1::uuid` would make it infer a uuid param
                    // type it cannot serialize a `&str` into.
                    "UPDATE dregg.submit_queue \
                     SET status = 'executed', receipt_hash = $2, error = NULL, \
                         resolved_at = now() \
                     WHERE id::text = $1 AND status = 'pending'",
                    &[&id, &receipt_hash.as_slice()],
                )
                .await
                .map_err(|e| format!("update executed: {e}"))?;
        }
        DrainOutcome::Refused { error } => {
            client
                .execute(
                    "UPDATE dregg.submit_queue \
                     SET status = 'refused', error = $2, resolved_at = now() \
                     WHERE id::text = $1 AND status = 'pending'",
                    &[&id, &error],
                )
                .await
                .map_err(|e| format!("update refused: {e}"))?;
        }
    }
    Ok(())
}

// ===========================================================================
// Integration test — drains against a LIVE pg18 (gated on the test URL).
// ===========================================================================
//
// Runs ONLY when `DREGG_PG_MIRROR_TEST_URL` names a live pg18 (the same gate the
// pg_mirror WRITE-side live test uses). It installs the §11 write outbox DDL,
// enqueues a turn, runs ONE drain pass, and asserts the row flipped to
// `executed`/`refused`. Skipped otherwise, so the default test run needs no
// postgres. This is the load-bearing M3 proof: a pg-enqueued intent walks to a
// terminal status through the REAL executor.

#[cfg(test)]
mod tests {
    use super::*;

    /// The deployed node installs the Lean-verified ML-DSA cores in `run()`; a lib
    /// test never reaches that, and `dregg-pq` ABORTS THE PROCESS rather than fall
    /// back to the unaudited `fips204` crate. Every drainer fixture therefore
    /// installs them first, exactly as `faucet_grant_e2e::faucet_node` does — the
    /// pre-existing tests in this module did not, which is why a
    /// `--features pg-mirror-live` run SIGABRTed before reaching an assertion.
    fn install_verified_pq_cores() {
        let _ = crate::install_mldsa_verified_keygen_core_real();
        let _ = crate::install_mldsa_verified_sign_core_real();
        let _ = crate::install_mldsa_verified_verify_core();
    }

    async fn operator_signed_empty_turn(state: &NodeState) -> SignedTurn {
        install_verified_pq_cores();
        let mut s = state.write().await;
        s.unlocked = true;
        let operator_pk = s.cclerk.public_key().0;
        let operator = crate::executor_setup::local_agent_cell(&s);
        let token = *blake3::hash(b"default").as_bytes();
        if s.ledger.get(&operator).is_none() {
            s.ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    operator_pk,
                    token,
                    1_000_000,
                ))
                .expect("insert operator cell");
        }
        let federation_id = crate::executor_setup::federation_id_for_executor(&s);
        let action = s
            .cclerk
            .make_action(operator, "pg-queue-noop", vec![], &federation_id);
        let mut call_forest = dregg_turn::CallForest::new();
        call_forest.add_root(action);
        let mut turn = dregg_turn::Turn {
            agent: operator,
            nonce: s
                .ledger
                .get(&operator)
                .expect("operator cell")
                .state
                .nonce(),
            fee: 0,
            memo: None,
            valid_until: Some(i64::MAX / 2),
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: s.cclerk.agent_receipt_head_hash(&operator),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: vec![],
            cross_effect_dependencies: vec![],
            effect_witness_index_map: vec![],
        };
        turn.fee = crate::executor_setup::new_submit_executor(&s).estimate_cost(&turn);
        s.cclerk.sign_turn(&turn)
    }

    fn refusal_error(outcome: DrainOutcome) -> String {
        match outcome {
            DrainOutcome::Refused { error } => error,
            DrainOutcome::Executed { .. } => panic!("hostile SignedTurn must be refused"),
            DrainOutcome::Deferred => {
                panic!("hostile SignedTurn must be refused, not submitted to consensus")
            }
        }
    }

    /// A solo node with a live blocklace + finality executor — the only shape in
    /// which a queued turn can reach a terminal `executed`, now that consensus
    /// finalization is the sole authoritative application.
    async fn drainer_node() -> (NodeState, tempfile::TempDir) {
        let (state, _app, _faucet, tmp) = crate::faucet_grant_e2e::faucet_node().await;
        (state, tmp)
    }

    /// Block until the operator's agent-scoped causal chain reaches `expected`.
    /// `execute_submission` resolves on the DURABLE commit log, which lands a beat
    /// before the in-RAM overlay/receipt projection; a follow-up turn must be built
    /// from the projected state, not from a read that raced it.
    async fn await_agent_receipt_count(
        state: &NodeState,
        agent: dregg_cell::CellId,
        expected: usize,
    ) {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
        loop {
            if state.read().await.cclerk.agent_receipt_count(&agent) >= expected {
                return;
            }
            assert!(
                tokio::time::Instant::now() < deadline,
                "agent receipt chain never reached {expected}"
            );
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    }

    /// ⚑ THE DEFECT, EXPRESSED AS A REFUSAL (issue #65, finding 6, second half).
    ///
    /// The drainer used to commit the queued turn's in-place execution itself —
    /// `commit_restore_point` + `append_receipt` — and submit nothing to the
    /// blocklace, which made it the only ingress that mutated authoritative state
    /// outside consensus. On a node with no blocklace handle at all that is now
    /// impossible to express: there is nowhere to send the turn, so it is refused,
    /// and the ledger is byte-identical afterwards.
    ///
    /// THE CANARY: restore the old `s.ledger.commit_restore_point()` +
    /// `s.cclerk.append_receipt(receipt)` arm and this goes RED on both the
    /// outcome and the ledger root.
    #[tokio::test]
    async fn a_node_without_consensus_refuses_rather_than_committing_locally() {
        install_verified_pq_cores();
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        let signed = operator_signed_empty_turn(&state).await;
        let agent = signed.turn.agent;
        let bytes = postcard::to_stdvec(&signed).expect("encode submission");

        let before = {
            let s = state.read().await;
            (
                dregg_persist::canonical_ledger_root(&s.ledger),
                s.cclerk.agent_receipt_count(&agent),
            )
        };
        assert_eq!(
            refusal_error(execute_submission(&state, &bytes).await),
            "node has no blocklace handle; a queued turn cannot reach finality"
        );
        let s = state.read().await;
        assert_eq!(
            dregg_persist::canonical_ledger_root(&s.ledger),
            before.0,
            "an admitted-but-unfinalized queued turn must leave the authoritative ledger alone"
        );
        assert_eq!(s.cclerk.agent_receipt_count(&agent), before.1);
    }

    /// The optional PostgreSQL transport is not a weaker alternate ingress:
    /// absent, invalid, and attacker-substituted outer ML-DSA halves all die in
    /// the same shared pre-mutation validator as HTTP/finalization.
    #[tokio::test]
    async fn drainer_rejects_stripped_invalid_and_substituted_outer_pq() {
        assert!(
            std::env::var("DREGG_REQUIRE_PQ")
                .map(|v| v != "0" && !v.eq_ignore_ascii_case("false"))
                .unwrap_or(true),
            "hostile native-PQ gate must run with required PQ enabled"
        );
        install_verified_pq_cores();
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        let signed = operator_signed_empty_turn(&state).await;

        let mut stripped = signed.clone();
        stripped.pq_signature.clear();
        stripped.pq_signer.clear();
        let stripped_bytes = postcard::to_stdvec(&stripped).expect("encode stripped");
        assert_eq!(
            refusal_error(execute_submission(&state, &stripped_bytes).await),
            "post-quantum turn signature required but absent"
        );

        let mut invalid = signed.clone();
        invalid.pq_signature[0] ^= 0x40;
        let invalid_bytes = postcard::to_stdvec(&invalid).expect("encode invalid");
        assert_eq!(
            refusal_error(execute_submission(&state, &invalid_bytes).await),
            "invalid post-quantum turn signature"
        );

        let attacker = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[0xA9; 32]);
        let mut substituted = signed.clone();
        substituted.pq_signer = attacker.public_bytes();
        substituted.pq_signature = attacker
            .sign(&signed.turn.hash())
            .expect("attacker produces valid ML-DSA signature under its own key");
        assert!(
            dregg_turn::pq::ml_dsa_verify(
                &substituted.pq_signer,
                &substituted.turn.hash(),
                &substituted.pq_signature,
            ),
            "substitution fixture must be cryptographically valid under the attacker key"
        );
        let substituted_bytes = postcard::to_stdvec(&substituted).expect("encode substituted");
        assert_eq!(
            refusal_error(execute_submission(&state, &substituted_bytes).await),
            "carried post-quantum signer does not match the canonical or migration identity"
        );

        let mut trailing = postcard::to_stdvec(&signed).expect("encode canonical SignedTurn");
        trailing.extend_from_slice(&[0x00, 0x7F]);
        assert_eq!(
            refusal_error(execute_submission(&state, &trailing).await),
            "trailing bytes after SignedTurn envelope: 2"
        );
    }

    /// A queued turn reaches a terminal `executed` only THROUGH CONSENSUS, and
    /// each finalized receipt advances the same agent-scoped durable log HTTP and
    /// finalization use.  Exact Option equality makes an omitted second-turn link
    /// a pre-mutation refusal rather than a new genesis.
    ///
    /// `Executed` is read from `store.lookup_turn`, so a green here is proof the
    /// envelope entered the DAG and `execute_finalized_turn` applied it — the
    /// drainer's own staging run is rolled back and can no longer produce it.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn drainer_finalizes_through_consensus_and_refuses_omitted_link() {
        assert!(
            std::env::var("DREGG_REQUIRE_PQ")
                .map(|v| v != "0" && !v.eq_ignore_ascii_case("false"))
                .unwrap_or(true),
            "PG chain gate must run with native PQ required"
        );
        let (state, _tmp) = drainer_node().await;

        let first = operator_signed_empty_turn(&state).await;
        let agent = first.turn.agent;
        let first_bytes = postcard::to_stdvec(&first).expect("encode first");
        assert!(matches!(
            execute_submission(&state, &first_bytes).await,
            DrainOutcome::Executed { .. }
        ));
        await_agent_receipt_count(&state, agent, 1).await;

        let second = operator_signed_empty_turn(&state).await;
        assert!(second.turn.previous_receipt_hash.is_some());
        let second_bytes = postcard::to_stdvec(&second).expect("encode second");
        assert!(matches!(
            execute_submission(&state, &second_bytes).await,
            DrainOutcome::Executed { .. }
        ));
        await_agent_receipt_count(&state, agent, 2).await;

        let (operator, before_nonce, omitted) = {
            let s = state.read().await;
            let operator = crate::executor_setup::local_agent_cell(&s);
            let before_nonce = s
                .ledger
                .get(&operator)
                .expect("operator cell")
                .state
                .nonce();
            let mut omitted_turn = second.turn.clone();
            omitted_turn.nonce = before_nonce;
            omitted_turn.previous_receipt_hash = None;
            (operator, before_nonce, s.cclerk.sign_turn(&omitted_turn))
        };
        let omitted_bytes = postcard::to_stdvec(&omitted).expect("encode omitted link");
        assert_eq!(
            refusal_error(execute_submission(&state, &omitted_bytes).await),
            "receipt chain mismatch"
        );
        let s = state.read().await;
        assert_eq!(s.cclerk.agent_receipt_count(&operator), 2);
        assert_eq!(
            s.ledger
                .get(&operator)
                .expect("operator cell")
                .state
                .nonce(),
            before_nonce,
            "omitted link must be refused before nonce mutation"
        );
    }

    /// The crash falsifier this module carried `#[ignore]`d, now RUNNABLE and
    /// asserted against the RECONSTRUCTED durable image rather than a reopen.
    ///
    /// It was named for the direct-PG architecture: the receipt sink was
    /// durable-first and fail-closed, but its redb transaction was not the
    /// finalized ledger/commit-log transaction, so a crash could restore a receipt
    /// whose ledger mutation was never durably committed. Its own `#[ignore]`
    /// reason said the fix was "until PG submissions enter consensus
    /// finalization" — which is what they now do, so it runs.
    ///
    /// The commit tail is read directly, which is the whole statement: a durable
    /// `CommitRecord` for THIS turn hash, carrying the receipt hash and the
    /// actor's post-state in `touched_cells`, whose recorded `ledger_root` equals
    /// the live ledger's root. Under the old direct-commit drainer none of that
    /// existed — the receipt was durable through its own sink and the ledger
    /// mutation lived only in RAM, which is exactly what the `#[ignore]` named.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn pg_submission_lands_receipt_and_ledger_in_one_durable_image() {
        let (state, _dir) = drainer_node().await;
        let signed = operator_signed_empty_turn(&state).await;
        let agent = signed.turn.agent;
        let turn_hash = signed.turn.hash();
        let bytes = postcard::to_stdvec(&signed).expect("encode submission");
        let receipt_hash = match execute_submission(&state, &bytes).await {
            DrainOutcome::Executed { receipt_hash } => receipt_hash,
            other => panic!(
                "the queued turn must finalize; got {}",
                match other {
                    DrainOutcome::Refused { error } => error,
                    _ => "deferred".to_string(),
                }
            ),
        };
        await_agent_receipt_count(&state, agent, 1).await;

        let s = state.read().await;
        let record = s
            .store
            .lookup_turn(&turn_hash)
            .expect("read the durable commit log")
            .expect("the drained turn must have a durable commit record");
        assert_eq!(record.receipt_hash, receipt_hash);
        assert_eq!(
            record.ledger_root,
            dregg_persist::canonical_ledger_root(&s.ledger),
            "the finalized commit's recorded root must equal the live ledger's root — a RAM-only \
             mutation shows up exactly here"
        );
        let durable_receipts = s.cclerk.agent_receipt_count(&agent) as u64;
        assert_eq!(durable_receipts, 1);
        let durable_actor = record
            .touched_cells
            .iter()
            .find(|cell| cell.id() == agent)
            .expect("the actor's post-state must ride the same durable transaction as the receipt");
        assert!(
            durable_actor.state.nonce() >= durable_receipts,
            "durable receipt head outran the durable ledger: receipts={durable_receipts}, nonce={}",
            durable_actor.state.nonce()
        );
    }

    /// A drain pass that takes an explicit client (so the test drives the same
    /// `drain_all_pending` the live loop uses, without standing up the LISTEN
    /// connection driver).
    async fn drain_once(client: &Client, state: &NodeState) -> Result<(), String> {
        drain_all_pending(client, state).await
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn drains_a_pending_submission_to_a_terminal_status() {
        let Ok(url) = std::env::var("DREGG_PG_MIRROR_TEST_URL") else {
            eprintln!(
                "drains_a_pending_submission_to_a_terminal_status: \
                 DREGG_PG_MIRROR_TEST_URL unset — skipping (needs a live pg18)"
            );
            return;
        };

        // Stand up the schema + the §11 write outbox in the target db (run the
        // DDL directly so the test is extension-version-independent).
        let (admin, admin_conn) = tokio_postgres::connect(&url, tokio_postgres::NoTls)
            .await
            .expect("connect admin");
        tokio::spawn(async move {
            let _ = admin_conn.await;
        });
        admin
            .batch_execute(&pg_dregg::mirror::ddl::tier_b())
            .await
            .expect("install Tier-B schema");
        admin
            .batch_execute(&pg_dregg::mirror::ddl::write_outbox())
            .await
            .expect("install the write outbox");
        admin
            .batch_execute("DELETE FROM dregg.submit_queue")
            .await
            .expect("clean prior rows");

        // A node with a funded operator agent cell, so a real signed turn from
        // that agent can execute.
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        let signed_bytes = {
            let mut s = state.write().await;
            s.unlocked = true;
            let operator_pk = s.cclerk.public_key().0;
            let operator = crate::executor_setup::local_agent_cell(&s);
            let token = *blake3::hash(b"default").as_bytes();
            let op_cell = dregg_cell::Cell::with_balance(operator_pk, token, 10_000_000);
            assert_eq!(op_cell.id(), operator, "agent-cell derivation must match");
            let _ = s.ledger.insert_cell(op_cell);

            // A second cell to receive a transfer (so the turn does real work).
            let dest_token = *blake3::hash(b"drainer-dest").as_bytes();
            let dest = dregg_cell::Cell::with_balance(operator_pk, dest_token, 0);
            let dest_id = dest.id();
            s.ledger.insert_cell(dest).expect("dest inserts");

            // Build + sign a turn the way a remote SDK client would: a single
            // Transfer from the operator agent, signed by the operator key.
            let federation_id = crate::executor_setup::federation_id_for_executor(&s);
            let action = s.cclerk.make_action(
                operator,
                "drainer_e2e_transfer",
                vec![dregg_turn::Effect::Transfer {
                    from: operator,
                    to: dest_id,
                    amount: 1_000,
                }],
                &federation_id,
            );
            let mut call_forest = dregg_turn::CallForest::new();
            call_forest.add_root(action);
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0);
            let mut turn = dregg_turn::Turn {
                agent: operator,
                nonce: s
                    .ledger
                    .get(&operator)
                    .map(|c| c.state.nonce())
                    .unwrap_or(0),
                fee: 0,
                memo: None,
                valid_until: Some(now + 3600),
                call_forest,
                depends_on: vec![],
                previous_receipt_hash: None,
                conservation_proof: None,
                sovereign_witnesses: std::collections::HashMap::new(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            };
            let estimator = crate::executor_setup::new_submit_executor(&s);
            turn.fee = estimator.estimate_cost(&turn);
            let signed = s.cclerk.sign_turn(&turn);
            postcard::to_stdvec(&signed).expect("encode SignedTurn")
        };

        // The agent column the §11 RLS gate keys on — the operator agent cell.
        let agent_bytes = {
            let s = state.read().await;
            crate::executor_setup::local_agent_cell(&s).0
        };

        // Enqueue it the way `dregg_submit_turn` does (here as the kernel,
        // bypassing the RLS gate — the gate is the WRITE-side's proof, exercised
        // in pg-dregg's own tests; THIS test exercises the DRAIN).
        admin
            .execute(
                "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES ($1, $2)",
                &[&agent_bytes.as_slice(), &signed_bytes.as_slice()],
            )
            .await
            .expect("enqueue pending submission");

        // ONE drain pass.
        drain_once(&admin, &state).await.expect("drain pass");

        // The row reached a terminal status with the outcome filled in.
        let row = admin
            .query_one(
                "SELECT status, receipt_hash IS NOT NULL, error \
                 FROM dregg.submit_queue ORDER BY submitted_at LIMIT 1",
                &[],
            )
            .await
            .expect("read resolved row");
        let status: String = row.get(0);
        let has_receipt: bool = row.get(1);
        let error: Option<String> = row.get(2);
        assert_ne!(status, "pending", "the drained row left pending");
        assert_eq!(
            status, "executed",
            "the funded operator transfer commits (error={error:?})"
        );
        assert!(has_receipt, "an executed row carries its receipt_hash");

        // Idempotency: a second drain pass is a no-op (the row is no longer
        // pending), so the status is unchanged.
        drain_once(&admin, &state).await.expect("second drain pass");
        let status2: String = admin
            .query_one(
                "SELECT status FROM dregg.submit_queue ORDER BY submitted_at LIMIT 1",
                &[],
            )
            .await
            .expect("re-read row")
            .get(0);
        assert_eq!(status2, "executed", "re-drain is idempotent");

        // A garbage submission is refused (not stuck pending).
        admin
            .execute(
                "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES ($1, $2)",
                &[&[0x11u8; 32].as_slice(), &b"not a signed turn".as_slice()],
            )
            .await
            .expect("enqueue a bad submission");
        drain_once(&admin, &state).await.expect("drain the bad row");
        let bad_status: String = admin
            .query_one(
                "SELECT status FROM dregg.submit_queue \
                 WHERE signed_turn = $1",
                &[&b"not a signed turn".as_slice()],
            )
            .await
            .expect("read bad row")
            .get(0);
        assert_eq!(
            bad_status, "refused",
            "a malformed turn is refused, never stuck"
        );
    }
}
