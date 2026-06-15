//! The node-side submit-queue DRAINER — the READ side of pg-dregg's write loop
//! (`docs/PG-DREGG.md` §11.4, M3), symmetric to the WRITE side in
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
//!    agent-derivation, receipt-chain), then executes it through THE ONE executor
//!    gate ([`crate::executor_setup::execute_via_producer`], #171) — the verified
//!    Lean producer is authoritative exactly as for an HTTP-submitted turn;
//! 3. writes the outcome back in one `UPDATE`:
//!    `status='executed', receipt_hash=…, resolved_at=now()` on commit, or
//!    `status='refused', error=…` on rejection.
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
//! `RootChain` ordinal discipline. The drainer's load-bearing contract is solely
//! "execute the queued intent through the real executor and resolve the row."
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

/// The outcome of executing one queued turn — what gets written back to the row.
enum DrainOutcome {
    /// The turn committed; carry the receipt hash back to the submitter.
    Executed { receipt_hash: [u8; 32] },
    /// The turn was refused (bad bytes, bad signature, agent mismatch, receipt
    /// chain mismatch, or the executor rejected it). The reason is recorded so a
    /// submitter polling `submit_queue.error` learns why.
    Refused { error: String },
}

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

/// Execute one queued signed turn through the REAL executor, returning the
/// outcome to write back. This mirrors the admission gates of
/// `api::post_submit_signed_turn` (the remote-ingress HTTP handler) exactly, so a
/// pg-submitted turn is held to the identical bar as one arriving over HTTP:
/// signature over the turn hash, agent == signer's default cell, receipt-chain
/// continuity, then [`crate::executor_setup::execute_via_producer`] — the ONE
/// executor gate (#171) routing through the verified Lean producer.
async fn execute_submission(state: &NodeState, signed_turn: &[u8]) -> DrainOutcome {
    // Decode the postcard SignedTurn bytes the pg-user enqueued.
    let signed: SignedTurn = match postcard::from_bytes(signed_turn) {
        Ok(s) => s,
        Err(e) => {
            return DrainOutcome::Refused {
                error: format!("malformed SignedTurn bytes: {e}"),
            };
        }
    };

    // Gate 1 — the signature must verify over the turn hash.
    let turn_hash_bytes = signed.turn.hash();
    if !signed.signer.verify(&turn_hash_bytes, &signed.signature) {
        return DrainOutcome::Refused {
            error: "invalid turn signature".to_string(),
        };
    }

    // Gate 2 — the turn's agent must be the signer's default agent cell (the
    // same derivation api.rs enforces: derive_raw(signer, blake3("default"))).
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let expected_agent = dregg_cell::CellId::derive_raw(&signed.signer.0, &default_token_id);
    if signed.turn.agent != expected_agent {
        return DrainOutcome::Refused {
            error: "turn agent does not match signer default cell".to_string(),
        };
    }

    // Take the write lock and execute under it (same lock the HTTP submit path
    // holds while executing — the ledger is the single authoritative writer).
    let mut s = state.write().await;
    if !s.unlocked {
        return DrainOutcome::Refused {
            error: "node cipherclerk is locked".to_string(),
        };
    }

    // Gate 3 — receipt-chain continuity for the node's own agent chain (matches
    // api.rs: if the turn claims a previous_receipt_hash it must equal the head).
    let expected_prev = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());
    if let Some(claimed_prev) = signed.turn.previous_receipt_hash {
        if Some(claimed_prev) != expected_prev {
            return DrainOutcome::Refused {
                error: "receipt chain mismatch".to_string(),
            };
        }
    }

    // THE ONE executor gate (#171): execute through the producer-aware path —
    // the verified Lean producer is authoritative for the covered set, exactly
    // as for a locally- or HTTP-submitted turn. No new execution path.
    let executor = crate::executor_setup::new_submit_executor(&s);
    if let Some(head) = expected_prev {
        executor.set_last_receipt_hash(signed.turn.agent, head);
    }
    let lean_producer_enabled = s.lean_producer_enabled;
    let exec_result = crate::executor_setup::execute_via_producer(
        &executor,
        &signed.turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

    match exec_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            // The receipt hash is the outcome carried back to the submitter. The
            // node's own cclerk receipt chain is NOT appended to here: that chain
            // tracks the node operator's own turns, and a pg-submitted turn is a
            // foreign agent's (the same reason the HTTP `/turns/submit` handler
            // only chains its gossip artifact, not this drainer's lane). The
            // authoritative ledger mutation already happened inside
            // `execute_via_producer`; the durable-commit + post-state mirror ride
            // the existing finality path, not this module.
            let receipt_hash = receipt.receipt_hash();
            tracing::info!(
                receipt_hash = %crate::trustline_service::hex_encode(&receipt_hash),
                "pg-drainer: queued turn COMMITTED through the verified executor"
            );
            DrainOutcome::Executed { receipt_hash }
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => DrainOutcome::Refused {
            error: format!("turn rejected: {reason}"),
        },
        dregg_turn::TurnResult::Expired => DrainOutcome::Refused {
            error: "turn expired".to_string(),
        },
        dregg_turn::TurnResult::Pending => DrainOutcome::Refused {
            error: "turn pending (conditional turns are not queue-drainable)".to_string(),
        },
    }
}

/// Write the outcome back to the row in ONE `UPDATE`, flipping `status` away from
/// `pending` and stamping `resolved_at`. On commit: `status='executed'` +
/// `receipt_hash`. On refusal: `status='refused'` + `error`. The `WHERE
/// status='pending'` guard makes a re-drain idempotent — a row another pass
/// already resolved is skipped (0 rows updated), so a coalesced wake or a restart
/// mid-drain never double-resolves.
async fn resolve_row(client: &Client, id: &str, outcome: DrainOutcome) -> Result<(), String> {
    match outcome {
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
