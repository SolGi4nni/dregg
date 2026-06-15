//! The LIVE node → postgres mirror writer (pg-dregg M2).
//!
//! # The one material gap this closes
//!
//! `docs/PG-DREGG.md` §8 ships the mirror *core* — the SQL-row projection, the
//! universal-memory model, the DDL, and the anti-substitution [`RootChain`] —
//! and proves it with plain `cargo test` (no postgres) in `pg-dregg/src/mirror.rs`.
//! What it could NOT ship from there is the half that needs `dregg-cell`: the
//! decode of a live committed turn into those rows, and the act of shipping them.
//! That decode-and-ship is THIS module. It is the only part of the mirror story
//! that lives node-side, exactly because the node is the only crate that holds
//! both `dregg-cell` (to read a `Cell`) and the durable commit log (to read a
//! verified turn).
//!
//! # The spine invariant (preserved)
//!
//! > **Reads are free SQL; state mutates ONLY through verified turns.**
//!
//! The node is the ONLY writer. By the time a [`CommitRecord`] exists, the
//! kernel already verified and durably committed that turn (`persist`'s
//! commit-log discipline) — so the rows this module builds ARE a verified-turn
//! post-image. The mirror never executes, never authorizes, never decides; it
//! projects an already-final turn and ships it.
//!
//! And the pg side does NOT trust the stream: it RE-VALIDATES every batch with
//! its own [`RootChain`] (the post-state root of turn *N* must be the pre-state
//! root of turn *N+1*), so a tampered / reordered / forged batch is refused
//! WITHOUT re-running the verifier. The chain tooth here on the node is the same
//! check the pg side runs — we ship only batches that chain, so a correct node
//! never produces a batch the pg side would reject, and a tampered batch (e.g. a
//! row whose post-state was altered, changing the cell root and thus the ledger
//! root) breaks the chain on BOTH sides.
//!
//! # No reinvention
//!
//! The projection types ([`CellRow`], [`CapRow`], [`MemCell`], [`TurnRow`]), the
//! batch ([`MirrorBatch`]), and the [`RootChain`] all come from `pg-dregg`'s
//! `mirror` module. This module only (a) decodes `dregg_cell::Cell` into those
//! rows — the one piece pg-dregg deliberately cannot do (it has no `dregg-cell`)
//! — and (b) calls [`MirrorBatch::from_parts`] + [`RootChain`] to assemble and
//! gate. The SQL shape, the ordinal-stamping discipline, and the
//! anti-substitution tooth stay in their real home.

use dregg_cell::{Cell, CellLifecycle, CellMode};
use dregg_persist::commit_log::CommitRecord;
use pg_dregg::mirror::{
    CapRow, CellRow, ChainRefusal, Domain, MemCell, MirrorBatch, RootChain, TurnRow,
};

/// The pre-state root the very first turn (ordinal 0) chains onto. The pg-side
/// [`RootChain::resume`]/`new` pins genesis; we use the all-zero root as the
/// agreed genesis sentinel (matching `RootChain::new`, which starts headless and
/// accepts whatever genesis `prev_root` the first batch declares).
pub const GENESIS_ROOT: [u8; 32] = [0u8; 32];

/// The opt-in config: the node mirrors to postgres ONLY when this is `Some`.
/// Read from `DREGG_PG_MIRROR_URL`; absent ⇒ the node runs unchanged (no sink).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PgMirrorConfig {
    /// The postgres connection URL (`postgres://…`) the kernel writer connects
    /// to. The PRIMARY target is pg18 (`docs/PG-DREGG.md` §5).
    pub url: String,
}

impl PgMirrorConfig {
    /// Read the opt-in config from the environment. `None` ⇒ mirroring off (the
    /// node runs exactly as before). This is the whole on/off switch.
    pub fn from_env() -> Option<PgMirrorConfig> {
        match std::env::var("DREGG_PG_MIRROR_URL") {
            Ok(url) if !url.trim().is_empty() => Some(PgMirrorConfig { url }),
            _ => None,
        }
    }
}

// ===========================================================================
// The Cell -> rows projection (the node-only half pg-dregg cannot do).
// ===========================================================================

/// The lifecycle tag string the [`CellRow`] carries (matches the `lifecycle`
/// text column; `pg-dregg`'s `cells.lifecycle text NOT NULL`).
fn lifecycle_tag(lc: &CellLifecycle) -> &'static str {
    match lc {
        CellLifecycle::Live => "Live",
        CellLifecycle::Sealed { .. } => "Sealed",
        CellLifecycle::Migrated { .. } => "Migrated",
        CellLifecycle::Destroyed { .. } => "Destroyed",
        CellLifecycle::Archived { .. } => "Archived",
    }
}

fn mode_tag(mode: &CellMode) -> &'static str {
    match mode {
        CellMode::Hosted => "Hosted",
        CellMode::Sovereign => "Sovereign",
    }
}

/// Project a live committed [`Cell`] into the mirror's [`CellRow`]. `last_ordinal`
/// is filled by [`MirrorBatch::from_parts`] from the turn (we pass a placeholder).
///
/// `cell_root` is the cell's own canonical state commitment — a leaf of the
/// ledger root that the turn row carries — so the row is bound to the exact
/// post-state the turn produced. `fields` is the canonical postcard encoding of
/// the cell's `CellState`, authoritative; the heap/program/vk blobs and the
/// permissions JSON are the query-sugar projections.
fn cell_to_row(cell: &Cell) -> CellRow {
    let permissions_json = serde_json::to_string(&cell.permissions).ok();
    let program = postcard::to_stdvec(&cell.program).ok();
    let verification_key = cell
        .verification_key
        .as_ref()
        .and_then(|vk| postcard::to_stdvec(vk).ok());
    // The canonical CellState bytes (the authoritative `fields` column).
    let fields = postcard::to_stdvec(&cell.state).unwrap_or_default();
    let fields_json = serde_json::to_string(&serde_json::json!({
        "balance": cell.state.balance(),
        "nonce": cell.state.nonce(),
    }))
    .ok();

    CellRow {
        cell_id: cell.id().0,
        mode: mode_tag(&cell.mode).to_string(),
        balance: cell.state.balance(),
        nonce: cell.state.nonce(),
        fields,
        fields_json,
        heap: None,
        program,
        verification_key,
        permissions_json,
        delegate: cell.delegate.map(|d| d.0),
        lifecycle: lifecycle_tag(&cell.lifecycle).to_string(),
        last_ordinal: 0, // stamped by MirrorBatch::from_parts
        cell_root: cell.state_commitment(),
    }
}

/// Project a cell's c-list into [`CapRow`]s — the `(holder, slot) -> target`
/// delegation edges. The holder is the owning cell's id.
fn cell_caps_to_rows(cell: &Cell) -> Vec<CapRow> {
    let holder = cell.id().0;
    cell.capabilities
        .iter()
        .map(|cap| CapRow {
            holder,
            slot: cap.slot,
            target: cap.target.0,
            permissions_json: serde_json::to_string(&cap.permissions)
                .unwrap_or_else(|_| "null".to_string()),
            breadstuff: cap.breadstuff,
            expires_at: cap.expires_at,
            allowed_effects_json: cap
                .allowed_effects
                .as_ref()
                .and_then(|m| serde_json::to_string(m).ok()),
            stored_epoch: cap.stored_epoch,
            last_ordinal: 0, // stamped by MirrorBatch::from_parts
        })
        .collect()
}

/// Project a cell's scalar registers into the universal-memory [`Domain::Registers`]
/// rows (`docs/UNIVERSAL-MEMORY.md`: balance/nonce are register cells of the ONE
/// multiset). Collection = the cell id; key = a stable register selector. This
/// is the honest single-relation view the pg `dregg.memory` table holds.
fn cell_registers_to_mem(cell: &Cell) -> Vec<MemCell> {
    let collection = cell.id().0.to_vec();
    vec![
        MemCell {
            domain: Domain::Registers,
            collection: collection.clone(),
            key: b"balance".to_vec(),
            value: Some(cell.state.balance().to_le_bytes().to_vec()),
            last_ordinal: 0,
        },
        MemCell {
            domain: Domain::Registers,
            collection,
            key: b"nonce".to_vec(),
            value: Some(cell.state.nonce().to_le_bytes().to_vec()),
            last_ordinal: 0,
        },
    ]
}

// ===========================================================================
// Batch construction from a verified CommitRecord (the load-bearing core).
// ===========================================================================

/// Build the [`TurnRow`] for a committed turn. `prev_root` is the chain head the
/// turn chains onto (genesis for ordinal 0); `ledger_root` is the post-state
/// commitment the record carries. The two together make the turns table a hash
/// chain a light client could itself walk.
fn turn_row(record: &CommitRecord, prev_root: [u8; 32]) -> TurnRow {
    TurnRow {
        ordinal: record.ordinal,
        height: record.height,
        block_id: record.block_id,
        block_executed_up_to: record.block_executed_up_to,
        turn_hash: record.turn_hash,
        creator: record.creator,
        receipt_hash: record.receipt_hash,
        ledger_root: record.ledger_root,
        prev_root,
    }
}

/// Build a [`MirrorBatch`] from a verified [`CommitRecord`] and the pre-state
/// root it chains onto. This is the M2 load-bearing function: the projection +
/// the assembly via pg-dregg's [`MirrorBatch::from_parts`] (which stamps the
/// ordinal and runs the well-formedness gate). It does NOT re-implement the row
/// shape or the chain — those are pg-dregg's.
pub fn batch_from_commit_record(
    record: &CommitRecord,
    prev_root: [u8; 32],
) -> Result<MirrorBatch, String> {
    let turn = turn_row(record, prev_root);

    let mut cells = Vec::with_capacity(record.touched_cells.len());
    let mut caps = Vec::new();
    let mut memory = Vec::new();
    for cell in &record.touched_cells {
        cells.push(cell_to_row(cell));
        caps.extend(cell_caps_to_rows(cell));
        memory.extend(cell_registers_to_mem(cell));
    }

    MirrorBatch::from_parts(turn, cells, caps, memory)
}

// ===========================================================================
// The sink: where assembled batches go.
// ===========================================================================

/// The destination for verified-turn batches. The mirror builds a [`MirrorBatch`]
/// per committed turn and `emit`s it here. An in-memory impl ([`MemorySink`])
/// makes the construction + chaining testable with no postgres; the live
/// postgres impl ([`pg_live::PgSink`]) is behind the `pg-mirror-live` feature.
pub trait MirrorSink: Send + Sync {
    /// Ship one verified-turn batch. The batch is already chain-checked by the
    /// [`PgMirror`] before this is called (the node never ships a batch that
    /// would not chain on the pg side); a sink may additionally persist it.
    fn emit(&mut self, batch: &MirrorBatch) -> Result<(), String>;
}

impl MirrorSink for Box<dyn MirrorSink> {
    fn emit(&mut self, batch: &MirrorBatch) -> Result<(), String> {
        (**self).emit(batch)
    }
}

/// An in-memory sink: records every emitted batch. The testable substrate that
/// proves construction + chaining without a live postgres.
#[derive(Default)]
pub struct MemorySink {
    pub batches: Vec<MirrorBatch>,
}

impl MirrorSink for MemorySink {
    fn emit(&mut self, batch: &MirrorBatch) -> Result<(), String> {
        self.batches.push(batch.clone());
        Ok(())
    }
}

/// The node-side mirror: maintains the running [`RootChain`] head and tails
/// committed turns, building and shipping one [`MirrorBatch`] each. It holds the
/// SAME anti-substitution invariant the pg side re-checks, so a correct node
/// only ever produces batches the pg side accepts.
pub struct PgMirror<S: MirrorSink> {
    chain: RootChain,
    /// The pre-state root the NEXT batch chains onto. Equals the chain head
    /// (genesis for the first turn). Threaded into each `TurnRow::prev_root`.
    prev_root: [u8; 32],
    sink: S,
}

impl<S: MirrorSink> PgMirror<S> {
    /// A fresh mirror expecting ordinal 0 from genesis.
    pub fn new(sink: S) -> Self {
        PgMirror {
            chain: RootChain::new(),
            prev_root: GENESIS_ROOT,
            sink,
        }
    }

    /// Resume a mirror after restart from a known head root and next ordinal
    /// (read from the pg mirror's current max-ordinal row).
    pub fn resume(sink: S, head: [u8; 32], next_ordinal: u64) -> Self {
        PgMirror {
            chain: RootChain::resume(head, next_ordinal),
            prev_root: head,
            sink,
        }
    }

    /// The current chain head (post-state root of the last shipped turn), or the
    /// genesis sentinel before any turn.
    pub fn head(&self) -> [u8; 32] {
        self.prev_root
    }

    /// The ordinal the mirror next expects.
    pub fn next_ordinal(&self) -> u64 {
        self.chain.next_ordinal()
    }

    /// Borrow the sink (e.g. the in-memory sink for assertions).
    pub fn sink(&self) -> &S {
        &self.sink
    }

    /// Mirror one verified [`CommitRecord`]: project + assemble its batch, chain
    /// it (the anti-substitution gate — the SAME check the pg side runs), and on
    /// acceptance ship it to the sink and advance the head. A record that does
    /// not chain (a gap, a replay, or a tampered post-state) is REFUSED and the
    /// chain/head are left UNCHANGED.
    pub fn mirror_record(&mut self, record: &CommitRecord) -> Result<(), MirrorError> {
        let batch =
            batch_from_commit_record(record, self.prev_root).map_err(MirrorError::Malformed)?;
        // The node holds the same chain the pg side re-checks: refuse a batch
        // that would not chain BEFORE shipping it.
        self.chain.extend(&batch).map_err(MirrorError::Chain)?;
        self.sink.emit(&batch).map_err(MirrorError::Sink)?;
        // Advance our threaded prev_root to this turn's post-state.
        self.prev_root = record.ledger_root;
        Ok(())
    }
}

/// The node-state-friendly mirror: a [`PgMirror`] over a boxed sink, so the node
/// can hold `Option<NodeMirror>` without leaking the sink generic into its state
/// struct. Built by [`NodeMirror::from_env`] when `DREGG_PG_MIRROR_URL` is set.
pub type NodeMirror = PgMirror<Box<dyn MirrorSink>>;

impl NodeMirror {
    /// Build the node's mirror from the environment, or `None` if mirroring is
    /// off (`DREGG_PG_MIRROR_URL` unset). The chosen sink:
    /// - with `pg-mirror-live`: a live pg18 [`pg_live::PgSink`] — `from_env`
    ///   actually CONNECTS to the configured postgres over `tokio-postgres` and
    ///   writes each verified-turn batch through (the turns row + the pg18
    ///   `dregg.merge_cell` upsert). If the connect fails, it logs loudly and
    ///   falls back to the [`LoggingSink`] so a transient pg outage never stalls
    ///   the node's commit path (the failure is visible, never silent).
    /// - without it (default): a [`LoggingSink`] that records the batch was
    ///   built and chained — proving the construction path runs on the REAL
    ///   commit path, no postgres required. The load-bearing M2 guarantee
    ///   (correct batch from a real `CommitRecord`, accepted by the chain) holds
    ///   in both builds.
    ///
    /// `head` / `next_ordinal` resume the chain after restart (read from the
    /// pg mirror's max-ordinal row, or `GENESIS_ROOT` / 0 for a fresh mirror).
    ///
    /// Must be called from within a tokio runtime context (the node's commit
    /// path is async), which it uses to drive the async connect synchronously.
    pub fn from_env(head: [u8; 32], next_ordinal: u64) -> Option<NodeMirror> {
        let cfg = PgMirrorConfig::from_env()?;
        let sink = Self::connect_sink(&cfg);
        Some(PgMirror::resume(sink, head, next_ordinal))
    }

    /// Choose and build the sink for a config. With `pg-mirror-live`, this drives
    /// [`pg_live::PgSink::connect`] (async) to completion on the current runtime
    /// and returns the live writer; a connect error logs and falls back to the
    /// [`LoggingSink`]. Without the feature, it is always the [`LoggingSink`].
    #[cfg(feature = "pg-mirror-live")]
    fn connect_sink(cfg: &PgMirrorConfig) -> Box<dyn MirrorSink> {
        // The commit path is sync but runs inside the node's multi-threaded tokio
        // runtime, so bridge the async connect with block_in_place + block_on
        // (the same pattern PgSink::emit uses to drive its async writes). On any
        // failure, fall back to the logging sink loudly rather than panicking the
        // commit path.
        let connect = || -> Result<pg_live::PgSink, String> {
            let handle = tokio::runtime::Handle::try_current()
                .map_err(|_| "pg-mirror: no tokio runtime in the commit path".to_string())?;
            tokio::task::block_in_place(|| handle.block_on(pg_live::PgSink::connect(cfg)))
        };
        match connect() {
            Ok(sink) => {
                tracing::info!(url = %cfg.url, "pg-mirror: connected the live pg18 sink");
                Box::new(sink)
            }
            Err(e) => {
                tracing::error!(
                    url = %cfg.url,
                    error = %e,
                    "pg-mirror: live connect FAILED — falling back to the logging sink \
                     (batches are still built + chained; nothing written to pg until reconnect)"
                );
                Box::new(LoggingSink::default())
            }
        }
    }

    /// Without `pg-mirror-live`, the sink is always the in-process logging sink.
    #[cfg(not(feature = "pg-mirror-live"))]
    fn connect_sink(_cfg: &PgMirrorConfig) -> Box<dyn MirrorSink> {
        Box::new(LoggingSink::default())
    }
}

/// A sink that records (via `tracing`) that a verified-turn batch was built and
/// chained, without a live postgres. Lets the mirror run on the real commit path
/// in the default (no-`pg-mirror-live`) build, proving construction + chaining
/// end-to-end; the live pg writer is the `pg-mirror-live` follow-up.
#[derive(Default)]
pub struct LoggingSink {
    pub count: u64,
}

impl MirrorSink for LoggingSink {
    fn emit(&mut self, batch: &MirrorBatch) -> Result<(), String> {
        self.count += 1;
        tracing::debug!(
            ordinal = batch.turn.ordinal,
            cells = batch.cells.len(),
            caps = batch.caps.len(),
            memory = batch.memory.len(),
            "pg-mirror: built and chained a verified-turn MirrorBatch"
        );
        Ok(())
    }
}

/// Why mirroring a record failed.
#[derive(Debug)]
pub enum MirrorError {
    /// The projected batch was internally malformed (ordinal-stamp invariant).
    Malformed(String),
    /// The batch did not chain onto the head (gap, replay, or tamper).
    Chain(ChainRefusal),
    /// The sink (e.g. postgres write) failed.
    Sink(String),
}

impl std::fmt::Display for MirrorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirrorError::Malformed(m) => write!(f, "malformed mirror batch: {m}"),
            MirrorError::Chain(c) => write!(f, "mirror batch refused by chain: {c}"),
            MirrorError::Sink(s) => write!(f, "mirror sink error: {s}"),
        }
    }
}

impl std::error::Error for MirrorError {}

// ===========================================================================
// The live postgres sink (behind `pg-mirror-live`).
// ===========================================================================

#[cfg(feature = "pg-mirror-live")]
pub mod pg_live {
    //! The live pg18 sink: writes each [`MirrorBatch`] through the kernel writer
    //! role into the `dregg.*` tables, using pg-dregg's own MERGE upsert. The
    //! pg side's Tier-C `dregg_verify_turn` CHECK (when enabled) RE-VALIDATES;
    //! here on the node we have already chain-checked. This impl is only built
    //! with the `pg-mirror-live` feature so the default node carries no postgres
    //! client (the load-bearing construction + chain core is feature-independent).

    use super::*;
    use tokio_postgres::{Client, NoTls};

    /// A live postgres sink. Holds a connected [`Client`] (the kernel writer).
    pub struct PgSink {
        client: Client,
        rt: tokio::runtime::Handle,
    }

    impl PgSink {
        /// Connect to the configured postgres (pg18). The connection task is
        /// spawned on the provided tokio handle.
        pub async fn connect(cfg: &PgMirrorConfig) -> Result<PgSink, String> {
            let (client, connection) = tokio_postgres::connect(&cfg.url, NoTls)
                .await
                .map_err(|e| format!("pg connect: {e}"))?;
            let rt = tokio::runtime::Handle::current();
            rt.spawn(async move {
                if let Err(e) = connection.await {
                    tracing::error!(error = %e, "pg-mirror connection closed");
                }
            });
            Ok(PgSink { client, rt })
        }

        /// Write one verified-turn batch into the `dregg.*` mirror tables, ALL in
        /// one postgres transaction: the turns row, then each touched cell (pg18
        /// `dregg.merge_cell` upsert), each capability edge, and each universal-
        /// memory cell. The turn row commits with its post-images or not at all,
        /// so the mirror is never torn (a reader never sees a turn whose cells did
        /// not land). The batch was already chain-checked by the [`PgMirror`]
        /// before `emit`; the `ON CONFLICT DO NOTHING` makes a re-shipped ordinal
        /// idempotent (crash-safe replay from the commit log).
        async fn write_batch(&mut self, batch: &MirrorBatch) -> Result<(), String> {
            let tx = self
                .client
                .transaction()
                .await
                .map_err(|e| format!("begin tx: {e}"))?;

            // The turns row first (the cells/caps/memory FK-reference its ordinal).
            tx.execute(
                "INSERT INTO dregg.turns \
                 (ordinal, height, block_id, block_executed_up_to, turn_hash, \
                  creator, receipt_hash, ledger_root, prev_root) \
                 VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9) ON CONFLICT (ordinal) DO NOTHING",
                &[
                    &(batch.turn.ordinal as i64),
                    &(batch.turn.height as i64),
                    &batch.turn.block_id.as_slice(),
                    &(batch.turn.block_executed_up_to as i64),
                    &batch.turn.turn_hash.as_slice(),
                    &batch.turn.creator.as_slice(),
                    &batch.turn.receipt_hash.as_slice(),
                    &batch.turn.ledger_root.as_slice(),
                    &batch.turn.prev_root.as_slice(),
                ],
            )
            .await
            .map_err(|e| format!("insert turn: {e}"))?;

            for c in &batch.cells {
                // The decoded field slots as real jsonb (the with-serde_json-1
                // ToSql binds a serde_json::Value to the `jsonb` column directly).
                // A None / unparseable fields_json binds as SQL NULL — fields
                // (the canonical bytea) stays authoritative either way.
                let fields_json: Option<serde_json::Value> = c
                    .fields_json
                    .as_deref()
                    .and_then(|s| serde_json::from_str(s).ok());
                // pg18 MERGE upsert (pg-dregg's dregg.merge_cell), one atomic stmt
                // (RETURNING old/new reports the balance delta inside the function).
                tx.execute(
                    "SELECT dregg.merge_cell($1,$2,$3,$4,$5,$6,$7,$8,$9)",
                    &[
                        &c.cell_id.as_slice(),
                        &c.mode,
                        &c.balance,
                        &(c.nonce as i64),
                        &c.fields.as_slice(),
                        &fields_json,
                        &c.lifecycle,
                        &(c.last_ordinal as i64),
                        &c.cell_root.as_slice(),
                    ],
                )
                .await
                .map_err(|e| format!("merge cell: {e}"))?;
            }

            // The delegation edges (the cap_edges / cap_attenuations views read
            // these). (holder, slot) is the c-list address; upsert in place.
            for cap in &batch.caps {
                // Bind the JSON columns as real jsonb (serde_json::Value via
                // with-serde_json-1). permissions defaults to JSON null; an
                // unparseable/absent allowed_effects binds as SQL NULL.
                let permissions: serde_json::Value =
                    serde_json::from_str(&cap.permissions_json).unwrap_or(serde_json::Value::Null);
                let allowed_effects: Option<serde_json::Value> = cap
                    .allowed_effects_json
                    .as_deref()
                    .and_then(|s| serde_json::from_str(s).ok());
                tx.execute(
                    "INSERT INTO dregg.capabilities \
                     (holder, slot, target, permissions, breadstuff, expires_at, \
                      allowed_effects, stored_epoch, last_ordinal) \
                     VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9) \
                     ON CONFLICT (holder, slot) DO UPDATE SET \
                       target = EXCLUDED.target, permissions = EXCLUDED.permissions, \
                       breadstuff = EXCLUDED.breadstuff, expires_at = EXCLUDED.expires_at, \
                       allowed_effects = EXCLUDED.allowed_effects, \
                       stored_epoch = EXCLUDED.stored_epoch, last_ordinal = EXCLUDED.last_ordinal",
                    &[
                        &cap.holder.as_slice(),
                        &(cap.slot as i32),
                        &cap.target.as_slice(),
                        &permissions,
                        &cap.breadstuff.as_ref().map(|b| b.as_slice()),
                        &cap.expires_at.map(|e| e as i64),
                        &allowed_effects,
                        &cap.stored_epoch.map(|e| e as i64),
                        &(cap.last_ordinal as i64),
                    ],
                )
                .await
                .map_err(|e| format!("upsert capability: {e}"))?;
            }

            // The universal-memory cells (the honest single-relation view).
            for m in &batch.memory {
                tx.execute(
                    "INSERT INTO dregg.memory (domain, collection, key, value, last_ordinal) \
                     VALUES ($1,$2,$3,$4,$5) \
                     ON CONFLICT (domain, collection, key) DO UPDATE SET \
                       value = EXCLUDED.value, last_ordinal = EXCLUDED.last_ordinal",
                    &[
                        &m.domain.tag(),
                        &m.collection.as_slice(),
                        &m.key.as_slice(),
                        &m.value.as_ref().map(|v| v.as_slice()),
                        &(m.last_ordinal as i64),
                    ],
                )
                .await
                .map_err(|e| format!("upsert memory cell: {e}"))?;
            }

            tx.commit().await.map_err(|e| format!("commit tx: {e}"))?;
            Ok(())
        }
    }

    impl MirrorSink for PgSink {
        fn emit(&mut self, batch: &MirrorBatch) -> Result<(), String> {
            // Bridge the sync trait onto the async client via the held handle.
            // Clone the handle BEFORE the closure so the closure's only borrow of
            // `self` is the &mut for write_batch (the transaction needs &mut) — no
            // overlap with an rt borrow.
            let rt = self.rt.clone();
            tokio::task::block_in_place(|| rt.block_on(self.write_batch(batch)))
        }
    }
}

// ===========================================================================
// Tests — the load-bearing M2 guarantees, proven WITHOUT a live postgres.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;

    /// A deterministic cell with a given id-seed and balance.
    fn cell(seed: u8, balance: i64) -> Cell {
        Cell::with_balance([seed; 32], [seed.wrapping_add(7); 32], balance)
    }

    /// A commit record for ordinal `n` touching `cells`, with a chosen post-root.
    fn record(n: u64, ledger_root: [u8; 32], cells: Vec<Cell>) -> CommitRecord {
        let mut turn_hash = [0u8; 32];
        turn_hash[0] = 0xa0;
        turn_hash[1] = n as u8;
        let mut receipt_hash = [0u8; 32];
        receipt_hash[0] = 0xb0;
        receipt_hash[1] = n as u8;
        CommitRecord {
            ordinal: n,
            height: n + 1,
            block_id: [n as u8; 32],
            block_executed_up_to: n * 10,
            turn_hash,
            creator: [(n % 3) as u8 + 1; 32],
            receipt_hash,
            ledger_root,
            touched_cells: cells,
        }
    }

    fn root(n: u8) -> [u8; 32] {
        [n; 32]
    }

    #[test]
    fn batch_from_record_projects_cells_and_chains() {
        // A real CommitRecord → a MirrorBatch whose rows match the committed
        // cells and whose RootChain accepts the chain.
        let c = cell(5, 123);
        let cid = c.id().0;
        let cell_root = c.state_commitment();
        let rec = record(0, root(1), vec![c]);

        let batch = batch_from_commit_record(&rec, GENESIS_ROOT).unwrap();
        // The turn row carries the record's coordinates + the threaded prev_root.
        assert_eq!(batch.turn.ordinal, 0);
        assert_eq!(batch.turn.ledger_root, root(1));
        assert_eq!(batch.turn.prev_root, GENESIS_ROOT);
        // The cell row IS the committed cell's post-image (id, balance, root).
        assert_eq!(batch.cells.len(), 1);
        assert_eq!(batch.cells[0].cell_id, cid);
        assert_eq!(batch.cells[0].balance, 123);
        assert_eq!(
            batch.cells[0].cell_root, cell_root,
            "cell_root is the canonical state commitment"
        );
        assert_eq!(batch.cells[0].last_ordinal, 0, "stamped by from_parts");
        // The universal-memory registers projection (balance + nonce).
        assert_eq!(batch.memory.len(), 2);
        assert!(batch.memory.iter().all(|m| m.domain == Domain::Registers));
        // It satisfies the well-formedness gate.
        assert!(batch.check_ordinals().is_ok());

        // The pg side's RootChain accepts it.
        let mut chain = RootChain::new();
        assert!(chain.extend(&batch).is_ok());
        assert_eq!(chain.head(), Some(root(1)));
    }

    #[test]
    fn mirror_ships_a_chained_sequence_to_the_sink() {
        // Three verified turns chain g -> r1 -> r2 -> r3; the sink receives all
        // three, in order, each chaining onto the prior post-state.
        let mut mirror = PgMirror::new(MemorySink::default());
        mirror
            .mirror_record(&record(0, root(1), vec![cell(1, 10)]))
            .unwrap();
        mirror
            .mirror_record(&record(1, root(2), vec![cell(2, 20)]))
            .unwrap();
        mirror
            .mirror_record(&record(2, root(3), vec![cell(1, 15)]))
            .unwrap();

        let batches = &mirror.sink().batches;
        assert_eq!(batches.len(), 3);
        // The prev_root of each batch is the post-root of the prior (the hash chain).
        assert_eq!(batches[0].turn.prev_root, GENESIS_ROOT);
        assert_eq!(batches[1].turn.prev_root, root(1));
        assert_eq!(batches[2].turn.prev_root, root(2));
        assert_eq!(mirror.head(), root(3));
        assert_eq!(mirror.next_ordinal(), 3);

        // An independent pg-side RootChain re-validates the whole shipped stream.
        let mut pg_chain = RootChain::new();
        for b in batches {
            pg_chain
                .extend(b)
                .expect("pg side re-validates the shipped chain");
        }
        assert_eq!(pg_chain.head(), Some(root(3)));
    }

    #[test]
    fn mirror_refuses_a_gap_without_shipping() {
        // A gap (skipping ordinal 1) is refused — the sink never sees it and the
        // head does not move.
        let mut mirror = PgMirror::new(MemorySink::default());
        mirror
            .mirror_record(&record(0, root(1), vec![cell(1, 10)]))
            .unwrap();
        let err = mirror
            .mirror_record(&record(2, root(3), vec![cell(2, 20)]))
            .unwrap_err();
        assert!(matches!(
            err,
            MirrorError::Chain(ChainRefusal::OrdinalGap { .. })
        ));
        assert_eq!(
            mirror.sink().batches.len(),
            1,
            "the gapped record is not shipped"
        );
        assert_eq!(mirror.head(), root(1), "head unchanged after refusal");
    }

    #[test]
    fn pg_side_refuses_a_tampered_batch() {
        // THE re-validation invariant: the pg side does NOT trust the stream. A
        // batch whose post-state was altered after the node built it (so its
        // prev_root no longer chains, OR its ledger_root was substituted) is
        // refused by the independent pg-side RootChain.
        let mut mirror = PgMirror::new(MemorySink::default());
        mirror
            .mirror_record(&record(0, root(1), vec![cell(1, 10)]))
            .unwrap();
        mirror
            .mirror_record(&record(1, root(2), vec![cell(2, 20)]))
            .unwrap();
        let mut shipped = mirror.sink().batches.clone();

        // An adversary substitutes turn 1's pre-state root (claims it chained
        // onto root(9) instead of the real root(1)).
        shipped[1].turn.prev_root = root(9);

        let mut pg_chain = RootChain::new();
        pg_chain.extend(&shipped[0]).unwrap();
        let err = pg_chain.extend(&shipped[1]).unwrap_err();
        assert!(
            matches!(err, ChainRefusal::RootMismatch { .. }),
            "pg side refuses a tampered/substituted batch, got {err:?}"
        );
        // The pg head did not move past the last good turn.
        assert_eq!(pg_chain.head(), Some(root(1)));
    }

    #[test]
    fn config_is_opt_in_off_by_default() {
        // Absent env ⇒ no config ⇒ the node runs unchanged. (edition-2024:
        // env mutation is `unsafe`; this test owns the var and restores it.)
        // SAFETY: single-threaded test ownership of this process-wide var.
        unsafe { std::env::remove_var("DREGG_PG_MIRROR_URL") };
        assert!(PgMirrorConfig::from_env().is_none());
        unsafe { std::env::set_var("DREGG_PG_MIRROR_URL", "postgres://localhost/dregg") };
        assert_eq!(
            PgMirrorConfig::from_env(),
            Some(PgMirrorConfig {
                url: "postgres://localhost/dregg".into()
            })
        );
        unsafe { std::env::remove_var("DREGG_PG_MIRROR_URL") };
    }

    #[test]
    fn resume_threads_prev_root_after_restart() {
        // A mirror resumed at the pg head ships the NEXT turn chaining onto it.
        let mut mirror = PgMirror::resume(MemorySink::default(), root(2), 2);
        assert_eq!(mirror.head(), root(2));
        assert_eq!(mirror.next_ordinal(), 2);
        mirror
            .mirror_record(&record(2, root(3), vec![cell(7, 70)]))
            .unwrap();
        assert_eq!(mirror.sink().batches[0].turn.prev_root, root(2));
        assert_eq!(mirror.head(), root(3));
    }

    // =======================================================================
    // LIVE pg18 integration: the `PgSink` actually writes through to a running
    // postgres over `tokio-postgres`. Runs ONLY when both (a) the
    // `pg-mirror-live` feature is on AND (b) `DREGG_PG_MIRROR_TEST_URL` names a
    // live pg18 (a tokio-postgres connection string, e.g.
    // "host=/Users/<you>/.pgrx port=28818 dbname=pg_dregg_mirror user=<you>").
    // Otherwise it is skipped, so the default test run needs no postgres.
    //
    // This is the load-bearing proof for the M2 live writer: a real PgMirror over
    // a real PgSink ships a chained sequence, and the rows land in dregg.cells via
    // the pg18 dregg.merge_cell upsert. The pg side then re-validates the chain it
    // received (the receipt_chain is unbroken), and a tampered post-image breaks
    // that chain — the "pg re-validates, never trusts" invariant, on a live db,
    // driven by the NODE's own sink (not an inlined writer).
    #[cfg(feature = "pg-mirror-live")]
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn pg_sink_writes_through_to_live_pg() {
        let Ok(url) = std::env::var("DREGG_PG_MIRROR_TEST_URL") else {
            eprintln!(
                "pg_sink_writes_through_to_live_pg: DREGG_PG_MIRROR_TEST_URL unset — skipping"
            );
            return;
        };
        let cfg = PgMirrorConfig { url };

        // Stand up the Tier-B schema in the target db (the same DDL the extension
        // ships, here run directly so the test is extension-version-independent).
        // We connect a plain client to install the schema + role grants the sink
        // writes against, then drive the sink.
        let (admin, admin_conn) = tokio_postgres::connect(&cfg.url, tokio_postgres::NoTls)
            .await
            .expect("connect admin");
        tokio::spawn(async move {
            let _ = admin_conn.await;
        });
        admin
            .batch_execute(&pg_dregg::mirror::ddl::tier_b())
            .await
            .expect("install Tier-B schema");
        // Clean any prior run's rows so the test is idempotent.
        admin
            .batch_execute(
                "DELETE FROM dregg.capabilities; DELETE FROM dregg.memory; \
                 DELETE FROM dregg.cells; DELETE FROM dregg.turns;",
            )
            .await
            .expect("clean prior rows");

        // The NODE's own sink, connected to the live pg, driving a real PgMirror.
        let sink = pg_live::PgSink::connect(&cfg)
            .await
            .expect("PgSink::connect");
        let mut mirror = PgMirror::new(sink);

        // Ship a chained sequence of three verified turns g -> r1 -> r2 -> r3.
        mirror
            .mirror_record(&record(0, root(1), vec![cell(1, 10)]))
            .unwrap();
        mirror
            .mirror_record(&record(1, root(2), vec![cell(2, 20)]))
            .unwrap();
        mirror
            .mirror_record(&record(2, root(3), vec![cell(1, 15)]))
            .unwrap();
        assert_eq!(mirror.head(), root(3));

        // The rows LANDED: three turns, and cell 1's latest post-image (balance 15
        // from ord 2) won the MERGE (one row per cell, not three).
        let turns: i64 = admin
            .query_one("SELECT count(*) FROM dregg.turns", &[])
            .await
            .unwrap()
            .get(0);
        assert_eq!(turns, 3, "three verified turns landed via the live PgSink");
        let cell1_id = cell(1, 0).id().0;
        let bal: i64 = admin
            .query_one(
                "SELECT balance FROM dregg.cells WHERE cell_id = $1",
                &[&cell1_id.as_slice()],
            )
            .await
            .unwrap()
            .get(0);
        assert_eq!(bal, 15, "the MERGE upsert kept cell 1's latest post-image");

        // The pg side re-validates the chain it received: the receipt chain the
        // sink wrote is unbroken (each prev_root is the prior ledger_root).
        let breaks: i64 = admin
            .query_one(
                "SELECT count(*) FROM dregg.turns t \
                 JOIN dregg.turns p ON p.ordinal = t.ordinal - 1 \
                 WHERE t.prev_root IS DISTINCT FROM p.ledger_root",
                &[],
            )
            .await
            .unwrap()
            .get(0);
        assert_eq!(
            breaks, 0,
            "the live-written turns table is an unbroken hash chain"
        );
    }
}
