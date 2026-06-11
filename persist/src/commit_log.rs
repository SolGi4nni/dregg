//! Durable, crash-consistent commit log + secondary index.
//!
//! # What problem this solves
//!
//! Before this module, the node's recovery anchor (`executed_up_to`) and the
//! finalized ledger state were persisted by *independent* transactions at
//! *different* cadences: `executed_up_to` advanced every batch
//! (`blocklace_sync::persist_blocklace_state`), while the ledger was
//! checkpointed only every `LEDGER_CHECKPOINT_INTERVAL` blocks
//! (`blocklace_sync::maybe_checkpoint_ledger`). A crash between those two writes
//! left the durable `executed_up_to` ahead of the durable ledger, and recovery
//! performed **no replay** for the gap — so every finalized turn between the
//! last ledger checkpoint and `executed_up_to` was silently lost from the
//! restored ledger (torn state). Receipts were never persisted at all
//! (the cipherclerk chain lived only in RAM).
//!
//! # The commit log
//!
//! The commit log is the authoritative, append-only record of the turns THIS
//! node has applied, in the node's tau-finalized order. Each [`CommitRecord`]
//! is written in the **same redb transaction** that:
//!   * advances the durable commit cursor ([`tables::META_COMMIT_CURSOR`]),
//!   * inserts the per-turn index entries (receipt-by-hash, turn-by-hash,
//!     turn-by-(height, creator)), and
//!   * upserts the per-turn cell snapshots into the cell-by-id index.
//!
//! redb is an ACID store: a transaction either fully commits (durably, with an
//! fsync at the commit boundary) or does not appear at all. Because all of the
//! above land in one transaction, the following invariants hold across an
//! arbitrary crash (even one that kills the process mid-write):
//!
//!   * **No torn state.** The cursor and the record at `cursor-1` are always
//!     consistent: `commit_cursor() == commit_log.len()`, and every ordinal in
//!     `0..cursor` resolves to a record.
//!   * **No lost finalized turn.** A turn the node *durably* committed (its
//!     record is in the log) is recoverable with its full coordinates and the
//!     post-state of every cell it touched.
//!   * **No double-apply.** Recovery resumes from `commit_cursor()`, which is
//!     advanced once per applied turn inside the commit transaction; a turn whose
//!     transaction did not commit is simply re-applied (idempotently) on the
//!     next poll, and one whose transaction *did* commit is never re-applied.
//!   * **Index agrees with the log.** Every index entry exists *iff* the commit
//!     log has the corresponding record. [`PersistentStore::verify_index_agrees_with_log`]
//!     checks this; [`PersistentStore::rebuild_index_from_log`] re-derives the
//!     entire index from the log alone.
//!
//! The commit cursor is the crash-consistent replacement for the prior
//! separately-written `executed_up_to`; recovery reads it via
//! [`PersistentStore::commit_cursor`].
//!
//! # Layering
//!
//! This module stays independent of `dregg-turn`: the node hashes the turn /
//! receipt coordinates and passes them in as plain bytes, alongside the
//! `(CellId, Cell)` snapshots of every cell the turn touched. `dregg-cell` is
//! already a dependency, so cell snapshots are serialized here.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use dregg_cell::{Cell, CellId};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// One durable record of a finalized turn this node applied to its ledger.
///
/// Stored in [`tables::COMMIT_LOG`] keyed by the commit ordinal (its dense,
/// gap-free position in the node's applied order). Carries everything needed to
/// (a) anchor recovery, (b) drive the secondary index, and (c) re-derive the
/// index from the log alone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommitRecord {
    /// The commit ordinal: this record's position in the applied order. Equals
    /// the redb key it is stored under. Dense and gap-free: `ordinal == n` means
    /// exactly `n` turns were applied before it.
    pub ordinal: u64,
    /// The node-assigned height this turn committed at (the attested-root height
    /// for the turn). Used by the `(height, creator)` index.
    pub height: u64,
    /// The blocklace block id that carried this turn (consensus anchor).
    pub block_id: [u8; 32],
    /// The blocklace block-level high-water mark (`executed_up_to`) AS OF this
    /// turn's commit. Persisted here, inside the same atomic transaction, so that
    /// recovery reads a block cursor that can never be torn ahead of the durable
    /// ledger: the node resumes block processing from the last committed turn's
    /// `block_executed_up_to`. (Non-turn blocks — membership/checkpoint — are
    /// idempotent on re-process, so only turns need the no-double-apply guard the
    /// commit log itself provides.)
    pub block_executed_up_to: u64,
    /// The turn hash (`Turn::hash`).
    pub turn_hash: [u8; 32],
    /// The agent/creator cell id of the turn.
    pub creator: [u8; 32],
    /// The receipt hash (`TurnReceipt::receipt_hash`) produced by applying it.
    pub receipt_hash: [u8; 32],
    /// The canonical ledger root AFTER this turn was applied. Binds the record
    /// to a concrete post-state so recovery can assert convergence.
    pub ledger_root: [u8; 32],
    /// Post-state snapshots of every cell this turn touched (created/mutated).
    /// These feed the cell-by-id index. Serialized `dregg_cell::Cell`s.
    pub touched_cells: Vec<Cell>,
}

impl CommitRecord {
    /// Encode the `(height, creator)` composite index key: 8-byte big-endian
    /// height ++ 32-byte creator. Big-endian height makes redb's lexicographic
    /// order a height-major order, so range scans are height-ordered.
    pub fn height_creator_key(height: u64, creator: &[u8; 32]) -> [u8; 40] {
        let mut key = [0u8; 40];
        key[0..8].copy_from_slice(&height.to_be_bytes());
        key[8..40].copy_from_slice(creator);
        key
    }
}

/// Report from [`PersistentStore::verify_index_agrees_with_log`].
///
/// `ok()` is true exactly when the secondary index is in perfect agreement with
/// the commit log: every record's index entries are present and correct, and the
/// index contains no entries that the log does not justify.
#[derive(Clone, Debug, Default)]
pub struct IndexAuditReport {
    /// Number of commit records examined.
    pub records: u64,
    /// `commit_cursor()` value (must equal `records` for a consistent store).
    pub cursor: u64,
    /// Index entries missing for a record that the log contains.
    pub missing_entries: Vec<String>,
    /// Index entries present that no log record justifies (orphans).
    pub orphan_entries: Vec<String>,
    /// Index entries present but pointing at the wrong ordinal.
    pub mismatched_entries: Vec<String>,
}

impl IndexAuditReport {
    /// Whether the index is fully consistent with the log.
    pub fn ok(&self) -> bool {
        self.cursor == self.records
            && self.missing_entries.is_empty()
            && self.orphan_entries.is_empty()
            && self.mismatched_entries.is_empty()
    }
}

impl PersistentStore {
    // =========================================================================
    // Commit cursor (the crash-consistent recovery anchor)
    // =========================================================================

    /// The durable commit cursor: the number of turns this node has committed
    /// and indexed = the next free commit ordinal = the high-water mark recovery
    /// must resume from. Returns 0 on a fresh node.
    ///
    /// This is read inside the per-turn commit transaction and advanced there, so
    /// it can never be torn against the record it counts.
    pub fn commit_cursor(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_COMMIT_CURSOR)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Number of records physically present in the commit log table.
    pub fn commit_log_len(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        Ok(table.len()?)
    }

    // =========================================================================
    // The atomic commit (single transaction = one fsync boundary)
    // =========================================================================

    /// Durably commit one finalized turn: append its [`CommitRecord`] at the
    /// current cursor, advance the cursor, and insert all index entries — ALL in
    /// a single redb transaction.
    ///
    /// `expected_ordinal` is the caller's view of the next ordinal (the prior
    /// `executed_up_to`/commit position). It MUST equal the store's current
    /// `commit_cursor`, otherwise the write is refused with an integrity error —
    /// this catches a caller that advanced its in-RAM cursor without durably
    /// committing (the exact torn-state hazard this module exists to remove), and
    /// makes the durable cursor the single source of truth.
    ///
    /// Idempotency: if `expected_ordinal < cursor` AND the record already present
    /// at `expected_ordinal` carries the same `turn_hash`, the call is a no-op
    /// success (a crash-replay re-applying an already-committed turn). Any other
    /// mismatch is an integrity error.
    ///
    /// Returns the ordinal the record was stored at.
    pub fn commit_finalized_turn(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let assigned;
        {
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let cursor = meta
                .get(tables::META_COMMIT_CURSOR)?
                .map(|g| g.value())
                .unwrap_or(0);

            if expected_ordinal != cursor {
                // Idempotent replay: the caller is re-applying a turn we already
                // committed durably. Accept iff the stored record matches.
                if expected_ordinal < cursor {
                    let log = write_txn.open_table(tables::COMMIT_LOG)?;
                    match log.get(expected_ordinal)? {
                        Some(guard) => {
                            let existing: CommitRecord = postcard::from_bytes(guard.value())?;
                            if existing.turn_hash == record.turn_hash {
                                // Already durably committed; nothing to do.
                                return Ok(expected_ordinal);
                            }
                            return Err(StoreError::Integrity(format!(
                                "commit_finalized_turn: ordinal {expected_ordinal} already holds a \
                                 different turn (stored turn_hash != supplied)"
                            )));
                        }
                        None => {
                            return Err(StoreError::Integrity(format!(
                                "commit_finalized_turn: cursor {cursor} > expected {expected_ordinal} \
                                 but no record at {expected_ordinal} (corrupt log)"
                            )));
                        }
                    }
                }
                return Err(StoreError::Integrity(format!(
                    "commit_finalized_turn: expected ordinal {expected_ordinal} but durable cursor \
                     is {cursor}; refusing to write a gap (torn-state guard)"
                )));
            }

            assigned = cursor;
            let stored_record = CommitRecord {
                ordinal: assigned,
                ..record.clone()
            };
            let encoded = postcard::to_stdvec(&stored_record)
                .map_err(|e| StoreError::Serialization(e.to_string()))?;

            // 1. Append the commit record.
            {
                let mut log = write_txn.open_table(tables::COMMIT_LOG)?;
                log.insert(assigned, encoded.as_slice())?;
            }

            // 2. Insert the secondary index entries (same txn → never torn).
            {
                let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
                idx_receipt.insert(&stored_record.receipt_hash, assigned)?;

                let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
                idx_turn.insert(&stored_record.turn_hash, assigned)?;

                let hc_key =
                    CommitRecord::height_creator_key(stored_record.height, &stored_record.creator);
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                idx_hc.insert(hc_key.as_slice(), assigned)?;

                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                for cell in &stored_record.touched_cells {
                    let cell_bytes = postcard::to_stdvec(cell)
                        .map_err(|e| StoreError::Serialization(e.to_string()))?;
                    idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                }
            }

            // 3. Advance the durable cursor LAST within the txn (still atomic).
            meta.insert(tables::META_COMMIT_CURSOR, assigned + 1)?;
        }
        write_txn.commit()?;
        Ok(assigned)
    }

    // =========================================================================
    // Commit-log reads
    // =========================================================================

    /// Load the commit record at an ordinal.
    pub fn commit_record_at(&self, ordinal: u64) -> Result<Option<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        match table.get(ordinal)? {
            Some(guard) => Ok(Some(postcard::from_bytes(guard.value())?)),
            None => Ok(None),
        }
    }

    /// Load every commit record from `start` (inclusive) to the cursor, in order.
    ///
    /// This is the replay source for recovery: feeding these records' post-state
    /// cell snapshots back over the last ledger checkpoint reconstructs the exact
    /// finalized ledger up to the cursor.
    pub fn commit_records_from(&self, start: u64) -> Result<Vec<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        for entry in table.range(start..)? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push(postcard::from_bytes(entry.1.value())?);
        }
        Ok(out)
    }

    /// The block-level high-water mark to resume blocklace processing from on
    /// recovery: the `block_executed_up_to` of the last durably-committed turn,
    /// or 0 if no turn has been committed.
    ///
    /// This is the crash-consistent replacement for the separately-written
    /// `BLOCKLACE_EXECUTED_UP_TO_KEY`: it was written inside the same transaction
    /// as the turn it accompanies, so it can never be ahead of the durable
    /// ledger/commit-log.
    pub fn recovered_block_cursor(&self) -> Result<u64> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(0);
        }
        match self.commit_record_at(cursor - 1)? {
            Some(rec) => Ok(rec.block_executed_up_to),
            None => Err(StoreError::Integrity(format!(
                "recovered_block_cursor: cursor {cursor} but no record at {}",
                cursor - 1
            ))),
        }
    }

    /// The durable post-state ledger root the node converged to: the
    /// `ledger_root` of the last committed turn, or `None` if no turn committed.
    ///
    /// A recovered node that reconstructs its ledger MUST reproduce this root
    /// (it is the on-chain-style commitment of the finalized state). This is the
    /// recovery-side analogue of LaceMerge convergence: independent of HOW the
    /// ledger is rebuilt (replay vs checkpoint+overlay), the resulting root must
    /// equal the root the committing node recorded.
    pub fn recovered_ledger_root(&self) -> Result<Option<[u8; 32]>> {
        let cursor = self.commit_cursor()?;
        if cursor == 0 {
            return Ok(None);
        }
        Ok(self.commit_record_at(cursor - 1)?.map(|r| r.ledger_root))
    }

    /// The last-writer-wins overlay of cell post-states committed since the most
    /// recent full ledger checkpoint at `checkpoint_height`.
    ///
    /// Returns the post-state of every cell touched by a committed turn whose
    /// `height > checkpoint_height`. Overlaying these on the checkpoint ledger
    /// reconstructs the finalized ledger up to the commit cursor WITHOUT
    /// re-executing — the cell-by-id index is exactly this overlay maintained
    /// incrementally, but this method re-derives it from the log so recovery
    /// never trusts the (rebuildable) index for correctness.
    pub fn cell_overlay_since(&self, checkpoint_height: u64) -> Result<Vec<Cell>> {
        use std::collections::HashMap;
        let read_txn = self.db.begin_read()?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        // ordinal-ascending iteration → later writers overwrite earlier ones.
        let mut latest: HashMap<[u8; 32], Cell> = HashMap::new();
        for entry in log.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let record: CommitRecord = postcard::from_bytes(entry.1.value())?;
            if record.height <= checkpoint_height {
                continue;
            }
            for cell in record.touched_cells {
                latest.insert(cell.id().0, cell);
            }
        }
        Ok(latest.into_values().collect())
    }

    // =========================================================================
    // Secondary index lookups
    // =========================================================================

    /// Resolve a receipt hash to its commit record (receipt-by-hash index).
    pub fn lookup_receipt(&self, receipt_hash: &[u8; 32]) -> Result<Option<CommitRecord>> {
        self.lookup_by_index(tables::IDX_RECEIPT_BY_HASH, receipt_hash)
    }

    /// Resolve a turn hash to its commit record (turn-by-hash index).
    pub fn lookup_turn(&self, turn_hash: &[u8; 32]) -> Result<Option<CommitRecord>> {
        self.lookup_by_index(tables::IDX_TURN_BY_HASH, turn_hash)
    }

    fn lookup_by_index(
        &self,
        idx: redb::TableDefinition<&[u8; 32], u64>,
        key: &[u8; 32],
    ) -> Result<Option<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let index = read_txn.open_table(idx)?;
        let ordinal = match index.get(key)? {
            Some(g) => g.value(),
            None => return Ok(None),
        };
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        match log.get(ordinal)? {
            Some(guard) => Ok(Some(postcard::from_bytes(guard.value())?)),
            None => Err(StoreError::Integrity(format!(
                "index points at ordinal {ordinal} but commit log has no record there"
            ))),
        }
    }

    /// Look up the current durable snapshot of a cell by id (cell-by-id index).
    ///
    /// Returns the latest post-state of the cell among all committed turns that
    /// touched it. `None` means no committed turn has touched this cell since the
    /// last full ledger checkpoint (callers fall back to the checkpoint).
    pub fn lookup_cell(&self, cell_id: &CellId) -> Result<Option<Cell>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::IDX_CELL_BY_ID)?;
        match table.get(&cell_id.0)? {
            Some(guard) => Ok(Some(postcard::from_bytes(guard.value())?)),
            None => Ok(None),
        }
    }

    /// All commit records at a given height, in creator order (turns-by-height).
    pub fn turns_at_height(&self, height: u64) -> Result<Vec<CommitRecord>> {
        let lo = CommitRecord::height_creator_key(height, &[0u8; 32]);
        let hi = CommitRecord::height_creator_key(height, &[0xffu8; 32]);
        self.turns_in_key_range(lo.as_slice(), hi.as_slice(), true)
    }

    /// All commit records by a given creator, in height order (turns-by-creator).
    ///
    /// Scans the `(height, creator)` index and filters by creator. Height-major
    /// key layout means the results come back height-ordered.
    pub fn turns_by_creator(&self, creator: &[u8; 32]) -> Result<Vec<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let index = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        for entry in index.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            if key.len() == 40 && &key[8..40] == creator.as_slice() {
                let ordinal = entry.1.value();
                if let Some(guard) = log.get(ordinal)? {
                    out.push(postcard::from_bytes(guard.value())?);
                }
            }
        }
        Ok(out)
    }

    fn turns_in_key_range(
        &self,
        lo: &[u8],
        hi: &[u8],
        inclusive_hi: bool,
    ) -> Result<Vec<CommitRecord>> {
        let read_txn = self.db.begin_read()?;
        let index = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        let iter = if inclusive_hi {
            index.range(lo..=hi)?
        } else {
            index.range(lo..hi)?
        };
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let ordinal = entry.1.value();
            if let Some(guard) = log.get(ordinal)? {
                out.push(postcard::from_bytes(guard.value())?);
            }
        }
        Ok(out)
    }

    // =========================================================================
    // Index ⟺ log invariant: verify + rebuild
    // =========================================================================

    /// Verify the "index entry exists iff the log has it" invariant.
    ///
    /// Walks the commit log and checks that each record's three hash-index
    /// entries resolve back to that record's ordinal, then walks each index and
    /// checks that no entry is an orphan (points at a missing record) or points
    /// at a record that does not carry that key. The cell-by-id index is checked
    /// for being a subset of the log's touched cells (it is a last-writer-wins
    /// projection, so its agreement criterion is "every cell entry equals the
    /// latest log record that touched that cell").
    pub fn verify_index_agrees_with_log(&self) -> Result<IndexAuditReport> {
        let mut report = IndexAuditReport {
            cursor: self.commit_cursor()?,
            ..Default::default()
        };

        let read_txn = self.db.begin_read()?;
        let log = read_txn.open_table(tables::COMMIT_LOG)?;
        let idx_receipt = read_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
        let idx_turn = read_txn.open_table(tables::IDX_TURN_BY_HASH)?;
        let idx_hc = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
        let idx_cell = read_txn.open_table(tables::IDX_CELL_BY_ID)?;

        // Forward direction: every log record has its index entries.
        // Also track the latest ordinal that touched each cell so we can check
        // the cell index is the correct last-writer-wins projection.
        use std::collections::HashMap;
        let mut latest_cell_writer: HashMap<[u8; 32], (u64, Cell)> = HashMap::new();

        for entry in log.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let ordinal = entry.0.value();
            let record: CommitRecord = postcard::from_bytes(entry.1.value())?;
            report.records += 1;

            check_hash_index(
                &idx_receipt,
                &record.receipt_hash,
                ordinal,
                "receipt_by_hash",
                &mut report,
            )?;
            check_hash_index(
                &idx_turn,
                &record.turn_hash,
                ordinal,
                "turn_by_hash",
                &mut report,
            )?;
            let hc_key = CommitRecord::height_creator_key(record.height, &record.creator);
            match idx_hc.get(hc_key.as_slice())? {
                Some(g) if g.value() == ordinal => {}
                Some(g) => report.mismatched_entries.push(format!(
                    "turn_by_height_creator(h={}) -> {} but record at ordinal {ordinal}",
                    record.height,
                    g.value()
                )),
                None => report.missing_entries.push(format!(
                    "turn_by_height_creator(h={}) missing for ordinal {ordinal}",
                    record.height
                )),
            }

            for cell in &record.touched_cells {
                latest_cell_writer
                    .entry(cell.id().0)
                    .and_modify(|slot| {
                        if ordinal >= slot.0 {
                            *slot = (ordinal, cell.clone());
                        }
                    })
                    .or_insert((ordinal, cell.clone()));
            }
        }

        // Reverse direction: no orphan hash-index entries.
        check_no_orphans(&idx_receipt, &log, "receipt_by_hash", &mut report)?;
        check_no_orphans(&idx_turn, &log, "turn_by_hash", &mut report)?;
        for entry in idx_hc.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let ordinal = entry.1.value();
            if log.get(ordinal)?.is_none() {
                report.orphan_entries.push(format!(
                    "turn_by_height_creator -> missing ordinal {ordinal}"
                ));
            }
        }

        // Cell index: must equal the last-writer-wins projection of the log.
        let mut cell_index_count = 0u64;
        for entry in idx_cell.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            cell_index_count += 1;
            let cell_id = *entry.0.value();
            let stored: Cell = postcard::from_bytes(entry.1.value())?;
            match latest_cell_writer.get(&cell_id) {
                Some((_, expected)) if *expected == stored => {}
                Some(_) => report.mismatched_entries.push(format!(
                    "cell_by_id({}) != latest log writer",
                    hex32(&cell_id)
                )),
                None => report
                    .orphan_entries
                    .push(format!("cell_by_id({}) has no log writer", hex32(&cell_id))),
            }
        }
        if (cell_index_count as usize) < latest_cell_writer.len() {
            for (cell_id, _) in &latest_cell_writer {
                if idx_cell.get(cell_id)?.is_none() {
                    report
                        .missing_entries
                        .push(format!("cell_by_id({}) missing", hex32(cell_id)));
                }
            }
        }

        Ok(report)
    }

    /// Rebuild the entire secondary index from the commit log alone.
    ///
    /// Clears every index table, then replays the log in ordinal order
    /// re-inserting all index entries. After this, the cell-by-id index is the
    /// last-writer-wins projection of the log's `touched_cells`. The commit
    /// cursor is left untouched (the log IS the source of truth). The whole
    /// rebuild runs in a single transaction, so a crash mid-rebuild leaves the
    /// previous (already-consistent) index in place.
    ///
    /// Returns the number of records replayed.
    pub fn rebuild_index_from_log(&self) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let mut replayed = 0u64;
        {
            // Collect the log first (immutable view), then rewrite indexes.
            let records: Vec<CommitRecord> = {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut v = Vec::new();
                for entry in log.iter()? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    v.push(postcard::from_bytes::<CommitRecord>(entry.1.value())?);
                }
                v
            };

            clear_table_u32(&write_txn, tables::IDX_RECEIPT_BY_HASH)?;
            clear_table_u32(&write_txn, tables::IDX_TURN_BY_HASH)?;
            {
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                let keys: Vec<Vec<u8>> = idx_hc
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| e.0.value().to_vec()))
                    .collect();
                for k in keys {
                    idx_hc.remove(k.as_slice())?;
                }
            }
            {
                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                let keys: Vec<[u8; 32]> = idx_cell
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| *e.0.value()))
                    .collect();
                for k in keys {
                    idx_cell.remove(&k)?;
                }
            }

            let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
            let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
            let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
            let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;

            for record in &records {
                idx_receipt.insert(&record.receipt_hash, record.ordinal)?;
                idx_turn.insert(&record.turn_hash, record.ordinal)?;
                let hc_key = CommitRecord::height_creator_key(record.height, &record.creator);
                idx_hc.insert(hc_key.as_slice(), record.ordinal)?;
                for cell in &record.touched_cells {
                    let cell_bytes = postcard::to_stdvec(cell)
                        .map_err(|e| StoreError::Serialization(e.to_string()))?;
                    idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                }
                replayed += 1;
            }
        }
        write_txn.commit()?;
        Ok(replayed)
    }
}

// =============================================================================
// Internal helpers
// =============================================================================

fn check_hash_index(
    index: &impl ReadableTable<&'static [u8; 32], u64>,
    key: &[u8; 32],
    ordinal: u64,
    name: &str,
    report: &mut IndexAuditReport,
) -> Result<()> {
    match index.get(key)? {
        Some(g) if g.value() == ordinal => {}
        Some(g) => report.mismatched_entries.push(format!(
            "{name}({}) -> {} but record at ordinal {ordinal}",
            hex32(key),
            g.value()
        )),
        None => report.missing_entries.push(format!(
            "{name}({}) missing for ordinal {ordinal}",
            hex32(key)
        )),
    }
    Ok(())
}

fn check_no_orphans(
    index: &impl ReadableTable<&'static [u8; 32], u64>,
    log: &impl ReadableTable<u64, &'static [u8]>,
    name: &str,
    report: &mut IndexAuditReport,
) -> Result<()> {
    for entry in index.iter()? {
        let entry = entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
        let ordinal = entry.1.value();
        if log.get(ordinal)?.is_none() {
            report
                .orphan_entries
                .push(format!("{name} -> missing ordinal {ordinal}"));
        }
    }
    Ok(())
}

fn clear_table_u32(
    txn: &redb::WriteTransaction,
    def: redb::TableDefinition<&'static [u8; 32], u64>,
) -> Result<()> {
    let mut table = txn.open_table(def)?;
    let keys: Vec<[u8; 32]> = table
        .iter()?
        .filter_map(|e| e.ok().map(|e| *e.0.value()))
        .collect();
    for k in keys {
        table.remove(&k)?;
    }
    Ok(())
}

fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PersistentStore;
    use dregg_cell::Cell;

    /// Build a deterministic commit record for ordinal `n`, touching `cells`.
    /// Callers overwrite `turn_hash` / `receipt_hash` to make them unique.
    fn record(n: u64, block_executed_up_to: u64, cells: Vec<Cell>) -> CommitRecord {
        let mut turn_hash = [0u8; 32];
        turn_hash[0] = 0xa0;
        turn_hash[1] = n as u8;
        let mut receipt_hash = [0u8; 32];
        receipt_hash[0] = 0xb0;
        receipt_hash[1] = n as u8;
        CommitRecord {
            ordinal: n, // overwritten by the store with the assigned ordinal
            height: n + 1,
            block_id: [n as u8; 32],
            turn_hash,
            creator: [(n % 3) as u8 + 1; 32],
            receipt_hash,
            ledger_root: [n as u8; 32],
            block_executed_up_to,
            touched_cells: cells,
        }
    }

    fn cell(seed: u8, balance: u64) -> Cell {
        Cell::with_balance([seed; 32], [seed.wrapping_add(7); 32], balance)
    }

    #[test]
    fn cursor_advances_one_per_commit_and_records_round_trip() {
        let store = PersistentStore::open_in_memory().unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 0);

        for n in 0..5u64 {
            let mut rec = record(n, n * 2, vec![cell(n as u8, 100 + n)]);
            rec.turn_hash[0] = 0xaa;
            rec.turn_hash[1] = n as u8;
            let assigned = store.commit_finalized_turn(n, &rec).unwrap();
            assert_eq!(assigned, n);
            assert_eq!(store.commit_cursor().unwrap(), n + 1);
        }
        assert_eq!(store.commit_log_len().unwrap(), 5);

        for n in 0..5u64 {
            let got = store.commit_record_at(n).unwrap().unwrap();
            assert_eq!(got.ordinal, n);
            assert_eq!(got.height, n + 1);
            assert_eq!(got.block_executed_up_to, n * 2);
        }
    }

    #[test]
    fn torn_state_guard_refuses_gap() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut rec = record(0, 0, vec![]);
        rec.turn_hash[0] = 1;
        store.commit_finalized_turn(0, &rec).unwrap();

        // Trying to write ordinal 2 while cursor is 1 must be refused (no gaps).
        let mut bad = record(2, 0, vec![]);
        bad.turn_hash[0] = 2;
        let err = store.commit_finalized_turn(2, &bad);
        assert!(matches!(err, Err(StoreError::Integrity(_))), "got {err:?}");
        // Cursor unchanged.
        assert_eq!(store.commit_cursor().unwrap(), 1);
    }

    #[test]
    fn idempotent_replay_of_already_committed_turn_is_noop() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut rec0 = record(0, 0, vec![cell(1, 10)]);
        rec0.turn_hash[0] = 0x11;
        let mut rec1 = record(1, 1, vec![cell(2, 20)]);
        rec1.turn_hash[0] = 0x22;
        store.commit_finalized_turn(0, &rec0).unwrap();
        store.commit_finalized_turn(1, &rec1).unwrap();

        // Re-apply ordinal 0 with the SAME turn hash: no-op success.
        let assigned = store.commit_finalized_turn(0, &rec0).unwrap();
        assert_eq!(assigned, 0);
        assert_eq!(
            store.commit_cursor().unwrap(),
            2,
            "cursor must not regress/advance"
        );

        // Re-apply ordinal 0 with a DIFFERENT turn hash: integrity error.
        let mut tampered = rec0.clone();
        tampered.turn_hash[0] = 0x99;
        let err = store.commit_finalized_turn(0, &tampered);
        assert!(matches!(err, Err(StoreError::Integrity(_))), "got {err:?}");
    }

    #[test]
    fn index_agrees_with_log_after_commits() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..8u64 {
            let mut rec = record(n, n, vec![cell((n % 4) as u8, 1000 + n)]);
            rec.turn_hash[0] = 0x30;
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[0] = 0x40;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "index disagrees with log: {report:?}");
        assert_eq!(report.records, 8);
        assert_eq!(report.cursor, 8);
    }

    #[test]
    fn lookups_resolve_through_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        let mut rec = record(0, 0, vec![cell(7, 555)]);
        rec.turn_hash = [0xcd; 32];
        rec.receipt_hash = [0xef; 32];
        rec.height = 42;
        rec.creator = [0x9a; 32];
        store.commit_finalized_turn(0, &rec).unwrap();

        // receipt-by-hash
        let by_receipt = store.lookup_receipt(&[0xef; 32]).unwrap().unwrap();
        assert_eq!(by_receipt.ordinal, 0);
        // turn-by-hash
        let by_turn = store.lookup_turn(&[0xcd; 32]).unwrap().unwrap();
        assert_eq!(by_turn.ordinal, 0);
        // turns-by-height
        let at_h = store.turns_at_height(42).unwrap();
        assert_eq!(at_h.len(), 1);
        assert_eq!(at_h[0].turn_hash, [0xcd; 32]);
        // turns-by-creator
        let by_creator = store.turns_by_creator(&[0x9a; 32]).unwrap();
        assert_eq!(by_creator.len(), 1);
        // cell-by-id
        let c = cell(7, 555);
        let got = store.lookup_cell(&c.id()).unwrap().unwrap();
        assert_eq!(got.state.balance(), 555);

        // Unknown keys resolve to None.
        assert!(store.lookup_receipt(&[0x00; 32]).unwrap().is_none());
        assert!(store.lookup_turn(&[0x00; 32]).unwrap().is_none());
    }

    #[test]
    fn cell_index_is_last_writer_wins() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Two turns touch the SAME cell id (same seed) with different balances.
        let c_low = cell(5, 100);
        let cid = c_low.id();
        let mut rec0 = record(0, 0, vec![c_low]);
        rec0.turn_hash[0] = 1;
        store.commit_finalized_turn(0, &rec0).unwrap();

        let c_high = cell(5, 999);
        let mut rec1 = record(1, 1, vec![c_high]);
        rec1.turn_hash[0] = 2;
        store.commit_finalized_turn(1, &rec1).unwrap();

        // The index reflects the LATER writer.
        let got = store.lookup_cell(&cid).unwrap().unwrap();
        assert_eq!(got.state.balance(), 999);
        // And the index still agrees with the log under the last-writer-wins rule.
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    #[test]
    fn rebuild_index_from_log_reproduces_identical_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..6u64 {
            let mut rec = record(n, n, vec![cell((n % 3) as u8, 10 + n), cell(9, 1000 + n)]);
            rec.turn_hash[0] = 0x50;
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[0] = 0x60;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        assert!(store.verify_index_agrees_with_log().unwrap().ok());

        // Rebuild from the log alone — must replay every record and re-agree.
        let replayed = store.rebuild_index_from_log().unwrap();
        assert_eq!(replayed, 6);
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "rebuilt index disagrees: {report:?}");

        // Cell 9 was written by every turn; index must hold the last (n=5) value.
        let c9 = cell(9, 1005);
        let got = store.lookup_cell(&c9.id()).unwrap().unwrap();
        assert_eq!(got.state.balance(), 1005);
    }

    /// CRASH-RECOVERY: simulate a process kill mid-write by performing a series
    /// of ATOMIC commits to an on-disk store, then dropping the store WITHOUT the
    /// next commit (the "torn" turn never lands), reopening, and asserting the
    /// store recovers to a consistent checkpoint: the cursor equals the number of
    /// turns that actually committed, every record round-trips, the index agrees
    /// with the log, and the block cursor / ledger root reflect the last
    /// committed turn (no torn state, no lost finalized turn, no double-apply).
    #[test]
    fn crash_recovery_is_consistent() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("crash.redb");

        // ── Phase 1: commit 4 turns durably, then "crash" (drop) ────────────
        {
            let store = PersistentStore::open(&path).unwrap();
            for n in 0..4u64 {
                let mut rec = record(n, n * 10, vec![cell(n as u8, 500 + n)]);
                rec.turn_hash[0] = 0x70;
                rec.turn_hash[1] = n as u8;
                rec.receipt_hash[0] = 0x80;
                rec.receipt_hash[1] = n as u8;
                rec.ledger_root = [n as u8; 32];
                store.commit_finalized_turn(n, &rec).unwrap();
            }
            // Model the crash: the 5th turn's commit transaction is begun in RAM
            // but the process dies BEFORE `commit_finalized_turn` returns. We
            // model that by simply NOT calling it, then dropping the store.
            // (redb guarantees an uncommitted txn leaves no trace.)
            drop(store);
        }

        // ── Phase 2: reopen and assert consistent recovery ─────────────────
        {
            let store = PersistentStore::open(&path).unwrap();
            // Cursor reflects exactly the committed turns.
            assert_eq!(store.commit_cursor().unwrap(), 4);
            assert_eq!(store.commit_log_len().unwrap(), 4);

            // No torn record: every ordinal in 0..cursor resolves.
            for n in 0..4u64 {
                let rec = store.commit_record_at(n).unwrap().unwrap();
                assert_eq!(rec.ordinal, n);
            }
            // The 5th (un-committed) turn left NO trace.
            assert!(store.commit_record_at(4).unwrap().is_none());

            // Index agrees with the log across the crash.
            assert!(store.verify_index_agrees_with_log().unwrap().ok());

            // Recovery anchors: block cursor + ledger root reflect the LAST
            // committed turn, never the torn one.
            assert_eq!(store.recovered_block_cursor().unwrap(), 30); // turn 3 → 3*10
            assert_eq!(store.recovered_ledger_root().unwrap(), Some([3u8; 32]));

            // ── No double-apply: re-applying turn 3 (already durable) is a
            // no-op success; the cursor does not advance. ──
            let mut rec3 = record(3, 30, vec![cell(3, 503)]);
            rec3.turn_hash[0] = 0x70;
            rec3.turn_hash[1] = 3;
            rec3.receipt_hash[0] = 0x80;
            rec3.receipt_hash[1] = 3;
            assert_eq!(store.commit_finalized_turn(3, &rec3).unwrap(), 3);
            assert_eq!(store.commit_cursor().unwrap(), 4);

            // ── Liveness: the recovered store accepts the NEXT turn at the
            // cursor and advances normally. ──
            let mut rec4 = record(4, 40, vec![cell(4, 504)]);
            rec4.turn_hash[0] = 0x70;
            rec4.turn_hash[1] = 4;
            rec4.receipt_hash[0] = 0x80;
            rec4.receipt_hash[1] = 4;
            assert_eq!(store.commit_finalized_turn(4, &rec4).unwrap(), 4);
            assert_eq!(store.commit_cursor().unwrap(), 5);
            assert!(store.verify_index_agrees_with_log().unwrap().ok());
        }
    }

    /// Recovery overlay: the cell-by-id deltas committed ABOVE a checkpoint
    /// height reconstruct the post-checkpoint ledger without re-execution, and
    /// the last-writer-wins overlay re-derived from the log matches the live
    /// cell index.
    #[test]
    fn cell_overlay_since_checkpoint_matches_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Heights 1..=6 (record(n).height == n+1). Checkpoint at height 3.
        for n in 0..6u64 {
            let mut rec = record(n, n, vec![cell((n % 2) as u8, 100 + n)]);
            rec.turn_hash[0] = 0x90;
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[0] = 0xa0;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        // Overlay above checkpoint height 3 = records with height > 3 = n>=3.
        let overlay = store.cell_overlay_since(3).unwrap();
        // Cells 0 and 1 (seeds) were both written by n in {3,4,5}; the overlay
        // holds their LATEST post-states: seed1 at n=5 (bal 105), seed0 at n=4
        // (bal 104).
        let bal = |seed: u8, b: u64| {
            let target = cell(seed, b).id();
            overlay
                .iter()
                .find(|c| c.id() == target)
                .map(|c| c.state.balance())
        };
        assert_eq!(bal(1, 105), Some(105));
        assert_eq!(bal(0, 104), Some(104));
    }
}
