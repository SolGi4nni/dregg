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
//!     consistent: every ordinal in `[compacted_floor, cursor)` resolves to a
//!     record, and `commit_cursor() == commit_log.len() + compacted_floor`
//!     (the `compacted_floor == 0` special case is the pre-compaction
//!     `cursor == len`; see [`Self::compact_below`]).
//!   * **No lost finalized turn.** A turn the node *durably* committed is
//!     recoverable with its full coordinates and the post-state of every cell it
//!     touched — either from its log record, OR (once [`Self::compact_below`]
//!     has removed that record under a covering checkpoint) from the checkpoint
//!     that subsumes it. Compaction never removes a record a checkpoint does not
//!     subsume, so the finalized state is never lost.
//!   * **No double-apply.** Recovery resumes from `commit_cursor()`, which is
//!     advanced once per applied turn inside the commit transaction; a turn whose
//!     transaction did not commit is simply re-applied (idempotently) on the
//!     next poll, and one whose transaction *did* commit is never re-applied.
//!     This holds across compaction: a compacted turn's `block_id` is retained
//!     (`COMMIT_COMPACTED_BLOCK_IDS`) and still reported by
//!     [`Self::commit_log_block_ids`], so the identity execution cursor still
//!     sees it as applied and never re-executes it on top of the checkpoint.
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
    /// Encode the `(height, creator, ordinal)` composite index key: 8-byte
    /// big-endian height ++ 32-byte creator ++ 8-byte big-endian ordinal.
    /// Big-endian height makes redb's lexicographic order a height-major
    /// order, so range scans are height-ordered. The trailing ordinal makes
    /// the key unique even when several turns commit at the same
    /// `(height, creator)` — which is the normal case for ROUTE-level turns
    /// (trustline/court/channels services), several of which can commit
    /// between two attested-height advances.
    pub fn height_creator_key(height: u64, creator: &[u8; 32], ordinal: u64) -> [u8; 48] {
        let mut key = [0u8; 48];
        key[0..8].copy_from_slice(&height.to_be_bytes());
        key[8..40].copy_from_slice(creator);
        key[40..48].copy_from_slice(&ordinal.to_be_bytes());
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
    /// Number of commit records physically examined in the (possibly compacted)
    /// log.
    pub records: u64,
    /// `commit_cursor()` value. For a consistent store
    /// `cursor == records + compacted` (the compaction-aware density invariant;
    /// `cursor == records` when nothing has been compacted).
    pub cursor: u64,
    /// `commit_compacted_floor()` value: records compacted away under a covering
    /// checkpoint. The live log holds ordinals `[compacted, cursor)`.
    pub compacted: u64,
    /// Index entries missing for a record that the log contains.
    pub missing_entries: Vec<String>,
    /// Index entries present that no log record justifies (orphans).
    pub orphan_entries: Vec<String>,
    /// Index entries present but pointing at the wrong ordinal.
    pub mismatched_entries: Vec<String>,
}

impl IndexAuditReport {
    /// Whether the index is fully consistent with the log.
    ///
    /// The density check is compaction-aware: `cursor == records + compacted`.
    /// Before any compaction `compacted == 0` and this is the original
    /// `cursor == records`; after compaction the live record count drops by
    /// exactly the compaction floor while the cursor (the applied high-water
    /// mark) is unchanged.
    pub fn ok(&self) -> bool {
        self.cursor == self.records + self.compacted
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
    ///
    /// After [`Self::compact_below`] has run, this is strictly less than
    /// [`Self::commit_cursor`] by exactly [`Self::commit_compacted_floor`]:
    /// `commit_cursor() == commit_log_len() + commit_compacted_floor()`.
    pub fn commit_log_len(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        Ok(table.len()?)
    }

    /// The durable commit-log compaction floor: the number of records compacted
    /// away by [`Self::compact_below`] = the lowest commit ordinal still
    /// physically present in the log. Every ordinal in
    /// `[commit_compacted_floor(), commit_cursor())` resolves to a record;
    /// ordinals below the floor were compacted because a finalized ledger
    /// checkpoint at/above their height subsumes their finalized state. Returns
    /// 0 on a node that has never compacted.
    pub fn commit_compacted_floor(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_COMMIT_COMPACTED)?
            .map(|g| g.value())
            .unwrap_or(0))
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
        self.commit_finalized_turn_with_burns(expected_ordinal, record, &[])
    }

    /// [`Self::commit_finalized_turn`] PLUS forever-digest burns in the SAME
    /// redb transaction — the same-transaction burn weld (docs/PERSISTENCE.md
    /// §3): a turn that burns an anti-replay digest (a trustline draw, a court
    /// slash) lands its commit record AND its digest atomically, so no crash
    /// can leave the turn durable without its burn or the burn durable without
    /// its turn. Each burn is `(namespace, scope, digest)` exactly as
    /// [`PersistentStore::record_forever_digest`] takes them.
    ///
    /// On an idempotent replay (the record at `expected_ordinal` already holds
    /// the same `turn_hash`), the burns were already written by the original
    /// commit and the call is a no-op success.
    pub fn commit_finalized_turn_with_burns(
        &self,
        expected_ordinal: u64,
        record: &CommitRecord,
        burns: &[(u8, [u8; 32], [u8; 32])],
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

                let hc_key = CommitRecord::height_creator_key(
                    stored_record.height,
                    &stored_record.creator,
                    assigned,
                );
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                idx_hc.insert(hc_key.as_slice(), assigned)?;

                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                for cell in &stored_record.touched_cells {
                    let cell_bytes = postcard::to_stdvec(cell)
                        .map_err(|e| StoreError::Serialization(e.to_string()))?;
                    idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                }
            }

            // 3. Burn the turn's forever digests in the SAME transaction (the
            //    same-transaction burn weld): the record and its anti-replay
            //    burns are one atomic durability event.
            if !burns.is_empty() {
                let mut forever = write_txn.open_table(tables::FOREVER_DIGESTS)?;
                for (namespace, scope, digest) in burns {
                    let key = crate::forever_digests::forever_key(*namespace, scope, digest);
                    forever.insert(&key, ())?;
                }
            }

            // 4. Advance the durable cursor LAST within the txn (still atomic).
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

    /// The blocklace `block_id` of every durably committed turn this node has
    /// applied — the LIVE-log ids followed by any COMPACTED ids.
    ///
    /// This is the exact identity set of turn-carrying blocks this node has
    /// durably applied (each id was written atomically with its turn's ledger
    /// commit), and is the turn half of the node's identity execution cursor on
    /// recovery: a turn block is re-executed after a restart iff its id is NOT
    /// here — no lost finalized turn, no double-apply.
    ///
    /// COMPACTION-STABILITY (load-bearing for no-double-apply): the contract is
    /// "every APPLIED turn's id appears here", NOT "every id in the live log".
    /// [`Self::compact_below`] removes a subsumed record from the live log but
    /// records its id in `COMMIT_COMPACTED_BLOCK_IDS`; this method unions that
    /// set back in, so the returned identity set is INVARIANT under compaction —
    /// a compacted (already-applied) turn is still reported as applied and is
    /// never re-executed on top of the checkpoint that already includes it.
    pub fn commit_log_block_ids(&self) -> Result<Vec<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::COMMIT_LOG)?;
        let mut out = Vec::new();
        // Live records first, in ordinal order.
        for entry in table.range(0u64..)? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let record: CommitRecord = postcard::from_bytes(entry.1.value())?;
            out.push(record.block_id);
        }
        // Then the ids of turns whose records were compacted away — still
        // applied, must remain in the identity execution cursor.
        let compacted = read_txn.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        for entry in compacted.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push(*entry.0.value());
        }
        Ok(out)
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
        let lo = CommitRecord::height_creator_key(height, &[0u8; 32], 0);
        let hi = CommitRecord::height_creator_key(height, &[0xffu8; 32], u64::MAX);
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
            if key.len() == 48 && &key[8..40] == creator.as_slice() {
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
            compacted: self.commit_compacted_floor()?,
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
            let hc_key = CommitRecord::height_creator_key(record.height, &record.creator, ordinal);
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
            let key = entry.0.value();
            let ordinal = entry.1.value();
            if key.len() != 48 {
                // Pre-(height,creator,ordinal) legacy key shape — the boot
                // migration (`migrate_height_creator_index`) rebuilds these.
                report.orphan_entries.push(format!(
                    "turn_by_height_creator legacy {}-byte key -> ordinal {ordinal}",
                    key.len()
                ));
                continue;
            }
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
                let hc_key = CommitRecord::height_creator_key(
                    record.height,
                    &record.creator,
                    record.ordinal,
                );
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

    // =========================================================================
    // Commit-log compaction (bound the WAL below a finalized checkpoint)
    // =========================================================================

    /// Compact (delete) commit-log records whose finalized state a checkpoint
    /// at/above `height` already subsumes, bounding the otherwise-unbounded
    /// write-ahead log. Returns the number of records compacted.
    ///
    /// # The safety constraint (provably safe — never best-effort)
    ///
    /// A node reconstructs its finalized ledger as `checkpoint ⊕ overlay`, where
    /// the overlay ([`Self::cell_overlay_since`]) is the post-state of every cell
    /// touched by a record with `record.height > checkpoint_height` — records
    /// with `record.height <= checkpoint_height` contribute NOTHING to the
    /// reconstruction (the checkpoint already folded them in). This is the
    /// machine-checked recovery model `CrashRecovery.recover_eq_replay`: the
    /// checkpoint is `replay genesis (take k)` and the overlay is the writes of
    /// `(drop k)`, so the `take k` records are redundant once the checkpoint
    /// exists.
    ///
    /// Compaction is therefore safe ONLY under a COVERING ledger checkpoint:
    /// this method removes records iff
    /// `latest_ledger_checkpoint_height() >= height`, and even then only the
    /// contiguous ordinal PREFIX of records with `record.height < height` (it
    /// stops at the first record with `record.height >= height`, so the live log
    /// `[compacted_floor, cursor)` stays dense — no gap is ever punched). Every
    /// removed record has `height < height <= checkpoint_height`, i.e. strictly
    /// below the checkpoint, so the overlay never references it and the
    /// checkpoint subsumes it.
    ///
    /// When there is NO covering checkpoint (`latest_ledger_checkpoint_height()
    /// < height`), this is a **no-op returning 0**: it refuses to delete any
    /// record a checkpoint does not subsume (deleting one would lose a finalized
    /// turn — the load-bearing "no lost finalized turn" invariant). `height == 0`
    /// is likewise a no-op (nothing is below it).
    ///
    /// # What compaction preserves
    ///
    /// * **The durable cursor is UNCHANGED.** [`Self::commit_cursor`] still
    ///   counts every applied turn; only the physical record count drops. The
    ///   compaction floor ([`Self::commit_compacted_floor`]) advances by exactly
    ///   the number removed, so `cursor == len + floor` holds and the
    ///   index-audit density invariant ([`IndexAuditReport::ok`]) is preserved.
    /// * **No lost finalized turn.** Reconstruction is identical before and
    ///   after: `checkpoint ⊕ cell_overlay_since(checkpoint_height)` is unchanged
    ///   because no compacted record was in that overlay (`recover_eq_replay`).
    /// * **No double-apply.** Each compacted turn's `block_id` is recorded in
    ///   `COMMIT_COMPACTED_BLOCK_IDS` in the SAME transaction, so
    ///   [`Self::commit_log_block_ids`] still reports it as applied and the
    ///   identity execution cursor never re-runs it over the checkpoint.
    /// * **The index agrees with the log.** The compacted records' receipt /
    ///   turn / (height, creator) entries are removed, and the cell-by-id index
    ///   is re-derived from the SURVIVING records (last-writer-wins), so
    ///   [`Self::verify_index_agrees_with_log`] stays `ok()`.
    ///
    /// All of the above land in ONE redb transaction (one fsync boundary): a
    /// crash mid-compaction leaves the pre-compaction (already-consistent) state
    /// in place.
    pub fn compact_below(&self, height: u64) -> Result<u64> {
        // ── Refuse without a covering checkpoint (the safety guard) ─────────
        // Compaction is sound only when a finalized ledger checkpoint at/above
        // `height` captures the state the to-be-removed records reconstruct.
        // No such checkpoint ⇒ delete nothing (a no-op refusal), never lose a
        // finalized turn.
        if height == 0 {
            return Ok(0);
        }
        let checkpoint_height = self.latest_ledger_checkpoint_height()?;
        if checkpoint_height < height {
            tracing::debug!(
                requested_height = height,
                checkpoint_height,
                "compact_below: no covering ledger checkpoint at/above the \
                 requested height — refusing (no-op), records are not subsumed"
            );
            return Ok(0);
        }

        let write_txn = self.db.begin_write()?;
        let compacted;
        {
            // 1. Identify the contiguous ordinal prefix of records strictly
            //    below `height`, collecting what we need to clean up their
            //    index entries, and the SURVIVORS' cells for the cell-index
            //    re-derivation. We stop at the first record with
            //    `height >= height` so the live log never gains a gap.
            struct Doomed {
                ordinal: u64,
                receipt_hash: [u8; 32],
                turn_hash: [u8; 32],
                hc_key: [u8; 48],
                block_id: [u8; 32],
            }
            let mut doomed: Vec<Doomed> = Vec::new();
            let mut survivors: Vec<CommitRecord> = Vec::new();
            {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut prefix_open = true;
                for entry in log.iter()? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    let ordinal = entry.0.value();
                    let record: CommitRecord = postcard::from_bytes(entry.1.value())?;
                    if prefix_open && record.height < height {
                        let hc_key = CommitRecord::height_creator_key(
                            record.height,
                            &record.creator,
                            ordinal,
                        );
                        doomed.push(Doomed {
                            ordinal,
                            receipt_hash: record.receipt_hash,
                            turn_hash: record.turn_hash,
                            hc_key,
                            block_id: record.block_id,
                        });
                    } else {
                        // First record at/above `height` closes the prefix; it
                        // and everything after it survive.
                        prefix_open = false;
                        survivors.push(record);
                    }
                }
            }

            compacted = doomed.len() as u64;
            if compacted == 0 {
                // Nothing to do — leave the store (and its cursor) untouched.
                drop(write_txn);
                return Ok(0);
            }

            // 2. Remove the doomed records from the commit log + their receipt /
            //    turn / (height, creator) index entries.
            {
                let mut log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
                let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                let mut compacted_ids = write_txn.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
                for d in &doomed {
                    log.remove(d.ordinal)?;
                    idx_receipt.remove(&d.receipt_hash)?;
                    idx_turn.remove(&d.turn_hash)?;
                    idx_hc.remove(d.hc_key.as_slice())?;
                    // Carry the applied turn's id forward (no double-apply).
                    compacted_ids.insert(&d.block_id, ())?;
                }
            }

            // 3. Re-derive the cell-by-id index from the SURVIVORS alone
            //    (last-writer-wins). A cell whose only/latest writer was
            //    compacted drops out of the index — correct: the checkpoint
            //    now holds it, and the cell index is exactly the deltas ABOVE
            //    the checkpoint. This keeps the audit's cell-projection check
            //    exact post-compaction.
            {
                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                let keys: Vec<[u8; 32]> = idx_cell
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| *e.0.value()))
                    .collect();
                for k in keys {
                    idx_cell.remove(&k)?;
                }
                // Survivors are already in ascending ordinal order → later
                // writers overwrite earlier ones (last-writer-wins).
                for record in &survivors {
                    for cell in &record.touched_cells {
                        let cell_bytes = postcard::to_stdvec(cell)
                            .map_err(|e| StoreError::Serialization(e.to_string()))?;
                        idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                    }
                }
            }

            // 4. Advance the compaction floor by exactly the count removed.
            //    The commit CURSOR is deliberately UNTOUCHED — it is the applied
            //    high-water mark, not the physical record count.
            {
                let mut meta = write_txn.open_table(tables::METADATA)?;
                let floor = meta
                    .get(tables::META_COMMIT_COMPACTED)?
                    .map(|g| g.value())
                    .unwrap_or(0);
                meta.insert(tables::META_COMMIT_COMPACTED, floor + compacted)?;
            }
        }
        write_txn.commit()?;
        tracing::info!(
            requested_height = height,
            checkpoint_height,
            compacted,
            "compacted commit-log records subsumed by a covering ledger checkpoint"
        );
        Ok(compacted)
    }

    // =========================================================================
    // Crash recovery: recover-to-last-consistent (never strand a divergent image)
    // =========================================================================

    /// Find the highest commit ordinal whose reconstructed ledger root matches
    /// the root that record durably claims, TRUNCATE every divergent record past
    /// it, and return how many records were dropped (0 ⇒ the image was already
    /// consistent — a no-op).
    ///
    /// # Why this exists
    ///
    /// The boot-recovery convergence check (`starbridge-v2::persistence::recover`,
    /// node `state.rs`) reconstructs `checkpoint ⊕ overlay` and asserts the
    /// resulting canonical root equals the root the LAST committed turn recorded
    /// ([`Self::recovered_ledger_root`]). A torn or poisoned write — a process
    /// killed between the input-turn config write and the commit-record txn, a
    /// genesis-path mutation recorded over a turn-touched cell, or a second writer
    /// tearing the same file — leaves the log's tail inconsistent with that
    /// recorded root, and the check refuses the whole image. That STRANDS the
    /// owner: a divergent tail makes the entire durable session unopenable.
    ///
    /// Recovery is the right answer, not refusal. Each [`CommitRecord`] carries
    /// its OWN post-state root (`ledger_root`), so the log is self-checking at
    /// every ordinal: reconstructing `checkpoint ⊕ overlay[..=k]` and comparing to
    /// `record[k].ledger_root` decides whether the prefix through `k` is internally
    /// consistent. This walks the live log in ordinal order, tracks the last `k`
    /// that converges, and TRUNCATES `(k, cursor)` — dropping the divergent tail —
    /// so the image opens at the last-good state and the convergence check then
    /// PASSES at the recovered point. The recovery model is unchanged for the
    /// surviving prefix (`CrashRecovery.recover_eq_replay`): we only discard turns
    /// whose durable post-state cannot be reproduced, which were never safely
    /// committed in the first place.
    ///
    /// # The canonical-root contract
    ///
    /// The per-prefix root MUST be computed with the SAME commitment the records
    /// were written under ([`crate::canonical_ledger_root`], the `v2` whole-cell
    /// Merkle), so a reconstructed prefix is compared byte-for-byte against the
    /// recorded `ledger_root`. The reconstruction is `checkpoint` (the records at
    /// or below the latest checkpoint height are already folded in) plus the
    /// last-writer-wins overlay of every record's `touched_cells` applied in
    /// ordinal order — identical to [`Self::recover`]'s reconstruction, evaluated
    /// at every step instead of only the head.
    ///
    /// # Atomicity
    ///
    /// The truncation (remove the doomed records, drop their index entries, reset
    /// the cursor, re-derive the cell index from survivors) runs in ONE redb
    /// transaction. A crash mid-truncation leaves the pre-recovery (still
    /// divergent-but-untouched) store in place, so recovery is itself idempotent
    /// and crash-safe: re-running it reaches the same last-good point.
    ///
    /// Returns the number of divergent records truncated (0 ⇒ already consistent).
    pub fn recover_to_last_consistent(&self) -> Result<u64> {
        let floor = self.commit_compacted_floor()?;
        let cursor = self.commit_cursor()?;
        if cursor <= floor {
            // No live records to check (fresh or fully compacted) — nothing to do.
            return Ok(0);
        }

        // Reconstruction base: the latest full ledger checkpoint (or empty). The
        // checkpoint already folds in every record at/below its height; the live
        // overlay re-asserts post-checkpoint cells last-writer-wins. We walk the
        // SAME reconstruction `recover` uses, but evaluate the canonical root after
        // EACH record so we find the last ordinal that converges to its claim.
        let checkpoint_height = self.latest_ledger_checkpoint_height()?;
        let mut ledger = match self.load_latest_ledger_checkpoint()? {
            Some((_, l)) => l,
            None => dregg_cell::Ledger::new(),
        };

        // Scan the live log in ordinal order, applying each record's touched cells
        // and remembering the last ordinal whose running root matches its claim.
        let mut last_good: Option<u64> = None;
        {
            let read_txn = self.db.begin_read()?;
            let log = read_txn.open_table(tables::COMMIT_LOG)?;
            for entry in log.range(floor..)? {
                let entry =
                    entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                let ordinal = entry.0.value();
                let record: CommitRecord = postcard::from_bytes(entry.1.value())?;
                // Apply this record's touched cells last-writer-wins. A record above
                // the checkpoint contributes the overlay; one at/below it merely
                // re-asserts cells the checkpoint already folded in (idempotent —
                // same id, same post-state). Either way, after applying this record
                // the ledger is the finalized state as of this turn, so its root is
                // comparable to the record's recorded `ledger_root`.
                for cell in &record.touched_cells {
                    let _ = ledger.remove(&cell.id());
                    let _ = ledger.insert_cell(cell.clone());
                }
                if crate::canonical_ledger_root(&ledger) == record.ledger_root {
                    last_good = Some(ordinal);
                }
            }
        }

        // The new cursor: one past the last converging ordinal. If NOTHING
        // converged, the entire live log is divergent — there is no salvageable
        // last-good point in the records (the caller must start fresh; we do not
        // silently empty the log here, that is the caller's explicit choice).
        let Some(last_good) = last_good else {
            return Err(StoreError::Integrity(
                "recover_to_last_consistent: NO commit-log prefix reconstructs to its recorded \
                 root — the image cannot be salvaged to a last-good point (start fresh)"
                    .to_string(),
            ));
        };
        let new_cursor = last_good + 1;
        if new_cursor == cursor {
            // The head already converges — the image is consistent, no tear.
            return Ok(0);
        }

        // ── TRUNCATE the divergent tail `(new_cursor, cursor)` in ONE txn ──────
        let write_txn = self.db.begin_write()?;
        let truncated;
        {
            // Collect doomed records (their index keys) so we can clean the index.
            struct Doomed {
                ordinal: u64,
                receipt_hash: [u8; 32],
                turn_hash: [u8; 32],
                hc_key: [u8; 48],
            }
            let mut doomed: Vec<Doomed> = Vec::new();
            {
                let log = write_txn.open_table(tables::COMMIT_LOG)?;
                for entry in log.range(new_cursor..)? {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    let ordinal = entry.0.value();
                    let record: CommitRecord = postcard::from_bytes(entry.1.value())?;
                    let hc_key = CommitRecord::height_creator_key(
                        record.height,
                        &record.creator,
                        ordinal,
                    );
                    doomed.push(Doomed {
                        ordinal,
                        receipt_hash: record.receipt_hash,
                        turn_hash: record.turn_hash,
                        hc_key,
                    });
                }
            }
            truncated = doomed.len() as u64;

            // Remove the doomed records + their receipt / turn / (h,c) index entries.
            {
                let mut log = write_txn.open_table(tables::COMMIT_LOG)?;
                let mut idx_receipt = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
                let mut idx_turn = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
                let mut idx_hc = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
                for d in &doomed {
                    log.remove(d.ordinal)?;
                    idx_receipt.remove(&d.receipt_hash)?;
                    idx_turn.remove(&d.turn_hash)?;
                    idx_hc.remove(d.hc_key.as_slice())?;
                }
            }

            // Re-derive the cell-by-id index from the SURVIVING records alone
            // (last-writer-wins) — a cell whose only/latest writer was truncated
            // drops to its checkpoint value (handled on the next recover overlay).
            {
                let survivors: Vec<CommitRecord> = {
                    let log = write_txn.open_table(tables::COMMIT_LOG)?;
                    let mut v = Vec::new();
                    for entry in log.range(floor..)? {
                        let entry = entry.map_err(|e: redb::StorageError| {
                            StoreError::Database(e.to_string())
                        })?;
                        v.push(postcard::from_bytes::<CommitRecord>(entry.1.value())?);
                    }
                    v
                };
                let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
                let keys: Vec<[u8; 32]> = idx_cell
                    .iter()?
                    .filter_map(|e| e.ok().map(|e| *e.0.value()))
                    .collect();
                for k in keys {
                    idx_cell.remove(&k)?;
                }
                for record in &survivors {
                    for cell in &record.touched_cells {
                        let cell_bytes = postcard::to_stdvec(cell)
                            .map_err(|e| StoreError::Serialization(e.to_string()))?;
                        idx_cell.insert(&cell.id().0, cell_bytes.as_slice())?;
                    }
                }
            }

            // Reset the durable cursor to the last-good high-water mark. Unlike
            // compaction (which leaves the cursor as the applied high-water mark),
            // a truncated turn was NEVER safely applied, so the cursor REGRESSES to
            // the last-good ordinal + 1 — the recovered applied count.
            {
                let mut meta = write_txn.open_table(tables::METADATA)?;
                meta.insert(tables::META_COMMIT_CURSOR, new_cursor)?;
            }
        }
        write_txn.commit()?;
        tracing::warn!(
            cursor,
            new_cursor,
            truncated,
            "recover_to_last_consistent: truncated a divergent commit-log tail to the last \
             root-converging ordinal (recovered the image instead of refusing it)"
        );
        Ok(truncated)
    }

    /// One-time migration: the `(height, creator)` index key gained a trailing
    /// ordinal (40 → 48 bytes) when route-level turns started committing to
    /// the log (several can share a `(height, creator)` pair). A store written
    /// by an older node carries 40-byte keys; rebuilding the index from the
    /// log (the source of truth) re-derives every entry in the new shape.
    /// Called from [`PersistentStore::open`]; a no-op on already-migrated and
    /// fresh stores.
    pub(crate) fn migrate_height_creator_index(&self) -> Result<()> {
        let needs_migration = {
            let read_txn = self.db.begin_read()?;
            let idx_hc = read_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
            let mut found_legacy = false;
            for entry in idx_hc.iter()? {
                let entry =
                    entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                if entry.0.value().len() != 48 {
                    found_legacy = true;
                    break;
                }
            }
            found_legacy
        };
        if needs_migration {
            let replayed = self.rebuild_index_from_log()?;
            tracing::info!(
                replayed,
                "migrated turn_by_height_creator index to the (height, creator, ordinal) key shape"
            );
        }
        Ok(())
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

    // signed-wells (ac01f9b7b): cell balances are i64; this test helper keeps a
    // u64 convenience param (callers pass small non-negative amounts) and
    // converts at the boundary.
    fn cell(seed: u8, balance: u64) -> Cell {
        Cell::with_balance([seed; 32], [seed.wrapping_add(7); 32], balance as i64)
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

    /// THE SAME-TRANSACTION BURN WELD (docs/PERSISTENCE.md): a turn's commit
    /// record and its forever-digest burns land in ONE redb transaction —
    /// after an arbitrary crash, either both are durable or neither is. The
    /// crash is modeled exactly as in `crash_recovery_is_consistent`: commits
    /// that returned are durable; everything after the last returned commit
    /// leaves no trace.
    #[test]
    fn burns_land_atomically_with_the_commit_record() {
        use crate::tables::NS_TRUSTLINE_DIGEST;

        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("burnweld.redb");
        let scope = [0x5c; 32];
        let digest = [0xd1; 32];

        {
            let store = PersistentStore::open(&path).unwrap();
            let mut rec = record(0, 0, vec![cell(1, 42)]);
            rec.turn_hash[0] = 0xb1;
            store
                .commit_finalized_turn_with_burns(0, &rec, &[(NS_TRUSTLINE_DIGEST, scope, digest)])
                .unwrap();
            // Crash before any further write.
            drop(store);
        }

        let store = PersistentStore::open(&path).unwrap();
        // BOTH halves survived: the record…
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert!(store.commit_record_at(0).unwrap().is_some());
        // …and the burn.
        assert!(
            store
                .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &digest)
                .unwrap(),
            "the digest burned in the commit transaction survives the crash"
        );

        // Idempotent replay re-accepts the same turn without disturbing the burn.
        let mut rec = record(0, 0, vec![cell(1, 42)]);
        rec.turn_hash[0] = 0xb1;
        assert_eq!(
            store
                .commit_finalized_turn_with_burns(0, &rec, &[(NS_TRUSTLINE_DIGEST, scope, digest)])
                .unwrap(),
            0
        );
        assert!(
            store
                .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &digest)
                .unwrap()
        );
    }

    /// Route-level turns commit several records at the SAME (height, creator)
    /// pair (several service turns between two attested-height advances) —
    /// the (height, creator, ordinal) key keeps every record indexed and the
    /// audit invariant exact.
    #[test]
    fn same_height_creator_records_all_index() {
        let store = PersistentStore::open_in_memory().unwrap();
        for n in 0..3u64 {
            let mut rec = record(n, 0, vec![]);
            rec.height = 7; // SAME height…
            rec.creator = [0x77; 32]; // …SAME creator
            rec.turn_hash[1] = n as u8;
            rec.receipt_hash[1] = n as u8;
            store.commit_finalized_turn(n, &rec).unwrap();
        }
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "index disagrees: {report:?}");
        let at_h = store.turns_at_height(7).unwrap();
        assert_eq!(at_h.len(), 3, "all three same-(height,creator) turns index");
        let by_creator = store.turns_by_creator(&[0x77; 32]).unwrap();
        assert_eq!(by_creator.len(), 3);
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

    // =========================================================================
    // Commit-log compaction (compact_below) — the WAL-bounding tooth.
    // =========================================================================

    use dregg_cell::Ledger;

    /// Reconstruct the finalized ledger AS RECOVERY DOES: the latest ledger
    /// checkpoint ⊕ `cell_overlay_since(checkpoint_height)` (last-writer-wins).
    /// This is `CrashRecovery.recover`; its root is what a recovered node
    /// reaches and MUST be invariant under compaction (`recover_eq_replay`).
    fn recovered_root(store: &PersistentStore) -> [u8; 32] {
        let cp_height = store.latest_ledger_checkpoint_height().unwrap();
        let mut ledger = match store.load_ledger_checkpoint_at(cp_height).unwrap() {
            Some(l) => l,
            None => Ledger::new(),
        };
        for c in store.cell_overlay_since(cp_height).unwrap() {
            // last-writer-wins overwrite (the overlay is already LWW-projected).
            let _ = ledger.remove(&c.id());
            let _ = ledger.insert_cell(c);
        }
        ledger.root()
    }

    /// Take a full-ledger checkpoint at `height` from the records committed
    /// so far whose `height <= height` (the `replay genesis (take k)` cut), and
    /// store it. Mirrors `node`'s "checkpoint the live full ledger" but built
    /// from the log so the test is self-contained. NOTE: stores via the
    /// low-level table so it does NOT co-drive compaction — the test drives
    /// `compact_below` explicitly to isolate it.
    fn checkpoint_from_log_no_codrive(store: &PersistentStore, height: u64) {
        let mut ledger = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            if rec.height <= height {
                for c in rec.touched_cells {
                    let _ = ledger.remove(&c.id());
                    let _ = ledger.insert_cell(c);
                }
            }
        }
        // Write the ledger checkpoint WITHOUT the checkpoint_ledger co-drive.
        let snapshot = crate::ledger_store::LedgerCheckpoint {
            height,
            cells: ledger.iter().map(|(_, c)| c.clone()).collect(),
            sovereign_commitments: Vec::new(),
            sovereign_registrations: Vec::new(),
        };
        store.store_ledger_checkpoint_snapshot(&snapshot).unwrap();
    }

    /// Commit `n` turns at heights 1..=n (record(k).height == k+1, so turn k
    /// lands at height k+1), each touching a distinct cell whose id is seeded by
    /// the turn index (so nothing is dominated and every record contributes a
    /// surviving cell to the reconstruction).
    fn commit_distinct(store: &PersistentStore, n: u64) {
        for k in 0..n {
            let mut rec = record(k, k * 10, vec![cell(k as u8, 100 + k)]);
            rec.turn_hash[0] = 0xc0;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0xd0;
            rec.receipt_hash[1] = k as u8;
            rec.block_id = [0xb0u8.wrapping_add(k as u8); 32];
            store.commit_finalized_turn(k, &rec).unwrap();
        }
    }

    /// THE SAFETY TOOTH (refuse without a covering checkpoint): with NO ledger
    /// checkpoint at/above the requested height, `compact_below` deletes NOTHING
    /// — a record a checkpoint does not subsume is never removed (no lost
    /// finalized turn). The reconstruction, cursor, floor, and audit are all
    /// untouched.
    #[test]
    fn compact_below_refuses_without_a_covering_checkpoint() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 5); // heights 1..=5
        let before = recovered_root(&store);
        let cursor_before = store.commit_cursor().unwrap();
        let len_before = store.commit_log_len().unwrap();

        // No checkpoint at all → refuse (no-op), 0 compacted.
        assert_eq!(store.compact_below(3).unwrap(), 0);

        // A checkpoint exists but BELOW the requested height → still refuse:
        // it does not subsume records up to height 4.
        checkpoint_from_log_no_codrive(&store, 2); // covers heights ≤2 only
        assert_eq!(
            store.compact_below(4).unwrap(),
            0,
            "checkpoint at 2 does NOT cover a compact_below(4) — must refuse"
        );

        // Nothing changed.
        assert_eq!(store.commit_log_len().unwrap(), len_before);
        assert_eq!(store.commit_cursor().unwrap(), cursor_before);
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);
        assert_eq!(recovered_root(&store), before);
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "audit must hold after a refusal: {report:?}");
    }

    /// THE COMPACTION TOOTH: a record BELOW a covering checkpoint IS compacted,
    /// the ledger STILL reconstructs to the same root, and the durable cursor is
    /// UNCHANGED. reconstruct-after-compact == reconstruct-before-compact.
    #[test]
    fn compact_below_removes_subsumed_records_preserving_reconstruction_and_cursor() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // heights 1..=6, ordinals 0..6
        let root_before = recovered_root(&store);
        let cursor_before = store.commit_cursor().unwrap();
        assert_eq!(cursor_before, 6);

        // A covering checkpoint at height 3 (subsumes records with height ≤ 3 =
        // ordinals 0,1,2 → heights 1,2,3). compact_below(3) removes the records
        // STRICTLY below height 3 = heights 1,2 = ordinals 0,1.
        checkpoint_from_log_no_codrive(&store, 3);
        let compacted = store.compact_below(3).unwrap();
        assert_eq!(compacted, 2, "heights 1 and 2 are strictly below 3");

        // Physical records dropped by 2; the CURSOR is unchanged; the floor rose.
        assert_eq!(store.commit_log_len().unwrap(), 4);
        assert_eq!(
            store.commit_cursor().unwrap(),
            cursor_before,
            "the durable applied high-water mark must NOT move under compaction"
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 2);

        // The compacted ordinals are physically gone; the survivors remain dense.
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert!(store.commit_record_at(1).unwrap().is_none());
        for o in 2..6 {
            assert_eq!(store.commit_record_at(o).unwrap().unwrap().ordinal, o);
        }

        // THE EQUIVALENCE: reconstruction is byte-for-byte identical.
        assert_eq!(
            recovered_root(&store),
            root_before,
            "checkpoint ⊕ overlay after compaction must equal the pre-compaction ledger"
        );
        // The head record (cursor-1) — recovery's anchors — is intact.
        assert_eq!(
            store
                .commit_record_at(cursor_before - 1)
                .unwrap()
                .unwrap()
                .ordinal,
            5
        );
        assert_eq!(store.recovered_block_cursor().unwrap(), 5 * 10);
        assert_eq!(
            store.recovered_ledger_root().unwrap().unwrap(),
            store.commit_record_at(5).unwrap().unwrap().ledger_root
        );
    }

    /// THE INDEX-AUDIT INVARIANT holds post-compaction: the compacted records'
    /// receipt / turn / (height,creator) entries are gone (no orphans), the
    /// cell-by-id index is the surviving log's last-writer-wins projection, and
    /// the compaction-aware density `cursor == records + compacted` holds.
    /// Lookups for survivors still resolve; lookups for compacted turns 404.
    #[test]
    fn index_audit_holds_after_compaction() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6);
        // Grab a compacted turn's and a surviving turn's hashes before compaction.
        let compacted_turn = store.commit_record_at(0).unwrap().unwrap();
        let surviving_turn = store.commit_record_at(4).unwrap().unwrap();

        checkpoint_from_log_no_codrive(&store, 3);
        assert_eq!(store.compact_below(3).unwrap(), 2);

        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "audit must hold after compaction: {report:?}");
        assert_eq!(report.records, 4, "4 survivors physically present");
        assert_eq!(report.compacted, 2);
        assert_eq!(report.cursor, 6, "cursor unchanged == records + compacted");

        // A compacted turn no longer resolves through the (removed) index entry…
        assert!(
            store
                .lookup_turn(&compacted_turn.turn_hash)
                .unwrap()
                .is_none()
        );
        assert!(
            store
                .lookup_receipt(&compacted_turn.receipt_hash)
                .unwrap()
                .is_none()
        );
        // …but a survivor still does.
        assert_eq!(
            store
                .lookup_turn(&surviving_turn.turn_hash)
                .unwrap()
                .unwrap()
                .ordinal,
            4
        );

        // Rebuilding the index from the (compacted) log re-agrees — the rebuild
        // is over the survivors and stays consistent.
        let replayed = store.rebuild_index_from_log().unwrap();
        assert_eq!(replayed, 4);
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// NO DOUBLE-APPLY across compaction: a compacted turn's `block_id` is
    /// retained, so `commit_log_block_ids` (the identity execution cursor's turn
    /// half) still reports EVERY applied turn — the returned id set is invariant
    /// under compaction. A compacted turn therefore never looks un-executed.
    #[test]
    fn compaction_preserves_the_applied_turn_identity_set() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6);
        let ids_before: std::collections::HashSet<[u8; 32]> =
            store.commit_log_block_ids().unwrap().into_iter().collect();
        assert_eq!(ids_before.len(), 6);

        checkpoint_from_log_no_codrive(&store, 3);
        assert_eq!(store.compact_below(3).unwrap(), 2);

        let ids_after: std::collections::HashSet<[u8; 32]> =
            store.commit_log_block_ids().unwrap().into_iter().collect();
        assert_eq!(
            ids_after, ids_before,
            "the applied-turn id set must be INVARIANT under compaction \
             (else a compacted turn re-executes on top of the checkpoint)"
        );
    }

    /// THE CHECKPOINT CO-DRIVE: `checkpoint_ledger` at height H drives
    /// `compact_below(H)`, so taking a finalized full-ledger checkpoint bounds
    /// the WAL automatically — and the recovered ledger is unchanged.
    #[test]
    fn checkpoint_ledger_co_drives_compaction() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // heights 1..=6
        let root_before = recovered_root(&store);

        // Build the FULL live ledger (what node passes to checkpoint_ledger).
        let mut full = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            for c in rec.touched_cells {
                let _ = full.remove(&c.id());
                let _ = full.insert_cell(c);
            }
        }
        // Checkpoint at height 6 → co-drives compact_below(6): every record with
        // height < 6 (ordinals 0..4 = heights 1..5) is subsumed and compacted.
        store.checkpoint_ledger(&full, 6).unwrap();

        assert_eq!(
            store.commit_compacted_floor().unwrap(),
            5,
            "checkpoint at 6 co-drove compaction of the 5 records below height 6"
        );
        assert_eq!(store.commit_log_len().unwrap(), 1, "only height-6 survives");
        assert_eq!(store.commit_cursor().unwrap(), 6, "cursor unchanged");
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
        assert_eq!(
            recovered_root(&store),
            root_before,
            "co-driven compaction preserves the recovered ledger"
        );
    }

    /// Compaction is CRASH-DURABLE: after compaction + reopen, the floor, the
    /// cursor, the survivors, the retained compacted ids, and the audit all
    /// survive the restart (one redb transaction = one fsync boundary).
    #[test]
    fn compaction_survives_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("compact.redb");

        let (root_before, head_root): ([u8; 32], [u8; 32]);
        {
            let store = PersistentStore::open(&path).unwrap();
            commit_distinct(&store, 6);
            root_before = recovered_root(&store);
            head_root = store.commit_record_at(5).unwrap().unwrap().ledger_root;
            checkpoint_from_log_no_codrive(&store, 4);
            assert_eq!(store.compact_below(4).unwrap(), 3); // heights 1,2,3
            drop(store);
        }

        let store = PersistentStore::open(&path).unwrap();
        // Durable post-compaction state.
        assert_eq!(store.commit_compacted_floor().unwrap(), 3);
        assert_eq!(store.commit_log_len().unwrap(), 3);
        assert_eq!(store.commit_cursor().unwrap(), 6);
        // The audit (compaction-aware density) holds across the reopen.
        let report = store.verify_index_agrees_with_log().unwrap();
        assert!(report.ok(), "audit after reopen: {report:?}");
        // The recovered ledger is unchanged across the compaction + restart.
        assert_eq!(recovered_root(&store), root_before);
        assert_eq!(store.recovered_ledger_root().unwrap(), Some(head_root));
        // The applied-turn identity set survived (no-double-apply across restart).
        assert_eq!(store.commit_log_block_ids().unwrap().len(), 6);
    }

    /// compact_below stops at the FIRST record at/above `height` — it removes a
    /// contiguous ordinal PREFIX only, never punching a gap into the live log,
    /// and never removing a record the overlay still needs (height ≥ the cut).
    #[test]
    fn compact_below_removes_only_the_contiguous_below_prefix() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // heights 1..=6
        // Cover up to height 6, but only ask to compact below height 4.
        checkpoint_from_log_no_codrive(&store, 6);
        let compacted = store.compact_below(4).unwrap();
        // heights 1,2,3 are strictly below 4 → ordinals 0,1,2 removed; the
        // record at height 4 (ordinal 3) and above survive.
        assert_eq!(compacted, 3);
        assert_eq!(store.commit_compacted_floor().unwrap(), 3);
        assert!(store.commit_record_at(2).unwrap().is_none());
        assert_eq!(store.commit_record_at(3).unwrap().unwrap().height, 4);
        // The live log [3,6) is dense — no gap.
        for o in 3..6 {
            assert!(store.commit_record_at(o).unwrap().is_some());
        }
        assert!(store.verify_index_agrees_with_log().unwrap().ok());

        // A second compaction at the same height is an idempotent no-op (the
        // below-prefix is already gone).
        assert_eq!(store.compact_below(4).unwrap(), 0);
        assert_eq!(store.commit_compacted_floor().unwrap(), 3);
    }

    /// Anti-vacuity: an over-broad deletion (dropping a record the overlay still
    /// needs) WOULD change the reconstruction — proving the height<cut guard is
    /// load-bearing, mirroring `CrashRecovery.lost_turn_changes_state`. Here we
    /// confirm that compacting a record whose cell is NOT dominated and is NOT
    /// in the checkpoint would lose it — so `compact_below` must (and does)
    /// refuse to touch records at/above the covering checkpoint's reach.
    #[test]
    fn keeping_overlay_records_is_load_bearing() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_distinct(&store, 6); // distinct cells per height → none dominated
        let full = recovered_root(&store);

        // Checkpoint at height 3 covers heights ≤3. Records at heights 4,5,6 are
        // the overlay and are LOAD-BEARING (distinct, undominated cells).
        checkpoint_from_log_no_codrive(&store, 3);
        assert_eq!(store.compact_below(3).unwrap(), 2); // only heights 1,2 go

        // The overlay records (4,5,6) are untouched and the ledger is intact.
        assert_eq!(recovered_root(&store), full);
        assert!(store.commit_record_at(3).unwrap().is_some()); // height 4 survives
        assert!(store.commit_record_at(5).unwrap().is_some()); // height 6 survives

        // And compact_below can NEVER be asked to remove them while the only
        // checkpoint is at 3: a request below height 4 leaves them; a request at
        // height 5 is REFUSED (checkpoint at 3 does not cover it).
        assert_eq!(store.compact_below(5).unwrap(), 0);
        assert_eq!(recovered_root(&store), full);
    }

    // =========================================================================
    // recover_to_last_consistent — RECOVER a torn/divergent image, never strand
    // =========================================================================

    /// Commit `n` turns at ascending heights, each touching a DISTINCT cell, with
    /// every record's `ledger_root` set to the canonical (v2) root of the
    /// reconstructed prefix THROUGH that turn — i.e. a genuine, self-consistent
    /// log where `recover_to_last_consistent` finds the head converging.
    fn commit_canonical(store: &PersistentStore, n: u64) {
        let mut ledger = Ledger::new();
        for k in 0..n {
            let c = cell(k as u8, 100 + k);
            let _ = ledger.remove(&c.id());
            let _ = ledger.insert_cell(c.clone());
            let mut rec = record(k, k * 10, vec![c]);
            rec.turn_hash[0] = 0xe0;
            rec.turn_hash[1] = k as u8;
            rec.receipt_hash[0] = 0xf0;
            rec.receipt_hash[1] = k as u8;
            // The TRUE post-state root the convergence check (and recovery) uses.
            rec.ledger_root = crate::canonical_ledger_root(&ledger);
            store.commit_finalized_turn(k, &rec).unwrap();
        }
    }

    /// A consistent image is left UNTOUCHED: `recover_to_last_consistent` is a
    /// no-op (0 truncated) when the head already reconstructs to its recorded
    /// root, and the convergence check (last record's root == reconstruction)
    /// holds before and after.
    #[test]
    fn recover_is_a_noop_on_a_consistent_image() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_canonical(&store, 5);
        let cursor_before = store.commit_cursor().unwrap();

        assert_eq!(
            store.recover_to_last_consistent().unwrap(),
            0,
            "a consistent image needs no truncation"
        );
        assert_eq!(store.commit_cursor().unwrap(), cursor_before);
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// THE STRAND-PREVENTION TOOTH: a TORN write leaves the log's tail
    /// inconsistent with its recorded root (the old path would refuse the whole
    /// image and STRAND the owner). `recover_to_last_consistent` finds the last
    /// root-converging ordinal, TRUNCATES the divergent tail, and the image then
    /// opens at the last-good state — recovery succeeds where refusal stranded.
    #[test]
    fn recover_truncates_a_divergent_tail_to_last_good() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Three genuine, self-consistent turns (ordinals 0,1,2).
        commit_canonical(&store, 3);

        // Model a TORN write: append two more records whose `ledger_root` does
        // NOT match the reconstruction (a crash mid-write / a poisoned cell left
        // the recorded root inconsistent with the post-state). They land in the
        // log (cursor advances), but the head no longer reconstructs to its claim.
        for k in 3..5u64 {
            let c = cell(k as u8, 100 + k);
            let mut bad = record(k, k * 10, vec![c]);
            bad.turn_hash[0] = 0xe0;
            bad.turn_hash[1] = k as u8;
            bad.receipt_hash[0] = 0xf0;
            bad.receipt_hash[1] = k as u8;
            // A WRONG root — the tear: the post-state does not match this claim.
            bad.ledger_root = [0xde; 32];
            store.commit_finalized_turn(k, &bad).unwrap();
        }
        assert_eq!(store.commit_cursor().unwrap(), 5);
        // Sanity: the head (ordinal 4) does NOT converge — the old check refuses.
        let head_root = store.recovered_ledger_root().unwrap().unwrap();
        assert_eq!(head_root, [0xde; 32], "the torn tail recorded a bogus root");

        // RECOVER: truncate the two divergent records, land at the last-good (2).
        let truncated = store.recover_to_last_consistent().unwrap();
        assert_eq!(truncated, 2, "the two torn records are dropped");
        assert_eq!(
            store.commit_cursor().unwrap(),
            3,
            "cursor regresses to last-good + 1"
        );
        assert!(store.commit_record_at(3).unwrap().is_none(), "tail dropped");
        assert!(store.commit_record_at(4).unwrap().is_none(), "tail dropped");
        assert!(store.commit_record_at(2).unwrap().is_some(), "last-good kept");

        // THE CONVERGENCE CHECK NOW PASSES at the recovered point: the head's
        // recorded root equals the reconstruction (this is what `recover` asserts).
        let mut ledger = Ledger::new();
        for c in store.cell_overlay_since(0).unwrap() {
            let _ = ledger.remove(&c.id());
            let _ = ledger.insert_cell(c);
        }
        assert_eq!(
            crate::canonical_ledger_root(&ledger),
            store.recovered_ledger_root().unwrap().unwrap(),
            "after recovery the reconstruction MATCHES the head's recorded root \
             (the integrity check passes — the image opens instead of stranding)"
        );

        // The index agrees with the truncated log, and the recovered store is
        // LIVE: it accepts the next turn at the recovered cursor.
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
        let c5 = cell(5, 105);
        let mut next = record(5, 50, vec![c5]);
        next.turn_hash[0] = 0xe0;
        next.turn_hash[1] = 9;
        next.receipt_hash[0] = 0xf0;
        next.receipt_hash[1] = 9;
        next.ledger_root = [0x5a; 32];
        assert_eq!(
            store.commit_finalized_turn(3, &next).unwrap(),
            3,
            "the recovered store accepts the NEXT turn at the recovered cursor"
        );
    }

    /// Recovery survives a real reopen (on-disk redb): commit a consistent
    /// prefix, "crash" with a divergent tail, drop, reopen, `recover_to_last_
    /// consistent`, and confirm the truncation is durable.
    #[test]
    fn recover_truncation_is_durable_across_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("recover.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            commit_canonical(&store, 3);
            // Torn tail: one bogus-root record.
            let c = cell(3, 103);
            let mut bad = record(3, 30, vec![c]);
            bad.turn_hash[0] = 0xe0;
            bad.turn_hash[1] = 3;
            bad.receipt_hash[0] = 0xf0;
            bad.receipt_hash[1] = 3;
            bad.ledger_root = [0xab; 32];
            store.commit_finalized_turn(3, &bad).unwrap();
            drop(store);
        }
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 4, "torn tail is on disk");
        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert_eq!(store.commit_cursor().unwrap(), 3);
        drop(store);

        // The truncation persisted: a fresh reopen sees the recovered cursor.
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 3);
        assert!(store.commit_record_at(3).unwrap().is_none());
        assert!(store.verify_index_agrees_with_log().unwrap().ok());
    }

    /// THE SINGLE-WRITER GUARD (against the OTHER corruption cause — concurrent
    /// writers): redb holds an exclusive advisory file lock per database file, so
    /// a SECOND process/handle opening the SAME durable image while the first
    /// holds it is REJECTED with a store error — it can never tear the file with a
    /// racing double-write. (This is why login's logout RELEASES the durable
    /// handle before a re-login reopens it, and why a fork is ephemeral.) A torn
    /// commit log from two cockpit processes on one image is thus prevented at the
    /// source: fail (the second open errors), never corrupt.
    #[test]
    fn a_second_concurrent_open_is_rejected_not_corrupting() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("single-writer.redb");

        // First handle commits a turn and stays OPEN (holding the lock).
        let first = PersistentStore::open(&path).unwrap();
        let mut rec = record(0, 0, vec![cell(1, 42)]);
        rec.turn_hash[0] = 0x11;
        first.commit_finalized_turn(0, &rec).unwrap();

        // A second open of the SAME file while `first` is alive must be REFUSED —
        // redb's single-writer lock fails-closed (no tearing double-write).
        let second = PersistentStore::open(&path);
        assert!(
            second.is_err(),
            "a concurrent open of the same durable image must be rejected (single-writer)"
        );

        // After the first handle is RELEASED, a reopen succeeds and the committed
        // turn is intact (the rejection protected, not corrupted, the image).
        drop(first);
        let reopened = PersistentStore::open(&path).unwrap();
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert!(reopened.commit_record_at(0).unwrap().is_some());
    }
}
