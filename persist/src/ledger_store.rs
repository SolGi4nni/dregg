//! Ledger checkpoint persistence.
//!
//! Implements checkpoint-based persistence for the cell ledger. The ledger is
//! derived state (reconstructible from the blocklace), but checkpoints allow
//! fast startup without replaying the entire history.
//!
//! # Strategy
//!
//! - **Periodic checkpoints**: Every N finalized blocks, serialize the full
//!   ledger state to redb.
//! - **Shutdown checkpoint**: On graceful shutdown, write the current ledger.
//! - **Startup restore**: Load the latest checkpoint. If no checkpoint exists,
//!   the ledger starts empty (the blocklace replay layer, when implemented,
//!   will fill in the gap).
//!
//! # Serialization
//!
//! The `Ledger` struct contains non-serializable runtime state (mpsc channels,
//! cached Merkle tree). We serialize only the essential data:
//! - All hosted cells (HashMap<CellId, Cell>)
//! - Sovereign commitments (HashMap<CellId, [u8; 32]>)
//! - Sovereign registrations (HashMap<CellId, SovereignRegistration>)
//!
//! On restore, the Merkle tree is rebuilt from the cells (lazy on first `root()` call).

use redb::ReadableTable;
use serde::{Deserialize, Serialize};

use dregg_cell::{Cell, CellId, Ledger, SovereignRegistration};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Serializable snapshot of ledger state for checkpoint persistence.
///
/// This captures all data needed to reconstruct a `Ledger` (minus ephemeral
/// runtime state like Merkle tree caches and witness subscribers).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LedgerCheckpoint {
    /// Block height at which this checkpoint was taken.
    pub height: u64,
    /// All hosted cells.
    pub cells: Vec<Cell>,
    /// Sovereign commitment entries: (cell_id_bytes, commitment).
    pub sovereign_commitments: Vec<([u8; 32], [u8; 32])>,
    /// Ephemeral sovereign registrations with TTL metadata.
    pub sovereign_registrations: Vec<([u8; 32], SovereignRegistration)>,
}

impl PersistentStore {
    // =========================================================================
    // Ledger Checkpoint Storage
    // =========================================================================

    /// Install one canonical checkpoint wire exactly once.
    ///
    /// A same-height retry is accepted only when its bytes are identical. Checkpoint identities
    /// are signed by PoA compact anchors and may also be trusted by snapshot consumers, so treating
    /// a height as an upsert would let a successful call poison those authorities for the next
    /// restart. A differing retry aborts its transaction before any table or metadata mutation.
    fn store_exact_ledger_checkpoint_wire(&self, height: u64, serialized: &[u8]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::LEDGER_CHECKPOINTS)?;
            let existing = table.get(height)?.map(|guard| guard.value().to_vec());
            match existing {
                Some(bytes) if bytes == serialized => {}
                Some(_) => {
                    return Err(StoreError::Integrity(format!(
                        "ledger checkpoint height {height} is already bound to different exact bytes"
                    )));
                }
                None => {
                    table.insert(height, serialized)?;
                }
            }

            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_latest = meta
                .get(tables::META_LATEST_LEDGER_CHECKPOINT_HEIGHT)?
                .map(|guard| guard.value())
                .unwrap_or(0);
            if height >= current_latest {
                meta.insert(tables::META_LATEST_LEDGER_CHECKPOINT_HEIGHT, height)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Serialize and persist the current ledger state as a checkpoint.
    ///
    /// The checkpoint is keyed by block height. Also updates the metadata
    /// tracking the latest ledger checkpoint height.
    ///
    /// The checkpoint write is committed first. The legacy unsigned compaction request below now
    /// deliberately refuses: subsumption alone cannot authenticate the compact authority carrier.
    /// A separate committee ceremony prepares and hybrid-signs
    /// `PoaCompactCheckpointStatementV1`, then calls
    /// `compact_below_with_poa_anchor_v1`. Until that producer is wired, the WAL stays larger.
    pub fn checkpoint_ledger(&self, ledger: &Ledger, height: u64) -> Result<()> {
        let snapshot = ledger_to_checkpoint(ledger, height);
        let serialized =
            postcard::to_stdvec(&snapshot).map_err(|e| StoreError::Serialization(e.to_string()))?;

        self.store_exact_ledger_checkpoint_wire(height, &serialized)?;

        // Ask the unsigned compatibility entry point. It is intentionally a no-op until the node
        // supplies the separately finalized signed anchor; a checkpoint remains useful without
        // granting itself deletion authority.
        match self.compact_below(height) {
            Ok(0) => {}
            Ok(n) => tracing::debug!(
                height,
                compacted = n,
                "checkpoint co-drove commit-log compaction"
            ),
            Err(e) => tracing::warn!(
                error = %e,
                height,
                "checkpoint-driven commit-log compaction failed (checkpoint is \
                 durable; WAL stays larger, next checkpoint retries)"
            ),
        }
        Ok(())
    }

    /// Load the latest ledger checkpoint.
    ///
    /// Returns `None` if no checkpoint has ever been written (fresh node).
    pub fn load_latest_ledger_checkpoint(&self) -> Result<Option<(u64, Ledger)>> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let height = match meta.get(tables::META_LATEST_LEDGER_CHECKPOINT_HEIGHT)? {
            Some(guard) => guard.value(),
            None => return Ok(None),
        };

        let table = read_txn.open_table(tables::LEDGER_CHECKPOINTS)?;
        match table.get(height)? {
            Some(value) => {
                let snapshot: LedgerCheckpoint = postcard::from_bytes(value.value())?;
                let ledger = checkpoint_to_ledger(snapshot);
                Ok(Some((height, ledger)))
            }
            None => Ok(None),
        }
    }

    /// Load a ledger checkpoint at a specific height.
    pub fn load_ledger_checkpoint_at(&self, height: u64) -> Result<Option<Ledger>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::LEDGER_CHECKPOINTS)?;

        match table.get(height)? {
            Some(value) => {
                let snapshot: LedgerCheckpoint = postcard::from_bytes(value.value())?;
                Ok(Some(checkpoint_to_ledger(snapshot)))
            }
            None => Ok(None),
        }
    }

    /// Load the highest-height ledger checkpoint at-or-below `target`, with its
    /// height. Used by snapshot shipping to pick the checkpoint base nearest a
    /// joiner's requested floor. `None` if no checkpoint at-or-below `target`
    /// exists.
    pub fn latest_ledger_checkpoint_at_or_below(
        &self,
        target: u64,
    ) -> Result<Option<(u64, LedgerCheckpoint)>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::LEDGER_CHECKPOINTS)?;
        // Range [0, target] descending: the last (highest) entry is the base.
        let mut best: Option<(u64, Vec<u8>)> = None;
        for entry in table.range(0u64..=target)? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let h = entry.0.value();
            // redb iterates ascending; keep overwriting → ends at the highest.
            best = Some((h, entry.1.value().to_vec()));
        }
        match best {
            Some((h, bytes)) => {
                let snapshot: LedgerCheckpoint = postcard::from_bytes(&bytes)?;
                Ok(Some((h, snapshot)))
            }
            None => Ok(None),
        }
    }

    /// Get the height of the latest ledger checkpoint, or 0 if none exists.
    pub fn latest_ledger_checkpoint_height(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_LATEST_LEDGER_CHECKPOINT_HEIGHT)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Store a pre-serialized [`LedgerCheckpoint`] (e.g. one received in a shipped
    /// snapshot) at its own height, updating the latest-checkpoint-height
    /// metadata. The counterpart to [`Self::checkpoint_ledger`] for a checkpoint
    /// the node did not compute locally. Same-height retries are exact-wire idempotent; a differing
    /// snapshot is refused before mutation.
    pub fn store_ledger_checkpoint_snapshot(&self, snapshot: &LedgerCheckpoint) -> Result<()> {
        let serialized =
            postcard::to_stdvec(snapshot).map_err(|e| StoreError::Serialization(e.to_string()))?;
        self.store_exact_ledger_checkpoint_wire(snapshot.height, &serialized)
    }

    /// Install a set of overlay cell post-states into the cell-by-id index (the
    /// snapshot-apply path). Each cell is upserted under its id (last-writer-wins
    /// by the overlay's own ordering — the overlay is already a last-writer-wins
    /// projection). Used by [`PersistentStore::install_snapshot`] so a joiner's
    /// `lookup_cell` / `cell_overlay_since` resolve the post-checkpoint deltas.
    pub fn install_overlay_into_cell_index(
        &self,
        overlay: &[crate::commit_log::CellOverlayOp],
    ) -> Result<()> {
        use crate::commit_log::CellOverlayOp;
        let write_txn = self.db.begin_write()?;
        {
            let mut idx_cell = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
            for op in overlay {
                match op {
                    CellOverlayOp::Upsert(cell) => {
                        let bytes = postcard::to_stdvec(cell)
                            .map_err(|e| StoreError::Serialization(e.to_string()))?;
                        idx_cell.insert(&cell.id().0, bytes.as_slice())?;
                    }
                    // A tombstone drops the id from the index — else `lookup_cell`
                    // resurrects the removed (MakeSovereign) cell as hosted.
                    CellOverlayOp::Remove(id) => {
                        idx_cell.remove(&id.0)?;
                    }
                }
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load every cell currently in the cell-by-id index (the installed overlay
    /// after a snapshot apply). Diagnostic / recovery helper.
    pub fn installed_overlay_cells(&self) -> Result<Vec<Cell>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::IDX_CELL_BY_ID)?;
        let mut out = Vec::new();
        for entry in table.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push(postcard::from_bytes(entry.1.value())?);
        }
        Ok(out)
    }

    /// Remove old ledger checkpoints, keeping only the most recent `keep_last_n`.
    ///
    /// This bounds storage growth: each checkpoint is O(cells) in size, so keeping
    /// too many wastes disk. Returns the number of checkpoints pruned.
    pub fn prune_ledger_checkpoints(&self, keep_last_n: usize) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::LEDGER_CHECKPOINTS)?;

        // Collect all checkpoint heights.
        let mut heights: Vec<u64> = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            heights.push(entry.0.value());
        }
        let compact_authority_checkpoints =
            crate::poa_compact_authority::required_checkpoint_heights_in_read(&read_txn)?;
        drop(table);
        drop(read_txn);

        if heights.len() <= keep_last_n {
            return Ok(0);
        }

        // Sort descending so we keep the largest heights.
        heights.sort_unstable_by(|a, b| b.cmp(a));
        let to_remove: Vec<u64> = heights[keep_last_n..]
            .iter()
            .copied()
            .filter(|height| !compact_authority_checkpoints.contains(height))
            .collect();

        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::LEDGER_CHECKPOINTS)?;
            for &h in &to_remove {
                table.remove(h)?;
            }
        }
        write_txn.commit()?;

        Ok(to_remove.len() as u64)
    }
}

// =============================================================================
// Conversion helpers
// =============================================================================

/// Extract serializable data from a `Ledger` into a `LedgerCheckpoint`.
fn ledger_to_checkpoint(ledger: &Ledger, height: u64) -> LedgerCheckpoint {
    let cells: Vec<Cell> = ledger.iter().map(|(_, cell)| cell.clone()).collect();

    let sovereign_commitments: Vec<([u8; 32], [u8; 32])> = ledger
        .iter_sovereign_commitments()
        .map(|(id, commitment)| (id.0, *commitment))
        .collect();

    let sovereign_registrations: Vec<([u8; 32], SovereignRegistration)> = ledger
        .iter_sovereign_registrations()
        .map(|(id, reg)| (id.0, reg.clone()))
        .collect();

    LedgerCheckpoint {
        height,
        cells,
        sovereign_commitments,
        sovereign_registrations,
    }
}

/// Reconstruct a `Ledger` from a borrowed `LedgerCheckpoint` (the snapshot-apply
/// path, which keeps the checkpoint to ship/verify). Same reconstruction as
/// [`checkpoint_to_ledger`], by reference.
pub(crate) fn checkpoint_to_ledger_snapshot(snapshot: &LedgerCheckpoint) -> Ledger {
    let mut ledger = Ledger::new();
    for cell in &snapshot.cells {
        let _ = ledger.insert_cell(cell.clone());
    }
    for (id_bytes, commitment) in &snapshot.sovereign_commitments {
        let cell_id = CellId(*id_bytes);
        let _ = ledger.register_sovereign_cell(cell_id, *commitment);
    }
    for (id_bytes, registration) in &snapshot.sovereign_registrations {
        // WHOLE-RECORD restore. `register_sovereign_cell_with_vk` hard-codes
        // `max_custom_effects: None` and `owner_public_key: None`, so restoring through it
        // silently dropped both: a declared custom-effect cap did not survive a restart,
        // and the sovereign-witness key commitment reverted to the zero sentinel.
        let cell_id = CellId(*id_bytes);
        let _ = ledger.register_sovereign_cell_record(cell_id, registration.clone());
    }
    ledger
}

/// Reconstruct a `Ledger` from a `LedgerCheckpoint`.
fn checkpoint_to_ledger(snapshot: LedgerCheckpoint) -> Ledger {
    let mut ledger = Ledger::new();

    // Insert all hosted cells.
    for cell in snapshot.cells {
        // Use insert_cell which handles the ID from the cell itself.
        let _ = ledger.insert_cell(cell);
    }

    // Restore sovereign commitments.
    for (id_bytes, commitment) in snapshot.sovereign_commitments {
        let cell_id = CellId(id_bytes);
        let _ = ledger.register_sovereign_cell(cell_id, commitment);
    }

    // Restore sovereign registrations — WHOLE RECORD (see the sibling projection above;
    // the `_with_vk` route drops `max_custom_effects` and `owner_public_key`).
    for (id_bytes, registration) in snapshot.sovereign_registrations {
        let cell_id = CellId(id_bytes);
        let _ = ledger.register_sovereign_cell_record(cell_id, registration);
    }

    ledger
}

#[cfg(test)]
mod tests {
    use super::*;

    fn snapshot(height: u64, tag: u8) -> LedgerCheckpoint {
        LedgerCheckpoint {
            height,
            cells: Vec::new(),
            sovereign_commitments: vec![([tag; 32], [tag.wrapping_add(1); 32])],
            sovereign_registrations: Vec::new(),
        }
    }

    #[test]
    fn checkpoint_height_is_exact_wire_idempotent_not_an_upsert() {
        let store = PersistentStore::open_in_memory().unwrap();
        let original = snapshot(7, 0x31);
        store.store_ledger_checkpoint_snapshot(&original).unwrap();
        store
            .store_ledger_checkpoint_snapshot(&original)
            .expect("byte-identical retry is idempotent");

        let substituted = snapshot(7, 0x41);
        let error = store
            .store_ledger_checkpoint_snapshot(&substituted)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("already bound to different exact bytes"),
            "{error}"
        );

        let (_, retained) = store
            .latest_ledger_checkpoint_at_or_below(7)
            .unwrap()
            .expect("original checkpoint remains");
        assert_eq!(retained.height, original.height);
        assert_eq!(
            retained.sovereign_commitments, original.sovereign_commitments,
            "refused substitution must not mutate the checkpoint"
        );
    }

    #[test]
    fn locally_computed_checkpoint_also_refuses_same_height_substitution() {
        let store = PersistentStore::open_in_memory().unwrap();
        let ledger = Ledger::new();
        store.checkpoint_ledger(&ledger, 9).unwrap();
        store
            .checkpoint_ledger(&ledger, 9)
            .expect("same ledger and height retry is idempotent");

        let error = store
            .store_ledger_checkpoint_snapshot(&snapshot(9, 0x51))
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("already bound to different exact bytes"),
            "{error}"
        );
        assert_eq!(store.latest_ledger_checkpoint_height().unwrap(), 9);
    }
}
