//! Checkpoint persistent storage and pruning operations.
//!
//! Stores checkpoints (federation-attested state snapshots) and provides
//! pruning operations that delete blocks, receipts, and audit log entries
//! older than the latest checkpoint.
//!
//! Pruning is always opt-in (archival nodes skip it). After pruning, the node
//! can still function normally — it just cannot serve historical data below
//! the checkpoint height.

use redb::ReadableTable;

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Result of a prune operation.
#[derive(Clone, Debug, Default)]
pub struct PruneResult {
    /// Number of attested roots removed.
    pub roots_pruned: u64,
    /// Number of audit log entries removed.
    pub audit_entries_pruned: u64,
}

impl PersistentStore {
    // =========================================================================
    // Checkpoint Storage
    // =========================================================================

    /// Store a checkpoint at its height.
    ///
    /// Also updates the metadata to track the latest checkpoint height.
    pub fn store_checkpoint(&self, checkpoint: &pyana_federation::Checkpoint) -> Result<()> {
        let serialized = postcard::to_stdvec(checkpoint)
            .map_err(|e| StoreError::Serialization(e.to_string()))?;

        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::CHECKPOINTS)?;
            table.insert(checkpoint.height, serialized.as_slice())?;

            // Update latest checkpoint height metadata.
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_latest = meta
                .get(tables::META_LATEST_CHECKPOINT_HEIGHT)?
                .map(|g| g.value())
                .unwrap_or(0);
            if checkpoint.height >= current_latest {
                meta.insert(tables::META_LATEST_CHECKPOINT_HEIGHT, checkpoint.height)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load the latest (highest-height) checkpoint.
    pub fn latest_checkpoint(&self) -> Result<Option<pyana_federation::Checkpoint>> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let height = match meta.get(tables::META_LATEST_CHECKPOINT_HEIGHT)? {
            Some(guard) => guard.value(),
            None => return Ok(None),
        };

        let table = read_txn.open_table(tables::CHECKPOINTS)?;
        match table.get(height)? {
            Some(value) => {
                let checkpoint: pyana_federation::Checkpoint = postcard::from_bytes(value.value())?;
                Ok(Some(checkpoint))
            }
            None => Ok(None),
        }
    }

    /// Load a checkpoint at a specific height.
    pub fn checkpoint_at_height(
        &self,
        height: u64,
    ) -> Result<Option<pyana_federation::Checkpoint>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::CHECKPOINTS)?;

        match table.get(height)? {
            Some(value) => {
                let checkpoint: pyana_federation::Checkpoint = postcard::from_bytes(value.value())?;
                Ok(Some(checkpoint))
            }
            None => Ok(None),
        }
    }

    /// Get the latest checkpoint height, or 0 if no checkpoints exist.
    pub fn latest_checkpoint_height(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_LATEST_CHECKPOINT_HEIGHT)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    // =========================================================================
    // Pruning Operations
    // =========================================================================

    /// Prune all data below the given height.
    ///
    /// Removes:
    /// - Attested roots at heights strictly below `height`
    /// - Audit log entries with sequence numbers below the checkpoint boundary
    ///
    /// Does NOT remove:
    /// - Revocations (they are a cumulative set, not height-indexed)
    /// - Note commitments (append-only tree, needed for proofs)
    /// - Nullifiers (cumulative set)
    /// - The checkpoints themselves (always retained)
    ///
    /// All pruning is performed within a single write transaction to ensure
    /// atomicity. A crash between pruning roots and audit entries cannot leave
    /// the store in a partially-pruned state.
    ///
    /// Returns a summary of what was pruned.
    pub fn prune_before(&self, height: u64) -> Result<PruneResult> {
        let mut result = PruneResult::default();

        let write_txn = self.db.begin_write()?;
        {
            // Prune attested roots below the checkpoint height.
            let mut roots_table = write_txn.open_table(tables::ATTESTED_ROOTS)?;
            let mut roots_to_remove = Vec::new();
            {
                let range = roots_table.range(0..height)?;
                for entry in range {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    roots_to_remove.push(entry.0.value());
                }
            }
            for key in &roots_to_remove {
                roots_table.remove(*key)?;
                result.roots_pruned += 1;
            }
            drop(roots_table);

            // Prune audit log entries older than the checkpoint.
            // We use a heuristic: audit entries are roughly 1:1 with block heights,
            // so we prune entries with sequence < height. This is approximate but safe.
            let mut log_table = write_txn.open_table(tables::AUDIT_LOG)?;
            let mut idx_table = write_txn.open_table(tables::AUDIT_TOKEN_INDEX)?;

            let mut to_remove = Vec::new();
            let mut index_keys_to_remove = Vec::new();
            {
                let range = log_table.range(0..height)?;
                for entry in range {
                    let entry = entry
                        .map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
                    let seq = entry.0.value();
                    to_remove.push(seq);

                    // Decode the event to find its token index key.
                    if let Ok(event) =
                        postcard::from_bytes::<crate::audit::StoredAuditEvent>(entry.1.value())
                    {
                        let token_hex: String =
                            event.token_id.iter().map(|b| format!("{b:02x}")).collect();
                        let index_key = format!("{token_hex}:{seq:020}");
                        index_keys_to_remove.push(index_key);
                    }
                }
            }

            for seq in &to_remove {
                log_table.remove(*seq)?;
                result.audit_entries_pruned += 1;
            }
            for key in &index_keys_to_remove {
                idx_table.remove(key.as_str())?;
            }
        }
        write_txn.commit()?;

        Ok(result)
    }
}
