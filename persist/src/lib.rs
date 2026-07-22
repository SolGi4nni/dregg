//! `dregg-persist`: the node's ONE durable store (.docs-history-noclaude/PERSISTENCE.md).
//!
//! This crate provides the node's durable storage — the commit log + index,
//! ledger checkpoints, blocklace blocks/meta, notes/nullifiers, attested
//! roots, forever-digest sets, channel rosters, and config blobs — backed by
//! `redb` (embedded ACID, WAL): every durable write is a transaction that
//! either commits fully (fsync at the commit boundary) or not at all.
//!
//! The [`commit_log`] module is the recovery spine: each applied turn's
//! durable record, the commit cursor advance, and every index entry
//! (receipt-by-hash, turn-by-hash, turn-by-(height, creator, ordinal),
//! cell-by-id) are written in ONE redb transaction, so recovery converges to
//! a consistent checkpoint with no torn state, no lost finalized turn, and no
//! double-apply. The index is rebuildable from — and provably agrees with —
//! the log (`verify_index_agrees_with_log`). A turn that burns anti-replay
//! digests can land them in the SAME transaction
//! (`commit_finalized_turn_with_burns` — the same-transaction burn weld).
//!
//! ## dregg1 residue, retired
//!
//! The `tokens` (TokenChain/fold steps), `recovery`
//! (`recover_federation_state`), `keys` (encrypted signing keys; the node
//! keeps its key in `node.key`) and `audit` (standalone audit log) modules
//! were dregg1-era residue with zero consumers outside this crate's own
//! tests; they were deleted under the cutover-ledger discipline (verified
//! zero external consumers by grep at deletion time). Their tables are no
//! longer created; pre-existing tables in an old store file are simply
//! ignored by redb.

pub mod blocklace_store;
pub mod channel_rosters;
pub mod checkpoint;
pub mod commit_log;
pub mod exact_fnsp_v3_frame_head;
pub mod exact_fnsp_v3_state;
pub mod faithful_note_root_history;
pub mod federation;
pub mod finalized_faithful_spend;
pub mod forever_digests;
pub mod image_builder;
pub mod ledger_store;
pub mod note_tree;
pub mod poseidon2_note_tree;
pub mod snapshot;
pub mod tables;

#[cfg(test)]
mod tests;

use std::path::Path;

use redb::{Database, ReadableTable, ReadableTableMetadata};

pub use blocklace_store::BlocklaceMeta;
pub use commit_log::{
    CellOverlayOp, CommitRecord, ExactFnspV3FrameCommitOutcome, FinalizedNullifierRecord,
    IndexAuditReport,
};
pub use exact_fnsp_v3_frame_head::{
    CommittedExactFnspV3FrameHeadV1, EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN,
    EXACT_FNSP_V3_FRAME_V1_WIRE_LEN, ExactFnspV3DurableReceiptLinkV1, ExactFnspV3FrameStoreError,
    StoreAuthenticatedExactFnspV3ActivationV1, UntrustedExactFnspV3ActivationV1,
    UntrustedExactFnspV3FrameV1,
};
pub use exact_fnsp_v3_state::{
    EXACT_FNSP_V3_APPEND_RECORD_V1_WIRE_LEN, EXACT_FNSP_V3_STATE_HEAD_V1_WIRE_LEN,
    ExactFnspV3StateCasV1, ExactFnspV3StateHeadV1, ExactFnspV3StateStoreError,
};
pub use faithful_note_root_history::{
    CanonicalFaithfulRoot, FaithfulNoteRootAnchorV1, FaithfulNoteRootEnvelopeV1,
    FaithfulNoteRootExpectationV1, FaithfulNoteRootHistoryError, FaithfulNoteRootHistoryV1,
    FaithfulNoteRootRecordV1, plan_faithful_note_root_transition_v1,
};
pub use federation::{QuorumSignature, StoredAttestedRoot};
pub use finalized_faithful_spend::{FinalizedFaithfulSpend, FinalizedFaithfulSpendInput};
pub use image_builder::{
    BuildError, CellSpec, ImageArtifact, ImageAttestation, ImageFacts, ImageManifest, VerifyError,
    build_image, verify_image,
};
pub use ledger_store::LedgerCheckpoint;
pub use note_tree::{NoteTree, PersistentNullifierSet};
pub use poseidon2_note_tree::Poseidon2NoteTree;
pub use snapshot::{Snapshot, SnapshotHead};

/// THE canonical ledger root — the byte-pinned full-ledger commitment both the
/// node (attested-root convergence across the quorum) and the single-image World
/// (durable-reopen convergence) check against. This is the ONE shared
/// implementation, lifted here so callers stop duplicating it (it was the node's
/// `pub(crate)` copy in `blocklace_sync.rs` + a byte-for-byte replica in
/// `starbridge-v2/src/persistence.rs`; the M4 "shared pub fn lift" tail).
///
/// `BLAKE3-derive-key("dregg-ledger-root-v2")` over the cells sorted by id,
/// length-prefixed, each leaf `BLAKE3(postcard(WHOLE cell))` — committing the whole
/// cell (public_key / token_id / capabilities / lifecycle / state), so two ledgers
/// that finalized the same turns but ended with divergent cell CONTENT (not just
/// balance/nonce) produce DIFFERENT roots — the divergence is loud, not silent.
///
/// Byte-stability is load-bearing (a persisted/attested root must reproduce
/// exactly), so the construction (domain key, sort order, length prefix, whole-cell
/// postcard leaves) is fixed; do not alter it without a domain bump.
pub fn canonical_ledger_root(ledger: &dregg_cell::Ledger) -> [u8; 32] {
    canonical_ledger_root_from_leaves(&canonical_ledger_leaves(ledger))
}

/// The sorted leaf set underlying [`canonical_ledger_root`]: `(cell_id,
/// BLAKE3(postcard(cell)))` for every cell, sorted by id. Exposed so an
/// inclusion-proof endpoint can hand a verifier the FULL leaf set to recompute the
/// root from (the flat root has no O(log n) opening). The construction MUST stay
/// byte-identical to `canonical_ledger_root` — both fold through
/// [`canonical_ledger_root_from_leaves`].
pub fn canonical_ledger_leaves(ledger: &dregg_cell::Ledger) -> Vec<([u8; 32], [u8; 32])> {
    let mut entries: Vec<([u8; 32], [u8; 32])> = ledger
        .iter()
        .map(|(id, cell)| {
            let bytes = postcard::to_stdvec(cell).unwrap_or_default();
            (*id.as_bytes(), *blake3::hash(&bytes).as_bytes())
        })
        .collect();
    entries.sort_by_key(|a| a.0);
    entries
}

/// Fold the domain-separated flat root over an ALREADY-SORTED leaf set. Callers that
/// already hold the leaves (an inclusion-proof verifier) reuse this instead of
/// re-hashing cells; the fold order (len prefix, then id then leaf-hash per entry)
/// is fixed and load-bearing.
pub fn canonical_ledger_root_from_leaves(entries: &[([u8; 32], [u8; 32])]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ledger-root-v2");
    hasher.update(&(entries.len() as u64).to_le_bytes());
    for (id, h) in entries {
        hasher.update(id);
        hasher.update(h);
    }
    *hasher.finalize().as_bytes()
}

/// Errors that can occur during store operations.
#[derive(Debug)]
pub enum StoreError {
    /// The underlying database returned an error.
    Database(String),
    /// Serialization/deserialization failure.
    Serialization(String),
    /// Encryption or decryption failure.
    Crypto(String),
    /// The requested item was not found.
    NotFound,
    /// Data integrity check failed.
    Integrity(String),
}

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Database(msg) => write!(f, "database error: {msg}"),
            Self::Serialization(msg) => write!(f, "serialization error: {msg}"),
            Self::Crypto(msg) => write!(f, "crypto error: {msg}"),
            Self::NotFound => write!(f, "not found"),
            Self::Integrity(msg) => write!(f, "integrity error: {msg}"),
        }
    }
}

impl std::error::Error for StoreError {}

impl From<redb::DatabaseError> for StoreError {
    fn from(e: redb::DatabaseError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::TableError> for StoreError {
    fn from(e: redb::TableError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::TransactionError> for StoreError {
    fn from(e: redb::TransactionError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::CommitError> for StoreError {
    fn from(e: redb::CommitError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<redb::StorageError> for StoreError {
    fn from(e: redb::StorageError) -> Self {
        Self::Database(e.to_string())
    }
}

impl From<postcard::Error> for StoreError {
    fn from(e: postcard::Error) -> Self {
        Self::Serialization(e.to_string())
    }
}

/// Result type alias for store operations.
pub type Result<T> = std::result::Result<T, StoreError>;

/// The persistent store for all dregg state.
///
/// Backed by `redb`, an embedded ACID key-value store. All operations are
/// crash-safe through redb's write-ahead logging.
pub struct PersistentStore {
    db: Database,
}

impl PersistentStore {
    /// Open a persistent store backed by a file on disk.
    ///
    /// Creates the file and all necessary tables if they don't exist.
    pub fn open(path: &Path) -> Result<Self> {
        let db = Database::create(path).map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self { db };
        store.initialize_tables()?;
        // One-time index-shape migration for stores written before the
        // (height, creator, ordinal) key (no-op on fresh/migrated stores).
        store.migrate_height_creator_index()?;
        store.validate_exact_fnsp_v3_receipt_authority_on_open()?;
        Ok(store)
    }

    /// Open an in-memory store (useful for testing).
    ///
    /// Data is lost when the store is dropped.
    pub fn open_in_memory() -> Result<Self> {
        let backend = redb::backends::InMemoryBackend::new();
        let db = Database::builder()
            .create_with_backend(backend)
            .map_err(|e| StoreError::Database(e.to_string()))?;
        let store = Self { db };
        store.initialize_tables()?;
        store.validate_exact_fnsp_v3_receipt_authority_on_open()?;
        Ok(store)
    }

    /// Initialize all tables in the database.
    fn initialize_tables(&self) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            // Federation tables.
            let _ = write_txn.open_table(tables::REVOCATIONS)?;
            let _ = write_txn.open_table(tables::ATTESTED_ROOTS)?;
            // Note tree tables.
            let _ = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            let _ = write_txn.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
            let _ = write_txn.open_table(tables::NULLIFIERS)?;
            let _ = write_txn.open_table(tables::NULLIFIER_RECORDS_V1)?;
            let _ = write_txn.open_table(tables::FINALIZED_FAITHFUL_SPENDS)?;
            let _ = write_txn.open_table(tables::FINALIZED_FAITHFUL_SPEND_TURNS)?;
            // Empty until the exact-v3 flag-day seeding transaction installs a head reconstructed
            // from the complete durable append-record image.
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_STATE_HEAD)?;
            let _ = write_txn.open_table(exact_fnsp_v3_state::EXACT_FNSP_V3_APPEND_RECORDS)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_ACTIVATION)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_FRAME_HEAD)?;
            let _ = write_txn.open_table(exact_fnsp_v3_frame_head::EXACT_FNSP_V3_FRAME_RECORDS)?;
            // Checkpoint tables.
            let _ = write_txn.open_table(tables::CHECKPOINTS)?;
            // Ledger checkpoint table.
            let _ = write_txn.open_table(tables::LEDGER_CHECKPOINTS)?;
            // Blocklace tables.
            let _ = write_txn.open_table(tables::BLOCKLACE_BLOCKS)?;
            let _ = write_txn.open_table(tables::BLOCKLACE_META)?;
            // Node witness artifact tables.
            let _ = write_txn.open_table(tables::WITNESSED_RECEIPTS)?;
            // Durable receipt chain (the served /api/receipts* log + MMR source).
            let _ = write_txn.open_table(tables::RECEIPT_CHAIN)?;
            // Durable commit log + index tables (crash-consistency).
            let _ = write_txn.open_table(tables::COMMIT_LOG)?;
            let _ = write_txn.open_table(tables::IDX_RECEIPT_BY_HASH)?;
            let _ = write_txn.open_table(tables::IDX_TURN_BY_HASH)?;
            let _ = write_txn.open_table(tables::IDX_TURN_BY_HEIGHT_CREATOR)?;
            let _ = write_txn.open_table(tables::IDX_CELL_BY_ID)?;
            // Compacted turn block-ids (the no-double-apply carrier for
            // commit-log compaction: ids of applied turns whose records were
            // compacted under a covering checkpoint — `compact_below`).
            let _ = write_txn.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
            // Forever-digest sets (restart-durable anti-replay carriers).
            let _ = write_txn.open_table(tables::FOREVER_DIGESTS)?;
            // Durable channel rosters (member→seal-pk content; the cell holds
            // only the commitment — .docs-history-noclaude/PERSISTENCE.md §3 roster caveat).
            let _ = write_txn.open_table(tables::CHANNEL_ROSTERS)?;
            // Metadata tables.
            let _ = write_txn.open_table(tables::METADATA)?;
            let _ = write_txn.open_table(tables::METADATA_BYTES)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Compact the database file, reclaiming unused space.
    pub fn compact(&mut self) -> Result<bool> {
        self.db
            .compact()
            .map_err(|e| StoreError::Database(e.to_string()))
    }

    /// Persist a caller-serialized witnessed receipt artifact vector.
    ///
    /// The node owns the typed `WitnessedReceipt` encoding; this crate stores the
    /// bytes under receipt hash so it can stay independent of `dregg-turn`.
    pub fn store_witnessed_receipts_raw(
        &self,
        receipt_hash: &[u8; 32],
        encoded: &[u8],
    ) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::WITNESSED_RECEIPTS)?;
            table.insert(receipt_hash, encoded)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Remove a persisted witnessed receipt artifact vector.
    pub fn remove_witnessed_receipts_raw(&self, receipt_hash: &[u8; 32]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::WITNESSED_RECEIPTS)?;
            table.remove(receipt_hash)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load every persisted witness artifact vector in key order.
    pub fn load_witnessed_receipts_raw(&self) -> Result<Vec<([u8; 32], Vec<u8>)>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::WITNESSED_RECEIPTS)?;
        let mut out = Vec::new();
        for entry in table.iter()? {
            let (key, value) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push((*key.value(), value.value().to_vec()));
        }
        Ok(out)
    }

    // =========================================================================
    // Durable receipt chain (the served /api/receipts* log + MMR source)
    // =========================================================================

    /// Durably append the caller-serialized `TurnReceipt` at its dense chain
    /// index. An existing byte-identical entry is an idempotent success; an
    /// overwrite, gap, or pre-existing gap is an integrity error.
    pub fn append_receipt_chain_entry(&self, index: u64, encoded: &[u8]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        Self::write_receipt_chain_entry_in(&write_txn, index, encoded, true)?;
        write_txn.commit()?;
        Ok(())
    }

    /// Validate and optionally append one receipt-log entry inside a caller-owned
    /// write transaction. `allow_insert = false` is the idempotent-replay check:
    /// the exact bytes must already exist at `index`.
    pub(crate) fn write_receipt_chain_entry_in(
        write_txn: &redb::WriteTransaction,
        index: u64,
        encoded: &[u8],
        allow_insert: bool,
    ) -> Result<()> {
        let mut table = write_txn.open_table(tables::RECEIPT_CHAIN)?;
        // For a u64-keyed table, `len = n` and `max_key = n - 1` implies the
        // key set is exactly 0..n: there are n distinct non-negative integers
        // and only n available positions below that maximum. This is the same
        // density proof as a full scan, without turning every append into O(n).
        let expected = {
            let count = table.len()?;
            match (count, table.last()?) {
                (0, None) => 0,
                (0, Some((key, _))) => {
                    return Err(StoreError::Integrity(format!(
                        "receipt log has key {} but reports zero entries",
                        key.value()
                    )));
                }
                (count, Some((key, _))) if key.value() == count - 1 => count,
                (count, Some((key, _))) => {
                    return Err(StoreError::Integrity(format!(
                        "receipt log is not dense: {count} entries but highest index is {}",
                        key.value()
                    )));
                }
                (count, None) => {
                    return Err(StoreError::Integrity(format!(
                        "receipt log reports {count} entries but has no last key"
                    )));
                }
            }
        };

        if index < expected {
            let existing = table.get(index)?.ok_or_else(|| {
                StoreError::Integrity(format!(
                    "receipt log index {index} is below length {expected} but missing"
                ))
            })?;
            if existing.value() != encoded {
                return Err(StoreError::Integrity(format!(
                    "receipt log index {index} already contains different bytes"
                )));
            }
            return Ok(());
        }
        if index != expected {
            return Err(StoreError::Integrity(format!(
                "receipt log append would create a gap: next index {expected}, supplied {index}"
            )));
        }
        if !allow_insert {
            return Err(StoreError::Integrity(format!(
                "finalized-turn replay is missing durable receipt log index {index}"
            )));
        }
        table.insert(index, encoded)?;
        Ok(())
    }

    /// Load the complete durable receipt chain. Any non-dense key is an integrity
    /// error: boot must not turn a corrupt tail into an accepted rollback to an
    /// earlier receipt head.
    pub fn load_receipt_chain(&self) -> Result<Vec<Vec<u8>>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::RECEIPT_CHAIN)?;
        let mut out = Vec::new();
        let mut expected: u64 = 0;
        for entry in table.iter()? {
            let (key, value) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            if key.value() != expected {
                return Err(StoreError::Integrity(format!(
                    "receipt log gap: expected index {expected}, found {}",
                    key.value()
                )));
            }
            out.push(value.value().to_vec());
            expected += 1;
        }
        Ok(out)
    }

    /// Length of the durable receipt chain. A gap is an integrity error, not a
    /// shorter accepted history.
    pub fn receipt_chain_len(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::RECEIPT_CHAIN)?;
        let count = table.len()?;
        match (count, table.last()?) {
            (0, None) => Ok(0),
            (0, Some((key, _))) => Err(StoreError::Integrity(format!(
                "receipt log has key {} but reports zero entries",
                key.value()
            ))),
            (count, Some((key, _))) if key.value() == count - 1 => Ok(count),
            (count, Some((key, _))) => Err(StoreError::Integrity(format!(
                "receipt log is not dense: {count} entries but highest index is {}",
                key.value()
            ))),
            (count, None) => Err(StoreError::Integrity(format!(
                "receipt log reports {count} entries but has no last key"
            ))),
        }
    }

    // =========================================================================
    // Note Tree Storage
    // =========================================================================

    /// Store a note commitment at the next position. Returns the position assigned.
    ///
    /// Invalidates the cached note tree root so the next call to `note_tree_root()`
    /// will recompute from the updated tree.
    pub fn store_note_commitment(
        &self,
        commitment: &dregg_cell::note::NoteCommitment,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let position;
        {
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_size = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0);
            position = current_size;

            let mut table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            table.insert(position, &commitment.0)?;

            meta.insert(tables::META_NOTE_TREE_SIZE, position + 1)?;

            // Invalidate the cached root within the same transaction.
            let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
            meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
        }
        write_txn.commit()?;
        Ok(position)
    }

    /// Store a nullifier (mark a note as spent).
    ///
    /// Returns Ok(()) if the nullifier was newly added, or an integrity error
    /// if it was already present (double-spend).
    pub fn store_nullifier(&self, nullifier: &dregg_cell::note::Nullifier) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::NULLIFIERS)?;
            if table.get(&nullifier.0)?.is_some() {
                return Err(StoreError::Integrity(
                    "nullifier already spent (double-spend)".to_string(),
                ));
            }
            table.insert(&nullifier.0, ())?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Check whether a nullifier has been spent (is in the set).
    pub fn is_nullifier_spent(&self, nullifier: &dregg_cell::note::Nullifier) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NULLIFIERS)?;
        Ok(table.get(&nullifier.0)?.is_some())
    }

    /// Get the current note tree root.
    ///
    /// Returns the cached root if available (O(1) read from metadata). Falls back
    /// to full tree reconstruction only if the cache is missing (e.g., first call
    /// on a database created before the cache was introduced, or after corruption
    /// recovery).
    ///
    /// On cache miss, a write transaction is used to atomically read the current
    /// commitments and write the computed root, preventing TOCTOU races where
    /// another writer could append a commitment between the read and the cache write.
    pub fn note_tree_root(&self) -> Result<[u8; 32]> {
        // Try to read the cached root first (fast path).
        let read_txn = self.db.begin_read()?;
        let meta_bytes = read_txn.open_table(tables::METADATA_BYTES)?;
        if let Some(guard) = meta_bytes.get(tables::META_NOTE_TREE_ROOT_CACHE)? {
            let cached = guard.value();
            if cached.len() == 32 {
                let mut root = [0u8; 32];
                root.copy_from_slice(cached);
                return Ok(root);
            }
        }
        drop(meta_bytes);
        drop(read_txn);

        // Cache miss: use a write transaction to atomically read commitments and
        // persist the computed root. This prevents a TOCTOU race where another
        // writer could append between our read and the cache write.
        let write_txn = self.db.begin_write()?;

        // Re-check the cache under the write lock (another thread may have
        // populated it while we were waiting for the write transaction).
        let cached_root = {
            let meta_bytes_table = write_txn.open_table(tables::METADATA_BYTES)?;
            let maybe_cached = meta_bytes_table.get(tables::META_NOTE_TREE_ROOT_CACHE)?;
            match maybe_cached {
                Some(guard) => {
                    let cached = guard.value();
                    if cached.len() == 32 {
                        let mut r = [0u8; 32];
                        r.copy_from_slice(cached);
                        Some(r)
                    } else {
                        None
                    }
                }
                None => None,
            }
        };

        if let Some(r) = cached_root {
            // No changes to commit; just abort the write transaction and return.
            return Ok(r);
        }

        // Read all commitments within this write transaction's snapshot.
        let count = {
            let meta = write_txn.open_table(tables::METADATA)?;
            meta.get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0)
        };

        let mut commitments = Vec::with_capacity(count as usize);
        {
            let commitment_table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            for pos in 0..count {
                match commitment_table.get(pos)? {
                    Some(guard) => {
                        commitments.push(dregg_cell::note::NoteCommitment(*guard.value()));
                    }
                    None => {
                        return Err(StoreError::Integrity(format!(
                            "missing note commitment at position {pos}"
                        )));
                    }
                }
            }
        }

        let mut tree = note_tree::NoteTree::from_commitments(commitments);
        let root = tree.root();

        // Persist the computed root.
        {
            let mut meta_bytes_w = write_txn.open_table(tables::METADATA_BYTES)?;
            meta_bytes_w.insert(tables::META_NOTE_TREE_ROOT_CACHE, root.as_slice())?;
        }
        write_txn.commit()?;

        Ok(root)
    }

    /// Get the number of note commitments stored.
    pub fn note_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_NOTE_TREE_SIZE)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Load all note commitments in order (for tree reconstruction).
    pub fn load_all_note_commitments(&self) -> Result<Vec<dregg_cell::note::NoteCommitment>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NOTE_COMMITMENTS)?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let count = meta
            .get(tables::META_NOTE_TREE_SIZE)?
            .map(|g| g.value())
            .unwrap_or(0);

        let mut commitments = Vec::with_capacity(count as usize);
        for pos in 0..count {
            match table.get(pos)? {
                Some(guard) => {
                    commitments.push(dregg_cell::note::NoteCommitment(*guard.value()));
                }
                None => {
                    return Err(StoreError::Integrity(format!(
                        "missing note commitment at position {pos}"
                    )));
                }
            }
        }
        Ok(commitments)
    }

    /// Load all nullifiers from persistent storage.
    pub fn load_all_nullifiers(&self) -> Result<Vec<dregg_cell::note::Nullifier>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::NULLIFIERS)?;

        let mut nullifiers = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            nullifiers.push(dregg_cell::note::Nullifier(*entry.0.value()));
        }
        Ok(nullifiers)
    }

    /// Load the complete circuit-facing nullifier accumulator record.
    ///
    /// Unlike [`Self::load_all_nullifiers`], this retains the public spent-note
    /// value and canonical append sequence needed to reconstruct the same
    /// eight-felt accumulator after restart. A nonempty legacy presence table
    /// without these additive rows is refused rather than guessed.
    pub fn load_faithful_nullifier_records(
        &self,
    ) -> Result<Vec<(dregg_cell::note::Nullifier, u64, u64)>> {
        let read_txn = self.db.begin_read()?;
        let presence = read_txn.open_table(tables::NULLIFIERS)?;
        let records = read_txn.open_table(tables::NULLIFIER_RECORDS_V1)?;
        let presence_len = presence.len()?;
        let records_len = records.len()?;
        if presence_len != records_len {
            return Err(StoreError::Integrity(format!(
                "nullifier presence/record table lengths disagree ({presence_len} != {records_len}); \
                 legacy nonempty images require an explicit value/sequence migration"
            )));
        }

        let capacity = usize::try_from(records_len).map_err(|_| {
            StoreError::Integrity("nullifier record count does not fit usize".to_string())
        })?;
        let mut out = Vec::with_capacity(capacity);
        let mut seen_seq = vec![false; capacity];
        for entry in records.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let nullifier = *entry.0.value();
            if presence.get(&nullifier)?.is_none() {
                return Err(StoreError::Integrity(
                    "nullifier record has no matching spent-presence row".to_string(),
                ));
            }
            let bytes = entry.1.value();
            let mut value = [0u8; 8];
            value.copy_from_slice(&bytes[..8]);
            let mut seq = [0u8; 8];
            seq.copy_from_slice(&bytes[8..]);
            let value = u64::from_le_bytes(value);
            let seq = u64::from_le_bytes(seq);
            let seq_index = usize::try_from(seq).map_err(|_| {
                StoreError::Integrity("nullifier append sequence does not fit usize".to_string())
            })?;
            if seq_index >= capacity || seen_seq[seq_index] {
                return Err(StoreError::Integrity(
                    "nullifier append sequence is duplicated or outside the dense durable range"
                        .to_string(),
                ));
            }
            seen_seq[seq_index] = true;
            out.push((dregg_cell::note::Nullifier(nullifier), value, seq));
        }
        if seen_seq.iter().any(|seen| !seen) {
            return Err(StoreError::Integrity(
                "nullifier append sequence has a durable gap".to_string(),
            ));
        }
        out.sort_by_key(|(nullifier, _, seq)| (*seq, *nullifier));
        Ok(out)
    }

    /// Return the exact durable faithful-nullifier row count without decoding
    /// the full accumulator.  The legacy presence table must have the same
    /// cardinality; disagreement is an integrity failure, never a cache key.
    pub fn faithful_nullifier_record_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let presence = read_txn.open_table(tables::NULLIFIERS)?;
        let records = read_txn.open_table(tables::NULLIFIER_RECORDS_V1)?;
        let presence_len = presence.len()?;
        let records_len = records.len()?;
        if presence_len != records_len {
            return Err(StoreError::Integrity(format!(
                "nullifier presence/record table lengths disagree ({presence_len} != {records_len}); \
                 legacy nonempty images require an explicit value/sequence migration"
            )));
        }
        Ok(records_len)
    }

    /// Exact durable eight-felt nullifier-accumulator root used by live root
    /// attestation. This is separate from [`Self::nullifier_set_root`], the
    /// legacy BLAKE3 key-only non-membership tree.
    pub fn faithful_nullifier_root(&self) -> Result<[u8; 32]> {
        let records = self.load_faithful_nullifier_records()?;
        let set = dregg_cell::nullifier_set::NullifierSet::from_records(records).map_err(|e| {
            StoreError::Integrity(format!(
                "durable nullifier accumulator cannot be reconstructed: {e}"
            ))
        })?;
        Ok(set.faithful_root8_exact().to_bytes32())
    }

    /// Compute, without mutating the store, the nullifier root that must be
    /// attested if `spends` are atomically appended to the current durable set.
    pub fn plan_faithful_nullifier_successor(
        &self,
        spends: &[commit_log::FinalizedNullifierRecord],
    ) -> Result<[u8; 32]> {
        let records = self.load_faithful_nullifier_records()?;
        let mut set =
            dregg_cell::nullifier_set::NullifierSet::from_records(records).map_err(|e| {
                StoreError::Integrity(format!(
                    "durable nullifier accumulator cannot be reconstructed: {e}"
                ))
            })?;
        for spend in spends {
            set.insert(dregg_cell::note::Nullifier(spend.nullifier), spend.value)
                .map_err(|_| {
                    StoreError::Integrity(
                        "nullifier already spent or duplicated within finalized turn".to_string(),
                    )
                })?;
        }
        Ok(set.faithful_root8_exact().to_bytes32())
    }

    /// Compute the nullifier set root from all stored nullifiers.
    pub fn nullifier_set_root(&self) -> Result<[u8; 32]> {
        let nullifiers = self.load_all_nullifiers()?;
        let set = note_tree::PersistentNullifierSet::from_nullifiers(nullifiers);
        Ok(set.root())
    }

    // =========================================================================
    // Generic Config Storage (METADATA_BYTES)
    // =========================================================================

    /// Store a byte blob under a config key.
    pub fn set_config(&self, key: &str, value: &[u8]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            table.insert(key, value)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load a byte blob stored under a config key.
    pub fn get_config(&self, key: &str) -> Result<Option<Vec<u8>>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;
        match table.get(key)? {
            Some(guard) => Ok(Some(guard.value().to_vec())),
            None => Ok(None),
        }
    }

    // =========================================================================
    // Proof Hash Nullifier Storage (for conditional turn replay prevention)
    // =========================================================================

    /// Store a proof hash (used in conditional turn resolution) to prevent replay.
    ///
    /// Returns Ok(true) if newly inserted, Ok(false) if already present.
    ///
    /// The check-and-insert is performed atomically within a single write
    /// transaction to prevent TOCTOU races where two concurrent calls could
    /// both pass the existence check.
    pub fn insert_proof_hash(&self, hash: &[u8; 32]) -> Result<bool> {
        // We reuse METADATA_BYTES with a "proof_hash:" prefix key.
        let key = format!("proof_hash:{}", hex_encode_bytes(hash));
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            if table.get(key.as_str())?.is_some() {
                return Ok(false);
            }
            table.insert(key.as_str(), &[1u8] as &[u8])?;
        }
        write_txn.commit()?;
        Ok(true)
    }

    /// Store a proof hash with an associated block height for TTL-based eviction.
    ///
    /// Returns Ok(true) if newly inserted, Ok(false) if already present.
    pub fn insert_proof_hash_with_height(&self, hash: &[u8; 32], height: u64) -> Result<bool> {
        let key = format!("proof_hash:{}", hex_encode_bytes(hash));
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            if table.get(key.as_str())?.is_some() {
                return Ok(false);
            }
            // Store the height as 8-byte LE value for later pruning.
            table.insert(key.as_str(), &height.to_le_bytes() as &[u8])?;
        }
        write_txn.commit()?;
        Ok(true)
    }

    /// Prune proof hashes older than `max_age` blocks from the current height.
    ///
    /// Entries stored without a height (legacy 1-byte value) are left intact.
    /// Returns the number of entries pruned.
    pub fn prune_old_proof_hashes(&self, current_height: u64, max_age: u64) -> Result<u64> {
        let min_height = current_height.saturating_sub(max_age);
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;

        let prefix = "proof_hash:";
        let mut keys_to_remove = Vec::new();

        let range = table.range(prefix..)?;
        for entry in range {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            if !key.starts_with(prefix) {
                break;
            }
            let value = entry.1.value();
            // Only prune entries that have height data (8 bytes).
            if value.len() == 8 {
                let stored_height = u64::from_le_bytes(value.try_into().unwrap());
                if stored_height < min_height {
                    keys_to_remove.push(key.to_string());
                }
            }
        }
        drop(table);
        drop(read_txn);

        if keys_to_remove.is_empty() {
            return Ok(0);
        }

        let count = keys_to_remove.len() as u64;
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::METADATA_BYTES)?;
            for key in &keys_to_remove {
                table.remove(key.as_str())?;
            }
        }
        write_txn.commit()?;
        Ok(count)
    }

    /// Load all stored proof hashes (for populating the in-memory set on startup).
    pub fn load_all_proof_hashes(&self) -> Result<std::collections::HashSet<[u8; 32]>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::METADATA_BYTES)?;
        let mut hashes = std::collections::HashSet::new();

        let prefix = "proof_hash:";
        let range = table.range(prefix..)?;
        for entry in range {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = entry.0.value();
            if !key.starts_with(prefix) {
                break;
            }
            // Parse the hex suffix back to [u8; 32].
            let hex_part = &key[prefix.len()..];
            if hex_part.len() == 64
                && let Ok(bytes) = hex_decode_bytes(hex_part)
            {
                hashes.insert(bytes);
            }
        }
        Ok(hashes)
    }

    /// Atomically spend a note: insert the nullifier and store the new commitment
    /// in a single transaction.
    ///
    /// This prevents the case where a nullifier is recorded but the new commitment
    /// is lost (or vice versa) due to a crash between two separate transactions.
    ///
    /// Returns the position of the new commitment in the note tree.
    /// Returns an integrity error if the nullifier was already spent (double-spend).
    pub fn spend_note_atomic(
        &self,
        nullifier: &dregg_cell::note::Nullifier,
        new_commitment: &dregg_cell::note::NoteCommitment,
    ) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let position;
        {
            // Check and insert nullifier.
            let mut nullifier_table = write_txn.open_table(tables::NULLIFIERS)?;
            if nullifier_table.get(&nullifier.0)?.is_some() {
                return Err(StoreError::Integrity(
                    "nullifier already spent (double-spend)".to_string(),
                ));
            }
            nullifier_table.insert(&nullifier.0, ())?;

            // Insert new commitment at the next position.
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_size = meta
                .get(tables::META_NOTE_TREE_SIZE)?
                .map(|g| g.value())
                .unwrap_or(0);
            position = current_size;

            let mut commitment_table = write_txn.open_table(tables::NOTE_COMMITMENTS)?;
            commitment_table.insert(position, &new_commitment.0)?;

            meta.insert(tables::META_NOTE_TREE_SIZE, position + 1)?;

            // Invalidate the cached note tree root.
            let mut meta_bytes = write_txn.open_table(tables::METADATA_BYTES)?;
            meta_bytes.remove(tables::META_NOTE_TREE_ROOT_CACHE)?;
        }
        write_txn.commit()?;
        Ok(position)
    }
}

// =============================================================================
// Internal hex helpers
// =============================================================================

fn hex_encode_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_bytes(s: &str) -> std::result::Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = hex_nibble(chunk[0]).ok_or(())?;
        let low = hex_nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}
