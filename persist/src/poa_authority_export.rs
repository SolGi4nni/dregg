//! Privacy-preserving durable commit snapshot for a PoA node-envelope diagnostic.
//!
//! The exact stored bytes are retained for a byte digest, while callers expose
//! only the public commit coordinates. `CommitRecord::touched_cells` and the
//! tombstone set remain inside the node.

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

const MAX_EXACT_COMMIT_RECORD_BYTES_V1: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug)]
pub struct PoaAuthorityCommitSnapshotV1 {
    record: CommitRecord,
    exact_bytes: Vec<u8>,
}

impl PoaAuthorityCommitSnapshotV1 {
    pub fn record(&self) -> &CommitRecord {
        &self.record
    }

    /// Exact redb value bytes, including the historical v0/v1 wire choice.
    pub fn exact_bytes(&self) -> &[u8] {
        &self.exact_bytes
    }
}

impl PersistentStore {
    pub fn poa_authority_commit_snapshot(
        &self,
        ordinal: u64,
    ) -> Result<Option<PoaAuthorityCommitSnapshotV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::COMMIT_LOG)?;
        let Some(value) = table.get(ordinal)? else {
            return Ok(None);
        };
        let bytes = value.value();
        if bytes.len() > MAX_EXACT_COMMIT_RECORD_BYTES_V1 {
            return Err(StoreError::Integrity(
                "PoA authority commit record exceeds the exact-export bound".into(),
            ));
        }
        let record = crate::commit_log::decode_commit_record(bytes)?;
        if record.ordinal != ordinal {
            return Err(StoreError::Integrity(
                "PoA authority commit key/ordinal mismatch".into(),
            ));
        }
        Ok(Some(PoaAuthorityCommitSnapshotV1 {
            record,
            exact_bytes: bytes.to_vec(),
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absent_commit_has_no_synthetic_authority_snapshot() {
        let store = PersistentStore::open_in_memory().unwrap();
        assert!(store.poa_authority_commit_snapshot(0).unwrap().is_none());
    }
}
