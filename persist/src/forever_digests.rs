//! Durable forever-digest sets: restart-surviving anti-replay carriers.
//!
//! A "forever digest" is one the protocol burns exactly once and must refuse
//! for the rest of time: a trustline draw digest (Lean
//! `no_double_draw_forever` / `draw_replay_refused_across_epochs`), a
//! settle-unapplied compensation digest, a court resolved-evidence digest
//! (no-double-resolve ⇒ no-double-slash). The node keeps these sets in memory
//! for the hot refusal path; THIS module is the durable backing that makes
//! "forever" hold across a process restart — the digest is written here
//! (one committed redb transaction, WAL-backed) before the in-memory insert
//! is acknowledged, and the whole set is reloaded at boot.
//!
//! The write is per-digest and append-only (digests are never removed:
//! deletion would be a guarded write under the persistence axis —
//! `docs/PERSISTENCE.md`; these collections sit at the `attested`-shaped
//! point: kept forever, refusal-load-bearing).

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Build the 65-byte composite key: namespace ++ scope ++ digest.
/// `pub(crate)` so the commit log can burn digests in the SAME transaction
/// as a turn's commit record (`commit_finalized_turn_with_burns`).
pub(crate) fn forever_key(namespace: u8, scope: &[u8; 32], digest: &[u8; 32]) -> [u8; 65] {
    let mut key = [0u8; 65];
    key[0] = namespace;
    key[1..33].copy_from_slice(scope);
    key[33..65].copy_from_slice(digest);
    key
}

impl PersistentStore {
    /// Durably burn a forever digest. Idempotent: returns `Ok(true)` if the
    /// digest was newly recorded, `Ok(false)` if it was already burned.
    ///
    /// The redb transaction commits (with an fsync at the commit boundary)
    /// before this returns, so a digest acknowledged here survives an
    /// arbitrary crash.
    pub fn record_forever_digest(
        &self,
        namespace: u8,
        scope: &[u8; 32],
        digest: &[u8; 32],
    ) -> Result<bool> {
        let key = forever_key(namespace, scope, digest);
        let write_txn = self.db.begin_write()?;
        let inserted;
        {
            let mut table = write_txn.open_table(tables::FOREVER_DIGESTS)?;
            inserted = table.insert(&key, ())?.is_none();
        }
        write_txn.commit()?;
        Ok(inserted)
    }

    /// Whether a forever digest has been durably burned.
    pub fn forever_digest_seen(
        &self,
        namespace: u8,
        scope: &[u8; 32],
        digest: &[u8; 32],
    ) -> Result<bool> {
        let key = forever_key(namespace, scope, digest);
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::FOREVER_DIGESTS)?;
        Ok(table.get(&key)?.is_some())
    }

    /// Load every `(scope, digest)` pair burned under `namespace`, for
    /// rebuilding the in-memory registry at boot.
    pub fn load_forever_digests(&self, namespace: u8) -> Result<Vec<([u8; 32], [u8; 32])>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::FOREVER_DIGESTS)?;
        let lo = forever_key(namespace, &[0u8; 32], &[0u8; 32]);
        let mut out = Vec::new();
        for entry in table.range::<&[u8; 65]>(&lo..)? {
            let (key_guard, _) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let key = key_guard.value();
            if key[0] != namespace {
                break;
            }
            let mut scope = [0u8; 32];
            scope.copy_from_slice(&key[1..33]);
            let mut digest = [0u8; 32];
            digest.copy_from_slice(&key[33..65]);
            out.push((scope, digest));
        }
        Ok(out)
    }
}
