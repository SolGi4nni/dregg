//! Durable channel rosters (docs/PERSISTENCE.md §3, the roster caveat).
//!
//! A channel-group cell pins only the roster's COMMITMENT
//! (`CH_MEMBER_ROOT_SLOT`); the member→seal-pk content is node-held —
//! verifiable against the cell but not derivable from it. Without a durable
//! carrier, a node that restarts mid-life serves `RosterStale` (fail-closed
//! but unavailable) until every member re-posts. This module is the carrier:
//! the node writes the postcard-encoded roster after every committed epoch
//! step and reloads it at boot, RE-COMMITTING each roster against the on-cell
//! root before trusting it (a stale durable roster is discarded loudly, so
//! `RosterStale` afterwards means genuine divergence, never a mere restart).
//!
//! This crate stores opaque bytes (the node owns the `Roster` type via
//! `dregg_sdk::channels`), keeping `dregg-persist` independent of the SDK.

use crate::tables;
use crate::{PersistentStore, Result, StoreError};
use redb::ReadableTable;

impl PersistentStore {
    /// Durably store (upsert) the roster bytes for one channel-group cell.
    /// One committed redb transaction: the roster survives an arbitrary
    /// crash from here on.
    pub fn store_channel_roster(&self, channel: &[u8; 32], roster_bytes: &[u8]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::CHANNEL_ROSTERS)?;
            table.insert(channel, roster_bytes)?;
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load every stored `(channel cell id, roster bytes)` pair, for room
    /// reconstruction at boot.
    pub fn load_channel_rosters(&self) -> Result<Vec<([u8; 32], Vec<u8>)>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::CHANNEL_ROSTERS)?;
        let mut out = Vec::new();
        for entry in table.iter()? {
            let (key, value) =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            out.push((*key.value(), value.value().to_vec()));
        }
        Ok(out)
    }

    /// Remove a stored roster (used when a load-time re-commitment check
    /// finds the durable roster stale — the discard is itself durable so the
    /// stale row does not re-alarm on every boot).
    pub fn remove_channel_roster(&self, channel: &[u8; 32]) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::CHANNEL_ROSTERS)?;
            table.remove(channel)?;
        }
        write_txn.commit()?;
        Ok(())
    }
}
