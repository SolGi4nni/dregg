//! Production worker loop for finalized private-Bazaar receipts.
//!
//! Public web/chat controllers never enter this module. A deployment-owned
//! worker polls a bounded out-of-band source, rejoins each finalized private
//! receipt to the exact hosted market and policy-pinned Dungeon target, and
//! publishes only the existing viewer-blind journey status. The worker journal
//! durably binds source cursor -> semantic source -> exact game operation before
//! the authority store can enter `Dispatching`.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use dregg_turn::{Finality, TurnReceipt};
use dregg_types::CellId;
use dreggnet_market::private_bazaar_authority::PrivateBazaarAuthorityPhase;
use dreggnet_market::private_bazaar_game_adapter::{
    PreparedPrivateBazaarXp, PrivateBazaarGameAdapterError,
};
use dreggnet_market::private_bazaar_live_host::PrivateBazaarLiveHostError;
use dreggnet_market::private_clearing::PrivateClearingReceipt;
use dreggnet_offerings::DreggIdentity;
use dungeon_on_dregg::progression::DungeonWorldCell;

use crate::private_bazaar_live::PrivateBazaarLiveDeployment;

const MAX_POLL_BATCH: usize = 32;
const MAX_RUN_TICKS: usize = 1_024;
const MAX_SPOOL_WINNER_BYTES: usize = 256;
const LEGACY_SPOOL_FILE_NAME: &str = "finalized-private-bazaar-v1.spool";
const SPOOL_FILE_NAME: &str = "finalized-private-bazaar-v2.spool";
const SPOOL_MAGIC: &[u8; 8] = b"DBSP0002";
const SPOOL_DOMAIN: &str = "dregg.private-bazaar-finalized-spool.v2";
const SEMANTIC_CORE_DOMAIN: &str = "dregg.private-bazaar-settlement-core.v1";
const CLAIM_MAGIC: &[u8; 8] = b"DBWK0001";
const CURSOR_MAGIC: &[u8; 8] = b"DBWC0001";
const CLAIM_DOMAIN: &str = "dregg.private-bazaar-worker-claim.v1";
const CURSOR_DOMAIN: &str = "dregg.private-bazaar-worker-cursor.v1";
const CLAIM_LEN: usize = 8 + 1 + 8 + 8 + (3 * 32) + 32;
const CURSOR_LEN: usize = 8 + 8 + 32;
// v2 is deliberately fixed-width. It supports the SETTLE receipt shape only:
// variable routing/introduction/derivation/event/capability collections must
// all be empty and an optional executor signature is exactly 64 bytes. Every
// integer is big-endian, every presence/bool flag is exactly 0 or 1, absent
// fixed slots and winner padding are zero, and no suffix bytes are accepted.
const SPOOL_RECORD_LEN: usize = 8 // magic/version
    + 8 // cursor
    + 8 // hosted session seed
    + 32 // checksum of physical predecessor record (zero only for first record)
    + 32 // deployment id
    + 32 // executor federation / protocol scope
    + 32 // exact market instance id
    + 32 // deployment policy id
    + 32 // restart-stable semantic settlement core id
    + (12 * 4) // proof public statement
    + 2 // winner byte length
    + MAX_SPOOL_WINNER_BYTES
    + (4 * 32) // turn/forest/pre-state/post-state hashes
    + 8 // timestamp
    + 32 // effects hash
    + 8 // computrons
    + 8 // action count
    + 1
    + 32 // optional previous receipt hash
    + 32 // agent cell
    + 32 // federation
    + 1
    + 64 // optional executor signature
    + 1 // finality (v1 accepts Final only)
    + 1 // encrypted flag
    + 1 // burn flag
    + 32 // reconstructed TurnReceipt hash
    + 32; // record checksum / next-record chain anchor

/// Deployment scope persisted in every fixed record.  The deterministic host
/// seed and market identity are per event; these values prevent byte-identical
/// market/policy claims from being replayed across deployments or federations.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct PrivateBazaarSpoolScope {
    deployment_id: [u8; 32],
    executor_federation: [u8; 32],
    policy_id: [u8; 32],
}

impl PrivateBazaarSpoolScope {
    pub(crate) const fn new(
        deployment_id: [u8; 32],
        executor_federation: [u8; 32],
        policy_id: [u8; 32],
    ) -> Self {
        Self {
            deployment_id,
            executor_federation,
            policy_id,
        }
    }
}

enum PrivateBazaarSpoolBinding {
    Live(PrivateBazaarLiveDeployment),
    #[cfg(test)]
    Detached {
        market_instance_id: [u8; 32],
    },
}

/// One finalized receipt delivered over a private worker transport.
///
/// Fields intentionally have no public accessors. A frontend cannot extract a
/// winner or raw receipt by receiving a worker poll report.
#[derive(Clone)]
pub struct FinalizedPrivateBazaarReceipt {
    cursor: u64,
    session_seed: u64,
    receipt: PrivateClearingReceipt,
}

impl std::fmt::Debug for FinalizedPrivateBazaarReceipt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FinalizedPrivateBazaarReceipt")
            .field("cursor", &self.cursor)
            .field("session_seed", &self.session_seed)
            .field("receipt", &"<worker-private>")
            .finish()
    }
}

impl FinalizedPrivateBazaarReceipt {
    /// Construct at the private transport boundary. Cursor zero and non-final
    /// executor evidence are refused again by the listener before any claim.
    pub fn new(cursor: u64, session_seed: u64, receipt: PrivateClearingReceipt) -> Self {
        Self {
            cursor,
            session_seed,
            receipt,
        }
    }
}

/// Bounded replayable transport interface. Implementations must return events
/// strictly after `after`, in ascending contiguous cursor order, and replay an
/// unacknowledged event after restart. Network/file/MPC transports can implement
/// this without exposing their bytes to any frontend crate.
pub trait FinalizedPrivateBazaarReceiptSource {
    fn poll_finalized_after(
        &mut self,
        after: u64,
        limit: usize,
    ) -> Result<Vec<FinalizedPrivateBazaarReceipt>, String>;
}

/// Deployment-custodied append-only source for finalized private receipts.
///
/// The file contains only checksummed v2 fixed records and is forced to mode
/// `0600` on Unix. Opening validates the complete historical cursor/checksum/
/// semantic-core chain. A small in-memory index points each logical cursor at
/// its latest append-only local-envelope revision, so each poll reads at most
/// one bounded batch. No raw receipt accessor or public rendering type is
/// introduced by this transport.
pub struct PrivateBazaarReceiptSpool {
    path: PathBuf,
    file: File,
    identity: SpoolFileIdentity,
    scope: PrivateBazaarSpoolScope,
    binding: PrivateBazaarSpoolBinding,
    latest_positions: Vec<u64>,
    latest_core_ids: Vec<[u8; 32]>,
    scanned_records: u64,
    tail_checksum: [u8; 32],
}

impl std::fmt::Debug for PrivateBazaarReceiptSpool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarReceiptSpool")
            .field("path", &self.path)
            .finish_non_exhaustive()
    }
}

impl PrivateBazaarReceiptSpool {
    pub(crate) fn open(
        deployment: PrivateBazaarLiveDeployment,
        root: impl AsRef<Path>,
    ) -> Result<Self, PrivateBazaarWorkerError> {
        let scope = deployment.private_spool_scope();
        Self::open_bound(root, scope, PrivateBazaarSpoolBinding::Live(deployment))
    }

    #[cfg(test)]
    fn open_test(root: impl AsRef<Path>) -> Result<Self, PrivateBazaarWorkerError> {
        Self::open_test_with_scope(root, test_spool_scope(0xD1), [0xD2; 32])
    }

    #[cfg(test)]
    fn open_test_with_scope(
        root: impl AsRef<Path>,
        scope: PrivateBazaarSpoolScope,
        market_instance_id: [u8; 32],
    ) -> Result<Self, PrivateBazaarWorkerError> {
        Self::open_bound(
            root,
            scope,
            PrivateBazaarSpoolBinding::Detached { market_instance_id },
        )
    }

    fn open_bound(
        root: impl AsRef<Path>,
        scope: PrivateBazaarSpoolScope,
        binding: PrivateBazaarSpoolBinding,
    ) -> Result<Self, PrivateBazaarWorkerError> {
        let root = root.as_ref();
        fs::create_dir_all(root)
            .map_err(|error| PrivateBazaarWorkerError::io("create receipt spool", error))?;
        ensure_private_directory(root)?;
        let root = fs::canonicalize(root)
            .map_err(|error| PrivateBazaarWorkerError::io("pin receipt spool directory", error))?;
        let path = root.join(SPOOL_FILE_NAME);
        if root.join(LEGACY_SPOOL_FILE_NAME).exists() {
            return Err(PrivateBazaarWorkerError::LegacySpoolRequiresMigration);
        }
        let created = !path.exists();
        let mut options = private_options();
        options.read(true).append(true).create(true);
        let file = options
            .open(&path)
            .map_err(|error| PrivateBazaarWorkerError::io("open receipt spool", error))?;
        secure_private_file_handle(&file, &root)?;
        file.sync_all()
            .map_err(|error| PrivateBazaarWorkerError::io("sync receipt spool", error))?;
        if created {
            sync_directory(&root)?;
        }
        let identity = SpoolFileIdentity::from_file(&file)?;
        let mut spool = Self {
            path,
            file,
            identity,
            scope,
            binding,
            latest_positions: Vec::new(),
            latest_core_ids: Vec::new(),
            scanned_records: 0,
            tail_checksum: [0; 32],
        };
        spool.revalidate_path_identity()?;
        spool
            .file
            .lock_shared()
            .map_err(|error| PrivateBazaarWorkerError::io("lock receipt spool reader", error))?;
        let validation = spool.refresh_index();
        let unlock = spool
            .file
            .unlock()
            .map_err(|error| PrivateBazaarWorkerError::io("unlock receipt spool reader", error));
        match (validation, unlock) {
            (Ok(()), Ok(())) => {}
            (Err(error), _) => return Err(error),
            (Ok(()), Err(error)) => return Err(error),
        }
        Ok(spool)
    }

    /// Append and fsync one finalized semantic receipt. Logical cursors remain
    /// contiguous. Retrying the exact tail is idempotent; a fresh local envelope
    /// for the identical live-validated semantic core is appended as a new
    /// physical revision. Any semantic change at that cursor is a fork.
    pub fn append(
        &mut self,
        cursor: u64,
        session_seed: u64,
        receipt: PrivateClearingReceipt,
    ) -> Result<(), PrivateBazaarWorkerError> {
        self.revalidate_path_identity()?;
        self.file
            .lock()
            .map_err(|error| PrivateBazaarWorkerError::io("lock receipt spool writer", error))?;
        let result = self.append_locked(cursor, session_seed, receipt);
        let unlock = self
            .file
            .unlock()
            .map_err(|error| PrivateBazaarWorkerError::io("unlock receipt spool writer", error));
        match (result, unlock) {
            (Ok(()), Ok(())) => Ok(()),
            (Err(error), _) => Err(error),
            (Ok(()), Err(error)) => Err(error),
        }
    }

    fn append_locked(
        &mut self,
        cursor: u64,
        session_seed: u64,
        receipt: PrivateClearingReceipt,
    ) -> Result<(), PrivateBazaarWorkerError> {
        self.revalidate_path_identity()?;
        let event = FinalizedPrivateBazaarReceipt::new(cursor, session_seed, receipt);
        validate_event(&event, cursor)?;
        let market_instance_id = self.bind_live_event(&event)?;
        self.refresh_index()?;
        let logical_tail = u64::try_from(self.latest_positions.len())
            .map_err(|_| PrivateBazaarWorkerError::CursorOverflow)?;
        let expected = logical_tail
            .checked_add(1)
            .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
        let core_id = semantic_core_id(self.scope, market_instance_id, &event)?;

        if cursor == logical_tail && logical_tail != 0 {
            let index = usize::try_from(cursor - 1)
                .map_err(|_| PrivateBazaarWorkerError::CursorOverflow)?;
            let position = self.latest_positions[index];
            let (found_bytes, found) = self.read_record(position)?;
            if found.semantic_core_id != core_id {
                return Err(PrivateBazaarWorkerError::SpoolFork {
                    expected,
                    found: cursor,
                });
            }
            let expected_bytes = encode_spool_record(
                self.scope,
                market_instance_id,
                &event,
                found.previous_checksum,
            )?;
            if found_bytes == expected_bytes {
                return Ok(());
            }
        }
        if cursor != expected && cursor != logical_tail {
            return Err(if cursor < expected {
                PrivateBazaarWorkerError::SpoolFork {
                    expected,
                    found: cursor,
                }
            } else {
                PrivateBazaarWorkerError::SpoolGap {
                    expected,
                    found: cursor,
                }
            });
        }

        let bytes =
            encode_spool_record(self.scope, market_instance_id, &event, self.tail_checksum)?;
        let mut file = self
            .file
            .try_clone()
            .map_err(|error| PrivateBazaarWorkerError::io("clone receipt spool", error))?;
        file.write_all(&bytes)
            .map_err(|error| PrivateBazaarWorkerError::io("write receipt spool", error))?;
        file.sync_all()
            .map_err(|error| PrivateBazaarWorkerError::io("sync receipt spool append", error))?;
        validate_private_file_handle(
            &self.file,
            self.path
                .parent()
                .ok_or(PrivateBazaarWorkerError::Corrupt("receipt spool parent"))?,
        )?;
        self.revalidate_path_identity()?;
        self.refresh_index()?;
        Ok(())
    }

    fn poll_bounded(
        &mut self,
        after: u64,
        limit: usize,
    ) -> Result<Vec<FinalizedPrivateBazaarReceipt>, PrivateBazaarWorkerError> {
        if limit == 0 || limit > MAX_POLL_BATCH {
            return Err(PrivateBazaarWorkerError::InvalidPollLimit {
                found: limit,
                max: MAX_POLL_BATCH,
            });
        }
        self.revalidate_path_identity()?;
        self.file
            .lock_shared()
            .map_err(|error| PrivateBazaarWorkerError::io("lock receipt spool reader", error))?;
        let result = self.poll_bounded_locked(after, limit);
        let unlock = self
            .file
            .unlock()
            .map_err(|error| PrivateBazaarWorkerError::io("unlock receipt spool reader", error));
        let events = match (result, unlock) {
            (Ok(events), Ok(())) => events,
            (Err(error), _) => return Err(error),
            (Ok(_), Err(error)) => return Err(error),
        };
        self.revalidate_path_identity()?;
        Ok(events)
    }

    fn poll_bounded_locked(
        &mut self,
        after: u64,
        limit: usize,
    ) -> Result<Vec<FinalizedPrivateBazaarReceipt>, PrivateBazaarWorkerError> {
        self.refresh_index()?;
        let logical_tail = u64::try_from(self.latest_positions.len())
            .map_err(|_| PrivateBazaarWorkerError::CursorOverflow)?;
        if after > logical_tail {
            return Err(PrivateBazaarWorkerError::SpoolCursorAhead {
                after,
                last: logical_tail,
            });
        }
        let start = usize::try_from(after).map_err(|_| PrivateBazaarWorkerError::CursorOverflow)?;
        let end = start.saturating_add(limit).min(self.latest_positions.len());
        let mut events = Vec::with_capacity(end - start);
        for logical_index in start..end {
            let (_, record) = self.read_record(self.latest_positions[logical_index])?;
            let expected = u64::try_from(logical_index)
                .map_err(|_| PrivateBazaarWorkerError::CursorOverflow)?
                .checked_add(1)
                .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
            if record.event.cursor != expected {
                return Err(cursor_order_error(expected, record.event.cursor));
            }
            self.revalidate_bound_record(&record)?;
            events.push(record.event);
        }
        Ok(events)
    }

    fn refresh_index(&mut self) -> Result<(), PrivateBazaarWorkerError> {
        let count = self.record_count()?;
        if count < self.scanned_records {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool was truncated",
            ));
        }
        for position in self.scanned_records..count {
            let (_, record) = self.read_record(position)?;
            if record.scope != self.scope {
                return Err(PrivateBazaarWorkerError::SpoolScopeMismatch);
            }
            let expected = u64::try_from(self.latest_positions.len())
                .map_err(|_| PrivateBazaarWorkerError::CursorOverflow)?
                .checked_add(1)
                .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
            if record.previous_checksum != self.tail_checksum {
                return Err(PrivateBazaarWorkerError::SpoolFork {
                    expected,
                    found: record.event.cursor,
                });
            }
            if record.event.cursor == expected {
                self.latest_positions.push(position);
                self.latest_core_ids.push(record.semantic_core_id);
            } else if record.event.cursor == expected.saturating_sub(1) && record.event.cursor != 0
            {
                let last = self.latest_positions.len() - 1;
                if self.latest_core_ids[last] != record.semantic_core_id {
                    return Err(PrivateBazaarWorkerError::SpoolFork {
                        expected,
                        found: record.event.cursor,
                    });
                }
                self.latest_positions[last] = position;
            } else {
                return Err(cursor_order_error(expected, record.event.cursor));
            }
            self.tail_checksum = record.checksum;
            self.scanned_records = position
                .checked_add(1)
                .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
        }
        Ok(())
    }

    fn bind_live_event(
        &self,
        event: &FinalizedPrivateBazaarReceipt,
    ) -> Result<[u8; 32], PrivateBazaarWorkerError> {
        match &self.binding {
            PrivateBazaarSpoolBinding::Live(deployment) => {
                deployment.validate_private_spool_receipt(event.session_seed, &event.receipt)
            }
            #[cfg(test)]
            PrivateBazaarSpoolBinding::Detached { market_instance_id } => Ok(*market_instance_id),
        }
    }

    fn revalidate_bound_record(
        &self,
        record: &DecodedSpoolRecord,
    ) -> Result<(), PrivateBazaarWorkerError> {
        match &self.binding {
            PrivateBazaarSpoolBinding::Live(deployment) => deployment
                .revalidate_private_spool_receipt(
                    record.event.session_seed,
                    record.market_instance_id,
                    &record.event.receipt,
                ),
            #[cfg(test)]
            PrivateBazaarSpoolBinding::Detached { market_instance_id }
                if *market_instance_id == record.market_instance_id =>
            {
                Ok(())
            }
            #[cfg(test)]
            PrivateBazaarSpoolBinding::Detached { .. } => {
                Err(PrivateBazaarWorkerError::SpoolScopeMismatch)
            }
        }
    }

    fn record_count(&self) -> Result<u64, PrivateBazaarWorkerError> {
        let metadata = self
            .file
            .metadata()
            .map_err(|error| PrivateBazaarWorkerError::io("stat receipt spool", error))?;
        validate_spool_metadata(&metadata, self.path.parent())?;
        let record_len = SPOOL_RECORD_LEN as u64;
        let trailing = metadata.len() % record_len;
        if trailing != 0 {
            return Err(PrivateBazaarWorkerError::SpoolTrailingBytes { found: trailing });
        }
        Ok(metadata.len() / record_len)
    }

    fn read_record(
        &self,
        position: u64,
    ) -> Result<(Vec<u8>, DecodedSpoolRecord), PrivateBazaarWorkerError> {
        let offset = position
            .checked_mul(SPOOL_RECORD_LEN as u64)
            .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
        let mut file = self
            .file
            .try_clone()
            .map_err(|error| PrivateBazaarWorkerError::io("clone receipt spool", error))?;
        file.seek(SeekFrom::Start(offset))
            .map_err(|error| PrivateBazaarWorkerError::io("seek receipt spool", error))?;
        let mut bytes = vec![0; SPOOL_RECORD_LEN];
        file.read_exact(&mut bytes)
            .map_err(|error| PrivateBazaarWorkerError::io("read receipt spool record", error))?;
        let record = decode_spool_record(&bytes)?;
        Ok((bytes, record))
    }

    fn revalidate_path_identity(&self) -> Result<(), PrivateBazaarWorkerError> {
        let mut options = private_options();
        options.read(true).write(false);
        let found = options.open(&self.path).map_err(|error| {
            PrivateBazaarWorkerError::io("reopen receipt spool identity", error)
        })?;
        validate_private_file_handle(
            &found,
            self.path
                .parent()
                .ok_or(PrivateBazaarWorkerError::Corrupt("receipt spool parent"))?,
        )?;
        if SpoolFileIdentity::from_file(&found)? != self.identity {
            return Err(PrivateBazaarWorkerError::SpoolFileReplaced);
        }
        if SpoolFileIdentity::from_file(&self.file)? != self.identity {
            return Err(PrivateBazaarWorkerError::SpoolFileReplaced);
        }
        Ok(())
    }
}

impl FinalizedPrivateBazaarReceiptSource for PrivateBazaarReceiptSpool {
    fn poll_finalized_after(
        &mut self,
        after: u64,
        limit: usize,
    ) -> Result<Vec<FinalizedPrivateBazaarReceipt>, String> {
        self.poll_bounded(after, limit)
            .map_err(|error| error.to_string())
    }
}

/// Deployment-wired file source plus the exact worker listener.
pub struct PrivateBazaarFileWorker {
    listener: PrivateBazaarWorkerListener,
    source: PrivateBazaarReceiptSpool,
}

impl PrivateBazaarFileWorker {
    pub(crate) fn new(
        listener: PrivateBazaarWorkerListener,
        source: PrivateBazaarReceiptSpool,
    ) -> Self {
        Self { listener, source }
    }

    /// Process at most one 32-record batch.
    pub fn tick(&mut self) -> Result<PrivateBazaarWorkerPoll, PrivateBazaarWorkerError> {
        self.listener.poll_once(&mut self.source)
    }

    /// Process bounded batches until the source is idle or `max_ticks` is
    /// exhausted. The result contains counts/cursors only, never receipt data.
    pub fn run_until_idle(
        &mut self,
        max_ticks: usize,
    ) -> Result<PrivateBazaarWorkerRun, PrivateBazaarWorkerError> {
        if max_ticks == 0 || max_ticks > MAX_RUN_TICKS {
            return Err(PrivateBazaarWorkerError::InvalidRunBound {
                found: max_ticks,
                max: MAX_RUN_TICKS,
            });
        }
        let mut run = PrivateBazaarWorkerRun {
            cursor: 0,
            processed: 0,
            ticks: 0,
            idle: false,
        };
        for _ in 0..max_ticks {
            let poll = self.tick()?;
            run.cursor = poll.cursor;
            run.processed = run
                .processed
                .checked_add(poll.processed)
                .ok_or(PrivateBazaarWorkerError::ProcessedCountOverflow)?;
            run.ticks += 1;
            if poll.processed == 0 {
                run.idle = true;
                break;
            }
        }
        Ok(run)
    }
}

/// Public-safe bounded-run result. Only operational progress is disclosed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarWorkerRun {
    pub cursor: u64,
    pub processed: usize,
    pub ticks: usize,
    pub idle: bool,
}

struct DecodedSpoolRecord {
    event: FinalizedPrivateBazaarReceipt,
    scope: PrivateBazaarSpoolScope,
    market_instance_id: [u8; 32],
    semantic_core_id: [u8; 32],
    previous_checksum: [u8; 32],
    checksum: [u8; 32],
}

/// Worker-owned registry of authoritative game targets. The private receipt's
/// policy-selected cell chooses the entry; an event cannot nominate a target.
#[derive(Clone, Default)]
pub struct PrivateBazaarWorkerTargets {
    inner: Arc<RwLock<Vec<(CellId, Arc<DungeonWorldCell>)>>>,
}

impl PrivateBazaarWorkerTargets {
    pub fn install(&self, target: Arc<DungeonWorldCell>) -> Result<(), PrivateBazaarWorkerError> {
        let cell = target.cell_id();
        let mut entries = self
            .inner
            .write()
            .map_err(|_| PrivateBazaarWorkerError::TargetRegistryPoisoned)?;
        if let Some(existing) = entries.iter_mut().find(|(candidate, _)| *candidate == cell) {
            existing.1 = target;
        } else {
            entries.push((cell, target));
        }
        Ok(())
    }

    fn resolve(&self, cell: CellId) -> Result<Arc<DungeonWorldCell>, PrivateBazaarWorkerError> {
        self.inner
            .read()
            .map_err(|_| PrivateBazaarWorkerError::TargetRegistryPoisoned)?
            .iter()
            .find(|(candidate, _)| *candidate == cell)
            .map(|(_, target)| Arc::clone(target))
            .ok_or(PrivateBazaarWorkerError::TargetNotInstalled(cell))
    }
}

/// Public-safe operational result. It reveals only cursor progress and count;
/// game status remains the existing viewer-blind offering projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarWorkerPoll {
    pub cursor: u64,
    pub processed: usize,
}

/// Single-owner production listener. It shares the exact deployment registry,
/// commitment custody, game adapter, and policy mounted by every frontend.
pub struct PrivateBazaarWorkerListener {
    deployment: PrivateBazaarLiveDeployment,
    targets: PrivateBazaarWorkerTargets,
    journal: WorkerJournal,
    batch_limit: usize,
}

impl PrivateBazaarWorkerListener {
    pub(crate) fn open(
        deployment: PrivateBazaarLiveDeployment,
        targets: PrivateBazaarWorkerTargets,
        root: impl AsRef<Path>,
    ) -> Result<Self, PrivateBazaarWorkerError> {
        Ok(Self {
            deployment,
            targets,
            journal: WorkerJournal::open(root)?,
            batch_limit: MAX_POLL_BATCH,
        })
    }

    /// Poll and completely process at most one bounded batch. The source cursor
    /// advances only after the viewer-blind journey publication is durable in
    /// the worker claim record. A crash at `Dispatching` is recovered from the
    /// target receipt chain; it is never redispatched.
    pub fn poll_once<S: FinalizedPrivateBazaarReceiptSource>(
        &self,
        source: &mut S,
    ) -> Result<PrivateBazaarWorkerPoll, PrivateBazaarWorkerError> {
        self.poll_once_inner(source, WorkerFault::None)
    }

    #[cfg(test)]
    pub(crate) fn poll_once_with_after_dispatch_crash<S: FinalizedPrivateBazaarReceiptSource>(
        &self,
        source: &mut S,
    ) -> Result<PrivateBazaarWorkerPoll, PrivateBazaarWorkerError> {
        self.poll_once_inner(source, WorkerFault::AfterTargetDispatch)
    }

    fn poll_once_inner<S: FinalizedPrivateBazaarReceiptSource>(
        &self,
        source: &mut S,
        fault: WorkerFault,
    ) -> Result<PrivateBazaarWorkerPoll, PrivateBazaarWorkerError> {
        let after = self.journal.cursor()?;
        let events = source
            .poll_finalized_after(after, self.batch_limit)
            .map_err(PrivateBazaarWorkerError::Source)?;
        if events.len() > self.batch_limit {
            return Err(PrivateBazaarWorkerError::SourceExceededBound {
                found: events.len(),
                limit: self.batch_limit,
            });
        }

        let mut cursor = after;
        let mut processed = 0usize;
        for event in events {
            let expected = cursor
                .checked_add(1)
                .ok_or(PrivateBazaarWorkerError::CursorOverflow)?;
            validate_event(&event, expected)?;
            self.process_event(&event, fault)?;
            cursor = expected;
            processed += 1;
        }
        Ok(PrivateBazaarWorkerPoll { cursor, processed })
    }

    fn process_event(
        &self,
        event: &FinalizedPrivateBazaarReceipt,
        fault: WorkerFault,
    ) -> Result<(), PrivateBazaarWorkerError> {
        let adapter = self.deployment.xp_adapter();
        let existing = self.journal.claim(event.cursor)?;
        if existing.is_some_and(|claim| {
            claim.cursor != event.cursor || claim.session_seed != event.session_seed
        }) {
            return Err(PrivateBazaarWorkerError::ClaimMismatch);
        }
        let result = self.deployment.registry().with_entered_typed(
            event.session_seed,
            |market, journey| {
                if let (Some(claim), Some(public)) = (existing, journey.receipt()) {
                    if public.source_use_id() == Some(claim.source_use_id)
                        && public.operation_id() == Some(claim.operation_id)
                    {
                        return Ok(());
                    }
                    if public.source_use_id().is_some() || public.operation_id().is_some() {
                        return Err(PrivateBazaarWorkerError::PublishedClaimMismatch);
                    }
                }

                let target_cell = journey
                    .policy()
                    .worker_target_cell_for_verified_receipt(&event.receipt)
                    .map_err(|error| PrivateBazaarWorkerError::Journey(error.to_string()))?;
                let target = self.targets.resolve(target_cell)?;

                let (operation, phase) = match existing {
                    Some(claim) => {
                        let resumed = adapter.resume(journey, market, &event.receipt, &target)?;
                        verify_claim(&claim, resumed.operation())?;
                        let phase = resumed.phase();
                        (resumed.into_operation(), phase)
                    }
                    None => match adapter.prepare(journey, market, &event.receipt, &target) {
                        Ok(operation) => {
                            self.journal.persist_claim(WorkerClaim::new(
                                event.cursor,
                                event.session_seed,
                                &operation,
                            ))?;
                            (operation, PrivateBazaarAuthorityPhase::Prepared)
                        }
                        Err(PrivateBazaarGameAdapterError::NeedsRecovery(_)) => {
                            // Crash after adapter prepare but before worker claim.
                            let resumed =
                                adapter.resume(journey, market, &event.receipt, &target)?;
                            self.journal.persist_claim(WorkerClaim::new(
                                event.cursor,
                                event.session_seed,
                                resumed.operation(),
                            ))?;
                            let phase = resumed.phase();
                            (resumed.into_operation(), phase)
                        }
                        Err(error) => return Err(error.into()),
                    },
                };

                match phase {
                    PrivateBazaarAuthorityPhase::Prepared => {
                        let dispatching = adapter.begin_dispatch(
                            operation,
                            journey,
                            market,
                            &event.receipt,
                            &target,
                        )?;
                        let applied = adapter.dispatch_to_target(dispatching, &target)?;
                        if fault == WorkerFault::AfterTargetDispatch {
                            return Err(PrivateBazaarWorkerError::InjectedAfterTargetDispatch);
                        }
                        adapter.record_applied_and_install(
                            applied,
                            journey,
                            market,
                            &event.receipt,
                            &target,
                        )?;
                    }
                    PrivateBazaarAuthorityPhase::Dispatching
                    | PrivateBazaarAuthorityPhase::Applied
                    | PrivateBazaarAuthorityPhase::Committed => {
                        adapter.recover_and_install(journey, market, &event.receipt, &target)?;
                    }
                }
                Ok(())
            },
        )?;
        result?;

        let claim = self
            .journal
            .claim(event.cursor)?
            .ok_or(PrivateBazaarWorkerError::ClaimMissingAfterApply)?;
        self.journal.complete(claim)?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WorkerFault {
    None,
    AfterTargetDispatch,
}

fn validate_event(
    event: &FinalizedPrivateBazaarReceipt,
    expected_cursor: u64,
) -> Result<(), PrivateBazaarWorkerError> {
    if event.cursor != expected_cursor {
        return Err(PrivateBazaarWorkerError::NonContiguousCursor {
            expected: expected_cursor,
            found: event.cursor,
        });
    }
    let turn = &event.receipt.settlement_turn;
    if event.cursor == 0
        || turn.finality != Finality::Final
        || turn.turn_hash == [0; 32]
        || turn.receipt_hash() == [0; 32]
    {
        return Err(PrivateBazaarWorkerError::UnfinalizedEvidence);
    }
    Ok(())
}

fn encode_spool_record(
    scope: PrivateBazaarSpoolScope,
    market_instance_id: [u8; 32],
    event: &FinalizedPrivateBazaarReceipt,
    previous_checksum: [u8; 32],
) -> Result<Vec<u8>, PrivateBazaarWorkerError> {
    validate_event(event, event.cursor)?;
    let receipt = &event.receipt;
    let turn = &receipt.settlement_turn;
    let winner = receipt.winner.0.as_bytes();
    if winner.is_empty() || winner.len() > MAX_SPOOL_WINNER_BYTES {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "winner length",
        ));
    }
    if !turn.routing_directives.is_empty() {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "routing directives",
        ));
    }
    if !turn.introduction_exports.is_empty() {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "introduction exports",
        ));
    }
    if !turn.derivation_records.is_empty() {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "derivation records",
        ));
    }
    if !turn.emitted_events.is_empty() {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "emitted events",
        ));
    }
    if !turn.consumed_capabilities.is_empty() {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "consumed capabilities",
        ));
    }
    let action_count = u64::try_from(turn.action_count).map_err(|_| {
        PrivateBazaarWorkerError::UnsupportedReceiptField("action count does not fit u64")
    })?;
    let winner_len =
        u16::try_from(winner.len()).expect("bounded private Bazaar spool winner length fits u16");
    let (signature_flag, signature) = match turn.executor_signature.as_deref() {
        None => (0, [0; 64]),
        Some(bytes) if bytes.len() == 64 => (
            1,
            bytes
                .try_into()
                .expect("executor signature length checked above"),
        ),
        Some(_) => {
            return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
                "executor signature length",
            ));
        }
    };

    let mut out = Vec::with_capacity(SPOOL_RECORD_LEN);
    out.extend_from_slice(SPOOL_MAGIC);
    out.extend_from_slice(&event.cursor.to_be_bytes());
    out.extend_from_slice(&event.session_seed.to_be_bytes());
    out.extend_from_slice(&previous_checksum);
    out.extend_from_slice(&scope.deployment_id);
    out.extend_from_slice(&scope.executor_federation);
    out.extend_from_slice(&market_instance_id);
    out.extend_from_slice(&scope.policy_id);
    out.extend_from_slice(&semantic_core_id(scope, market_instance_id, event)?);
    out.extend_from_slice(&receipt.statement.session.to_be_bytes());
    out.extend_from_slice(&receipt.statement.rule.to_be_bytes());
    for lane in receipt.statement.order_root {
        out.extend_from_slice(&lane.to_be_bytes());
    }
    out.extend_from_slice(&receipt.statement.p_star.to_be_bytes());
    out.extend_from_slice(&receipt.statement.v_star.to_be_bytes());
    out.extend_from_slice(&winner_len.to_be_bytes());
    out.extend_from_slice(winner);
    out.resize(out.len() + (MAX_SPOOL_WINNER_BYTES - winner.len()), 0);
    out.extend_from_slice(&turn.turn_hash);
    out.extend_from_slice(&turn.forest_hash);
    out.extend_from_slice(&turn.pre_state_hash);
    out.extend_from_slice(&turn.post_state_hash);
    out.extend_from_slice(&turn.timestamp.to_be_bytes());
    out.extend_from_slice(&turn.effects_hash);
    out.extend_from_slice(&turn.computrons_used.to_be_bytes());
    out.extend_from_slice(&action_count.to_be_bytes());
    match turn.previous_receipt_hash {
        Some(hash) => {
            out.push(1);
            out.extend_from_slice(&hash);
        }
        None => {
            out.push(0);
            out.extend_from_slice(&[0; 32]);
        }
    }
    out.extend_from_slice(turn.agent.as_bytes());
    out.extend_from_slice(&turn.federation_id);
    out.push(signature_flag);
    out.extend_from_slice(&signature);
    out.push(1); // Finality::Final is the only v1 value.
    out.push(u8::from(turn.was_encrypted));
    out.push(u8::from(turn.was_burn));
    out.extend_from_slice(&turn.receipt_hash());
    let checksum = checksum(SPOOL_DOMAIN, &out);
    out.extend_from_slice(&checksum);
    if out.len() != SPOOL_RECORD_LEN {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool encoder length",
        ));
    }
    // The producer must refuse a noncanonical typed value before fsync, not
    // merely rely on the consumer to discover it later.
    let _ = decode_spool_record(&out)?;
    Ok(out)
}

fn decode_spool_record(bytes: &[u8]) -> Result<DecodedSpoolRecord, PrivateBazaarWorkerError> {
    if bytes.len() != SPOOL_RECORD_LEN || &bytes[..8] != SPOOL_MAGIC {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool record schema",
        ));
    }
    if checksum(SPOOL_DOMAIN, &bytes[..SPOOL_RECORD_LEN - 32]) != bytes[SPOOL_RECORD_LEN - 32..] {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool record checksum",
        ));
    }

    let mut reader = FixedRecordReader::new(bytes);
    if reader.array::<8>()? != *SPOOL_MAGIC {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool record magic",
        ));
    }
    let cursor = reader.u64()?;
    let session_seed = reader.u64()?;
    let previous_checksum = reader.array::<32>()?;
    let deployment_id = reader.array::<32>()?;
    let executor_federation = reader.array::<32>()?;
    let market_instance_id = reader.array::<32>()?;
    let policy_id = reader.array::<32>()?;
    let scope = PrivateBazaarSpoolScope {
        deployment_id,
        executor_federation,
        policy_id,
    };
    let expected_semantic_core_id = reader.array::<32>()?;
    let session = reader.u32()?;
    let rule = reader.u32()?;
    let mut order_root = [0; 8];
    for lane in &mut order_root {
        *lane = reader.u32()?;
    }
    let price = reader.u32()?;
    let volume = reader.u32()?;
    let winner_len = usize::from(reader.u16()?);
    let winner_slot = reader.array::<MAX_SPOOL_WINNER_BYTES>()?;
    if winner_len == 0
        || winner_len > MAX_SPOOL_WINNER_BYTES
        || winner_slot[winner_len..].iter().any(|byte| *byte != 0)
    {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool winner encoding",
        ));
    }
    let winner = String::from_utf8(winner_slot[..winner_len].to_vec())
        .map_err(|error| PrivateBazaarWorkerError::ReceiptCodec(error.to_string()))?;

    let turn_hash = reader.array::<32>()?;
    let forest_hash = reader.array::<32>()?;
    let pre_state_hash = reader.array::<32>()?;
    let post_state_hash = reader.array::<32>()?;
    let timestamp = reader.i64()?;
    let effects_hash = reader.array::<32>()?;
    let computrons_used = reader.u64()?;
    let action_count = usize::try_from(reader.u64()?).map_err(|_| {
        PrivateBazaarWorkerError::ReceiptCodec("action count does not fit usize".to_owned())
    })?;
    let previous_flag = reader.u8()?;
    let previous_bytes = reader.array::<32>()?;
    let previous_receipt_hash = match previous_flag {
        0 if previous_bytes == [0; 32] => None,
        1 => Some(previous_bytes),
        _ => {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool previous-hash encoding",
            ));
        }
    };
    let agent = CellId(reader.array::<32>()?);
    let federation_id = reader.array::<32>()?;
    let signature_flag = reader.u8()?;
    let signature_bytes = reader.array::<64>()?;
    let executor_signature = match signature_flag {
        0 if signature_bytes == [0; 64] => None,
        1 => Some(signature_bytes.to_vec()),
        _ => {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool signature encoding",
            ));
        }
    };
    if reader.u8()? != 1 {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool finality encoding",
        ));
    }
    let was_encrypted = decode_bool(reader.u8()?, "receipt spool encrypted flag")?;
    let was_burn = decode_bool(reader.u8()?, "receipt spool burn flag")?;
    let expected_receipt_hash = reader.array::<32>()?;
    let record_checksum = reader.array::<32>()?;
    if !reader.is_finished() {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool decoder length",
        ));
    }

    let settlement_turn = TurnReceipt {
        turn_hash,
        forest_hash,
        pre_state_hash,
        post_state_hash,
        timestamp,
        effects_hash,
        computrons_used,
        action_count,
        previous_receipt_hash,
        agent,
        federation_id,
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature,
        finality: Finality::Final,
        was_encrypted,
        was_burn,
        consumed_capabilities: Vec::new(),
    };
    if settlement_turn.receipt_hash() != expected_receipt_hash {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool reconstructed receipt hash",
        ));
    }
    let receipt = PrivateClearingReceipt::from_worker_spool_v1_parts(
        session,
        rule,
        order_root,
        price,
        volume,
        DreggIdentity(winner),
        settlement_turn,
    )
    .map_err(|error| PrivateBazaarWorkerError::ReceiptCodec(error.to_string()))?;
    let event = FinalizedPrivateBazaarReceipt::new(cursor, session_seed, receipt);
    validate_event(&event, cursor)?;
    if semantic_core_id(scope, market_instance_id, &event)? != expected_semantic_core_id {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool semantic core",
        ));
    }
    Ok(DecodedSpoolRecord {
        event,
        scope,
        market_instance_id,
        semantic_core_id: expected_semantic_core_id,
        previous_checksum,
        checksum: record_checksum,
    })
}

fn cursor_order_error(expected: u64, found: u64) -> PrivateBazaarWorkerError {
    if found < expected {
        PrivateBazaarWorkerError::SpoolFork { expected, found }
    } else {
        PrivateBazaarWorkerError::SpoolGap { expected, found }
    }
}

fn decode_bool(value: u8, field: &'static str) -> Result<bool, PrivateBazaarWorkerError> {
    match value {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(PrivateBazaarWorkerError::Corrupt(field)),
    }
}

struct FixedRecordReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> FixedRecordReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], PrivateBazaarWorkerError> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(PrivateBazaarWorkerError::Corrupt(
                "receipt spool field offset",
            ))?;
        let found = self
            .bytes
            .get(self.offset..end)
            .ok_or(PrivateBazaarWorkerError::Corrupt(
                "receipt spool short field",
            ))?;
        self.offset = end;
        Ok(found
            .try_into()
            .expect("fixed record reader checked field length"))
    }

    fn u8(&mut self) -> Result<u8, PrivateBazaarWorkerError> {
        Ok(self.array::<1>()?[0])
    }

    fn u16(&mut self) -> Result<u16, PrivateBazaarWorkerError> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u32(&mut self) -> Result<u32, PrivateBazaarWorkerError> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, PrivateBazaarWorkerError> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn i64(&mut self) -> Result<i64, PrivateBazaarWorkerError> {
        Ok(i64::from_be_bytes(self.array()?))
    }

    fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

fn verify_claim(
    claim: &WorkerClaim,
    operation: &PreparedPrivateBazaarXp,
) -> Result<(), PrivateBazaarWorkerError> {
    if claim.source_use_id != operation.source_use_id()
        || claim.operation_id != operation.operation_id()
        || claim.lookup_id != operation.lookup_id()
    {
        return Err(PrivateBazaarWorkerError::ClaimMismatch);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum WorkerClaimPhase {
    Claimed = 1,
    Completed = 2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct WorkerClaim {
    phase: WorkerClaimPhase,
    cursor: u64,
    session_seed: u64,
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    lookup_id: [u8; 32],
}

impl WorkerClaim {
    fn new(cursor: u64, session_seed: u64, operation: &PreparedPrivateBazaarXp) -> Self {
        Self {
            phase: WorkerClaimPhase::Claimed,
            cursor,
            session_seed,
            source_use_id: operation.source_use_id(),
            operation_id: operation.operation_id(),
            lookup_id: operation.lookup_id(),
        }
    }

    fn encode(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(CLAIM_LEN);
        out.extend_from_slice(CLAIM_MAGIC);
        out.push(self.phase as u8);
        out.extend_from_slice(&self.cursor.to_be_bytes());
        out.extend_from_slice(&self.session_seed.to_be_bytes());
        out.extend_from_slice(&self.source_use_id);
        out.extend_from_slice(&self.operation_id);
        out.extend_from_slice(&self.lookup_id);
        let checksum = checksum(CLAIM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self, PrivateBazaarWorkerError> {
        if bytes.len() != CLAIM_LEN || &bytes[..8] != CLAIM_MAGIC {
            return Err(PrivateBazaarWorkerError::Corrupt("claim schema"));
        }
        if checksum(CLAIM_DOMAIN, &bytes[..CLAIM_LEN - 32]) != bytes[CLAIM_LEN - 32..] {
            return Err(PrivateBazaarWorkerError::Corrupt("claim checksum"));
        }
        let phase = match bytes[8] {
            1 => WorkerClaimPhase::Claimed,
            2 => WorkerClaimPhase::Completed,
            _ => return Err(PrivateBazaarWorkerError::Corrupt("claim phase")),
        };
        let claim = Self {
            phase,
            cursor: u64::from_be_bytes(array_at(bytes, 9)),
            session_seed: u64::from_be_bytes(array_at(bytes, 17)),
            source_use_id: array_at(bytes, 25),
            operation_id: array_at(bytes, 57),
            lookup_id: array_at(bytes, 89),
        };
        if claim.cursor == 0
            || claim.source_use_id == [0; 32]
            || claim.operation_id == [0; 32]
            || claim.lookup_id == [0; 32]
        {
            return Err(PrivateBazaarWorkerError::Corrupt("zero claim field"));
        }
        Ok(claim)
    }
}

struct WorkerJournal {
    root: PathBuf,
}

impl WorkerJournal {
    fn open(root: impl AsRef<Path>) -> Result<Self, PrivateBazaarWorkerError> {
        let root = root.as_ref().to_path_buf();
        fs::create_dir_all(root.join("claims"))
            .map_err(|error| PrivateBazaarWorkerError::io("create worker journal", error))?;
        sync_directory(&root)?;
        Ok(Self { root })
    }

    fn cursor(&self) -> Result<u64, PrivateBazaarWorkerError> {
        let path = self.root.join("cursor");
        let bytes = match fs::read(path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(0),
            Err(error) => return Err(PrivateBazaarWorkerError::io("read cursor", error)),
        };
        if bytes.len() != CURSOR_LEN || &bytes[..8] != CURSOR_MAGIC {
            return Err(PrivateBazaarWorkerError::Corrupt("cursor schema"));
        }
        if checksum(CURSOR_DOMAIN, &bytes[..CURSOR_LEN - 32]) != bytes[CURSOR_LEN - 32..] {
            return Err(PrivateBazaarWorkerError::Corrupt("cursor checksum"));
        }
        Ok(u64::from_be_bytes(array_at(&bytes, 8)))
    }

    fn claim(&self, cursor: u64) -> Result<Option<WorkerClaim>, PrivateBazaarWorkerError> {
        match fs::read(self.claim_path(cursor)) {
            Ok(bytes) => {
                let claim = WorkerClaim::decode(&bytes)?;
                if claim.cursor != cursor {
                    return Err(PrivateBazaarWorkerError::Corrupt(
                        "claim cursor/path mismatch",
                    ));
                }
                Ok(Some(claim))
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(PrivateBazaarWorkerError::io("read worker claim", error)),
        }
    }

    fn persist_claim(&self, claim: WorkerClaim) -> Result<(), PrivateBazaarWorkerError> {
        write_new_or_verify(&self.claim_path(claim.cursor), &claim.encode())
    }

    fn complete(&self, mut claim: WorkerClaim) -> Result<(), PrivateBazaarWorkerError> {
        let current = self.cursor()?;
        if current == claim.cursor {
            return Ok(());
        }
        if current.checked_add(1) != Some(claim.cursor) {
            return Err(PrivateBazaarWorkerError::NonContiguousCursor {
                expected: current.saturating_add(1),
                found: claim.cursor,
            });
        }
        claim.phase = WorkerClaimPhase::Completed;
        atomic_replace(&self.claim_path(claim.cursor), &claim.encode())?;
        atomic_replace(&self.root.join("cursor"), &encode_cursor(claim.cursor))?;
        Ok(())
    }

    fn claim_path(&self, cursor: u64) -> PathBuf {
        self.root.join("claims").join(format!("{cursor:020}.claim"))
    }
}

fn encode_cursor(cursor: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(CURSOR_LEN);
    out.extend_from_slice(CURSOR_MAGIC);
    out.extend_from_slice(&cursor.to_be_bytes());
    let checksum = checksum(CURSOR_DOMAIN, &out);
    out.extend_from_slice(&checksum);
    out
}

fn checksum(domain: &str, bytes: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(domain)
        .update(bytes)
        .finalize()
        .as_bytes()
}

/// Restart-stable settlement identity.  It includes every semantic public
/// clearing coordinate and the canonical winner under an explicit deployment,
/// federation, market, policy, logical cursor, and deterministic host seed.
/// Proof randomness and every local [`TurnReceipt`] envelope field are excluded.
fn semantic_core_id(
    scope: PrivateBazaarSpoolScope,
    market_instance_id: [u8; 32],
    event: &FinalizedPrivateBazaarReceipt,
) -> Result<[u8; 32], PrivateBazaarWorkerError> {
    let winner = event.receipt.winner.0.as_bytes();
    let winner_len = u16::try_from(winner.len())
        .map_err(|_| PrivateBazaarWorkerError::UnsupportedReceiptField("winner length"))?;
    if winner_len == 0 || winner.len() > MAX_SPOOL_WINNER_BYTES {
        return Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
            "winner length",
        ));
    }
    let mut hasher = blake3::Hasher::new_derive_key(SEMANTIC_CORE_DOMAIN);
    hasher.update(b"DBSC0001");
    hasher.update(&scope.deployment_id);
    hasher.update(&scope.executor_federation);
    hasher.update(&market_instance_id);
    hasher.update(&scope.policy_id);
    hasher.update(&event.cursor.to_be_bytes());
    hasher.update(&event.session_seed.to_be_bytes());
    hasher.update(&event.receipt.statement.session.to_be_bytes());
    hasher.update(&event.receipt.statement.rule.to_be_bytes());
    for lane in event.receipt.statement.order_root {
        hasher.update(&lane.to_be_bytes());
    }
    hasher.update(&event.receipt.statement.p_star.to_be_bytes());
    hasher.update(&event.receipt.statement.v_star.to_be_bytes());
    hasher.update(&winner_len.to_be_bytes());
    hasher.update(winner);
    Ok(*hasher.finalize().as_bytes())
}

#[cfg(test)]
const fn test_spool_scope(tag: u8) -> PrivateBazaarSpoolScope {
    PrivateBazaarSpoolScope::new(
        [tag; 32],
        [tag.wrapping_add(1); 32],
        [tag.wrapping_add(2); 32],
    )
}

fn array_at<const N: usize>(bytes: &[u8], offset: usize) -> [u8; N] {
    bytes[offset..offset + N]
        .try_into()
        .expect("fixed worker record length checked")
}

fn private_options() -> OpenOptions {
    let mut options = OpenOptions::new();
    options.write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600).custom_flags(unix_no_follow_flag());
    }
    options
}

#[cfg(any(target_os = "linux", target_os = "android"))]
const fn unix_no_follow_flag() -> i32 {
    // O_NOFOLLOW from the Linux UAPI. Keeping the constant here avoids adding
    // a full libc dependency to the frontend-neutral catalog crate.
    0o400_000
}

#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "netbsd",
    target_os = "openbsd"
))]
const fn unix_no_follow_flag() -> i32 {
    // O_NOFOLLOW on Darwin and the BSD family.
    0x100
}

#[cfg(all(
    unix,
    not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "dragonfly",
        target_os = "netbsd",
        target_os = "openbsd"
    ))
))]
compile_error!("private Bazaar spool requires a reviewed O_NOFOLLOW value for this Unix target");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SpoolFileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
}

impl SpoolFileIdentity {
    fn from_file(file: &File) -> Result<Self, PrivateBazaarWorkerError> {
        let metadata = file
            .metadata()
            .map_err(|error| PrivateBazaarWorkerError::io("stat pinned receipt spool", error))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            Ok(Self {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        }
        #[cfg(not(unix))]
        {
            let _ = metadata;
            Ok(Self {})
        }
    }
}

fn ensure_private_directory(path: &Path) -> Result<(), PrivateBazaarWorkerError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o700))
            .map_err(|error| PrivateBazaarWorkerError::io("secure worker directory", error))?;
    }
    Ok(())
}

fn secure_private_file_handle(file: &File, parent: &Path) -> Result<(), PrivateBazaarWorkerError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let initial = file
            .metadata()
            .map_err(|error| PrivateBazaarWorkerError::io("stat worker file mode", error))?;
        validate_spool_metadata(&initial, Some(parent))?;
        let parent_metadata = fs::metadata(parent)
            .map_err(|error| PrivateBazaarWorkerError::io("stat worker directory owner", error))?;
        if initial.uid() != parent_metadata.uid() {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "worker file owner differs from worker directory owner",
            ));
        }
        file.set_permissions(fs::Permissions::from_mode(0o600))
            .map_err(|error| PrivateBazaarWorkerError::io("secure worker file", error))?;
    }
    validate_private_file_handle(file, parent)
}

fn validate_private_file_handle(
    file: &File,
    parent: &Path,
) -> Result<(), PrivateBazaarWorkerError> {
    let metadata = file
        .metadata()
        .map_err(|error| PrivateBazaarWorkerError::io("stat worker file", error))?;
    validate_spool_metadata(&metadata, Some(parent))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let parent_metadata = fs::metadata(parent)
            .map_err(|error| PrivateBazaarWorkerError::io("stat worker directory owner", error))?;
        if metadata.uid() != parent_metadata.uid() {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "worker file owner differs from worker directory owner",
            ));
        }
        if metadata.permissions().mode() & 0o777 != 0o600 {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "worker file permissions are not 0600",
            ));
        }
    }
    #[cfg(not(unix))]
    validate_spool_metadata(&metadata, Some(parent))?;
    Ok(())
}

fn validate_spool_metadata(
    metadata: &fs::Metadata,
    _parent: Option<&Path>,
) -> Result<(), PrivateBazaarWorkerError> {
    if !metadata.is_file() {
        return Err(PrivateBazaarWorkerError::Corrupt(
            "receipt spool is not a regular file",
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.nlink() != 1 {
            return Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool link count is not one",
            ));
        }
    }
    Ok(())
}

fn write_new_or_verify(path: &Path, expected: &[u8]) -> Result<(), PrivateBazaarWorkerError> {
    match fs::read(path) {
        Ok(found) if found == expected => return Ok(()),
        Ok(_) => return Err(PrivateBazaarWorkerError::ClaimMismatch),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(PrivateBazaarWorkerError::io("read worker claim", error)),
    }
    // The listener is explicitly single-owner. Write the immutable claim via a
    // recoverable temporary file so a power loss cannot leave a short final
    // record that permanently wedges replay. A stale temp from that crash is
    // truncated on the next attempt.
    atomic_replace(path, expected)
}

fn atomic_replace(path: &Path, bytes: &[u8]) -> Result<(), PrivateBazaarWorkerError> {
    let temp = path.with_extension("next");
    let mut options = private_options();
    options.create(true).truncate(true);
    let mut file = options
        .open(&temp)
        .map_err(|error| PrivateBazaarWorkerError::io("create replacement", error))?;
    file.write_all(bytes)
        .map_err(|error| PrivateBazaarWorkerError::io("write replacement", error))?;
    file.sync_all()
        .map_err(|error| PrivateBazaarWorkerError::io("sync replacement", error))?;
    drop(file);
    fs::rename(&temp, path)
        .map_err(|error| PrivateBazaarWorkerError::io("install replacement", error))?;
    sync_parent(path)
}

fn sync_parent(path: &Path) -> Result<(), PrivateBazaarWorkerError> {
    let parent = path
        .parent()
        .ok_or(PrivateBazaarWorkerError::Corrupt("path parent"))?;
    sync_directory(parent)
}

fn sync_directory(path: &Path) -> Result<(), PrivateBazaarWorkerError> {
    File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| PrivateBazaarWorkerError::io("sync worker directory", error))
}

#[derive(Debug)]
pub enum PrivateBazaarWorkerError {
    Source(String),
    SourceExceededBound {
        found: usize,
        limit: usize,
    },
    InvalidPollLimit {
        found: usize,
        max: usize,
    },
    InvalidRunBound {
        found: usize,
        max: usize,
    },
    ProcessedCountOverflow,
    NonContiguousCursor {
        expected: u64,
        found: u64,
    },
    SpoolGap {
        expected: u64,
        found: u64,
    },
    SpoolFork {
        expected: u64,
        found: u64,
    },
    SpoolCursorAhead {
        after: u64,
        last: u64,
    },
    SpoolTrailingBytes {
        found: u64,
    },
    SpoolFileReplaced,
    LegacySpoolRequiresMigration,
    SpoolScopeMismatch,
    StaleLiveMarket,
    CursorOverflow,
    UnfinalizedEvidence,
    UnsupportedReceiptField(&'static str),
    ReceiptCodec(String),
    TargetRegistryPoisoned,
    TargetNotInstalled(CellId),
    Host(String),
    GameAdapter(String),
    Journey(String),
    ClaimMismatch,
    PublishedClaimMismatch,
    ClaimMissingAfterApply,
    Corrupt(&'static str),
    InjectedAfterTargetDispatch,
    Io {
        operation: &'static str,
        detail: String,
    },
}

impl PrivateBazaarWorkerError {
    fn io(operation: &'static str, error: io::Error) -> Self {
        Self::Io {
            operation,
            detail: error.to_string(),
        }
    }
}

impl From<PrivateBazaarLiveHostError> for PrivateBazaarWorkerError {
    fn from(error: PrivateBazaarLiveHostError) -> Self {
        Self::Host(error.to_string())
    }
}

impl From<PrivateBazaarGameAdapterError> for PrivateBazaarWorkerError {
    fn from(error: PrivateBazaarGameAdapterError) -> Self {
        Self::GameAdapter(error.to_string())
    }
}

impl std::fmt::Display for PrivateBazaarWorkerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar worker refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarWorkerError {}

#[cfg(test)]
mod tests {
    use super::*;

    const PRIVATE_BAZAAR_RULE_V1: u32 = 1_430_520_836;

    fn receipt(tag: u8) -> PrivateClearingReceipt {
        let turn = TurnReceipt {
            turn_hash: [tag; 32],
            forest_hash: [tag.wrapping_add(1); 32],
            pre_state_hash: [tag.wrapping_add(2); 32],
            post_state_hash: [tag.wrapping_add(3); 32],
            timestamp: i64::from(tag),
            effects_hash: [tag.wrapping_add(4); 32],
            computrons_used: u64::from(tag),
            action_count: 4,
            previous_receipt_hash: Some([tag.wrapping_add(5); 32]),
            agent: CellId([tag.wrapping_add(6); 32]),
            federation_id: [tag.wrapping_add(7); 32],
            executor_signature: Some(vec![tag.wrapping_add(8); 64]),
            finality: Finality::Final,
            was_encrypted: true,
            was_burn: false,
            ..TurnReceipt::default()
        };
        PrivateClearingReceipt::from_worker_spool_v1_parts(
            17,
            PRIVATE_BAZAAR_RULE_V1,
            [19; 8],
            3,
            1,
            DreggIdentity(format!("worker-private-winner-{tag}")),
            turn,
        )
        .unwrap()
    }

    #[test]
    fn fixed_spool_replays_unacknowledged_records_and_is_private_and_bounded() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("worker");
        let mut spool = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        let first = receipt(0x21);
        spool.append(1, 0xA1, first.clone()).unwrap();
        spool
            .append(1, 0xA1, first)
            .expect("exact tail retry is idempotent");

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                fs::metadata(root.join(SPOOL_FILE_NAME))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o777,
                0o600
            );
        }

        let mut reopened = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        let first_poll = reopened.poll_bounded(0, 1).unwrap();
        assert_eq!(first_poll.len(), 1);
        assert_eq!(first_poll[0].cursor, 1);
        assert_eq!(first_poll[0].session_seed, 0xA1);
        assert_eq!(first_poll[0].receipt.winner.0, "worker-private-winner-33");
        assert_eq!(first_poll[0].receipt.settlement_turn.turn_hash, [0x21; 32]);
        assert_eq!(reopened.poll_bounded(0, 1).unwrap().len(), 1);
        assert!(reopened.poll_bounded(1, 1).unwrap().is_empty());
        assert!(matches!(
            reopened.poll_bounded(0, MAX_POLL_BATCH + 1),
            Err(PrivateBazaarWorkerError::InvalidPollLimit { .. })
        ));

        let rendered = format!("{:?}", first_poll[0]);
        assert!(rendered.contains("<worker-private>"), "{rendered}");
        assert!(!rendered.contains("worker-private-winner"), "{rendered}");
        assert!(matches!(
            reopened.append(3, 0xA3, receipt(0x23)),
            Err(PrivateBazaarWorkerError::SpoolGap {
                expected: 2,
                found: 3
            })
        ));
        assert!(matches!(
            reopened.append(1, 0xFF, receipt(0x24)),
            Err(PrivateBazaarWorkerError::SpoolFork { .. })
        ));
    }

    #[test]
    fn semantic_tail_reissue_appends_only_a_fresh_envelope_and_polls_latest() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("worker");
        let mut spool = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        let first = receipt(0x29);
        let mut reissued = first.clone();
        reissued.settlement_turn.turn_hash = [0xA1; 32];
        reissued.settlement_turn.forest_hash = [0xA2; 32];
        reissued.settlement_turn.pre_state_hash = [0xA3; 32];
        reissued.settlement_turn.post_state_hash = [0xA4; 32];
        reissued.settlement_turn.timestamp = 9_999;
        reissued.settlement_turn.previous_receipt_hash = Some([0xA5; 32]);
        reissued.settlement_turn.executor_signature = Some(vec![0xA6; 64]);

        spool.append(1, 0xBEEF, first.clone()).unwrap();
        spool.append(1, 0xBEEF, reissued.clone()).unwrap();
        assert_eq!(
            fs::metadata(root.join(SPOOL_FILE_NAME)).unwrap().len(),
            (2 * SPOOL_RECORD_LEN) as u64,
            "a semantic retry is an append-only envelope revision"
        );

        let mut reopened = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        let events = reopened.poll_bounded(0, 1).unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(events[0].receipt.statement, first.statement);
        assert_eq!(events[0].receipt.winner.0, first.winner.0);
        assert_eq!(
            events[0].receipt.settlement_turn.receipt_hash(),
            reissued.settlement_turn.receipt_hash()
        );
        reopened
            .append(1, 0xBEEF, reissued)
            .expect("exact latest envelope retry is idempotent");
        assert_eq!(
            fs::metadata(root.join(SPOOL_FILE_NAME)).unwrap().len(),
            (2 * SPOOL_RECORD_LEN) as u64
        );

        let mut changed_root = first;
        changed_root.statement.order_root[0] = 20;
        assert!(matches!(
            reopened.append(1, 0xBEEF, changed_root),
            Err(PrivateBazaarWorkerError::SpoolFork { .. })
        ));
        let mut changed_price = receipt(0x29);
        changed_price.statement.p_star = 2;
        assert!(matches!(
            reopened.append(1, 0xBEEF, changed_price),
            Err(PrivateBazaarWorkerError::SpoolFork { .. })
        ));
        let mut changed_winner = receipt(0x29);
        changed_winner.winner = DreggIdentity("other-private-winner".to_owned());
        assert!(matches!(
            reopened.append(1, 0xBEEF, changed_winner),
            Err(PrivateBazaarWorkerError::SpoolFork { .. })
        ));
    }

    #[test]
    fn semantic_spool_refuses_cross_deployment_and_corrupt_core() {
        let legacy = tempfile::tempdir().unwrap();
        fs::write(legacy.path().join(LEGACY_SPOOL_FILE_NAME), []).unwrap();
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(legacy.path()),
            Err(PrivateBazaarWorkerError::LegacySpoolRequiresMigration)
        ));

        let cross = tempfile::tempdir().unwrap();
        let scope_a = test_spool_scope(0x31);
        let scope_b = test_spool_scope(0x41);
        let market = [0x51; 32];
        let mut spool =
            PrivateBazaarReceiptSpool::open_test_with_scope(cross.path(), scope_a, market).unwrap();
        spool.append(1, 7, receipt(0x35)).unwrap();
        drop(spool);
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test_with_scope(cross.path(), scope_b, market),
            Err(PrivateBazaarWorkerError::SpoolScopeMismatch)
        ));

        let corrupt = tempfile::tempdir().unwrap();
        let mut spool = PrivateBazaarReceiptSpool::open_test(corrupt.path()).unwrap();
        spool.append(1, 8, receipt(0x36)).unwrap();
        let path = spool.path.clone();
        drop(spool);
        let mut bytes = fs::read(&path).unwrap();
        const CORE_OFFSET: usize = 8 + 8 + 8 + 32 + (4 * 32);
        bytes[CORE_OFFSET] ^= 1;
        let record_checksum = checksum(SPOOL_DOMAIN, &bytes[..SPOOL_RECORD_LEN - 32]);
        bytes[SPOOL_RECORD_LEN - 32..].copy_from_slice(&record_checksum);
        fs::write(&path, bytes).unwrap();
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(corrupt.path()),
            Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool semantic core"
            ))
        ));
    }

    #[test]
    fn fixed_spool_refuses_unsupported_receipt_collections_and_trailing_bytes() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("worker");
        let mut spool = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        let mut unsupported = receipt(0x31);
        unsupported
            .settlement_turn
            .emitted_events
            .push(dregg_turn::EmittedEvent {
                cell: CellId([0x32; 32]),
                topic: [0x33; 32],
                data: Vec::new(),
            });
        assert!(matches!(
            spool.append(1, 7, unsupported),
            Err(PrivateBazaarWorkerError::UnsupportedReceiptField(
                "emitted events"
            ))
        ));

        spool.append(1, 7, receipt(0x34)).unwrap();
        let mut file = OpenOptions::new()
            .append(true)
            .open(root.join(SPOOL_FILE_NAME))
            .unwrap();
        file.write_all(&[0xFF]).unwrap();
        file.sync_all().unwrap();
        assert!(matches!(
            spool.poll_bounded(0, 1),
            Err(PrivateBazaarWorkerError::SpoolTrailingBytes { found: 1 })
        ));
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(&root),
            Err(PrivateBazaarWorkerError::SpoolTrailingBytes { found: 1 })
        ));
    }

    #[test]
    fn fixed_spool_refuses_corruption_gaps_and_forks_on_reopen() {
        fn write_records(
            root: &Path,
            first: FinalizedPrivateBazaarReceipt,
            second: FinalizedPrivateBazaarReceipt,
        ) -> PathBuf {
            let spool = PrivateBazaarReceiptSpool::open_test(root).unwrap();
            let scope = spool.scope;
            let market_instance_id = [0xD2; 32];
            let first = encode_spool_record(scope, market_instance_id, &first, [0; 32]).unwrap();
            let first_checksum = array_at::<32>(&first, SPOOL_RECORD_LEN - 32);
            let second =
                encode_spool_record(scope, market_instance_id, &second, first_checksum).unwrap();
            let mut file = private_options().truncate(true).open(&spool.path).unwrap();
            file.write_all(&first).unwrap();
            file.write_all(&second).unwrap();
            file.sync_all().unwrap();
            spool.path
        }

        let gap_temp = tempfile::tempdir().unwrap();
        write_records(
            gap_temp.path(),
            FinalizedPrivateBazaarReceipt::new(1, 1, receipt(0x41)),
            FinalizedPrivateBazaarReceipt::new(3, 3, receipt(0x43)),
        );
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(gap_temp.path()),
            Err(PrivateBazaarWorkerError::SpoolGap {
                expected: 2,
                found: 3
            })
        ));

        let fork_temp = tempfile::tempdir().unwrap();
        write_records(
            fork_temp.path(),
            FinalizedPrivateBazaarReceipt::new(1, 1, receipt(0x51)),
            FinalizedPrivateBazaarReceipt::new(1, 2, receipt(0x52)),
        );
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(fork_temp.path()),
            Err(PrivateBazaarWorkerError::SpoolFork {
                expected: 2,
                found: 1
            })
        ));

        let corrupt_temp = tempfile::tempdir().unwrap();
        let path = write_records(
            corrupt_temp.path(),
            FinalizedPrivateBazaarReceipt::new(1, 1, receipt(0x61)),
            FinalizedPrivateBazaarReceipt::new(2, 2, receipt(0x62)),
        );
        let mut bytes = fs::read(&path).unwrap();
        bytes[100] ^= 1;
        fs::write(&path, bytes).unwrap();
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(corrupt_temp.path()),
            Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool record checksum"
            ))
        ));
    }

    #[test]
    fn fixed_spool_v2_record_length_is_pinned() {
        assert_eq!(SPOOL_RECORD_LEN, 935);
    }

    #[cfg(unix)]
    #[test]
    fn fixed_spool_refuses_symlinks_hardlinks_and_path_replacement() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let symlink_temp = tempfile::tempdir().unwrap();
        let symlink_root = symlink_temp.path().join("worker");
        fs::create_dir_all(&symlink_root).unwrap();
        let symlink_target = symlink_temp.path().join("attacker-target");
        fs::write(&symlink_target, []).unwrap();
        symlink(&symlink_target, symlink_root.join(SPOOL_FILE_NAME)).unwrap();
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(&symlink_root),
            Err(PrivateBazaarWorkerError::Io {
                operation: "open receipt spool",
                ..
            })
        ));

        let hardlink_temp = tempfile::tempdir().unwrap();
        let hardlink_root = hardlink_temp.path().join("worker");
        fs::create_dir_all(&hardlink_root).unwrap();
        let hardlink_target = hardlink_temp.path().join("attacker-target");
        fs::write(&hardlink_target, []).unwrap();
        fs::set_permissions(&hardlink_target, fs::Permissions::from_mode(0o600)).unwrap();
        fs::hard_link(&hardlink_target, hardlink_root.join(SPOOL_FILE_NAME)).unwrap();
        assert!(matches!(
            PrivateBazaarReceiptSpool::open_test(&hardlink_root),
            Err(PrivateBazaarWorkerError::Corrupt(
                "receipt spool link count is not one"
            ))
        ));

        let replace_temp = tempfile::tempdir().unwrap();
        let replace_root = replace_temp.path().join("worker");
        let mut spool = PrivateBazaarReceiptSpool::open_test(&replace_root).unwrap();
        spool.append(1, 1, receipt(0x71)).unwrap();
        let pinned_path = spool.path.clone();
        let displaced = replace_root.join("displaced-spool");
        fs::rename(&pinned_path, &displaced).unwrap();
        fs::copy(&displaced, &pinned_path).unwrap();
        assert!(matches!(
            spool.poll_bounded(0, 1),
            Err(PrivateBazaarWorkerError::SpoolFileReplaced)
        ));
        assert!(matches!(
            spool.append(2, 2, receipt(0x72)),
            Err(PrivateBazaarWorkerError::SpoolFileReplaced)
        ));
        assert_eq!(
            fs::metadata(&pinned_path).unwrap().len(),
            SPOOL_RECORD_LEN as u64
        );
    }

    #[cfg(unix)]
    #[test]
    fn fixed_spool_serializes_producers_on_the_pinned_inode() {
        use std::sync::mpsc;
        use std::thread;
        use std::time::Duration;

        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("worker");
        let locked = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        let mut writer = PrivateBazaarReceiptSpool::open_test(&root).unwrap();
        locked.file.lock().unwrap();
        let (sent, received) = mpsc::channel();
        let thread = thread::spawn(move || {
            sent.send(writer.append(1, 1, receipt(0x73))).unwrap();
        });
        assert!(received.recv_timeout(Duration::from_millis(100)).is_err());
        locked.file.unlock().unwrap();
        received
            .recv_timeout(Duration::from_secs(5))
            .expect("writer resumes after pinned-inode lock release")
            .unwrap();
        thread.join().unwrap();
    }
}
