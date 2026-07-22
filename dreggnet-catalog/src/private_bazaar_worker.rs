//! Production worker loop for finalized private-Bazaar receipts.
//!
//! Public web/chat controllers never enter this module. A deployment-owned
//! worker polls a bounded out-of-band source, rejoins each finalized private
//! receipt to the exact hosted market and policy-pinned Dungeon target, and
//! publishes only the existing viewer-blind journey status. The worker journal
//! durably binds source cursor -> semantic source -> exact game operation before
//! the authority store can enter `Dispatching`.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use dregg_turn::Finality;
use dregg_types::CellId;
use dreggnet_market::private_bazaar_authority::PrivateBazaarAuthorityPhase;
use dreggnet_market::private_bazaar_game_adapter::{
    PreparedPrivateBazaarXp, PrivateBazaarGameAdapterError,
};
use dreggnet_market::private_bazaar_live_host::PrivateBazaarLiveHostError;
use dreggnet_market::private_clearing::PrivateClearingReceipt;
use dungeon_on_dregg::progression::DungeonWorldCell;

use crate::private_bazaar_live::PrivateBazaarLiveDeployment;

const MAX_POLL_BATCH: usize = 32;
const CLAIM_MAGIC: &[u8; 8] = b"DBWK0001";
const CURSOR_MAGIC: &[u8; 8] = b"DBWC0001";
const CLAIM_DOMAIN: &str = "dregg.private-bazaar-worker-claim.v1";
const CURSOR_DOMAIN: &str = "dregg.private-bazaar-worker-cursor.v1";
const CLAIM_LEN: usize = 8 + 1 + 8 + 8 + (3 * 32) + 32;
const CURSOR_LEN: usize = 8 + 8 + 32;

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
        options.mode(0o600);
    }
    options
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
    NonContiguousCursor {
        expected: u64,
        found: u64,
    },
    CursorOverflow,
    UnfinalizedEvidence,
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
