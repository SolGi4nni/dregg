//! Atomic process-local composition of authenticated fhEgg clearing and the
//! exact source-bound owned-asset crossing.
//!
//! Every fallible market, attestation, replay, ownership, balance, escrow, and
//! provenance check runs before live mutation. The trade executes in a detached
//! [`TradeWorld`] image and the replay guard is cloned and consumed off to the
//! side. The auction lifecycle (`close + reveals + resolve`) is one executor
//! multi-action turn, so its cell effects commit or roll back together. Once
//! that turn lands, installing the already-executed world image, replay image,
//! and in-process auction mirror is infallible.
//!
//! This is a real atomic boundary for one process holding exclusive mutable
//! access to the market, trade world, and cloneable replay guard. The durable
//! entry point adds a strict prepare/commit record and a file-backed CAS journal
//! so a restarted host can classify exact before/after images and idempotently
//! finish only missing phases. The host must restore its market, world, and
//! replay images; this is not a distributed hyperedge spanning independently
//! committed federation and asset ledgers.

use std::collections::BTreeMap;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use dregg_app_framework::{Action as CellAction, TurnReceipt, field_from_u64};
use dreggnet_offerings::DreggIdentity;
use dreggnet_trade::{AssetId, LegSpec, PreparedAtomicSale, Settlement, TradeError, TradeWorld};
use fhegg_fhe::attestation::{
    AttestedClearingReceipt, ComputationIntegrityVerifier, Digest32, ExpectedClearingContext,
    InputDigestKind, ReplayGuard,
};
use starbridge_sealed_auction::{
    Auction, AuctionError, Phase, close_commit_effects, resolve_effects, reveal_bid_effects,
};

use crate::asset_backed::{AssetBackedClearing, AssetBackedError};
use crate::fhegg_settlement::{FheggSettlementError, FheggSettlementReceipt, live_clear};
use crate::{Clearing, DarkBazaarOffering, DarkBazaarSession, GOOD, PAY};

const ATOMIC_AUDIT_DOMAIN: &str = "dreggnet-market/fhegg/atomic-asset-settlement/v1";
const JOURNAL_AUDIT_DOMAIN: &str = "dreggnet-market/fhegg/atomic-journal-audit/v1";
const JOURNAL_CHECKSUM_DOMAIN: &str = "dreggnet-market/fhegg/atomic-journal-wire/v1";
const JOURNAL_FILE_CHECKSUM_DOMAIN: &str = "dreggnet-market/fhegg/atomic-journal-file/v1";
const SOURCE_BOARD_DOMAIN: &str = "dreggnet-market/fhegg/live-sealed-board/v1";
const SOURCE_SESSION_DOMAIN: &str = "dreggnet-market/fhegg/settlement-session/v1";
const JOURNAL_MAGIC: &[u8; 8] = b"FHEGGJ01";
const JOURNAL_VERSION: u8 = 1;
const MAX_JOURNAL_IDENTITY_BYTES: usize = 256;
pub const MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES: usize = 1024;
const JOURNAL_FILE_MAGIC: &[u8; 8] = b"FHEGGFS1";
const JOURNAL_FILE_VERSION: u8 = 1;
pub const MAX_FILE_ATOMIC_SETTLEMENT_RECORDS: usize = 4096;
const MAX_JOURNAL_FILE_BYTES: usize = 8
    + 1
    + 4
    + MAX_FILE_ATOMIC_SETTLEMENT_RECORDS * (32 + 32 + 2 + MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES)
    + 32;

/// Digest-bearing preview supplied to a pre-commit hook after every detached
/// validation succeeds but before any live market/world/replay mutation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicSettlementPreview {
    pub claim_digest: [u8; 32],
    pub source_commitment: [u8; 32],
    pub asset: AssetId,
    pub world_before: [u8; 32],
    pub world_after: [u8; 32],
    pub price: u64,
    pub seller: DreggIdentity,
    pub winner: DreggIdentity,
}

/// Optional host hook for journal reservation or deterministic fault injection.
/// A refusal here is guaranteed to precede every live state mutation.
pub trait AtomicSettlementCommitHook {
    fn before_commit(&mut self, preview: &AtomicSettlementPreview) -> Result<(), String>;
}

#[derive(Default)]
pub struct NoopAtomicSettlementHook;

impl AtomicSettlementCommitHook for NoopAtomicSettlementHook {
    fn before_commit(&mut self, _preview: &AtomicSettlementPreview) -> Result<(), String> {
        Ok(())
    }
}

/// Complete evidence for the indivisible process-local clear + asset/value
/// cross. `audit_digest` binds the fhEgg claim, source board, listing asset,
/// auction turn receipt, identities, price, and before/after trade-world images.
#[derive(Clone, Debug)]
pub struct AtomicFheggAssetSettlementReceipt {
    pub fhegg: FheggSettlementReceipt,
    pub asset: AssetBackedClearing,
    pub world_before: [u8; 32],
    pub world_after: [u8; 32],
    pub audit_digest: [u8; 32],
    /// Present for the durable API. This additionally binds the transaction id,
    /// replay id, expected market turn, and journal phase transition.
    pub journal_audit: Option<AtomicFheggAssetSettlementAudit>,
}

/// Canonical bounded audit plan retained by the durable prepare/commit journal.
/// `market_receipt_hash` is absent only in the prepare record, before the
/// executor has produced timestamped receipt evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicFheggAssetSettlementAudit {
    pub transaction_id: Digest32,
    pub replay_id: Digest32,
    pub claim_digest: Digest32,
    pub source_commitment: Digest32,
    pub asset: AssetId,
    pub world_before: Digest32,
    pub world_after: Digest32,
    pub market_receipts_before: u32,
    pub price: u64,
    pub seller: DreggIdentity,
    pub winner: DreggIdentity,
    pub market_turn_hash: Digest32,
    pub market_receipt_hash: Option<Digest32>,
}

impl AtomicFheggAssetSettlementAudit {
    pub fn digest(&self) -> Digest32 {
        let mut hasher = blake3::Hasher::new_derive_key(JOURNAL_AUDIT_DOMAIN);
        hasher.update(&self.transaction_id);
        hasher.update(&self.replay_id);
        hasher.update(&self.claim_digest);
        hasher.update(&self.source_commitment);
        hasher.update(&self.asset.0);
        hasher.update(&self.world_before);
        hasher.update(&self.world_after);
        hasher.update(&self.market_receipts_before.to_be_bytes());
        hasher.update(&self.price.to_be_bytes());
        hash_bounded_identity(&mut hasher, &self.seller);
        hash_bounded_identity(&mut hasher, &self.winner);
        hasher.update(&self.market_turn_hash);
        match self.market_receipt_hash {
            Some(receipt) => {
                hasher.update(&[1]);
                hasher.update(&receipt);
            }
            None => {
                hasher.update(&[0]);
            }
        }
        *hasher.finalize().as_bytes()
    }

    fn validate(&self) -> Result<(), AtomicSettlementJournalError> {
        if self.seller.0.is_empty()
            || self.seller.0.len() > MAX_JOURNAL_IDENTITY_BYTES
            || self.winner.0.is_empty()
            || self.winner.0.len() > MAX_JOURNAL_IDENTITY_BYTES
        {
            return Err(AtomicSettlementJournalError::IdentityOutOfBounds);
        }
        if self.world_before == self.world_after {
            return Err(AtomicSettlementJournalError::DegenerateWorldTransition);
        }
        Ok(())
    }
}

fn hash_bounded_identity(hasher: &mut blake3::Hasher, identity: &DreggIdentity) {
    hasher.update(&(identity.0.len() as u16).to_be_bytes());
    hasher.update(identity.0.as_bytes());
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AtomicSettlementJournalPhase {
    Prepared = 0,
    MarketApplied = 1,
    WorldApplied = 2,
    Committed = 3,
}

/// Strict on-disk value. The checksum detects torn/corrupt bytes; rollback
/// resistance and atomicity of compare-and-swap belong to the storage trait.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicSettlementJournalRecord {
    pub phase: AtomicSettlementJournalPhase,
    pub audit: AtomicFheggAssetSettlementAudit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicSettlementJournalError {
    Storage(String),
    MalformedWire,
    ChecksumMismatch,
    NonCanonicalPhase,
    IdentityOutOfBounds,
    DegenerateWorldTransition,
    CompareExchangeConflict,
    ReplayReservationConflict,
    LiveStateMismatch(&'static str),
}

impl fmt::Display for AtomicSettlementJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Storage(reason) => write!(f, "journal storage failed: {reason}"),
            Self::MalformedWire => write!(f, "malformed atomic-settlement journal bytes"),
            Self::ChecksumMismatch => write!(f, "atomic-settlement journal checksum mismatch"),
            Self::NonCanonicalPhase => {
                write!(f, "journal phase/audit combination is non-canonical")
            }
            Self::IdentityOutOfBounds => {
                write!(f, "journal identity is empty or exceeds 256 bytes")
            }
            Self::DegenerateWorldTransition => write!(f, "journal world transition is degenerate"),
            Self::CompareExchangeConflict => write!(f, "journal compare-and-swap conflict"),
            Self::ReplayReservationConflict => {
                write!(f, "replay id is reserved by another transaction")
            }
            Self::LiveStateMismatch(reason) => write!(f, "journal/live-state mismatch: {reason}"),
        }
    }
}

impl std::error::Error for AtomicSettlementJournalError {}

impl AtomicSettlementJournalRecord {
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, AtomicSettlementJournalError> {
        self.audit.validate()?;
        if matches!(self.phase, AtomicSettlementJournalPhase::Prepared)
            != self.audit.market_receipt_hash.is_none()
        {
            return Err(AtomicSettlementJournalError::NonCanonicalPhase);
        }
        let mut out = Vec::with_capacity(MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES);
        out.extend_from_slice(JOURNAL_MAGIC);
        out.push(JOURNAL_VERSION);
        out.push(self.phase as u8);
        for field in [
            self.audit.transaction_id,
            self.audit.replay_id,
            self.audit.claim_digest,
            self.audit.source_commitment,
            self.audit.asset.0,
            self.audit.world_before,
            self.audit.world_after,
        ] {
            out.extend_from_slice(&field);
        }
        out.extend_from_slice(&self.audit.market_receipts_before.to_be_bytes());
        out.extend_from_slice(&self.audit.price.to_be_bytes());
        encode_identity(&mut out, &self.audit.seller);
        encode_identity(&mut out, &self.audit.winner);
        out.extend_from_slice(&self.audit.market_turn_hash);
        match self.audit.market_receipt_hash {
            Some(receipt) => {
                out.push(1);
                out.extend_from_slice(&receipt);
            }
            None => out.push(0),
        }
        let checksum = blake3::derive_key(JOURNAL_CHECKSUM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        if out.len() > MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES {
            return Err(AtomicSettlementJournalError::MalformedWire);
        }
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, AtomicSettlementJournalError> {
        if bytes.len() < 8 + 2 + 7 * 32 + 4 + 8 + 2 + 1 + 2 + 1 + 32 + 1 + 32
            || bytes.len() > MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES
        {
            return Err(AtomicSettlementJournalError::MalformedWire);
        }
        let (body, encoded_checksum) = bytes.split_at(bytes.len() - 32);
        if blake3::derive_key(JOURNAL_CHECKSUM_DOMAIN, body) != encoded_checksum {
            return Err(AtomicSettlementJournalError::ChecksumMismatch);
        }
        let mut cursor = JournalCursor::new(body);
        if cursor.take::<8>()? != *JOURNAL_MAGIC || cursor.byte()? != JOURNAL_VERSION {
            return Err(AtomicSettlementJournalError::MalformedWire);
        }
        let phase = match cursor.byte()? {
            0 => AtomicSettlementJournalPhase::Prepared,
            1 => AtomicSettlementJournalPhase::MarketApplied,
            2 => AtomicSettlementJournalPhase::WorldApplied,
            3 => AtomicSettlementJournalPhase::Committed,
            _ => return Err(AtomicSettlementJournalError::NonCanonicalPhase),
        };
        let transaction_id = cursor.take()?;
        let replay_id = cursor.take()?;
        let claim_digest = cursor.take()?;
        let source_commitment = cursor.take()?;
        let asset = AssetId(cursor.take()?);
        let world_before = cursor.take()?;
        let world_after = cursor.take()?;
        let market_receipts_before = u32::from_be_bytes(cursor.take()?);
        let price = u64::from_be_bytes(cursor.take()?);
        let seller = cursor.identity()?;
        let winner = cursor.identity()?;
        let market_turn_hash = cursor.take()?;
        let market_receipt_hash = match cursor.byte()? {
            0 => None,
            1 => Some(cursor.take()?),
            _ => return Err(AtomicSettlementJournalError::MalformedWire),
        };
        if !cursor.finished() {
            return Err(AtomicSettlementJournalError::MalformedWire);
        }
        let record = Self {
            phase,
            audit: AtomicFheggAssetSettlementAudit {
                transaction_id,
                replay_id,
                claim_digest,
                source_commitment,
                asset,
                world_before,
                world_after,
                market_receipts_before,
                price,
                seller,
                winner,
                market_turn_hash,
                market_receipt_hash,
            },
        };
        record.audit.validate()?;
        if matches!(record.phase, AtomicSettlementJournalPhase::Prepared)
            != record.audit.market_receipt_hash.is_none()
        {
            return Err(AtomicSettlementJournalError::NonCanonicalPhase);
        }
        Ok(record)
    }
}

fn encode_identity(out: &mut Vec<u8>, identity: &DreggIdentity) {
    out.extend_from_slice(&(identity.0.len() as u16).to_be_bytes());
    out.extend_from_slice(identity.0.as_bytes());
}

struct JournalCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> JournalCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], AtomicSettlementJournalError> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(AtomicSettlementJournalError::MalformedWire)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(AtomicSettlementJournalError::MalformedWire)?;
        self.offset = end;
        value
            .try_into()
            .map_err(|_| AtomicSettlementJournalError::MalformedWire)
    }

    fn byte(&mut self) -> Result<u8, AtomicSettlementJournalError> {
        Ok(self.take::<1>()?[0])
    }

    fn identity(&mut self) -> Result<DreggIdentity, AtomicSettlementJournalError> {
        let length = u16::from_be_bytes(self.take()?) as usize;
        if length == 0 || length > MAX_JOURNAL_IDENTITY_BYTES {
            return Err(AtomicSettlementJournalError::IdentityOutOfBounds);
        }
        let end = self
            .offset
            .checked_add(length)
            .ok_or(AtomicSettlementJournalError::MalformedWire)?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or(AtomicSettlementJournalError::MalformedWire)?;
        self.offset = end;
        let identity =
            std::str::from_utf8(bytes).map_err(|_| AtomicSettlementJournalError::MalformedWire)?;
        Ok(DreggIdentity(identity.to_owned()))
    }

    fn finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

/// Typed result of one journal compare-and-swap attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicSettlementCasOutcome {
    Applied,
    Unchanged,
    ReplayReservationConflict,
}

/// Durable storage boundary. `compare_exchange` must atomically persist the
/// replacement and, on initial insert, reserve `replay_id` globally so a second
/// transaction cannot prepare the same fhEgg session under another id. Every
/// non-`Applied` outcome must leave durable bytes unchanged.
pub trait AtomicSettlementJournal {
    fn load(&self, transaction_id: Digest32) -> Result<Option<Vec<u8>>, String>;

    fn compare_exchange(
        &mut self,
        transaction_id: Digest32,
        replay_id: Digest32,
        expected: Option<&[u8]>,
        replacement: &[u8],
    ) -> Result<AtomicSettlementCasOutcome, String>;
}

/// Restart-safe implementation of [`AtomicSettlementJournal`] backed by one
/// canonical snapshot file.
///
/// Every mutation takes an OS advisory lock, checks the expected bytes and the
/// global replay reservation in one in-memory image, then persists that whole
/// image with write + `fsync` + atomic rename + directory `fsync`. Because the
/// lock is held on a separate inode it survives replacement of the state file,
/// and the kernel releases it if the process dies. A leftover temporary file is
/// never read; the next lock holder removes it and creates a fresh sibling.
///
/// This makes the journal itself durable and CAS-safe across cooperating host
/// processes. The market, trade-world, and replay implementations remain the
/// host's responsibility to restore before calling settlement recovery. The
/// snapshot deliberately caps retained transactions at
/// [`MAX_FILE_ATOMIC_SETTLEMENT_RECORDS`]; archival/rotation must retain replay
/// protection in rollback-resistant host state.
#[derive(Clone, Debug)]
pub struct FileAtomicSettlementJournal {
    root: PathBuf,
}

impl FileAtomicSettlementJournal {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, String> {
        let root = root.as_ref().to_path_buf();
        std::fs::create_dir_all(&root).map_err(|error| error.to_string())?;
        let root = std::fs::canonicalize(root).map_err(|error| error.to_string())?;
        let root_dir = File::open(&root).map_err(|error| error.to_string())?;
        root_dir.sync_all().map_err(|error| error.to_string())?;
        Ok(Self { root })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    fn state_path(&self) -> PathBuf {
        self.root.join("atomic-settlements.bin")
    }

    fn temporary_path(&self) -> PathBuf {
        self.root.join("atomic-settlements.tmp")
    }

    fn lock_path(&self) -> PathBuf {
        self.root.join("atomic-settlements.lock")
    }

    fn with_exclusive_lock<T>(
        &self,
        operation: impl FnOnce(&Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let lock_file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(self.lock_path())
            .map_err(|error| error.to_string())?;
        lock_file.lock().map_err(|error| error.to_string())?;
        let result = operation(self);
        let unlock = lock_file.unlock().map_err(|error| error.to_string());
        match (result, unlock) {
            (Ok(value), Ok(())) => Ok(value),
            (Err(error), _) => Err(error),
            (Ok(_), Err(error)) => Err(error),
        }
    }

    fn read_state_unlocked(&self) -> Result<BTreeMap<Digest32, (Digest32, Vec<u8>)>, String> {
        let path = self.state_path();
        let mut file = match File::open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                return Ok(BTreeMap::new());
            }
            Err(error) => return Err(error.to_string()),
        };
        let length = usize::try_from(file.metadata().map_err(|error| error.to_string())?.len())
            .map_err(|_| "journal snapshot length exceeds usize".to_owned())?;
        if length > MAX_JOURNAL_FILE_BYTES {
            return Err("journal snapshot exceeds its fixed bound".into());
        }
        let mut wire = Vec::with_capacity(length);
        Read::by_ref(&mut file)
            .take((MAX_JOURNAL_FILE_BYTES + 1) as u64)
            .read_to_end(&mut wire)
            .map_err(|error| error.to_string())?;
        if wire.len() > MAX_JOURNAL_FILE_BYTES {
            return Err("journal snapshot exceeds its fixed bound".into());
        }
        decode_journal_file(&wire)
    }

    fn write_state_unlocked(
        &self,
        state: &BTreeMap<Digest32, (Digest32, Vec<u8>)>,
    ) -> Result<(), String> {
        let wire = encode_journal_file(state)?;
        let temporary = self.temporary_path();
        match std::fs::remove_file(&temporary) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.to_string()),
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|error| error.to_string())?;
        file.write_all(&wire).map_err(|error| error.to_string())?;
        file.sync_all().map_err(|error| error.to_string())?;
        std::fs::rename(&temporary, self.state_path()).map_err(|error| error.to_string())?;
        File::open(&self.root)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| error.to_string())
    }
}

impl AtomicSettlementJournal for FileAtomicSettlementJournal {
    fn load(&self, transaction_id: Digest32) -> Result<Option<Vec<u8>>, String> {
        self.with_exclusive_lock(|journal| {
            Ok(journal
                .read_state_unlocked()?
                .get(&transaction_id)
                .map(|(_, record)| record.clone()))
        })
    }

    fn compare_exchange(
        &mut self,
        transaction_id: Digest32,
        replay_id: Digest32,
        expected: Option<&[u8]>,
        replacement: &[u8],
    ) -> Result<AtomicSettlementCasOutcome, String> {
        let decoded = AtomicSettlementJournalRecord::from_wire_bytes(replacement)
            .map_err(|error| error.to_string())?;
        if decoded.audit.transaction_id != transaction_id || decoded.audit.replay_id != replay_id {
            return Err("replacement key mismatch".into());
        }
        self.with_exclusive_lock(|journal| {
            let mut state = journal.read_state_unlocked()?;
            match expected {
                None => {
                    if state.contains_key(&transaction_id) {
                        return Ok(AtomicSettlementCasOutcome::Unchanged);
                    }
                    if state.values().any(|(reserved, _)| *reserved == replay_id) {
                        return Ok(AtomicSettlementCasOutcome::ReplayReservationConflict);
                    }
                }
                Some(expected) => {
                    let Some((reserved, current)) = state.get(&transaction_id) else {
                        return Ok(AtomicSettlementCasOutcome::Unchanged);
                    };
                    if reserved != &replay_id || current.as_slice() != expected {
                        return Ok(AtomicSettlementCasOutcome::Unchanged);
                    }
                }
            }
            state.insert(transaction_id, (replay_id, replacement.to_vec()));
            journal.write_state_unlocked(&state)?;
            Ok(AtomicSettlementCasOutcome::Applied)
        })
    }
}

fn encode_journal_file(state: &BTreeMap<Digest32, (Digest32, Vec<u8>)>) -> Result<Vec<u8>, String> {
    if state.len() > MAX_FILE_ATOMIC_SETTLEMENT_RECORDS {
        return Err("journal snapshot contains too many records".into());
    }
    let mut wire = Vec::new();
    wire.extend_from_slice(JOURNAL_FILE_MAGIC);
    wire.push(JOURNAL_FILE_VERSION);
    wire.extend_from_slice(&(state.len() as u32).to_be_bytes());
    let mut replay_ids = BTreeMap::new();
    for (transaction_id, (replay_id, record)) in state {
        if record.len() > MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES {
            return Err("journal record exceeds its fixed bound".into());
        }
        let decoded = AtomicSettlementJournalRecord::from_wire_bytes(record)
            .map_err(|error| error.to_string())?;
        if decoded.audit.transaction_id != *transaction_id || decoded.audit.replay_id != *replay_id
        {
            return Err("journal record key mismatch".into());
        }
        if replay_ids.insert(*replay_id, *transaction_id).is_some() {
            return Err("duplicate replay reservation in journal snapshot".into());
        }
        wire.extend_from_slice(transaction_id);
        wire.extend_from_slice(replay_id);
        wire.extend_from_slice(&(record.len() as u16).to_be_bytes());
        wire.extend_from_slice(record);
    }
    let checksum = blake3::derive_key(JOURNAL_FILE_CHECKSUM_DOMAIN, &wire);
    wire.extend_from_slice(&checksum);
    if wire.len() > MAX_JOURNAL_FILE_BYTES {
        return Err("journal snapshot exceeds its fixed bound".into());
    }
    Ok(wire)
}

fn decode_journal_file(wire: &[u8]) -> Result<BTreeMap<Digest32, (Digest32, Vec<u8>)>, String> {
    if wire.len() < JOURNAL_FILE_MAGIC.len() + 1 + 4 + 32 || wire.len() > MAX_JOURNAL_FILE_BYTES {
        return Err("malformed journal snapshot length".into());
    }
    let (body, checksum) = wire.split_at(wire.len() - 32);
    if blake3::derive_key(JOURNAL_FILE_CHECKSUM_DOMAIN, body).as_slice() != checksum {
        return Err("journal snapshot checksum mismatch".into());
    }
    let mut cursor = JournalCursor::new(body);
    if cursor.take::<8>().map_err(|error| error.to_string())? != *JOURNAL_FILE_MAGIC
        || cursor.byte().map_err(|error| error.to_string())? != JOURNAL_FILE_VERSION
    {
        return Err("unsupported journal snapshot format".into());
    }
    let count = u32::from_be_bytes(cursor.take().map_err(|error| error.to_string())?) as usize;
    if count > MAX_FILE_ATOMIC_SETTLEMENT_RECORDS {
        return Err("journal snapshot contains too many records".into());
    }
    let mut state = BTreeMap::new();
    let mut replay_ids = BTreeMap::new();
    let mut previous = None;
    for _ in 0..count {
        let transaction_id = cursor.take().map_err(|error| error.to_string())?;
        let replay_id = cursor.take().map_err(|error| error.to_string())?;
        if previous.is_some_and(|prior| prior >= transaction_id) {
            return Err("journal snapshot keys are not canonical".into());
        }
        previous = Some(transaction_id);
        let length = u16::from_be_bytes(cursor.take().map_err(|error| error.to_string())?) as usize;
        if length == 0 || length > MAX_ATOMIC_SETTLEMENT_JOURNAL_BYTES {
            return Err("journal record length is out of bounds".into());
        }
        let end = cursor
            .offset
            .checked_add(length)
            .ok_or_else(|| "malformed journal snapshot".to_owned())?;
        let record = cursor
            .bytes
            .get(cursor.offset..end)
            .ok_or_else(|| "malformed journal snapshot".to_owned())?
            .to_vec();
        cursor.offset = end;
        let decoded = AtomicSettlementJournalRecord::from_wire_bytes(&record)
            .map_err(|error| error.to_string())?;
        if decoded.audit.transaction_id != transaction_id || decoded.audit.replay_id != replay_id {
            return Err("journal record key mismatch".into());
        }
        if replay_ids.insert(replay_id, transaction_id).is_some() {
            return Err("duplicate replay reservation in journal snapshot".into());
        }
        state.insert(transaction_id, (replay_id, record));
    }
    if !cursor.finished() {
        return Err("journal snapshot has trailing bytes".into());
    }
    Ok(state)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicSettlementCrashPoint {
    AfterPrepared,
    AfterMarketApplied,
    AfterWorldApplied,
    AfterReplayApplied,
    AfterCommitted,
}

pub trait AtomicSettlementCrashInjector {
    fn checkpoint(&mut self, point: AtomicSettlementCrashPoint) -> Result<(), String>;
}

#[derive(Default)]
pub struct NoAtomicSettlementCrash;

impl AtomicSettlementCrashInjector for NoAtomicSettlementCrash {
    fn checkpoint(&mut self, _point: AtomicSettlementCrashPoint) -> Result<(), String> {
        Ok(())
    }
}

impl AtomicFheggAssetSettlementReceipt {
    /// Recompute the public cross-domain audit commitment from the receipt's
    /// exact fhEgg, listing-asset, identity, price, executor-turn, and world
    /// transition fields.
    pub fn recompute_audit_digest(&self) -> [u8; 32] {
        atomic_audit_digest(
            &AtomicSettlementPreview {
                claim_digest: self.fhegg.claim_digest,
                source_commitment: self.fhegg.source_commitment,
                asset: self.asset.asset,
                world_before: self.world_before,
                world_after: self.world_after,
                price: self.asset.price,
                seller: self.asset.seller.clone(),
                winner: self.asset.winner.clone(),
            },
            &self.fhegg,
        )
    }

    /// Whether the receipt still carries its originally committed audit image.
    pub fn audit_digest_verifies(&self) -> bool {
        self.audit_digest == self.recompute_audit_digest()
    }
}

#[derive(Debug)]
pub enum AtomicFheggAssetSettlementError {
    Settlement(FheggSettlementError),
    Asset(AssetBackedError),
    Trade(TradeError),
    StalePreparedWorld,
    PreCommitRefused(String),
    Journal(AtomicSettlementJournalError),
    SimulatedCrash {
        point: AtomicSettlementCrashPoint,
        reason: String,
    },
}

impl fmt::Display for AtomicFheggAssetSettlementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Settlement(error) => write!(f, "atomic fhEgg settlement refused: {error}"),
            Self::Asset(error) => write!(f, "atomic fhEgg asset join refused: {error}"),
            Self::Trade(error) => write!(f, "atomic fhEgg trade refused: {error}"),
            Self::StalePreparedWorld => {
                write!(
                    f,
                    "the trade world changed after its atomic sale was prepared"
                )
            }
            Self::PreCommitRefused(reason) => write!(f, "atomic pre-commit refused: {reason}"),
            Self::Journal(error) => write!(f, "durable atomic settlement refused: {error}"),
            Self::SimulatedCrash { point, reason } => {
                write!(f, "simulated crash at {point:?}: {reason}")
            }
        }
    }
}

impl std::error::Error for AtomicFheggAssetSettlementError {}

impl From<FheggSettlementError> for AtomicFheggAssetSettlementError {
    fn from(value: FheggSettlementError) -> Self {
        Self::Settlement(value)
    }
}

impl From<TradeError> for AtomicFheggAssetSettlementError {
    fn from(value: TradeError) -> Self {
        Self::Trade(value)
    }
}

impl From<AtomicSettlementJournalError> for AtomicFheggAssetSettlementError {
    fn from(value: AtomicSettlementJournalError) -> Self {
        Self::Journal(value)
    }
}

struct PreparedMarketClear {
    auction: Auction,
    clearing: Clearing,
    actions: Vec<CellAction>,
}

impl DarkBazaarOffering {
    /// Verify and commit the authenticated clearing and exact owned-asset sale
    /// as one process-local transaction.
    pub fn settle_fhegg_asset_atomic<V, R>(
        &self,
        session: &mut DarkBazaarSession,
        world: &mut TradeWorld,
        asset: AssetId,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
    ) -> Result<AtomicFheggAssetSettlementReceipt, AtomicFheggAssetSettlementError>
    where
        V: ComputationIntegrityVerifier,
        R: ReplayGuard + Clone,
    {
        self.settle_fhegg_asset_atomic_with_hook(
            session,
            world,
            asset,
            receipt,
            expected,
            verifier,
            replay_guard,
            &mut NoopAtomicSettlementHook,
        )
    }

    /// Hook-bearing form used by durable hosts and rollback/fault-injection
    /// tests. The hook fires after detached execution and before live commit.
    #[allow(clippy::too_many_arguments)]
    pub fn settle_fhegg_asset_atomic_with_hook<V, R, H>(
        &self,
        session: &mut DarkBazaarSession,
        world: &mut TradeWorld,
        asset: AssetId,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
        hook: &mut H,
    ) -> Result<AtomicFheggAssetSettlementReceipt, AtomicFheggAssetSettlementError>
    where
        V: ComputationIntegrityVerifier,
        R: ReplayGuard + Clone,
        H: AtomicSettlementCommitHook,
    {
        let live = live_clear(session)?;
        let source_commitment = session.fhegg_source_commitment()?;
        if expected.session.nonce() != session.fhegg_settlement_session_nonce()? {
            return Err(FheggSettlementError::SessionMismatch.into());
        }
        let found = expected
            .ordered_inputs
            .iter()
            .filter(|input| {
                input.kind == InputDigestKind::Commitment && input.digest == source_commitment
            })
            .count();
        if found != 1 {
            return Err(FheggSettlementError::SourceCommitmentCount { found }.into());
        }
        session.verify_fhegg_source_bfv_identity(expected.bfv, expected.session.buckets())?;
        session.verify_fhegg_bound_order_inputs(expected.ordered_inputs)?;
        if expected.crossing.p_star != Some(live.price as usize) || expected.crossing.v_star != 1 {
            return Err(FheggSettlementError::ResultMismatch {
                expected_price: live.price,
                claimed_price: expected.crossing.p_star,
                claimed_volume: expected.crossing.v_star,
            }
            .into());
        }

        let listing_source = session
            .market
            .fhegg_listing_source
            .ok_or(FheggSettlementError::UnboundListingSource)?;
        if listing_source.asset != asset.0 {
            return Err(AtomicFheggAssetSettlementError::Asset(
                AssetBackedError::SourceAssetMismatch {
                    expected: AssetId(listing_source.asset),
                    provided: asset,
                },
            ));
        }
        let seller = session
            .market
            .seller
            .clone()
            .ok_or(FheggSettlementError::NotListed)?;

        // Replay consumption is staged in a clone. A later trade/hook/executor
        // refusal drops it, so a failed atomic attempt never burns the claim.
        let mut staged_replay = replay_guard.clone();
        receipt
            .verify_full(expected, verifier, &mut staged_replay)
            .map_err(FheggSettlementError::Attestation)?;

        let prepared_market = prepare_market_clear(session)?;
        let prepared_sale =
            world.prepare_atomic_sale(seller.as_str(), live.winner.as_str(), asset, live.price)?;
        let preview = AtomicSettlementPreview {
            claim_digest: receipt.claim_digest(),
            source_commitment,
            asset,
            world_before: prepared_sale.before_digest(),
            world_after: prepared_sale.after_digest(),
            price: live.price,
            seller: seller.clone(),
            winner: live.winner.clone(),
        };
        hook.before_commit(&preview)
            .map_err(AtomicFheggAssetSettlementError::PreCommitRefused)?;
        if !prepared_sale.is_fresh_for(world) {
            return Err(AtomicFheggAssetSettlementError::StalePreparedWorld);
        }

        // One real executor turn contains every auction lifecycle action. The
        // executor journals all touched cells and rolls the whole forest back
        // if any root/effect/predicate fails.
        let turn = session
            .market
            .cclerk
            .make_turn_with_actions(prepared_market.actions);
        let settlement_turn = session
            .market
            .executor
            .submit_turn(&turn)
            .map_err(|error| {
                AtomicFheggAssetSettlementError::Settlement(
                    FheggSettlementError::SettlementRefused(error.to_string()),
                )
            })?;

        // Everything below is ownership replacement/assignment from already
        // validated values and therefore has no refusal path.
        session.market.auction = Some(prepared_market.auction);
        session.market.clearing = Some(prepared_market.clearing);
        session.market.receipts.push(settlement_turn.clone());
        let sale = prepared_sale.commit(world);
        *replay_guard = staged_replay;

        let asset_clearing = AssetBackedClearing {
            asset,
            seller: seller.clone(),
            winner: live.winner.clone(),
            price: live.price,
            settlement: sale.settlement,
            provenance: sale.provenance,
        };
        let fhegg = FheggSettlementReceipt {
            claim_digest: receipt.claim_digest(),
            source_commitment,
            price: live.price,
            volume: 1,
            winner: live.winner,
            settlement_turn,
        };
        let audit_digest = atomic_audit_digest(&preview, &fhegg);
        Ok(AtomicFheggAssetSettlementReceipt {
            fhegg,
            asset: asset_clearing,
            world_before: sale.before_digest,
            world_after: sale.after_digest,
            audit_digest,
            journal_audit: None,
        })
    }

    /// Crash-recoverable form of the process-local atomic settlement.
    ///
    /// The journal's initial CAS both persists the bounded prepare record and
    /// reserves the fhEgg replay id. Recovery then classifies each live domain
    /// by its exact before/after digest before advancing one phase. Repeating
    /// this call after any successful checkpoint is idempotent.
    ///
    /// This protocol assumes one host owns the mutable market, trade world,
    /// replay guard, and journal namespace. It repairs process crashes; it is
    /// not a distributed transaction across independently committing ledgers.
    #[allow(clippy::too_many_arguments)]
    pub fn settle_fhegg_asset_atomic_durable<V, R, J, C>(
        &self,
        transaction_id: Digest32,
        session: &mut DarkBazaarSession,
        world: &mut TradeWorld,
        asset: AssetId,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
        journal: &mut J,
        crash: &mut C,
    ) -> Result<AtomicFheggAssetSettlementReceipt, AtomicFheggAssetSettlementError>
    where
        V: ComputationIntegrityVerifier,
        R: ReplayGuard + Clone,
        J: AtomicSettlementJournal,
        C: AtomicSettlementCrashInjector,
    {
        if journal_load(journal, transaction_id)?.is_none() {
            let audit = prepare_durable_audit(
                transaction_id,
                session,
                world,
                asset,
                receipt,
                expected,
                verifier,
                replay_guard,
            )?;
            let prepared = AtomicSettlementJournalRecord {
                phase: AtomicSettlementJournalPhase::Prepared,
                audit,
            };
            journal_initial_insert(journal, &prepared)?;
            crash_checkpoint(crash, AtomicSettlementCrashPoint::AfterPrepared)?;
        }

        loop {
            let encoded = journal_load(journal, transaction_id)?.ok_or(
                AtomicSettlementJournalError::LiveStateMismatch(
                    "prepared journal record disappeared",
                ),
            )?;
            let record = AtomicSettlementJournalRecord::from_wire_bytes(&encoded)?;
            if record.audit.transaction_id != transaction_id || record.audit.asset != asset {
                return Err(AtomicSettlementJournalError::LiveStateMismatch(
                    "transaction id or requested asset differs from the reserved prepare record",
                )
                .into());
            }
            let replay_id = validate_recovery_context(
                session,
                asset,
                receipt,
                expected,
                verifier,
                &record.audit,
            )?;
            if replay_id != record.audit.replay_id {
                return Err(AtomicSettlementJournalError::LiveStateMismatch(
                    "receipt replay id differs from the prepare record",
                )
                .into());
            }

            let market = classify_market_state(session, &record.audit)?;
            let world_state = classify_world_state(world, &record.audit)?;
            match record.phase {
                AtomicSettlementJournalPhase::Prepared => {
                    if !replay_is_fresh(replay_guard, replay_id) {
                        return Err(AtomicSettlementJournalError::LiveStateMismatch(
                            "replay was consumed before the world phase",
                        )
                        .into());
                    }
                    let market_receipt = match market {
                        MarketJournalState::Before => {
                            if world_state != WorldJournalState::Before {
                                return Err(AtomicSettlementJournalError::LiveStateMismatch(
                                    "world advanced before the market phase",
                                )
                                .into());
                            }
                            commit_market_from_audit(session, world, &record.audit)?
                        }
                        MarketJournalState::After(receipt) => {
                            if world_state != WorldJournalState::Before {
                                return Err(AtomicSettlementJournalError::LiveStateMismatch(
                                    "prepared record observed a market/world phase split it cannot classify",
                                )
                                .into());
                            }
                            receipt
                        }
                    };
                    let mut promoted = record.audit.clone();
                    promoted.market_receipt_hash = Some(market_receipt.receipt_hash());
                    crash_checkpoint(crash, AtomicSettlementCrashPoint::AfterMarketApplied)?;
                    journal_advance(
                        journal,
                        &encoded,
                        AtomicSettlementJournalRecord {
                            phase: AtomicSettlementJournalPhase::MarketApplied,
                            audit: promoted,
                        },
                    )?;
                }
                AtomicSettlementJournalPhase::MarketApplied => {
                    if !matches!(market, MarketJournalState::After(_)) {
                        return Err(AtomicSettlementJournalError::LiveStateMismatch(
                            "journal says market applied but market is still before",
                        )
                        .into());
                    }
                    match world_state {
                        WorldJournalState::Before => {
                            let sale = prepare_sale_from_audit(world, &record.audit)?;
                            sale.commit(world);
                        }
                        WorldJournalState::After => {}
                    }
                    crash_checkpoint(crash, AtomicSettlementCrashPoint::AfterWorldApplied)?;
                    journal_advance(
                        journal,
                        &encoded,
                        AtomicSettlementJournalRecord {
                            phase: AtomicSettlementJournalPhase::WorldApplied,
                            audit: record.audit,
                        },
                    )?;
                }
                AtomicSettlementJournalPhase::WorldApplied => {
                    let market_receipt = match market {
                        MarketJournalState::After(receipt) => receipt,
                        MarketJournalState::Before => {
                            return Err(AtomicSettlementJournalError::LiveStateMismatch(
                                "journal says world applied but market is still before",
                            )
                            .into());
                        }
                    };
                    if world_state != WorldJournalState::After {
                        return Err(AtomicSettlementJournalError::LiveStateMismatch(
                            "journal says world applied but world is still before",
                        )
                        .into());
                    }
                    if replay_is_fresh(replay_guard, replay_id)
                        && !replay_guard.check_and_record(replay_id)
                    {
                        return Err(AtomicSettlementJournalError::LiveStateMismatch(
                            "replay changed concurrently during recovery",
                        )
                        .into());
                    }
                    crash_checkpoint(crash, AtomicSettlementCrashPoint::AfterReplayApplied)?;
                    let completed = AtomicSettlementJournalRecord {
                        phase: AtomicSettlementJournalPhase::Committed,
                        audit: record.audit.clone(),
                    };
                    journal_advance(journal, &encoded, completed.clone())?;
                    crash_checkpoint(crash, AtomicSettlementCrashPoint::AfterCommitted)?;
                    return receipt_from_recovered_state(world, &completed.audit, market_receipt);
                }
                AtomicSettlementJournalPhase::Committed => {
                    let market_receipt = match market {
                        MarketJournalState::After(receipt) => receipt,
                        MarketJournalState::Before => {
                            return Err(AtomicSettlementJournalError::LiveStateMismatch(
                                "committed journal has an unapplied market",
                            )
                            .into());
                        }
                    };
                    if world_state != WorldJournalState::After {
                        return Err(AtomicSettlementJournalError::LiveStateMismatch(
                            "committed journal has an unapplied world",
                        )
                        .into());
                    }
                    if replay_is_fresh(replay_guard, replay_id) {
                        return Err(AtomicSettlementJournalError::LiveStateMismatch(
                            "committed journal has an unconsumed replay id",
                        )
                        .into());
                    }
                    return receipt_from_recovered_state(world, &record.audit, market_receipt);
                }
            }
        }
    }

    /// Durable settlement without a failure-injection hook.
    #[allow(clippy::too_many_arguments)]
    pub fn settle_fhegg_asset_atomic_recover<V, R, J>(
        &self,
        transaction_id: Digest32,
        session: &mut DarkBazaarSession,
        world: &mut TradeWorld,
        asset: AssetId,
        receipt: &AttestedClearingReceipt,
        expected: &ExpectedClearingContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
        journal: &mut J,
    ) -> Result<AtomicFheggAssetSettlementReceipt, AtomicFheggAssetSettlementError>
    where
        V: ComputationIntegrityVerifier,
        R: ReplayGuard + Clone,
        J: AtomicSettlementJournal,
    {
        self.settle_fhegg_asset_atomic_durable(
            transaction_id,
            session,
            world,
            asset,
            receipt,
            expected,
            verifier,
            replay_guard,
            journal,
            &mut NoAtomicSettlementCrash,
        )
    }
}

struct CaptureReplay<'a, R> {
    inner: &'a mut R,
    replay_id: Option<Digest32>,
}

impl<R: ReplayGuard> ReplayGuard for CaptureReplay<'_, R> {
    fn check_and_record(&mut self, replay_id: Digest32) -> bool {
        self.replay_id = Some(replay_id);
        self.inner.check_and_record(replay_id)
    }
}

#[derive(Default)]
struct AcceptReplay {
    replay_id: Option<Digest32>,
}

impl ReplayGuard for AcceptReplay {
    fn check_and_record(&mut self, replay_id: Digest32) -> bool {
        self.replay_id = Some(replay_id);
        true
    }
}

#[allow(clippy::too_many_arguments)]
fn prepare_durable_audit<V, R>(
    transaction_id: Digest32,
    session: &DarkBazaarSession,
    world: &TradeWorld,
    asset: AssetId,
    receipt: &AttestedClearingReceipt,
    expected: &ExpectedClearingContext<'_>,
    verifier: &V,
    replay_guard: &R,
) -> Result<AtomicFheggAssetSettlementAudit, AtomicFheggAssetSettlementError>
where
    V: ComputationIntegrityVerifier,
    R: ReplayGuard + Clone,
{
    let live = live_clear(session)?;
    let source_commitment = validate_static_source(session, asset, expected)?;
    if expected.crossing.p_star != Some(live.price as usize) || expected.crossing.v_star != 1 {
        return Err(FheggSettlementError::ResultMismatch {
            expected_price: live.price,
            claimed_price: expected.crossing.p_star,
            claimed_volume: expected.crossing.v_star,
        }
        .into());
    }
    let seller = session
        .market
        .seller
        .clone()
        .ok_or(FheggSettlementError::NotListed)?;
    let mut staged_replay = replay_guard.clone();
    let mut capture = CaptureReplay {
        inner: &mut staged_replay,
        replay_id: None,
    };
    receipt
        .verify_full(expected, verifier, &mut capture)
        .map_err(FheggSettlementError::Attestation)?;
    let replay_id = capture
        .replay_id
        .ok_or(AtomicSettlementJournalError::LiveStateMismatch(
            "attestation did not expose a replay id",
        ))?;
    let prepared_market = prepare_market_clear(session)?;
    let prepared_sale =
        world.prepare_atomic_sale(seller.as_str(), live.winner.as_str(), asset, live.price)?;
    let turn = session
        .market
        .cclerk
        .make_turn_with_actions(prepared_market.actions);
    let market_receipts_before = u32::try_from(session.market.receipts.len()).map_err(|_| {
        AtomicSettlementJournalError::LiveStateMismatch("market receipt count exceeds u32")
    })?;
    let audit = AtomicFheggAssetSettlementAudit {
        transaction_id,
        replay_id,
        claim_digest: receipt.claim_digest(),
        source_commitment,
        asset,
        world_before: prepared_sale.before_digest(),
        world_after: prepared_sale.after_digest(),
        market_receipts_before,
        price: live.price,
        seller,
        winner: live.winner,
        market_turn_hash: planned_executed_turn_hash(session, &turn),
        market_receipt_hash: None,
    };
    audit.validate()?;
    Ok(audit)
}

fn validate_static_source(
    session: &DarkBazaarSession,
    asset: AssetId,
    expected: &ExpectedClearingContext<'_>,
) -> Result<Digest32, AtomicFheggAssetSettlementError> {
    let source_commitment = recovery_source_commitment(session)?;
    let expected_nonce = *blake3::Hasher::new_derive_key(SOURCE_SESSION_DOMAIN)
        .update(&source_commitment)
        .finalize()
        .as_bytes();
    if expected.session.nonce() != expected_nonce {
        return Err(FheggSettlementError::SessionMismatch.into());
    }
    let found = expected
        .ordered_inputs
        .iter()
        .filter(|input| {
            input.kind == InputDigestKind::Commitment && input.digest == source_commitment
        })
        .count();
    if found != 1 {
        return Err(FheggSettlementError::SourceCommitmentCount { found }.into());
    }
    session.verify_fhegg_source_bfv_identity(expected.bfv, expected.session.buckets())?;
    session.verify_fhegg_bound_order_inputs(expected.ordered_inputs)?;
    let listing_source = session
        .market
        .fhegg_listing_source
        .ok_or(FheggSettlementError::UnboundListingSource)?;
    if listing_source.asset != asset.0 {
        return Err(AtomicFheggAssetSettlementError::Asset(
            AssetBackedError::SourceAssetMismatch {
                expected: AssetId(listing_source.asset),
                provided: asset,
            },
        ));
    }
    Ok(source_commitment)
}

/// Reconstruct the immutable source board during recovery without the normal
/// settlement preflight, which deliberately rejects an already-settled market.
fn recovery_source_commitment(
    session: &DarkBazaarSession,
) -> Result<Digest32, AtomicFheggAssetSettlementError> {
    let mut hasher = blake3::Hasher::new_derive_key(SOURCE_BOARD_DOMAIN);
    hasher.update(&session.market.seed.to_be_bytes());
    hasher.update(&session.market.reserve.to_be_bytes());
    let seller = session
        .market
        .seller
        .as_ref()
        .ok_or(FheggSettlementError::NotListed)?;
    hasher.update(&(seller.0.len() as u64).to_be_bytes());
    hasher.update(seller.0.as_bytes());
    let listing = session
        .market
        .fhegg_listing_source
        .ok_or(FheggSettlementError::UnboundListingSource)?;
    hasher.update(&listing.asset);
    hasher.update(
        &session
            .market
            .fhegg_listing_source_seal()
            .ok_or(FheggSettlementError::UnboundListingSource)?,
    );
    hasher.update(&listing.session_digest);
    hasher.update(&listing.binding_digest);
    hasher.update(&listing.message_digest);
    hasher.update(&listing.ciphertext_digest);
    hasher.update(&(session.market.bids.len() as u64).to_be_bytes());
    for placed in &session.market.bids {
        let source = placed
            .fhegg_source
            .ok_or(FheggSettlementError::UnboundSource { slot: placed.slot })?;
        hasher.update(&(placed.who.0.len() as u64).to_be_bytes());
        hasher.update(placed.who.0.as_bytes());
        hasher.update(&[placed.handle]);
        hasher.update(&(placed.slot as u64).to_be_bytes());
        hasher.update(&placed.seal());
        hasher.update(&source.session_digest);
        hasher.update(&source.binding_digest);
        hasher.update(&source.message_digest);
        hasher.update(&source.ciphertext_digest);
    }
    Ok(*hasher.finalize().as_bytes())
}

fn validate_recovery_context<V: ComputationIntegrityVerifier>(
    session: &DarkBazaarSession,
    asset: AssetId,
    receipt: &AttestedClearingReceipt,
    expected: &ExpectedClearingContext<'_>,
    verifier: &V,
    audit: &AtomicFheggAssetSettlementAudit,
) -> Result<Digest32, AtomicFheggAssetSettlementError> {
    let source_commitment = validate_static_source(session, asset, expected)?;
    if source_commitment != audit.source_commitment
        || receipt.claim_digest() != audit.claim_digest
        || expected.crossing.p_star != Some(audit.price as usize)
        || expected.crossing.v_star != 1
        || session.market.seller.as_ref() != Some(&audit.seller)
    {
        return Err(AtomicSettlementJournalError::LiveStateMismatch(
            "static source, result, claim, or seller differs from prepare",
        )
        .into());
    }
    let mut capture = AcceptReplay::default();
    receipt
        .verify_full(expected, verifier, &mut capture)
        .map_err(FheggSettlementError::Attestation)?;
    capture.replay_id.ok_or_else(|| {
        AtomicSettlementJournalError::LiveStateMismatch("attestation did not expose a replay id")
            .into()
    })
}

#[derive(Clone, Debug)]
enum MarketJournalState {
    Before,
    After(TurnReceipt),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WorldJournalState {
    Before,
    After,
}

fn classify_market_state(
    session: &DarkBazaarSession,
    audit: &AtomicFheggAssetSettlementAudit,
) -> Result<MarketJournalState, AtomicSettlementJournalError> {
    let receipts_before = audit.market_receipts_before as usize;
    let phase = session.market.phase();
    let onledger = session.market.onledger_phase();
    if phase == Some(Phase::Commit)
        && onledger == Some(0)
        && session.market.clearing.is_none()
        && session.market.receipts.len() == receipts_before
    {
        return Ok(MarketJournalState::Before);
    }
    if phase == Some(Phase::Settled)
        && onledger == Some(2)
        && session.market.receipts.len() == receipts_before + 1
    {
        let clearing = session.market.clearing.as_ref().ok_or(
            AtomicSettlementJournalError::LiveStateMismatch(
                "settled market lacks a clearing mirror",
            ),
        )?;
        let winner = session.market.winning_actor().ok_or(
            AtomicSettlementJournalError::LiveStateMismatch(
                "settled market lacks a winner identity",
            ),
        )?;
        let receipt = session.market.receipts.last().cloned().ok_or(
            AtomicSettlementJournalError::LiveStateMismatch(
                "settled market lacks its executor receipt",
            ),
        )?;
        if clearing.winner.value != audit.price as i128 {
            return Err(AtomicSettlementJournalError::LiveStateMismatch(
                "settled price differs from prepare",
            ));
        }
        if winner != &audit.winner {
            return Err(AtomicSettlementJournalError::LiveStateMismatch(
                "settled winner differs from prepare",
            ));
        }
        if receipt.turn_hash != audit.market_turn_hash {
            return Err(AtomicSettlementJournalError::LiveStateMismatch(
                "settled market turn hash differs from prepare",
            ));
        }
        if audit
            .market_receipt_hash
            .is_some_and(|expected| expected != receipt.receipt_hash())
        {
            return Err(AtomicSettlementJournalError::LiveStateMismatch(
                "settled market receipt hash differs from journal",
            ));
        }
        return Ok(MarketJournalState::After(receipt));
    }
    Err(AtomicSettlementJournalError::LiveStateMismatch(
        "market is neither the exact prepared nor exact applied image",
    ))
}

fn classify_world_state(
    world: &TradeWorld,
    audit: &AtomicFheggAssetSettlementAudit,
) -> Result<WorldJournalState, AtomicSettlementJournalError> {
    let digest = world.state_audit_digest();
    if digest == audit.world_before {
        Ok(WorldJournalState::Before)
    } else if digest == audit.world_after {
        Ok(WorldJournalState::After)
    } else {
        Err(AtomicSettlementJournalError::LiveStateMismatch(
            "trade world is neither the exact before nor exact after image",
        ))
    }
}

fn prepare_sale_from_audit(
    world: &TradeWorld,
    audit: &AtomicFheggAssetSettlementAudit,
) -> Result<PreparedAtomicSale, AtomicFheggAssetSettlementError> {
    let sale = world.prepare_atomic_sale(
        audit.seller.as_str(),
        audit.winner.as_str(),
        audit.asset,
        audit.price,
    )?;
    if sale.before_digest() != audit.world_before || sale.after_digest() != audit.world_after {
        return Err(AtomicSettlementJournalError::LiveStateMismatch(
            "reconstructed trade image differs from prepare",
        )
        .into());
    }
    Ok(sale)
}

fn commit_market_from_audit(
    session: &mut DarkBazaarSession,
    world: &TradeWorld,
    audit: &AtomicFheggAssetSettlementAudit,
) -> Result<TurnReceipt, AtomicFheggAssetSettlementError> {
    let prepared_market = prepare_market_clear(session)?;
    let sale = prepare_sale_from_audit(world, audit)?;
    drop(sale);
    let turn = session
        .market
        .cclerk
        .make_turn_with_actions(prepared_market.actions);
    if planned_executed_turn_hash(session, &turn) != audit.market_turn_hash {
        return Err(AtomicSettlementJournalError::LiveStateMismatch(
            "reconstructed market turn differs from prepare",
        )
        .into());
    }
    let settlement_turn = session
        .market
        .executor
        .submit_turn(&turn)
        .map_err(|error| {
            AtomicFheggAssetSettlementError::Settlement(FheggSettlementError::SettlementRefused(
                error.to_string(),
            ))
        })?;
    session.market.auction = Some(prepared_market.auction);
    session.market.clearing = Some(prepared_market.clearing);
    session.market.receipts.push(settlement_turn.clone());
    Ok(settlement_turn)
}

fn planned_executed_turn_hash(
    session: &DarkBazaarSession,
    turn: &dregg_app_framework::Turn,
) -> Digest32 {
    let mut executed = turn.clone();
    if executed.fee == 0 {
        executed.fee = 10_000;
    }
    executed.nonce = session.market.executor.agent_nonce();
    executed.hash()
}

fn replay_is_fresh<R: ReplayGuard + Clone>(replay_guard: &R, replay_id: Digest32) -> bool {
    let mut probe = replay_guard.clone();
    probe.check_and_record(replay_id)
}

fn receipt_from_recovered_state(
    world: &TradeWorld,
    audit: &AtomicFheggAssetSettlementAudit,
    settlement_turn: TurnReceipt,
) -> Result<AtomicFheggAssetSettlementReceipt, AtomicFheggAssetSettlementError> {
    if audit.market_receipt_hash != Some(settlement_turn.receipt_hash()) {
        return Err(AtomicSettlementJournalError::LiveStateMismatch(
            "executor receipt differs from committed journal audit",
        )
        .into());
    }
    let provenance = world.verify_provenance(audit.asset);
    if !provenance.verified
        || world.current_holder_label(audit.asset) != Some(audit.winner.as_str())
    {
        return Err(AtomicSettlementJournalError::LiveStateMismatch(
            "applied world does not contain the verified asset at the winner",
        )
        .into());
    }
    let asset = AssetBackedClearing {
        asset: audit.asset,
        seller: audit.seller.clone(),
        winner: audit.winner.clone(),
        price: audit.price,
        settlement: Settlement {
            a_gave: LegSpec::Asset(audit.asset),
            b_gave: LegSpec::Dregg(audit.price),
        },
        provenance,
    };
    let fhegg = FheggSettlementReceipt {
        claim_digest: audit.claim_digest,
        source_commitment: audit.source_commitment,
        price: audit.price,
        volume: 1,
        winner: audit.winner.clone(),
        settlement_turn,
    };
    let preview = AtomicSettlementPreview {
        claim_digest: audit.claim_digest,
        source_commitment: audit.source_commitment,
        asset: audit.asset,
        world_before: audit.world_before,
        world_after: audit.world_after,
        price: audit.price,
        seller: audit.seller.clone(),
        winner: audit.winner.clone(),
    };
    let audit_digest = atomic_audit_digest(&preview, &fhegg);
    Ok(AtomicFheggAssetSettlementReceipt {
        fhegg,
        asset,
        world_before: audit.world_before,
        world_after: audit.world_after,
        audit_digest,
        journal_audit: Some(audit.clone()),
    })
}

fn journal_load<J: AtomicSettlementJournal>(
    journal: &J,
    transaction_id: Digest32,
) -> Result<Option<Vec<u8>>, AtomicSettlementJournalError> {
    journal
        .load(transaction_id)
        .map_err(AtomicSettlementJournalError::Storage)
}

fn journal_initial_insert<J: AtomicSettlementJournal>(
    journal: &mut J,
    record: &AtomicSettlementJournalRecord,
) -> Result<(), AtomicSettlementJournalError> {
    let bytes = record.to_wire_bytes()?;
    let outcome = journal
        .compare_exchange(
            record.audit.transaction_id,
            record.audit.replay_id,
            None,
            &bytes,
        )
        .map_err(AtomicSettlementJournalError::Storage)?;
    match outcome {
        AtomicSettlementCasOutcome::Applied => Ok(()),
        AtomicSettlementCasOutcome::Unchanged => {
            Err(AtomicSettlementJournalError::CompareExchangeConflict)
        }
        AtomicSettlementCasOutcome::ReplayReservationConflict => {
            Err(AtomicSettlementJournalError::ReplayReservationConflict)
        }
    }
}

fn journal_advance<J: AtomicSettlementJournal>(
    journal: &mut J,
    expected: &[u8],
    replacement: AtomicSettlementJournalRecord,
) -> Result<(), AtomicSettlementJournalError> {
    let bytes = replacement.to_wire_bytes()?;
    let outcome = journal
        .compare_exchange(
            replacement.audit.transaction_id,
            replacement.audit.replay_id,
            Some(expected),
            &bytes,
        )
        .map_err(AtomicSettlementJournalError::Storage)?;
    match outcome {
        AtomicSettlementCasOutcome::Applied => Ok(()),
        AtomicSettlementCasOutcome::Unchanged => {
            Err(AtomicSettlementJournalError::CompareExchangeConflict)
        }
        AtomicSettlementCasOutcome::ReplayReservationConflict => {
            Err(AtomicSettlementJournalError::ReplayReservationConflict)
        }
    }
}

fn crash_checkpoint<C: AtomicSettlementCrashInjector>(
    crash: &mut C,
    point: AtomicSettlementCrashPoint,
) -> Result<(), AtomicFheggAssetSettlementError> {
    crash
        .checkpoint(point)
        .map_err(|reason| AtomicFheggAssetSettlementError::SimulatedCrash { point, reason })
}

fn prepare_market_clear(
    session: &DarkBazaarSession,
) -> Result<PreparedMarketClear, FheggSettlementError> {
    let cell = session
        .market
        .auction_cell
        .ok_or(FheggSettlementError::MissingAuctionCell)?;
    let mut auction = session
        .market
        .auction
        .clone()
        .ok_or(FheggSettlementError::NotListed)?;
    if auction.phase != Phase::Commit {
        return Err(FheggSettlementError::PhaseNotCommit(Some(auction.phase)));
    }
    auction.seal_commit_phase();
    for placed in &session.market.bids {
        match placed.fhegg_source {
            Some(source) => auction.reveal_source_bound(placed.bid, &source.binding_digest),
            None => return Err(FheggSettlementError::UnboundSource { slot: placed.slot }),
        }
        .map_err(|error| FheggSettlementError::SettlementRefused(error.to_string()))?;
    }
    let ledger = session.market.fund_settlement();
    let pay_before = ledger.total_asset(&PAY);
    let good_before = ledger.total_asset(&GOOD);
    let (post, winner) = auction.settle(&ledger).map_err(|error| match error {
        AuctionError::NoWinner => FheggSettlementError::NoBids,
        other => FheggSettlementError::SettlementRefused(other.to_string()),
    })?;
    if winner.value < session.market.reserve {
        return Err(FheggSettlementError::BelowReserve {
            high: winner.value,
            reserve: session.market.reserve,
        });
    }
    let pay_after = post.total_asset(&PAY);
    let good_after = post.total_asset(&GOOD);

    let mut actions = Vec::with_capacity(session.market.bids.len() + 2);
    actions.push(session.market.cclerk.make_action(
        cell,
        "close_commit",
        close_commit_effects(cell),
    ));
    for placed in &session.market.bids {
        actions.push(session.market.cclerk.make_action(
            cell,
            "reveal_bid",
            reveal_bid_effects(
                cell,
                field_from_u64(placed.bid.bidder as u64),
                placed.bid.value.max(0) as u64,
            ),
        ));
    }
    actions.push(session.market.cclerk.make_action(
        cell,
        "resolve",
        resolve_effects(
            cell,
            field_from_u64(winner.bidder as u64),
            winner.value.max(0) as u64,
        ),
    ));
    Ok(PreparedMarketClear {
        auction,
        clearing: Clearing {
            winner,
            post,
            pay_conserved: (pay_before, pay_after),
            good_conserved: (good_before, good_after),
        },
        actions,
    })
}

fn atomic_audit_digest(
    preview: &AtomicSettlementPreview,
    fhegg: &FheggSettlementReceipt,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ATOMIC_AUDIT_DOMAIN);
    hasher.update(&preview.claim_digest);
    hasher.update(&preview.source_commitment);
    hasher.update(&preview.asset.0);
    hasher.update(&preview.world_before);
    hasher.update(&preview.world_after);
    hasher.update(&preview.price.to_be_bytes());
    for actor in [&preview.seller, &preview.winner] {
        hasher.update(&(actor.0.len() as u64).to_be_bytes());
        hasher.update(actor.0.as_bytes());
    }
    hasher.update(&fhegg.settlement_turn.receipt_hash());
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use std::{
        collections::HashMap,
        path::PathBuf,
        sync::{
            Arc, Barrier,
            atomic::{AtomicU64, Ordering},
        },
        time::Duration,
    };

    use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig};
    use dreggnet_trade::{AssetId, TradeError, TradeWorld};
    use ed25519_dalek::SigningKey;
    use fhegg_fhe::attestation::{
        AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
        ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
        InMemoryReplayGuard, InputDigest,
    };
    use fhegg_fhe::mpc::Crossing;
    use fhegg_fhe::mpc_party::{PartyMpcSession, simulate_public_transcript};
    use fhegg_fhe::order_ingress::{
        AuthenticatedOrderBook, OrderEncryptionOpening, OrderIngressSession, SignedOrderSubmission,
    };
    use fhegg_fhe::threshold::{
        BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    };
    use fhegg_fhe::{Order, Side};
    use rand::{SeedableRng, rngs::StdRng};

    use starbridge_sealed_auction::Phase;

    use super::{
        AtomicFheggAssetSettlementAudit, AtomicFheggAssetSettlementError,
        AtomicSettlementCasOutcome, AtomicSettlementCommitHook, AtomicSettlementCrashInjector,
        AtomicSettlementCrashPoint, AtomicSettlementJournal, AtomicSettlementJournalError,
        AtomicSettlementJournalPhase, AtomicSettlementJournalRecord, AtomicSettlementPreview,
        FileAtomicSettlementJournal, NoAtomicSettlementCrash,
    };
    use crate::asset_backed::AssetBackedError;
    use crate::fhegg_settlement::FheggSettlementError;
    use crate::{DarkBazaarOffering, DarkBazaarSession, TURN_LIST};

    const MARKET_SEED: u64 = 0xA7_0C_1C;
    const SELLER: &str = "descent-player:alice";
    const WINNER: &str = "bazaar-bidder:carol";
    static NEXT_JOURNAL_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestJournalDirectory(PathBuf);

    impl TestJournalDirectory {
        fn new(case: usize) -> Self {
            let unique = NEXT_JOURNAL_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            Self(std::env::temp_dir().join(format!(
                "dregg-fhegg-atomic-journal-{}-{case}-{unique}",
                std::process::id()
            )))
        }
    }

    impl Drop for TestJournalDirectory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    struct Fixture {
        offering: DarkBazaarOffering,
        market: DarkBazaarSession,
        replay_market: DarkBazaarSession,
        world: TradeWorld,
        asset: AssetId,
        mpc: PartyMpcSession,
        verifier: AuthenticatedQuorumVerifier,
        bfv: BfvPublicIdentity,
        inputs: Vec<InputDigest>,
        transcript: fhegg_fhe::mpc_party::DistributedTranscript,
        crossing: Crossing,
        receipt: AttestedClearingReceipt,
    }

    fn actor(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_string())
    }

    fn collective_key(params: &BfvParams) -> (KeygenSession, CollectivePublicKey) {
        let keygen = KeygenSession::from_seed(2, [0x21; 32]).unwrap();
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        for party in 0..2 {
            let (state, contribution) = ThresholdParty::join(&keygen, party, params).unwrap();
            coordinator.accept(contribution).unwrap();
            drop(state);
        }
        (keygen, coordinator.finish().unwrap())
    }

    fn open_board(
        offering: &DarkBazaarOffering,
        actions: &[(Action, DreggIdentity)],
    ) -> DarkBazaarSession {
        let mut market = offering
            .open(SessionConfig::with_seed(MARKET_SEED))
            .unwrap();
        assert!(
            offering
                .advance(
                    &mut market,
                    Action::new("list", TURN_LIST, 3, true),
                    actor(SELLER),
                )
                .landed()
        );
        for (action, who) in actions {
            assert!(
                offering
                    .advance(&mut market, action.clone(), who.clone())
                    .landed()
            );
        }
        market
    }

    fn fixture() -> Fixture {
        let mut world = TradeWorld::new();
        let asset = world.mint(SELLER, b"atomic-descent-loot");
        let source_verifier = SigningKey::from_bytes(&[0x29; 32]);
        let offering = DarkBazaarOffering::new()
            .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
            .unwrap();
        let mut genesis = offering
            .open(SessionConfig::with_seed(MARKET_SEED))
            .unwrap();
        assert!(
            offering
                .advance(
                    &mut genesis,
                    Action::new("list", TURN_LIST, 3, true),
                    actor(SELLER),
                )
                .landed()
        );

        let params = BfvParams::fold_set();
        let (keygen, collective) = collective_key(&params);
        let ingress = OrderIngressSession::new(
            genesis.fhegg_order_ingress_nonce().unwrap(),
            4,
            &params,
            &collective,
        )
        .unwrap();
        let keys = [
            SigningKey::from_bytes(&[0x40; 32]),
            SigningKey::from_bytes(&[0x41; 32]),
            SigningKey::from_bytes(&[0x42; 32]),
        ];
        let rows = [
            (
                SELLER,
                Order {
                    side: Side::Ask,
                    limit: 3,
                    qty: 1,
                },
            ),
            (
                "bazaar-bidder:bob",
                Order {
                    side: Side::Bid,
                    limit: 2,
                    qty: 1,
                },
            ),
            (
                WINNER,
                Order {
                    side: Side::Bid,
                    limit: 3,
                    qty: 1,
                },
            ),
        ];
        let mut book = AuthenticatedOrderBook::new(
            ingress.clone(),
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
        )
        .unwrap();
        let mut actions = Vec::new();
        for (trader, ((who, order), key)) in rows.iter().zip(&keys).enumerate() {
            let opening = OrderEncryptionOpening::from_seed([0x51 + trader as u8; 32]);
            let (submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
                &ingress,
                trader,
                0,
                order,
                &params,
                &collective,
                key,
                opening,
            )
            .unwrap();
            let binding = book
                .accept_opened(submission, order, opening, &params, &collective)
                .unwrap();
            let action = if matches!(order.side, Side::Ask) {
                let certificate =
                    binding.certify_listing_for_market(who.as_bytes(), asset.0, &source_verifier);
                DarkBazaarOffering::fhegg_listing_source_action(&certificate)
            } else {
                let certificate = binding.certify_for_market(who.as_bytes(), &source_verifier);
                DarkBazaarOffering::fhegg_source_bound_bid_action(order.limit as i64, &certificate)
            };
            actions.push((action, actor(who)));
        }
        // `genesis` already carries LIST; land only the exact source actions.
        for (action, who) in &actions {
            assert!(
                offering
                    .advance(&mut genesis, action.clone(), who.clone())
                    .landed()
            );
        }
        let replay_market = open_board(&offering, &actions);

        let (_, mut inputs) = book.finish().into_parts();
        inputs.push(genesis.fhegg_source_input().unwrap());
        let bfv = BfvPublicIdentity::from_public(&params, &keygen, &collective);
        let mpc = PartyMpcSession::new(
            genesis.fhegg_settlement_session_nonce().unwrap(),
            2,
            4,
            8,
            params.plaintext_modulus(),
            Duration::from_secs(1),
        )
        .unwrap();
        let committee = [
            SigningKey::from_bytes(&[0x61; 32]),
            SigningKey::from_bytes(&[0x62; 32]),
        ];
        let verifier = AuthenticatedQuorumVerifier::new(
            committee
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            2,
        )
        .unwrap();
        let crossing = Crossing {
            p_star: Some(3),
            v_star: 1,
        };
        let transcript =
            simulate_public_transcript(&crossing, &mpc, &mut StdRng::seed_from_u64(MARKET_SEED))
                .unwrap();
        let expected = ExpectedClearingContext {
            session: &mpc,
            ordered_roster: verifier.ordered_roster(),
            bfv: &bfv,
            ordered_inputs: &inputs,
            transcript: &transcript,
            crossing: &crossing,
        };
        let mut receipt = AttestedClearingReceipt::issue(
            &expected,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .unwrap();
        let signatures = committee
            .iter()
            .enumerate()
            .map(|(party, key)| {
                verifier
                    .sign_claim(&receipt.claim_digest(), party, key)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        receipt.computation_integrity = verifier
            .assemble_evidence(&receipt.claim_digest(), &signatures)
            .unwrap();

        Fixture {
            offering,
            market: genesis,
            replay_market,
            world,
            asset,
            mpc,
            verifier,
            bfv,
            inputs,
            transcript,
            crossing,
            receipt,
        }
    }

    fn market_image(session: &DarkBazaarSession) -> (usize, Option<Phase>, Option<u64>, bool) {
        (
            session.market().receipts_len(),
            session.market().phase(),
            session.market().onledger_phase(),
            session.is_settled(),
        )
    }

    struct RejectAfterValidation;

    impl AtomicSettlementCommitHook for RejectAfterValidation {
        fn before_commit(&mut self, preview: &AtomicSettlementPreview) -> Result<(), String> {
            assert_ne!(preview.world_before, preview.world_after);
            Err("injected application failure".into())
        }
    }

    #[derive(Default)]
    struct InMemoryJournal {
        records: HashMap<[u8; 32], Vec<u8>>,
        replay_reservations: HashMap<[u8; 32], [u8; 32]>,
    }

    impl AtomicSettlementJournal for InMemoryJournal {
        fn load(&self, transaction_id: [u8; 32]) -> Result<Option<Vec<u8>>, String> {
            Ok(self.records.get(&transaction_id).cloned())
        }

        fn compare_exchange(
            &mut self,
            transaction_id: [u8; 32],
            replay_id: [u8; 32],
            expected: Option<&[u8]>,
            replacement: &[u8],
        ) -> Result<AtomicSettlementCasOutcome, String> {
            let decoded = AtomicSettlementJournalRecord::from_wire_bytes(replacement)
                .map_err(|error| error.to_string())?;
            if decoded.audit.transaction_id != transaction_id
                || decoded.audit.replay_id != replay_id
            {
                return Err("replacement key mismatch".into());
            }
            match expected {
                None => {
                    if self.records.contains_key(&transaction_id) {
                        return Ok(AtomicSettlementCasOutcome::Unchanged);
                    }
                    if self
                        .replay_reservations
                        .get(&replay_id)
                        .is_some_and(|reserved| reserved != &transaction_id)
                    {
                        return Ok(AtomicSettlementCasOutcome::ReplayReservationConflict);
                    }
                    self.replay_reservations.insert(replay_id, transaction_id);
                    self.records.insert(transaction_id, replacement.to_vec());
                    Ok(AtomicSettlementCasOutcome::Applied)
                }
                Some(expected) => {
                    if self.records.get(&transaction_id).map(Vec::as_slice) != Some(expected) {
                        return Ok(AtomicSettlementCasOutcome::Unchanged);
                    }
                    if self.replay_reservations.get(&replay_id) != Some(&transaction_id) {
                        return Err("replay reservation disappeared".into());
                    }
                    self.records.insert(transaction_id, replacement.to_vec());
                    Ok(AtomicSettlementCasOutcome::Applied)
                }
            }
        }
    }

    struct CrashOnce(Option<AtomicSettlementCrashPoint>);

    impl AtomicSettlementCrashInjector for CrashOnce {
        fn checkpoint(&mut self, point: AtomicSettlementCrashPoint) -> Result<(), String> {
            if self.0 == Some(point) {
                self.0 = None;
                Err("power loss".into())
            } else {
                Ok(())
            }
        }
    }

    fn sample_prepared_record(
        transaction_id: [u8; 32],
        replay_id: [u8; 32],
    ) -> AtomicSettlementJournalRecord {
        AtomicSettlementJournalRecord {
            phase: AtomicSettlementJournalPhase::Prepared,
            audit: AtomicFheggAssetSettlementAudit {
                transaction_id,
                replay_id,
                claim_digest: [0x93; 32],
                source_commitment: [0x94; 32],
                asset: AssetId([0x95; 32]),
                world_before: [0x96; 32],
                world_after: [0x97; 32],
                market_receipts_before: 4,
                price: 7,
                seller: DreggIdentity("seller".into()),
                winner: DreggIdentity("winner".into()),
                market_turn_hash: [0x98; 32],
                market_receipt_hash: None,
            },
        }
    }

    #[test]
    fn journal_record_wire_is_strict_bounded_and_canonical() {
        crate::support::install_verified_settlement_gate();
        let prepared = sample_prepared_record([0x81; 32], [0x82; 32]);
        let wire = prepared.to_wire_bytes().unwrap();
        assert_eq!(
            AtomicSettlementJournalRecord::from_wire_bytes(&wire).unwrap(),
            prepared
        );
        for end in 0..wire.len() {
            assert!(AtomicSettlementJournalRecord::from_wire_bytes(&wire[..end]).is_err());
        }
        let mut trailing = wire.clone();
        trailing.push(0);
        assert!(AtomicSettlementJournalRecord::from_wire_bytes(&trailing).is_err());

        let mut unknown_phase = wire;
        unknown_phase[9] = 0xFF;
        let checksum_offset = unknown_phase.len() - 32;
        let checksum = blake3::derive_key(
            super::JOURNAL_CHECKSUM_DOMAIN,
            &unknown_phase[..checksum_offset],
        );
        unknown_phase[checksum_offset..].copy_from_slice(&checksum);
        assert!(matches!(
            AtomicSettlementJournalRecord::from_wire_bytes(&unknown_phase),
            Err(AtomicSettlementJournalError::NonCanonicalPhase)
        ));

        let mut bad_phase_binding = prepared.clone();
        bad_phase_binding.phase = AtomicSettlementJournalPhase::MarketApplied;
        assert!(matches!(
            bad_phase_binding.to_wire_bytes(),
            Err(AtomicSettlementJournalError::NonCanonicalPhase)
        ));
        let mut oversized_identity = prepared.clone();
        oversized_identity.audit.winner = DreggIdentity("w".repeat(257));
        assert!(matches!(
            oversized_identity.to_wire_bytes(),
            Err(AtomicSettlementJournalError::IdentityOutOfBounds)
        ));
        let mut degenerate = prepared;
        degenerate.audit.world_after = degenerate.audit.world_before;
        assert!(matches!(
            degenerate.to_wire_bytes(),
            Err(AtomicSettlementJournalError::DegenerateWorldTransition)
        ));
    }

    #[test]
    fn file_journal_persists_atomic_cas_and_refuses_corruption() {
        crate::support::install_verified_settlement_gate();
        let directory = TestJournalDirectory::new(99);
        let transaction_id = [0x91; 32];
        let replay_id = [0x92; 32];
        let prepared = sample_prepared_record(transaction_id, replay_id);
        let prepared_wire = prepared.to_wire_bytes().unwrap();
        let mut journal = FileAtomicSettlementJournal::open(&directory.0).unwrap();
        assert_eq!(
            journal
                .compare_exchange(transaction_id, replay_id, None, &prepared_wire)
                .unwrap(),
            AtomicSettlementCasOutcome::Applied
        );

        drop(journal);
        std::fs::write(directory.0.join("atomic-settlements.tmp"), b"torn write").unwrap();
        let mut journal = FileAtomicSettlementJournal::open(&directory.0).unwrap();
        assert_eq!(
            journal.load(transaction_id).unwrap(),
            Some(prepared_wire.clone())
        );

        let mut conflicting = prepared.clone();
        conflicting.audit.transaction_id = [0x99; 32];
        let conflicting_wire = conflicting.to_wire_bytes().unwrap();
        assert_eq!(
            journal
                .compare_exchange(
                    conflicting.audit.transaction_id,
                    replay_id,
                    None,
                    &conflicting_wire,
                )
                .unwrap(),
            AtomicSettlementCasOutcome::ReplayReservationConflict
        );

        let mut applied = prepared;
        applied.phase = AtomicSettlementJournalPhase::MarketApplied;
        applied.audit.market_receipt_hash = Some([0x9A; 32]);
        let applied_wire = applied.to_wire_bytes().unwrap();
        assert_eq!(
            journal
                .compare_exchange(
                    transaction_id,
                    replay_id,
                    Some(&prepared_wire),
                    &applied_wire,
                )
                .unwrap(),
            AtomicSettlementCasOutcome::Applied
        );
        assert_eq!(
            journal
                .compare_exchange(
                    transaction_id,
                    replay_id,
                    Some(&prepared_wire),
                    &applied_wire,
                )
                .unwrap(),
            AtomicSettlementCasOutcome::Unchanged
        );
        assert_eq!(journal.load(transaction_id).unwrap(), Some(applied_wire));

        drop(journal);
        let state_path = directory.0.join("atomic-settlements.bin");
        let mut corrupt = std::fs::read(&state_path).unwrap();
        corrupt[20] ^= 1;
        std::fs::write(&state_path, corrupt).unwrap();
        let journal = FileAtomicSettlementJournal::open(&directory.0).unwrap();
        assert!(
            journal
                .load(transaction_id)
                .unwrap_err()
                .contains("checksum")
        );
    }

    #[test]
    fn file_journal_serializes_competing_replay_reservations() {
        crate::support::install_verified_settlement_gate();
        let directory = TestJournalDirectory::new(100);
        FileAtomicSettlementJournal::open(&directory.0).unwrap();
        let barrier = Arc::new(Barrier::new(2));
        let replay_id = [0xB0; 32];
        let mut workers = Vec::new();
        for transaction_id in [[0xB1; 32], [0xB2; 32]] {
            let root = directory.0.clone();
            let barrier = Arc::clone(&barrier);
            workers.push(std::thread::spawn(move || {
                let record = sample_prepared_record(transaction_id, replay_id);
                let wire = record.to_wire_bytes().unwrap();
                let mut journal = FileAtomicSettlementJournal::open(root).unwrap();
                barrier.wait();
                journal
                    .compare_exchange(transaction_id, replay_id, None, &wire)
                    .unwrap()
            }));
        }
        let outcomes = workers
            .into_iter()
            .map(|worker| worker.join().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            outcomes
                .iter()
                .filter(|outcome| **outcome == AtomicSettlementCasOutcome::Applied)
                .count(),
            1
        );
        assert_eq!(
            outcomes
                .iter()
                .filter(|outcome| {
                    **outcome == AtomicSettlementCasOutcome::ReplayReservationConflict
                })
                .count(),
            1
        );
        let journal = FileAtomicSettlementJournal::open(&directory.0).unwrap();
        assert_eq!(
            [[0xB1; 32], [0xB2; 32]]
                .into_iter()
                .filter(|transaction_id| journal.load(*transaction_id).unwrap().is_some())
                .count(),
            1
        );
    }

    #[test]
    fn atomic_fhegg_asset_cross_rolls_back_every_refusal_and_commits_every_leg_once() {
        crate::support::install_verified_settlement_gate();
        let mut f = fixture();
        let market_before = market_image(&f.market);
        let world_before = f.world.state_audit_digest();
        let mut replay = InMemoryReplayGuard::default();

        let expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic(
                &mut f.market,
                &mut f.world,
                AssetId([0xFF; 32]),
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
            ),
            Err(AtomicFheggAssetSettlementError::Asset(
                AssetBackedError::SourceAssetMismatch { .. }
            ))
        ));
        assert_eq!(market_image(&f.market), market_before);
        assert_eq!(f.world.state_audit_digest(), world_before);

        // A valid proof cannot burn its replay id or move the asset when the
        // buyer is short. The exact same claim remains usable afterward.
        let expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic(
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
            ),
            Err(AtomicFheggAssetSettlementError::Trade(
                TradeError::InsufficientDregg { have: 0, need: 3 }
            ))
        ));
        assert_eq!(market_image(&f.market), market_before);
        assert_eq!(f.world.state_audit_digest(), world_before);

        f.world.fund_dregg(WINNER, 3);
        let funded_before = f.world.state_audit_digest();
        let mut wrong_owner_world = f.world.detached_state_clone();
        wrong_owner_world
            .assets()
            .transfer(f.asset, SELLER, "loot-thief")
            .unwrap();
        let wrong_owner_before = wrong_owner_world.state_audit_digest();
        let expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic(
                &mut f.market,
                &mut wrong_owner_world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
            ),
            Err(AtomicFheggAssetSettlementError::Trade(TradeError::Asset(_)))
        ));
        assert_eq!(market_image(&f.market), market_before);
        assert_eq!(wrong_owner_world.state_audit_digest(), wrong_owner_before);

        let mut wrong_inputs = f.inputs.clone();
        *wrong_inputs.last_mut().unwrap() = InputDigest::commitment([0x99; 32]);
        let wrong_expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &wrong_inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic(
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &wrong_expected,
                &f.verifier,
                &mut replay,
            ),
            Err(AtomicFheggAssetSettlementError::Settlement(
                FheggSettlementError::SourceCommitmentCount { found: 0 }
            ))
        ));
        assert_eq!(market_image(&f.market), market_before);
        assert_eq!(f.world.state_audit_digest(), funded_before);

        let expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic_with_hook(
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
                &mut RejectAfterValidation,
            ),
            Err(AtomicFheggAssetSettlementError::PreCommitRefused(reason))
                if reason.contains("injected")
        ));
        assert_eq!(market_image(&f.market), market_before);
        assert_eq!(f.world.state_audit_digest(), funded_before);

        let replay_world_before_success = f.world.detached_state_clone();
        let expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        let settled = f
            .offering
            .settle_fhegg_asset_atomic(
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
            )
            .expect("all detached checks and the one-turn market commit succeed");
        assert!(f.market.is_settled());
        assert_eq!(f.market.market().phase(), Some(Phase::Settled));
        assert_eq!(f.market.market().onledger_phase(), Some(2));
        assert_eq!(f.market.market().receipts_len(), market_before.0 + 1);
        assert_eq!(settled.fhegg.settlement_turn.action_count, 4);
        assert_eq!(settled.asset.asset, f.asset);
        assert_eq!(settled.asset.seller, actor(SELLER));
        assert_eq!(settled.asset.winner, actor(WINNER));
        assert_eq!(settled.asset.price, 3);
        assert!(settled.asset.provenance.verified);
        assert_eq!(settled.world_before, funded_before);
        assert_eq!(settled.world_after, f.world.state_audit_digest());
        assert_ne!(settled.world_before, settled.world_after);
        assert_ne!(settled.audit_digest, [0; 32]);
        assert!(settled.audit_digest_verifies());
        let mut tampered = settled.clone();
        tampered.asset.price += 1;
        assert!(!tampered.audit_digest_verifies());
        assert_eq!(f.world.current_holder_label(f.asset), Some(WINNER));
        assert_eq!(f.world.lineage_len(f.asset), 3);
        assert_eq!(f.world.dregg_balance(WINNER), 0);
        assert_eq!(f.world.dregg_balance(SELLER), 3);

        // A replay against an independently reconstructed identical market is
        // refused without consuming its board or the supplied world image.
        let mut replay_world = replay_world_before_success;
        let replay_market_before = market_image(&f.replay_market);
        let replay_world_before = replay_world.state_audit_digest();
        let replay_expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic(
                &mut f.replay_market,
                &mut replay_world,
                f.asset,
                &f.receipt,
                &replay_expected,
                &f.verifier,
                &mut replay,
            ),
            Err(AtomicFheggAssetSettlementError::Settlement(
                FheggSettlementError::Attestation(AttestationError::ReplayDetected)
            ))
        ));
        assert_eq!(market_image(&f.replay_market), replay_market_before);
        assert_eq!(replay_world.state_audit_digest(), replay_world_before);
    }

    #[test]
    fn durable_journal_recovers_idempotently_at_every_commit_boundary() {
        crate::support::install_verified_settlement_gate();
        let crash_points = [
            AtomicSettlementCrashPoint::AfterPrepared,
            AtomicSettlementCrashPoint::AfterMarketApplied,
            AtomicSettlementCrashPoint::AfterWorldApplied,
            AtomicSettlementCrashPoint::AfterReplayApplied,
            AtomicSettlementCrashPoint::AfterCommitted,
        ];
        for (case, crash_point) in crash_points.into_iter().enumerate() {
            let mut f = fixture();
            f.world.fund_dregg(WINNER, 3);
            let transaction_id = [0xA0 + case as u8; 32];
            let market_receipts_before = f.market.market().receipts_len();
            let world_before = f.world.state_audit_digest();
            let mut replay = InMemoryReplayGuard::default();
            let journal_directory = TestJournalDirectory::new(case);
            let mut journal = FileAtomicSettlementJournal::open(&journal_directory.0)
                .expect("open a production file-backed journal");
            let expected = ExpectedClearingContext {
                session: &f.mpc,
                ordered_roster: f.verifier.ordered_roster(),
                bfv: &f.bfv,
                ordered_inputs: &f.inputs,
                transcript: &f.transcript,
                crossing: &f.crossing,
            };
            let crashed = f.offering.settle_fhegg_asset_atomic_durable(
                transaction_id,
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
                &mut journal,
                &mut CrashOnce(Some(crash_point)),
            );
            assert!(matches!(
                crashed,
                Err(AtomicFheggAssetSettlementError::SimulatedCrash { point, .. })
                    if point == crash_point
            ));

            // A new object reads the fsync+rename snapshot, just as a restarted
            // host would after reconstructing its market/world/replay images.
            drop(journal);
            let mut journal = FileAtomicSettlementJournal::open(&journal_directory.0)
                .expect("reopen the persisted journal after the simulated crash");

            if crash_point == AtomicSettlementCrashPoint::AfterPrepared {
                assert!(matches!(
                    f.offering.settle_fhegg_asset_atomic_recover(
                        [0xE0; 32],
                        &mut f.market,
                        &mut f.world,
                        f.asset,
                        &f.receipt,
                        &expected,
                        &f.verifier,
                        &mut replay,
                        &mut journal,
                    ),
                    Err(AtomicFheggAssetSettlementError::Journal(
                        AtomicSettlementJournalError::ReplayReservationConflict
                    ))
                ));
                assert!(!f.market.is_settled());
                assert_eq!(f.world.current_holder_label(f.asset), Some(SELLER));
            }

            let recovered = f
                .offering
                .settle_fhegg_asset_atomic_durable(
                    transaction_id,
                    &mut f.market,
                    &mut f.world,
                    f.asset,
                    &f.receipt,
                    &expected,
                    &f.verifier,
                    &mut replay,
                    &mut journal,
                    &mut NoAtomicSettlementCrash,
                )
                .expect("recovery advances only the missing idempotent phases");
            assert_eq!(recovered.world_before, world_before);
            assert_eq!(recovered.world_after, f.world.state_audit_digest());
            assert!(recovered.audit_digest_verifies());
            let durable_audit = recovered
                .journal_audit
                .as_ref()
                .expect("durable receipt carries the transaction audit");
            assert_eq!(durable_audit.transaction_id, transaction_id);
            assert_eq!(durable_audit.asset, f.asset);
            assert_eq!(
                durable_audit.market_receipt_hash,
                Some(recovered.fhegg.settlement_turn.receipt_hash())
            );
            assert_ne!(durable_audit.digest(), [0; 32]);
            assert_eq!(f.market.market().receipts_len(), market_receipts_before + 1);
            assert_eq!(f.world.current_holder_label(f.asset), Some(WINNER));
            assert_eq!(f.world.lineage_len(f.asset), 3);
            assert_eq!(f.world.dregg_balance(WINNER), 0);
            assert_eq!(f.world.dregg_balance(SELLER), 3);

            let committed_world = f.world.state_audit_digest();
            let committed_receipts = f.market.market().receipts_len();
            let repeated = f
                .offering
                .settle_fhegg_asset_atomic_recover(
                    transaction_id,
                    &mut f.market,
                    &mut f.world,
                    f.asset,
                    &f.receipt,
                    &expected,
                    &f.verifier,
                    &mut replay,
                    &mut journal,
                )
                .expect("committed recovery is a read-only idempotent success");
            assert_eq!(repeated.audit_digest, recovered.audit_digest);
            assert_eq!(f.world.state_audit_digest(), committed_world);
            assert_eq!(f.market.market().receipts_len(), committed_receipts);
            assert_eq!(f.world.lineage_len(f.asset), 3);

            let encoded = journal
                .load(transaction_id)
                .unwrap()
                .expect("committed record remains in the file snapshot");
            let record = AtomicSettlementJournalRecord::from_wire_bytes(&encoded).unwrap();
            assert_eq!(record.phase, AtomicSettlementJournalPhase::Committed);
            assert_eq!(record.audit, *durable_audit);
        }
    }

    #[test]
    fn durable_journal_rejects_corruption_and_unclassifiable_live_state() {
        crate::support::install_verified_settlement_gate();
        let mut f = fixture();
        f.world.fund_dregg(WINNER, 3);
        let transaction_id = [0xD7; 32];
        let mut replay = InMemoryReplayGuard::default();
        let mut journal = InMemoryJournal::default();
        let expected = ExpectedClearingContext {
            session: &f.mpc,
            ordered_roster: f.verifier.ordered_roster(),
            bfv: &f.bfv,
            ordered_inputs: &f.inputs,
            transcript: &f.transcript,
            crossing: &f.crossing,
        };
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic_durable(
                transaction_id,
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
                &mut journal,
                &mut CrashOnce(Some(AtomicSettlementCrashPoint::AfterPrepared)),
            ),
            Err(AtomicFheggAssetSettlementError::SimulatedCrash {
                point: AtomicSettlementCrashPoint::AfterPrepared,
                ..
            })
        ));

        // A second transaction id cannot reserve the same fhEgg replay id
        // while the first prepare still owns the otherwise-untouched state.
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic_recover(
                [0xD8; 32],
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
                &mut journal,
            ),
            Err(AtomicFheggAssetSettlementError::Journal(
                AtomicSettlementJournalError::ReplayReservationConflict
            ))
        ));
        assert!(!f.market.is_settled());
        assert_eq!(f.world.current_holder_label(f.asset), Some(SELLER));

        // A third state is neither before nor the journal-bound after image.
        f.world.fund_dregg("unrelated-wallet", 1);
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic_recover(
                transaction_id,
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
                &mut journal,
            ),
            Err(AtomicFheggAssetSettlementError::Journal(
                AtomicSettlementJournalError::LiveStateMismatch(_)
            ))
        ));
        assert!(!f.market.is_settled());
        assert_eq!(f.world.current_holder_label(f.asset), Some(SELLER));

        // Strict decoding refuses one-bit corruption rather than guessing a phase.
        let encoded = journal.records.get_mut(&transaction_id).unwrap();
        encoded[24] ^= 1;
        assert!(matches!(
            f.offering.settle_fhegg_asset_atomic_recover(
                transaction_id,
                &mut f.market,
                &mut f.world,
                f.asset,
                &f.receipt,
                &expected,
                &f.verifier,
                &mut replay,
                &mut journal,
            ),
            Err(AtomicFheggAssetSettlementError::Journal(
                AtomicSettlementJournalError::ChecksumMismatch
            ))
        ));
    }
}
