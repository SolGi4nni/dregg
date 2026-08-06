//! Exact-byte durability substrate for Path of Angels' Lean-owned Bazaar state.
//!
//! This module deliberately does not know the shape of `BazaarGame.StateKey`.
//! The only admissible payload is a bounded, non-empty canonical state image
//! emitted by Lean.  Persistence compares the complete image byte-for-byte;
//! it never substitutes a digest, reconstructs a partial Rust state, or runs a
//! second copy of the Bazaar transition semantics.
//!
//! The wire formats are fixed and versioned. Every successful CAS first appends
//! a sequence-checked, hash-chained expected/replacement record to the
//! authoritative journal and fsyncs it; the checksummed head is only a replay-
//! checked cache. A process crash or uncertain write while holding the
//! create-new lock leaves a fail-closed lock file for operator recovery rather
//! than risking a second writer.
//!
//! This is the native engine behind the private checked-Bool persistence and
//! in-memory-replay admission portals. The dependent admission objects are
//! created only by Lean wrappers after those checks succeed. This store still
//! cannot reconstruct private typed Bazaar state from a fresh process by
//! itself; it authenticates the exact replay tail.

use std::fmt;
use std::fs::File;
use std::io::{self, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

const HEAD_MAGIC: &[u8; 8] = b"POAHEAD2";
const JOURNAL_MAGIC: &[u8; 8] = b"POAJNL03";
const JOURNAL_RECORD_MAGIC: &[u8; 8] = b"POAREC03";
const LEGACY_HEAD_MAGIC: &[u8; 8] = b"POAHEAD1";
const LEGACY_JOURNAL_MAGIC: &[u8; 8] = b"POAJNL01";
const STATE_ONLY_JOURNAL_MAGIC: &[u8; 8] = b"POAJNL02";
const HEAD_WIRE_VERSION: u16 = 2;
const JOURNAL_WIRE_VERSION: u16 = 3;
const HEAD_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.durable-head.v2";
const JOURNAL_HEADER_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.journal-header.v3";
const JOURNAL_RECORD_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.journal-record.v3";
const JOURNAL_RECORD_DIGEST_DOMAIN: &str = "dregg.poa-bazaar.journal-chain.v3";
const JOURNAL_GENESIS_DIGEST_DOMAIN: &str = "dregg.poa-bazaar.journal-genesis.v3";
const HEAD_FILE: &str = "bazaar-head-v1.bin";
const JOURNAL_FILE: &str = "bazaar-cas-v1.journal";
const LOCK_FILE: &str = "bazaar-head-v1.lock";
const IDENTITY_FILE: &str = "bazaar-store-identity-v1";
const TEMP_PREFIX: &str = ".bazaar-head-v1.tmp";
const IDENTITY_FORMAT: &str = "POA-BAZAAR-STORE-ID-1";

/// A generous hard ceiling against hostile or corrupt allocation lengths.
/// It is a wire bound, not a claim about the current semantic state size.
pub const MAX_CANONICAL_STATE_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_CANONICAL_EVENT_BYTES: usize = 16 * 1024 * 1024;
const JOURNAL_HEADER_BYTES: usize = 8 + 2 + 32 + 32 + 32;
const MAX_JOURNAL_RECORD_BYTES: usize =
    8 + 2 + 8 + 32 + 1 + 4 + 4 + 4 + MAX_CANONICAL_STATE_BYTES * 2 + MAX_CANONICAL_EVENT_BYTES + 32;
const MAX_JOURNAL_RECORDS: u64 = 1_000_000;

/// Opaque bytes reserved for a complete Lean-emitted `StateKey` image.
///
/// This type does not infer canonicality from byte content. Its constructor is
/// crate-visible so only the eventual Lean bridge (and this crate's tests) can
/// assert that provenance; downstream callers cannot bless arbitrary bytes.
#[derive(Clone, PartialEq, Eq)]
pub struct CanonicalStateBytes(Vec<u8>);

impl CanonicalStateBytes {
    pub(crate) fn new_checked(bytes: Vec<u8>) -> Result<Self, BazaarRestartError> {
        validate_state_len(bytes.len())?;
        Ok(Self(bytes))
    }

    #[cfg(test)]
    pub(crate) fn new(bytes: Vec<u8>) -> Result<Self, BazaarRestartError> {
        Self::new_checked(bytes)
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.0
    }
}

/// Exact canonical command-event payload emitted and decoded by Lean.
#[derive(Clone, PartialEq, Eq)]
pub struct CanonicalEventBytes(Vec<u8>);

impl CanonicalEventBytes {
    pub(crate) fn new_checked(bytes: Vec<u8>) -> Result<Self, BazaarRestartError> {
        if bytes.is_empty() {
            return Err(BazaarRestartError::InvalidWire("empty canonical event"));
        }
        if bytes.len() > MAX_CANONICAL_EVENT_BYTES {
            return Err(BazaarRestartError::InvalidWire(
                "canonical event exceeds maximum",
            ));
        }
        Ok(Self(bytes))
    }

    #[cfg(test)]
    pub(crate) fn new(bytes: Vec<u8>) -> Result<Self, BazaarRestartError> {
        Self::new_checked(bytes)
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for CanonicalEventBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CanonicalEventBytes")
            .field("len", &self.0.len())
            .field("digest", &blake3::hash(&self.0).to_hex().as_str())
            .finish()
    }
}

impl fmt::Debug for CanonicalStateBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CanonicalStateBytes")
            .field("len", &self.0.len())
            .field("digest", &blake3::hash(&self.0).to_hex().as_str())
            .finish()
    }
}

/// Exact request produced from Lean's dependent `RuntimeCasRequest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BazaarCasRequest {
    expected: Option<CanonicalStateBytes>,
    replacement: CanonicalStateBytes,
}

impl BazaarCasRequest {
    pub(crate) fn new_checked(
        expected: Option<CanonicalStateBytes>,
        replacement: CanonicalStateBytes,
    ) -> Self {
        Self {
            expected,
            replacement,
        }
    }

    #[cfg(test)]
    pub(crate) fn new(
        expected: Option<CanonicalStateBytes>,
        replacement: CanonicalStateBytes,
    ) -> Self {
        Self::new_checked(expected, replacement)
    }

    pub fn expected(&self) -> Option<&CanonicalStateBytes> {
        self.expected.as_ref()
    }

    pub fn replacement(&self) -> &CanonicalStateBytes {
        &self.replacement
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BazaarCasOutcome {
    Applied {
        previous: Option<CanonicalStateBytes>,
        current: CanonicalStateBytes,
    },
    Stale {
        observed: Option<CanonicalStateBytes>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct JournalEvent {
    sequence: u64,
    predecessor_digest: [u8; 32],
    expected: Option<CanonicalStateBytes>,
    replacement: CanonicalStateBytes,
    command_event: Option<CanonicalEventBytes>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AuthenticatedJournalRecord {
    pub sequence: u64,
    pub predecessor_digest: [u8; 32],
    pub expected: Option<CanonicalStateBytes>,
    pub replacement: CanonicalStateBytes,
    pub command_event: CanonicalEventBytes,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct JournalReplay {
    record_count: u64,
    tail_digest: [u8; 32],
    tail: Option<CanonicalStateBytes>,
}

impl JournalReplay {
    fn empty(identity: &[u8; 32], deployment_id: &[u8; 32]) -> Self {
        Self {
            record_count: 0,
            tail_digest: journal_bound_digest(
                JOURNAL_GENESIS_DIGEST_DOMAIN,
                identity,
                deployment_id,
                &[],
            ),
            tail: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BazaarStoreIdentity {
    encoded: String,
    binding: [u8; 32],
}

impl BazaarStoreIdentity {
    fn parse(value: String) -> Result<Self, BazaarRestartError> {
        if value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            let mut binding = [0u8; 32];
            for (index, chunk) in value.as_bytes().chunks_exact(2).enumerate() {
                binding[index] = (hex_nibble(chunk[0]) << 4) | hex_nibble(chunk[1]);
            }
            Ok(Self {
                encoded: value,
                binding,
            })
        } else {
            Err(BazaarRestartError::Configuration(
                "Bazaar store identity must be 64 lowercase hexadecimal digits".into(),
            ))
        }
    }

    #[cfg(test)]
    pub(crate) fn test(value: u8) -> Self {
        Self {
            encoded: format!("{value:02x}").repeat(32),
            binding: [value; 32],
        }
    }
}

fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => unreachable!("store identity was validated before decoding"),
    }
}

pub(crate) fn parse_hex_digest(value: &str, label: &str) -> Result<[u8; 32], BazaarRestartError> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(BazaarRestartError::Configuration(format!(
            "{label} must be 64 lowercase hexadecimal digits"
        )));
    }
    let mut digest = [0u8; 32];
    for (index, chunk) in value.as_bytes().chunks_exact(2).enumerate() {
        digest[index] = (hex_nibble(chunk[0]) << 4) | hex_nibble(chunk[1]);
    }
    Ok(digest)
}

const UNBOUND_STORE_IDENTITY: [u8; 32] = [0; 32];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BazaarRecoveryOutcome {
    pub record_count: u64,
    pub recovered_head: CanonicalStateBytes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CasFault {
    AfterJournalWrite,
    AfterJournalSync,
    AfterHeadRename,
}

#[derive(Debug)]
pub enum BazaarRestartError {
    InvalidWire(&'static str),
    Busy,
    Configuration(String),
    IndeterminateCommit(io::Error),
    UnsafePath(&'static str),
    Io(io::Error),
}

impl fmt::Display for BazaarRestartError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWire(reason) => write!(f, "invalid Bazaar restart wire: {reason}"),
            Self::Busy => write!(f, "Bazaar head is locked by another writer or recovery"),
            Self::Configuration(reason) => {
                write!(f, "invalid Bazaar runtime configuration: {reason}")
            }
            Self::IndeterminateCommit(error) => write!(
                f,
                "Bazaar CAS may have reached durable storage; recovery lock preserved: {error}"
            ),
            Self::UnsafePath(reason) => write!(f, "unsafe Bazaar store path: {reason}"),
            Self::Io(error) => write!(f, "Bazaar restart I/O error: {error}"),
        }
    }
}

impl std::error::Error for BazaarRestartError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) | Self::IndeterminateCommit(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for BazaarRestartError {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}

/// One deployment's exact canonical Bazaar head.
#[derive(Clone, Debug)]
pub struct DurableBazaarHeadStore {
    root: PathBuf,
    root_dir: Arc<File>,
    owner_uid: u32,
    identity: Option<BazaarStoreIdentity>,
    deployment_id: [u8; 32],
}

impl DurableBazaarHeadStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, BazaarRestartError> {
        let owner_uid = platform_effective_uid()?;
        Self::open_inner(root.as_ref(), owner_uid, None, [0; 32])
    }

    fn open_inner(
        root: &Path,
        owner_uid: u32,
        identity: Option<BazaarStoreIdentity>,
        deployment_id: [u8; 32],
    ) -> Result<Self, BazaarRestartError> {
        if !root.is_absolute() {
            return Err(BazaarRestartError::UnsafePath(
                "store root must be absolute",
            ));
        }
        let root_dir = secure_open_root(root, owner_uid)?;
        let store = Self {
            root: root.to_path_buf(),
            root_dir: Arc::new(root_dir),
            owner_uid,
            identity,
            deployment_id,
        };
        if store.identity.is_some() {
            store.verify_or_create_identity()?;
        }
        Ok(store)
    }

    pub(crate) fn open_bound(
        root: impl AsRef<Path>,
        identity: BazaarStoreIdentity,
    ) -> Result<Self, BazaarRestartError> {
        let owner_uid = platform_effective_uid()?;
        Self::open_inner(root.as_ref(), owner_uid, Some(identity), [0; 32])
    }

    pub(crate) fn open_bound_deployment(
        root: impl AsRef<Path>,
        identity: BazaarStoreIdentity,
        deployment_id: [u8; 32],
    ) -> Result<Self, BazaarRestartError> {
        let owner_uid = platform_effective_uid()?;
        Self::open_inner(root.as_ref(), owner_uid, Some(identity), deployment_id)
    }

    #[cfg(test)]
    pub(crate) fn open_with_expected_owner(
        root: impl AsRef<Path>,
        owner_uid: u32,
    ) -> Result<Self, BazaarRestartError> {
        Self::open_inner(root.as_ref(), owner_uid, None, [0; 32])
    }

    pub fn load(&self) -> Result<Option<CanonicalStateBytes>, BazaarRestartError> {
        self.verify_root_path_still_same()?;
        self.verify_identity()?;
        let replay = replay_journal(self)?;
        let mut cached =
            match secure_open_regular_at(&self.root_dir, HEAD_FILE, self.owner_uid, false, false) {
                Ok(file) => file,
                Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::NotFound => {
                    if replay.record_count == 0 {
                        self.verify_root_path_still_same()?;
                        return Ok(None);
                    }
                    return Err(BazaarRestartError::InvalidWire(
                        "journal has records but head cache is absent",
                    ));
                }
                Err(error) => return Err(error),
            };
        let maximum = 8 + 2 + 32 + 4 + MAX_CANONICAL_STATE_BYTES + 32;
        let mut bytes = Vec::new();
        (&mut cached)
            .take((maximum + 1) as u64)
            .read_to_end(&mut bytes)?;
        verify_name_still_same(&self.root_dir, HEAD_FILE, &cached, self.owner_uid)?;
        if bytes.len() > maximum {
            return Err(BazaarRestartError::InvalidWire("head exceeds maximum"));
        }
        let head = decode_head(&bytes, self.format_identity())?;
        if replay.record_count == 0 {
            return Err(BazaarRestartError::InvalidWire(
                "head cache exists without an authoritative journal",
            ));
        }
        if replay.tail.as_ref() != Some(&head) {
            return Err(BazaarRestartError::InvalidWire(
                "head cache does not match replayed journal tail",
            ));
        }
        self.verify_root_path_still_same()?;
        Ok(Some(head))
    }

    fn verify_root_path_still_same(&self) -> Result<(), BazaarRestartError> {
        secure_verify_root_still_same(&self.root, &self.root_dir, self.owner_uid)
    }

    fn format_identity(&self) -> &[u8; 32] {
        self.identity
            .as_ref()
            .map_or(&UNBOUND_STORE_IDENTITY, |identity| &identity.binding)
    }

    fn identity_bytes(identity: &BazaarStoreIdentity) -> Vec<u8> {
        format!("{IDENTITY_FORMAT}\n{}\n", identity.encoded).into_bytes()
    }

    fn verify_or_create_identity(&self) -> Result<(), BazaarRestartError> {
        let Some(identity) = &self.identity else {
            return Ok(());
        };
        match self.read_identity() {
            Ok(observed) => {
                if observed == Self::identity_bytes(identity) {
                    Ok(())
                } else {
                    Err(BazaarRestartError::UnsafePath(
                        "store identity does not match pinned deployment",
                    ))
                }
            }
            Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::NotFound => {
                for entry in [HEAD_FILE, JOURNAL_FILE, LOCK_FILE] {
                    match secure_open_regular_at(
                        &self.root_dir,
                        entry,
                        self.owner_uid,
                        false,
                        false,
                    ) {
                        Err(BazaarRestartError::Io(error))
                            if error.kind() == io::ErrorKind::NotFound => {}
                        Ok(_) => {
                            return Err(BazaarRestartError::UnsafePath(
                                "store identity is absent beside existing durable state",
                            ));
                        }
                        Err(error) => return Err(error),
                    }
                }
                let mut file = secure_open_regular_at(
                    &self.root_dir,
                    IDENTITY_FILE,
                    self.owner_uid,
                    true,
                    false,
                )?;
                file.write_all(&Self::identity_bytes(identity))?;
                file.sync_all()?;
                self.root_dir.sync_all()?;
                verify_name_still_same(&self.root_dir, IDENTITY_FILE, &file, self.owner_uid)?;
                self.verify_root_path_still_same()?;
                Ok(())
            }
            Err(error) => Err(error),
        }
    }

    fn read_identity(&self) -> Result<Vec<u8>, BazaarRestartError> {
        let mut file =
            secure_open_regular_at(&self.root_dir, IDENTITY_FILE, self.owner_uid, false, false)?;
        let mut bytes = Vec::new();
        (&mut file).take(256).read_to_end(&mut bytes)?;
        verify_name_still_same(&self.root_dir, IDENTITY_FILE, &file, self.owner_uid)?;
        Ok(bytes)
    }

    fn verify_identity(&self) -> Result<(), BazaarRestartError> {
        let Some(identity) = &self.identity else {
            return Ok(());
        };
        if self.read_identity()? == Self::identity_bytes(identity) {
            Ok(())
        } else {
            Err(BazaarRestartError::UnsafePath(
                "store identity does not match pinned deployment",
            ))
        }
    }

    fn install_head_cache(
        &self,
        state: &CanonicalStateBytes,
        fault: Option<CasFault>,
    ) -> Result<(), BazaarRestartError> {
        let bytes = encode_head(state, self.format_identity());
        let temp = format!("{TEMP_PREFIX}.{}.{}", std::process::id(), unique_nonce());
        let write_result = (|| -> Result<(), BazaarRestartError> {
            let mut file =
                secure_open_regular_at(&self.root_dir, &temp, self.owner_uid, true, false)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            verify_name_still_same(&self.root_dir, &temp, &file, self.owner_uid)?;
            secure_rename_at(&self.root_dir, &temp, HEAD_FILE)?;
            if fault == Some(CasFault::AfterHeadRename) {
                return Err(BazaarRestartError::IndeterminateCommit(io::Error::other(
                    "injected failure after head rename",
                )));
            }
            self.root_dir.sync_all()?;
            Ok(())
        })();
        if write_result.is_err() {
            let _ = secure_unlink_at(&self.root_dir, &temp);
        }
        write_result
    }

    fn validate_existing_head_path(&self) -> Result<(), BazaarRestartError> {
        match secure_open_regular_at(&self.root_dir, HEAD_FILE, self.owner_uid, false, false) {
            Ok(file) => verify_name_still_same(&self.root_dir, HEAD_FILE, &file, self.owner_uid),
            Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            Err(error) => Err(error),
        }
    }

    /// Administrative recovery only. It grants no game admission and accepts
    /// no caller state: the exact cache image is rebuilt solely from a fully
    /// replayed, pinned-store journal tail. The sticky writer lock is cleared
    /// only after a second full load verifies journal, cache, and identity.
    pub(crate) fn recover_sticky_head<F>(
        &self,
        mut validate_canonical: F,
    ) -> Result<BazaarRecoveryOutcome, BazaarRestartError>
    where
        F: FnMut(&[u8]) -> Result<bool, BazaarRestartError>,
    {
        if self.identity.is_none() {
            return Err(BazaarRestartError::Configuration(
                "Bazaar recovery requires a pinned store identity".into(),
            ));
        }
        let mut recovery_lock = WriterLock::acquire_recovery(self)?;
        self.verify_identity()?;
        sync_journal(self)?;
        let replay = replay_journal_with_validator(self, &mut validate_canonical)?;
        let tail = replay.tail.clone().ok_or(BazaarRestartError::InvalidWire(
            "cannot recover an empty journal",
        ))?;
        self.validate_existing_head_path()?;
        self.install_head_cache(&tail, None)?;
        if self.load()?.as_ref() != Some(&tail) {
            return Err(BazaarRestartError::InvalidWire(
                "recovered head did not match replayed journal tail",
            ));
        }
        self.verify_identity()?;
        recovery_lock.release_on_drop();
        drop(recovery_lock);
        Ok(BazaarRecoveryOutcome {
            record_count: replay.record_count,
            recovered_head: tail,
        })
    }

    /// Compare the complete expected canonical image and durably install the
    /// complete replacement. `expected = None` succeeds only at genesis.
    pub fn compare_and_swap(
        &self,
        request: &BazaarCasRequest,
    ) -> Result<BazaarCasOutcome, BazaarRestartError> {
        self.compare_and_swap_inner(request, None, None)
    }

    pub(crate) fn compare_and_swap_journaled(
        &self,
        request: &BazaarCasRequest,
        command_event: CanonicalEventBytes,
    ) -> Result<BazaarCasOutcome, BazaarRestartError> {
        self.compare_and_swap_inner(request, Some(command_event), None)
    }

    pub(crate) fn require_replay_context(
        &self,
        store_identity: &[u8; 32],
        deployment_id: &[u8; 32],
    ) -> Result<(), BazaarRestartError> {
        if self.format_identity() != store_identity {
            return Err(BazaarRestartError::InvalidWire(
                "command event store identity mismatch",
            ));
        }
        if &self.deployment_id != deployment_id {
            return Err(BazaarRestartError::InvalidWire(
                "command event deployment identity mismatch",
            ));
        }
        Ok(())
    }

    fn compare_and_swap_inner(
        &self,
        request: &BazaarCasRequest,
        command_event: Option<CanonicalEventBytes>,
        fault: Option<CasFault>,
    ) -> Result<BazaarCasOutcome, BazaarRestartError> {
        let mut lock = WriterLock::acquire(self)?;
        let observed = self.load()?;
        if observed.as_ref() != request.expected.as_ref() {
            lock.release_on_drop();
            return Ok(BazaarCasOutcome::Stale { observed });
        }

        let replay = replay_journal(self)?;
        if replay.tail.as_ref() != observed.as_ref() {
            return Err(BazaarRestartError::InvalidWire(
                "journal tail changed during serialized CAS",
            ));
        }
        let event = JournalEvent {
            sequence: replay.record_count,
            predecessor_digest: replay.tail_digest,
            expected: request.expected.clone(),
            replacement: request.replacement.clone(),
            command_event,
        };
        append_journal_event(self, &event, fault)?;

        self.install_head_cache(&request.replacement, fault)?;
        self.verify_root_path_still_same()?;
        lock.release_on_drop();
        drop(lock);

        Ok(BazaarCasOutcome::Applied {
            previous: observed,
            current: request.replacement.clone(),
        })
    }

    #[cfg(test)]
    pub(crate) fn compare_and_swap_with_fault(
        &self,
        request: &BazaarCasRequest,
        fault: CasFault,
    ) -> Result<BazaarCasOutcome, BazaarRestartError> {
        self.compare_and_swap_inner(request, None, Some(fault))
    }

    /// Test seam for the descriptor/pathname stability check. It deliberately
    /// replaces the cache pathname after opening the original inode; the
    /// verifier must refuse even though the replacement bytes are identical.
    #[cfg(test)]
    pub(crate) fn detect_head_inode_substitution(&self) -> Result<(), BazaarRestartError> {
        let mut opened =
            secure_open_regular_at(&self.root_dir, HEAD_FILE, self.owner_uid, false, false)?;
        let mut bytes = Vec::new();
        opened.read_to_end(&mut bytes)?;
        let old = format!("{TEMP_PREFIX}.substituted.{}", unique_nonce());
        secure_rename_at(&self.root_dir, HEAD_FILE, &old)?;
        let mut replacement =
            secure_open_regular_at(&self.root_dir, HEAD_FILE, self.owner_uid, true, false)?;
        replacement.write_all(&bytes)?;
        replacement.sync_all()?;
        self.root_dir.sync_all()?;
        verify_name_still_same(&self.root_dir, HEAD_FILE, &opened, self.owner_uid)
    }
}

struct WriterLock {
    root_dir: Arc<File>,
    file: File,
    owner_uid: u32,
    remove_on_drop: bool,
}

impl WriterLock {
    fn acquire(store: &DurableBazaarHeadStore) -> Result<Self, BazaarRestartError> {
        let mut file = match secure_open_regular_at(
            &store.root_dir,
            LOCK_FILE,
            store.owner_uid,
            true,
            false,
        ) {
            Ok(file) => file,
            Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::AlreadyExists => {
                // An existing lock is still untrusted input. Validate its
                // owner, mode, type, and link count before reporting Busy.
                let existing = secure_open_regular_at(
                    &store.root_dir,
                    LOCK_FILE,
                    store.owner_uid,
                    false,
                    false,
                )?;
                match secure_try_lock_exclusive(&existing) {
                    Ok(()) | Err(BazaarRestartError::Busy) => {
                        return Err(BazaarRestartError::Busy);
                    }
                    Err(error) => return Err(error),
                }
            }
            Err(error) => return Err(error),
        };
        secure_try_lock_exclusive(&file)?;
        file.write_all(format!("{}\n", std::process::id()).as_bytes())?;
        file.sync_all()?;
        verify_name_still_same(&store.root_dir, LOCK_FILE, &file, store.owner_uid)?;
        store.root_dir.sync_all()?;
        Ok(Self {
            root_dir: store.root_dir.clone(),
            file,
            owner_uid: store.owner_uid,
            remove_on_drop: false,
        })
    }

    fn acquire_recovery(store: &DurableBazaarHeadStore) -> Result<Self, BazaarRestartError> {
        let file =
            secure_open_regular_at(&store.root_dir, LOCK_FILE, store.owner_uid, false, true)?;
        secure_try_lock_exclusive(&file)?;
        verify_name_still_same(&store.root_dir, LOCK_FILE, &file, store.owner_uid)?;
        Ok(Self {
            root_dir: store.root_dir.clone(),
            file,
            owner_uid: store.owner_uid,
            remove_on_drop: false,
        })
    }

    fn release_on_drop(&mut self) {
        self.remove_on_drop = true;
    }
}

impl Drop for WriterLock {
    fn drop(&mut self) {
        if !self.remove_on_drop {
            return;
        }
        if verify_name_still_same(&self.root_dir, LOCK_FILE, &self.file, self.owner_uid).is_err() {
            return;
        }
        if secure_unlink_at(&self.root_dir, LOCK_FILE).is_ok() {
            let _ = self.root_dir.sync_all();
        }
    }
}

fn encode_journal_header(identity: &[u8; 32], deployment_id: &[u8; 32]) -> Vec<u8> {
    let mut header = Vec::with_capacity(JOURNAL_HEADER_BYTES);
    header.extend_from_slice(JOURNAL_MAGIC);
    header.extend_from_slice(&JOURNAL_WIRE_VERSION.to_be_bytes());
    header.extend_from_slice(identity);
    header.extend_from_slice(deployment_id);
    append_journal_checksum(
        &mut header,
        JOURNAL_HEADER_CHECKSUM_DOMAIN,
        identity,
        deployment_id,
    );
    header
}

fn decode_journal_header(
    bytes: &[u8],
    expected_identity: &[u8; 32],
    expected_deployment_id: &[u8; 32],
) -> Result<(), BazaarRestartError> {
    if bytes.starts_with(LEGACY_JOURNAL_MAGIC) {
        return Err(BazaarRestartError::InvalidWire(
            "legacy journal format lacks embedded store identity",
        ));
    }
    if bytes.starts_with(STATE_ONLY_JOURNAL_MAGIC) {
        return Err(BazaarRestartError::InvalidWire(
            "legacy state-only journal lacks canonical command events",
        ));
    }
    if bytes.len() != JOURNAL_HEADER_BYTES {
        return Err(BazaarRestartError::InvalidWire("journal header length"));
    }
    if bytes[..8] != *JOURNAL_MAGIC {
        return Err(BazaarRestartError::InvalidWire("journal magic"));
    }
    if u16::from_be_bytes(
        bytes[8..10]
            .try_into()
            .map_err(|_| BazaarRestartError::InvalidWire("journal version width"))?,
    ) != JOURNAL_WIRE_VERSION
    {
        return Err(BazaarRestartError::InvalidWire("journal version"));
    }
    if bytes[10..42] != expected_identity[..] {
        return Err(BazaarRestartError::InvalidWire(
            "journal store identity mismatch",
        ));
    }
    if bytes[42..74] != expected_deployment_id[..] {
        return Err(BazaarRestartError::InvalidWire(
            "journal deployment identity mismatch",
        ));
    }
    checked_journal_body(
        bytes,
        JOURNAL_HEADER_CHECKSUM_DOMAIN,
        expected_identity,
        expected_deployment_id,
    )?;
    Ok(())
}

fn encode_journal_event(
    event: &JournalEvent,
    identity: &[u8; 32],
    deployment_id: &[u8; 32],
) -> Vec<u8> {
    let expected_len = event.expected.as_ref().map_or(0, |value| value.0.len());
    let event_len = event
        .command_event
        .as_ref()
        .map_or(0, |value| value.0.len());
    let mut record = Vec::with_capacity(
        8 + 2 + 8 + 32 + 1 + 4 + 4 + 4 + expected_len + event.replacement.0.len() + event_len + 32,
    );
    record.extend_from_slice(JOURNAL_RECORD_MAGIC);
    record.extend_from_slice(&JOURNAL_WIRE_VERSION.to_be_bytes());
    record.extend_from_slice(&event.sequence.to_be_bytes());
    record.extend_from_slice(&event.predecessor_digest);
    record.push(u8::from(event.expected.is_some()));
    record.extend_from_slice(&(expected_len as u32).to_be_bytes());
    record.extend_from_slice(&(event.replacement.0.len() as u32).to_be_bytes());
    record.extend_from_slice(&(event_len as u32).to_be_bytes());
    if let Some(expected) = &event.expected {
        record.extend_from_slice(&expected.0);
    }
    record.extend_from_slice(&event.replacement.0);
    if let Some(command_event) = &event.command_event {
        record.extend_from_slice(&command_event.0);
    }
    append_journal_checksum(
        &mut record,
        JOURNAL_RECORD_CHECKSUM_DOMAIN,
        identity,
        deployment_id,
    );
    record
}

fn decode_journal_event(
    bytes: &[u8],
    identity: &[u8; 32],
    deployment_id: &[u8; 32],
) -> Result<JournalEvent, BazaarRestartError> {
    if bytes.len() > MAX_JOURNAL_RECORD_BYTES {
        return Err(BazaarRestartError::InvalidWire(
            "journal record exceeds maximum",
        ));
    }
    let body = checked_journal_body(
        bytes,
        JOURNAL_RECORD_CHECKSUM_DOMAIN,
        identity,
        deployment_id,
    )?;
    let mut cursor = 0usize;
    if take::<8>(body, &mut cursor)? != *JOURNAL_RECORD_MAGIC {
        return Err(BazaarRestartError::InvalidWire("journal record magic"));
    }
    if u16::from_be_bytes(take::<2>(body, &mut cursor)?) != JOURNAL_WIRE_VERSION {
        return Err(BazaarRestartError::InvalidWire("journal record version"));
    }
    let sequence = u64::from_be_bytes(take::<8>(body, &mut cursor)?);
    let predecessor_digest = take::<32>(body, &mut cursor)?;
    let expected_present = match take::<1>(body, &mut cursor)?[0] {
        0 => false,
        1 => true,
        _ => return Err(BazaarRestartError::InvalidWire("journal option tag")),
    };
    let expected_len = decode_len(body, &mut cursor)?;
    let replacement_len = decode_len(body, &mut cursor)?;
    let event_len = decode_len(body, &mut cursor)?;
    if expected_present != (expected_len != 0) {
        return Err(BazaarRestartError::InvalidWire(
            "journal expected tag/length mismatch",
        ));
    }
    if expected_present {
        validate_state_len(expected_len)?;
    }
    validate_state_len(replacement_len)?;
    if event_len > MAX_CANONICAL_EVENT_BYTES {
        return Err(BazaarRestartError::InvalidWire(
            "canonical event exceeds maximum",
        ));
    }
    let expected = if expected_present {
        Some(CanonicalStateBytes(take_vec(
            body,
            &mut cursor,
            expected_len,
        )?))
    } else {
        None
    };
    let replacement = CanonicalStateBytes(take_vec(body, &mut cursor, replacement_len)?);
    let command_event = if event_len == 0 {
        None
    } else {
        Some(CanonicalEventBytes(take_vec(body, &mut cursor, event_len)?))
    };
    if cursor != body.len() {
        return Err(BazaarRestartError::InvalidWire(
            "journal record trailing bytes",
        ));
    }
    Ok(JournalEvent {
        sequence,
        predecessor_digest,
        expected,
        replacement,
        command_event,
    })
}

fn journal_record_digest(record: &[u8], identity: &[u8; 32], deployment_id: &[u8; 32]) -> [u8; 32] {
    journal_bound_digest(
        JOURNAL_RECORD_DIGEST_DOMAIN,
        identity,
        deployment_id,
        record,
    )
}

fn replay_journal(store: &DurableBazaarHeadStore) -> Result<JournalReplay, BazaarRestartError> {
    replay_journal_core(store, &mut |_| Ok(true), &mut |_| Ok(()))
}

fn replay_journal_with_validator<F>(
    store: &DurableBazaarHeadStore,
    validate_canonical: &mut F,
) -> Result<JournalReplay, BazaarRestartError>
where
    F: FnMut(&[u8]) -> Result<bool, BazaarRestartError>,
{
    replay_journal_core(store, validate_canonical, &mut |_| Ok(()))
}

fn replay_journal_core<F, V>(
    store: &DurableBazaarHeadStore,
    validate_canonical: &mut F,
    visit: &mut V,
) -> Result<JournalReplay, BazaarRestartError>
where
    F: FnMut(&[u8]) -> Result<bool, BazaarRestartError>,
    V: FnMut(&JournalEvent) -> Result<(), BazaarRestartError>,
{
    let file = match secure_open_regular_at(
        &store.root_dir,
        JOURNAL_FILE,
        store.owner_uid,
        false,
        false,
    ) {
        Ok(file) => file,
        Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::NotFound => {
            return Ok(JournalReplay::empty(
                store.format_identity(),
                &store.deployment_id,
            ));
        }
        Err(error) => return Err(error),
    };
    let mut reader = BufReader::new(file);
    let mut header = [0u8; JOURNAL_HEADER_BYTES];
    reader
        .read_exact(&mut header[..8])
        .map_err(|_| BazaarRestartError::InvalidWire("truncated journal magic"))?;
    if header[..8] == *LEGACY_JOURNAL_MAGIC {
        return Err(BazaarRestartError::InvalidWire(
            "legacy journal format lacks embedded store identity",
        ));
    }
    if header[..8] == *STATE_ONLY_JOURNAL_MAGIC {
        return Err(BazaarRestartError::InvalidWire(
            "legacy state-only journal lacks canonical command events",
        ));
    }
    reader
        .read_exact(&mut header[8..])
        .map_err(|_| BazaarRestartError::InvalidWire("truncated journal header"))?;
    decode_journal_header(&header, store.format_identity(), &store.deployment_id)?;

    let mut replay = JournalReplay::empty(store.format_identity(), &store.deployment_id);
    loop {
        let mut first = [0u8; 1];
        match reader.read(&mut first) {
            Ok(0) => break,
            Ok(1) => {}
            Ok(_) => unreachable!("one-byte buffer"),
            Err(error) => return Err(error.into()),
        }
        let mut length_bytes = [0u8; 4];
        length_bytes[0] = first[0];
        reader
            .read_exact(&mut length_bytes[1..])
            .map_err(|_| BazaarRestartError::InvalidWire("truncated journal frame length"))?;
        let record_len = u32::from_be_bytes(length_bytes) as usize;
        if record_len == 0 || record_len > MAX_JOURNAL_RECORD_BYTES {
            return Err(BazaarRestartError::InvalidWire(
                "journal frame length exceeds bound",
            ));
        }
        if replay.record_count >= MAX_JOURNAL_RECORDS {
            return Err(BazaarRestartError::InvalidWire(
                "journal record count exceeds bound",
            ));
        }
        let mut record = vec![0u8; record_len];
        reader
            .read_exact(&mut record)
            .map_err(|_| BazaarRestartError::InvalidWire("truncated journal record"))?;
        let event = decode_journal_event(&record, store.format_identity(), &store.deployment_id)?;
        if event.sequence != replay.record_count {
            return Err(BazaarRestartError::InvalidWire(
                "journal sequence is not contiguous",
            ));
        }
        if event.predecessor_digest != replay.tail_digest {
            return Err(BazaarRestartError::InvalidWire(
                "journal predecessor digest mismatch",
            ));
        }
        if event.expected != replay.tail {
            return Err(BazaarRestartError::InvalidWire(
                "journal expected state does not match prior replacement",
            ));
        }
        if !validate_canonical(event.replacement.as_bytes())? {
            return Err(BazaarRestartError::InvalidWire(
                "journal replacement is not a canonical Lean StateKey",
            ));
        }
        visit(&event)?;
        replay.record_count += 1;
        replay.tail_digest =
            journal_record_digest(&record, store.format_identity(), &store.deployment_id);
        replay.tail = Some(event.replacement);
    }
    let file = reader.into_inner();
    verify_name_still_same(&store.root_dir, JOURNAL_FILE, &file, store.owner_uid)?;
    Ok(replay)
}

impl DurableBazaarHeadStore {
    pub(crate) fn load_authenticated_journal_records(
        &self,
    ) -> Result<Vec<AuthenticatedJournalRecord>, BazaarRestartError> {
        self.verify_root_path_still_same()?;
        self.verify_identity()?;
        let mut records = Vec::new();
        replay_journal_core(self, &mut |_| Ok(true), &mut |event| {
            let command_event =
                event
                    .command_event
                    .clone()
                    .ok_or(BazaarRestartError::InvalidWire(
                        "journal record lacks canonical command event",
                    ))?;
            records.push(AuthenticatedJournalRecord {
                sequence: event.sequence,
                predecessor_digest: event.predecessor_digest,
                expected: event.expected.clone(),
                replacement: event.replacement.clone(),
                command_event,
            });
            Ok(())
        })?;
        Ok(records)
    }
}

fn append_journal_event(
    store: &DurableBazaarHeadStore,
    event: &JournalEvent,
    fault: Option<CasFault>,
) -> Result<(), BazaarRestartError> {
    let (mut file, new_file) =
        match secure_open_regular_at(&store.root_dir, JOURNAL_FILE, store.owner_uid, false, true) {
            Ok(file) => (file, false),
            Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::NotFound => (
                secure_open_regular_at(&store.root_dir, JOURNAL_FILE, store.owner_uid, true, true)?,
                true,
            ),
            Err(error) => return Err(error),
        };
    if new_file {
        file.write_all(&encode_journal_header(
            store.format_identity(),
            &store.deployment_id,
        ))?;
    }
    let record = encode_journal_event(event, store.format_identity(), &store.deployment_id);
    let record_len = u32::try_from(record.len())
        .map_err(|_| BazaarRestartError::InvalidWire("journal record length overflow"))?;
    file.write_all(&record_len.to_be_bytes())?;
    file.write_all(&record)?;
    if fault == Some(CasFault::AfterJournalWrite) {
        return Err(BazaarRestartError::IndeterminateCommit(io::Error::other(
            "injected failure after journal write",
        )));
    }
    file.sync_all()
        .map_err(BazaarRestartError::IndeterminateCommit)?;
    verify_name_still_same(&store.root_dir, JOURNAL_FILE, &file, store.owner_uid)?;
    if fault == Some(CasFault::AfterJournalSync) {
        return Err(BazaarRestartError::IndeterminateCommit(io::Error::other(
            "injected failure after journal sync",
        )));
    }
    store
        .root_dir
        .sync_all()
        .map_err(BazaarRestartError::IndeterminateCommit)?;
    Ok(())
}

fn sync_journal(store: &DurableBazaarHeadStore) -> Result<(), BazaarRestartError> {
    let file = secure_open_regular_at(&store.root_dir, JOURNAL_FILE, store.owner_uid, false, true)?;
    file.sync_all()?;
    verify_name_still_same(&store.root_dir, JOURNAL_FILE, &file, store.owner_uid)?;
    store.root_dir.sync_all()?;
    store.verify_root_path_still_same()?;
    Ok(())
}

fn encode_head(state: &CanonicalStateBytes, identity: &[u8; 32]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + 2 + 32 + 4 + state.0.len() + 32);
    out.extend_from_slice(HEAD_MAGIC);
    out.extend_from_slice(&HEAD_WIRE_VERSION.to_be_bytes());
    out.extend_from_slice(identity);
    out.extend_from_slice(&(state.0.len() as u32).to_be_bytes());
    out.extend_from_slice(&state.0);
    append_checksum(&mut out, HEAD_CHECKSUM_DOMAIN, identity);
    out
}

fn decode_head(
    bytes: &[u8],
    expected_identity: &[u8; 32],
) -> Result<CanonicalStateBytes, BazaarRestartError> {
    if bytes.starts_with(LEGACY_HEAD_MAGIC) {
        return Err(BazaarRestartError::InvalidWire(
            "legacy head format lacks embedded store identity",
        ));
    }
    if bytes.len() < 8 + 2 + 32 + 4 + 32 {
        return Err(BazaarRestartError::InvalidWire("truncated head"));
    }
    if bytes[..8] != *HEAD_MAGIC {
        return Err(BazaarRestartError::InvalidWire("head magic"));
    }
    if u16::from_be_bytes(
        bytes[8..10]
            .try_into()
            .map_err(|_| BazaarRestartError::InvalidWire("head version width"))?,
    ) != HEAD_WIRE_VERSION
    {
        return Err(BazaarRestartError::InvalidWire("head version"));
    }
    if bytes[10..42] != expected_identity[..] {
        return Err(BazaarRestartError::InvalidWire(
            "head store identity mismatch",
        ));
    }
    let body = checked_body(bytes, HEAD_CHECKSUM_DOMAIN, expected_identity)?;
    let mut cursor = 0usize;
    if take::<8>(body, &mut cursor)? != *HEAD_MAGIC {
        return Err(BazaarRestartError::InvalidWire("head magic"));
    }
    if u16::from_be_bytes(take::<2>(body, &mut cursor)?) != HEAD_WIRE_VERSION {
        return Err(BazaarRestartError::InvalidWire("head version"));
    }
    if take::<32>(body, &mut cursor)? != *expected_identity {
        return Err(BazaarRestartError::InvalidWire(
            "head store identity mismatch",
        ));
    }
    let len = decode_len(body, &mut cursor)?;
    validate_state_len(len)?;
    let state = CanonicalStateBytes(take_vec(body, &mut cursor, len)?);
    if cursor != body.len() {
        return Err(BazaarRestartError::InvalidWire("head trailing bytes"));
    }
    Ok(state)
}

fn validate_state_len(len: usize) -> Result<(), BazaarRestartError> {
    if len == 0 {
        Err(BazaarRestartError::InvalidWire("empty canonical state"))
    } else if len > MAX_CANONICAL_STATE_BYTES {
        Err(BazaarRestartError::InvalidWire(
            "canonical state exceeds maximum",
        ))
    } else {
        Ok(())
    }
}

fn identity_bound_digest(domain: &str, identity: &[u8; 32], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(identity);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn journal_bound_digest(
    domain: &str,
    identity: &[u8; 32],
    deployment_id: &[u8; 32],
    bytes: &[u8],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(identity);
    hasher.update(deployment_id);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn append_checksum(bytes: &mut Vec<u8>, domain: &str, identity: &[u8; 32]) {
    let digest = identity_bound_digest(domain, identity, bytes);
    bytes.extend_from_slice(&digest);
}

fn append_journal_checksum(
    bytes: &mut Vec<u8>,
    domain: &str,
    identity: &[u8; 32],
    deployment_id: &[u8; 32],
) {
    let digest = journal_bound_digest(domain, identity, deployment_id, bytes);
    bytes.extend_from_slice(&digest);
}

fn checked_body<'a>(
    bytes: &'a [u8],
    domain: &str,
    identity: &[u8; 32],
) -> Result<&'a [u8], BazaarRestartError> {
    if bytes.len() < 32 {
        return Err(BazaarRestartError::InvalidWire("truncated checksum"));
    }
    let (body, checksum) = bytes.split_at(bytes.len() - 32);
    if identity_bound_digest(domain, identity, body).as_slice() != checksum {
        return Err(BazaarRestartError::InvalidWire("checksum"));
    }
    Ok(body)
}

fn checked_journal_body<'a>(
    bytes: &'a [u8],
    domain: &str,
    identity: &[u8; 32],
    deployment_id: &[u8; 32],
) -> Result<&'a [u8], BazaarRestartError> {
    if bytes.len() < 32 {
        return Err(BazaarRestartError::InvalidWire("truncated checksum"));
    }
    let (body, checksum) = bytes.split_at(bytes.len() - 32);
    if journal_bound_digest(domain, identity, deployment_id, body).as_slice() != checksum {
        return Err(BazaarRestartError::InvalidWire("checksum"));
    }
    Ok(body)
}

fn decode_len(bytes: &[u8], cursor: &mut usize) -> Result<usize, BazaarRestartError> {
    Ok(u32::from_be_bytes(take::<4>(bytes, cursor)?) as usize)
}

fn take<const N: usize>(bytes: &[u8], cursor: &mut usize) -> Result<[u8; N], BazaarRestartError> {
    let end = cursor
        .checked_add(N)
        .filter(|end| *end <= bytes.len())
        .ok_or(BazaarRestartError::InvalidWire("truncated field"))?;
    let value = bytes[*cursor..end]
        .try_into()
        .map_err(|_| BazaarRestartError::InvalidWire("field width"))?;
    *cursor = end;
    Ok(value)
}

fn take_vec(bytes: &[u8], cursor: &mut usize, len: usize) -> Result<Vec<u8>, BazaarRestartError> {
    let end = cursor
        .checked_add(len)
        .filter(|end| *end <= bytes.len())
        .ok_or(BazaarRestartError::InvalidWire("truncated payload"))?;
    let value = bytes[*cursor..end].to_vec();
    *cursor = end;
    Ok(value)
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
mod secure_fs {
    use super::{BazaarRestartError, File, Path};
    use std::ffi::CString;
    use std::io;
    use std::os::fd::{AsRawFd, FromRawFd};
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    use std::path::Component;

    const O_RDONLY: i32 = 0;
    const O_WRONLY: i32 = 1;
    const LOCK_EX: i32 = 2;
    const LOCK_NB: i32 = 4;

    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_APPEND: i32 = 0x400;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_CREAT: i32 = 0x40;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_EXCL: i32 = 0x80;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_CLOEXEC: i32 = 0x8_0000;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_DIRECTORY: i32 = 0x1_0000;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_NOFOLLOW: i32 = 0x2_0000;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    const ELOOP: i32 = 40;

    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const O_APPEND: i32 = 0x0008;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const O_CREAT: i32 = 0x0200;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const O_EXCL: i32 = 0x0800;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const O_CLOEXEC: i32 = 0x100_0000;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const O_DIRECTORY: i32 = 0x10_0000;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const O_NOFOLLOW: i32 = 0x0100;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    const ELOOP: i32 = 62;

    unsafe extern "C" {
        fn openat(dirfd: i32, path: *const i8, flags: i32, mode: u32) -> i32;
        fn renameat(olddirfd: i32, oldpath: *const i8, newdirfd: i32, newpath: *const i8) -> i32;
        fn unlinkat(dirfd: i32, path: *const i8, flags: i32) -> i32;
        fn geteuid() -> u32;
        fn flock(fd: i32, operation: i32) -> i32;
    }

    fn name(value: &str) -> Result<CString, BazaarRestartError> {
        if value.is_empty() || value.as_bytes().contains(&b'/') {
            return Err(BazaarRestartError::UnsafePath(
                "store entry name is not one path component",
            ));
        }
        CString::new(value).map_err(|_| BazaarRestartError::UnsafePath("store entry contains NUL"))
    }

    fn openat_file(
        directory: &File,
        path: &CString,
        flags: i32,
        mode: u32,
    ) -> Result<File, BazaarRestartError> {
        // SAFETY: both descriptors and the NUL-terminated path are live for the call.
        let fd = unsafe { openat(directory.as_raw_fd(), path.as_ptr(), flags, mode) };
        if fd < 0 {
            return Err(io::Error::last_os_error().into());
        }
        // SAFETY: successful `openat` returns one newly owned descriptor.
        Ok(unsafe { File::from_raw_fd(fd) })
    }

    fn validate_root(file: &File, owner_uid: u32) -> Result<(), BazaarRestartError> {
        let metadata = file.metadata()?;
        if !metadata.is_dir() {
            return Err(BazaarRestartError::UnsafePath("root is not a directory"));
        }
        if metadata.uid() != owner_uid {
            return Err(BazaarRestartError::UnsafePath(
                "root owner does not match trusted runtime user",
            ));
        }
        if metadata.mode() & 0o077 != 0 {
            return Err(BazaarRestartError::UnsafePath(
                "root permissions are not private",
            ));
        }
        Ok(())
    }

    fn validate_regular(file: &File, owner_uid: u32) -> Result<(), BazaarRestartError> {
        let metadata = file.metadata()?;
        if !metadata.is_file() {
            return Err(BazaarRestartError::UnsafePath(
                "store entry is not a regular file",
            ));
        }
        if metadata.uid() != owner_uid {
            return Err(BazaarRestartError::UnsafePath(
                "store entry owner does not match trusted runtime user",
            ));
        }
        if metadata.mode() & 0o077 != 0 {
            return Err(BazaarRestartError::UnsafePath(
                "store entry permissions are not private",
            ));
        }
        if metadata.nlink() != 1 {
            return Err(BazaarRestartError::UnsafePath(
                "store entry link count is not one",
            ));
        }
        Ok(())
    }

    pub fn effective_uid() -> u32 {
        // SAFETY: `geteuid` has no arguments or memory effects visible to Rust.
        unsafe { geteuid() }
    }

    pub fn open_root(path: &Path, owner_uid: u32) -> Result<File, BazaarRestartError> {
        let mut directory = File::open("/")?;
        let mut saw_root = false;
        for component in path.components() {
            match component {
                Component::RootDir => saw_root = true,
                Component::Normal(part) if saw_root => {
                    let part = CString::new(part.as_bytes()).map_err(|_| {
                        BazaarRestartError::UnsafePath("store path component contains NUL")
                    })?;
                    directory = openat_file(
                        &directory,
                        &part,
                        O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC,
                        0,
                    )
                    .map_err(|error| match error {
                        BazaarRestartError::Io(io_error)
                            if io_error.kind() == io::ErrorKind::NotFound =>
                        {
                            BazaarRestartError::Io(io_error)
                        }
                        _ => BazaarRestartError::UnsafePath(
                            "store path has a symlink or non-directory ancestor",
                        ),
                    })?;
                }
                _ => {
                    return Err(BazaarRestartError::UnsafePath(
                        "store path is not a normalized absolute path",
                    ));
                }
            }
        }
        validate_root(&directory, owner_uid)?;
        Ok(directory)
    }

    pub fn verify_root_same(
        path: &Path,
        opened: &File,
        owner_uid: u32,
    ) -> Result<(), BazaarRestartError> {
        validate_root(opened, owner_uid)?;
        let current = open_root(path, owner_uid).map_err(|_| {
            BazaarRestartError::UnsafePath("configured root no longer names the opened store")
        })?;
        let opened_metadata = opened.metadata()?;
        let current_metadata = current.metadata()?;
        if opened_metadata.dev() != current_metadata.dev()
            || opened_metadata.ino() != current_metadata.ino()
        {
            return Err(BazaarRestartError::UnsafePath(
                "configured root inode changed during operation",
            ));
        }
        Ok(())
    }

    pub fn open_regular(
        root: &File,
        entry: &str,
        owner_uid: u32,
        create_new: bool,
        append: bool,
    ) -> Result<File, BazaarRestartError> {
        let mut flags = if append {
            O_WRONLY | O_APPEND
        } else if create_new {
            O_WRONLY
        } else {
            O_RDONLY
        };
        flags |= O_NOFOLLOW | O_CLOEXEC;
        if create_new {
            flags |= O_CREAT | O_EXCL;
        }
        let file = match openat_file(root, &name(entry)?, flags, 0o600) {
            Err(BazaarRestartError::Io(error)) if error.raw_os_error() == Some(ELOOP) => {
                return Err(BazaarRestartError::UnsafePath("store entry is a symlink"));
            }
            result => result?,
        };
        if create_new {
            // `openat` is variadic and Darwin's `mode_t` is narrower than
            // Linux's. Normalize the descriptor itself before it is ever
            // reopened or published; the containing root is already 0700.
            file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
        }
        validate_regular(&file, owner_uid)?;
        Ok(file)
    }

    pub fn verify_same(
        root: &File,
        entry: &str,
        open_file: &File,
        owner_uid: u32,
    ) -> Result<(), BazaarRestartError> {
        validate_regular(open_file, owner_uid)?;
        let current = open_regular(root, entry, owner_uid, false, false)?;
        let opened = open_file.metadata()?;
        let now = current.metadata()?;
        if opened.dev() != now.dev() || opened.ino() != now.ino() {
            return Err(BazaarRestartError::UnsafePath(
                "store entry inode changed during operation",
            ));
        }
        Ok(())
    }

    pub fn rename(root: &File, old: &str, new: &str) -> Result<(), BazaarRestartError> {
        let old = name(old)?;
        let new = name(new)?;
        // SAFETY: one live root descriptor anchors both validated component names.
        if unsafe {
            renameat(
                root.as_raw_fd(),
                old.as_ptr(),
                root.as_raw_fd(),
                new.as_ptr(),
            )
        } != 0
        {
            return Err(io::Error::last_os_error().into());
        }
        Ok(())
    }

    pub fn unlink(root: &File, entry: &str) -> Result<(), BazaarRestartError> {
        let entry = name(entry)?;
        // SAFETY: the root descriptor and component name are live and `flags=0` targets a file.
        if unsafe { unlinkat(root.as_raw_fd(), entry.as_ptr(), 0) } != 0 {
            return Err(io::Error::last_os_error().into());
        }
        Ok(())
    }

    pub fn try_lock_exclusive(file: &File) -> Result<(), BazaarRestartError> {
        // SAFETY: `flock` operates on the live descriptor and does not retain it.
        if unsafe { flock(file.as_raw_fd(), LOCK_EX | LOCK_NB) } != 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::WouldBlock {
                return Err(BazaarRestartError::Busy);
            }
            return Err(error.into());
        }
        Ok(())
    }
}

fn platform_effective_uid() -> Result<u32, BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        Ok(secure_fs::effective_uid())
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn secure_open_root(path: &Path, owner_uid: u32) -> Result<File, BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::open_root(path, owner_uid)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = (path, owner_uid);
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn secure_verify_root_still_same(
    path: &Path,
    opened: &File,
    owner_uid: u32,
) -> Result<(), BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::verify_root_same(path, opened, owner_uid)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = (path, opened, owner_uid);
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn secure_open_regular_at(
    root: &File,
    entry: &str,
    owner_uid: u32,
    create_new: bool,
    append: bool,
) -> Result<File, BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::open_regular(root, entry, owner_uid, create_new, append)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = (root, entry, owner_uid, create_new, append);
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn verify_name_still_same(
    root: &File,
    entry: &str,
    open_file: &File,
    owner_uid: u32,
) -> Result<(), BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::verify_same(root, entry, open_file, owner_uid)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = (root, entry, open_file, owner_uid);
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn secure_rename_at(root: &File, old: &str, new: &str) -> Result<(), BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::rename(root, old, new)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = (root, old, new);
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn secure_unlink_at(root: &File, entry: &str) -> Result<(), BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::unlink(root, entry)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = (root, entry);
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix descriptor-relative filesystem primitives",
        ))
    }
}

fn secure_try_lock_exclusive(file: &File) -> Result<(), BazaarRestartError> {
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    ))]
    {
        secure_fs::try_lock_exclusive(file)
    }
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    {
        let _ = file;
        Err(BazaarRestartError::UnsafePath(
            "Bazaar store requires Unix advisory-lock primitives",
        ))
    }
}

/// Trusted node configuration for the single Bazaar journal served by this
/// process. The path is pinned on first use so a mutable environment cannot
/// redirect later CAS calls across deployments.
pub const BAZAAR_STORE_DIR_ENV: &str = "DREGG_POA_BAZAAR_STORE_DIR";
pub const BAZAAR_STORE_ID_ENV: &str = "DREGG_POA_BAZAAR_STORE_ID";
pub const BAZAAR_DEPLOYMENT_ID_ENV: &str = "DREGG_POA_BAZAAR_DEPLOYMENT_ID";

struct BazaarRuntimeConfig {
    root: PathBuf,
    identity: BazaarStoreIdentity,
    deployment_id: [u8; 32],
}

fn configured_runtime() -> Result<&'static BazaarRuntimeConfig, BazaarRestartError> {
    use std::sync::OnceLock;

    static CONFIG: OnceLock<Result<BazaarRuntimeConfig, String>> = OnceLock::new();
    CONFIG
        .get_or_init(|| {
            let raw = std::env::var_os(BAZAAR_STORE_DIR_ENV)
                .ok_or_else(|| format!("{BAZAAR_STORE_DIR_ENV} is not set"))?;
            let path = PathBuf::from(raw);
            if !path.is_absolute() {
                return Err(format!("{BAZAAR_STORE_DIR_ENV} must be absolute"));
            }
            let identity = std::env::var(BAZAAR_STORE_ID_ENV)
                .map_err(|_| format!("{BAZAAR_STORE_ID_ENV} is not set"))?;
            let identity =
                BazaarStoreIdentity::parse(identity).map_err(|error| error.to_string())?;
            let deployment_id = std::env::var(BAZAAR_DEPLOYMENT_ID_ENV)
                .map_err(|_| format!("{BAZAAR_DEPLOYMENT_ID_ENV} is not set"))?;
            let deployment_id = parse_hex_digest(&deployment_id, "Bazaar deployment identity")
                .map_err(|error| error.to_string())?;
            Ok(BazaarRuntimeConfig {
                root: path,
                identity,
                deployment_id,
            })
        })
        .as_ref()
        .map_err(|reason| BazaarRestartError::Configuration(reason.clone()))
}

pub(crate) fn configured_runtime_store() -> Result<DurableBazaarHeadStore, BazaarRestartError> {
    let config = configured_runtime()?;
    DurableBazaarHeadStore::open_bound_deployment(
        &config.root,
        config.identity.clone(),
        config.deployment_id,
    )
}

pub(crate) fn load_configured_canonical_head(
) -> Result<Option<CanonicalStateBytes>, BazaarRestartError> {
    configured_runtime_store()?.load()
}

pub(crate) fn recover_configured_runtime_store<F>(
    validate_canonical: F,
) -> Result<BazaarRecoveryOutcome, BazaarRestartError>
where
    F: FnMut(&[u8]) -> Result<bool, BazaarRestartError>,
{
    configured_runtime_store()?.recover_sticky_head(validate_canonical)
}

fn unique_nonce() -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    NEXT.fetch_add(1, Ordering::Relaxed)
}
