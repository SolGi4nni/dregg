//! Durable one-shot custody for certified PartyMPC preprocessing.
//!
//! An `FHTRI004` protected row is a one-time pad. Its signatures and sacrifice
//! receipt prove which row was released, but those public facts cannot stop a
//! host from presenting the exact same valid row twice. This module supplies
//! the missing host-side compare-and-set boundary.
//!
//! [`PreprocessingUseLedger::reserve`] first revalidates the complete certified
//! material, then derives a record from the signed batch digest, party slot,
//! exact row commitment, base-session digest, and an unsalted local-row
//! fingerprint. The filename is keyed by that stable fingerprint so merely
//! re-certifying the same secret row cannot reset custody. It atomically
//! creates and durably flushes a checksummed `Reserved` tombstone before the
//! material can reach a hosted MPC runner. A successful run appends and
//! durably flushes a checksummed `Consumed` transition. Both states permanently
//! refuse another reservation after a restart. A crash after reservation
//! therefore sacrifices availability rather than risking one-time-pad reuse;
//! partial writes and corrupt transitions also fail closed.
//!
//! # Storage and platform boundary
//!
//! This module is compiled only on Linux and macOS. It pins the ledger
//! directory with `O_DIRECTORY|O_NOFOLLOW`, performs every record operation
//! relative to that descriptor with `O_NOFOLLOW`, validates owner/mode and
//! inode identity, and serializes record transitions with an advisory file
//! lock. Linux uses `fsync`; macOS uses `F_FULLFSYNC` for both the record and
//! directory. The ledger namespace must be exclusively controlled by the
//! party process identity: another process with the same uid can ignore the
//! advisory lock and Unix supplies no way to defend a directory from its own
//! owner. ACLs must not grant write authority hidden by the mode bits. Root,
//! `CAP_DAC_OVERRIDE`, mount-namespace mutation, unqualified remote/FUSE
//! filesystems, and a kernel or storage device that lies about durable flushes
//! are outside the boundary. Initial ancestor resolution, restart-time pathname
//! resolution, and stable storage/rollback policy remain deployment trust
//! anchors.
//!
//! This is deliberately a narrow runtime-host primitive. It does not make the
//! centralized FHTRI004 candidate/MAC/beacon setup distributed or maliciously
//! secure, and it cannot survive rollback of the entire trusted ledger
//! filesystem. A deployment must keep one stable, rollback-resistant ledger
//! root per party authority and must not copy a row to a fresh ledger root.

use std::fmt;
use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rand::{rngs::OsRng, RngCore};
use rustix::fs::{self as rfs, AtFlags, FlockOperation, Mode, OFlags, Stat};
use sha2::{Digest, Sha256};

use super::{
    run_party_comparison_custody_authorized, run_party_custody_authorized,
    run_party_equality_custody_authorized, PartyArithmeticInput, PartyChannels,
    PartyComparisonInput, PartyEqualityInput, PartyMpcError, PartyMpcSession, PartyReport,
    TripleMaterial,
};

const RECORD_MAGIC: &[u8; 8] = b"FHTUSE02";
const TRANSITION_MAGIC: &[u8; 8] = b"FHTDON02";
const RECORD_VERSION: u32 = 2;
const RESERVED_STATE: u8 = 1;
const CONSUMED_STATE: u8 = 2;
const RECORD_DOMAIN: &[u8] = b"fhegg/fhtri004/preprocessing-use-record/v2";
const TRANSITION_DOMAIN: &[u8] = b"fhegg/fhtri004/preprocessing-use-transition/v2";
const KEY_DOMAIN: &[u8] = b"fhegg/preprocessing-use-stable-key/v2";
const LOCAL_ROW_FINGERPRINT_DOMAIN: &[u8] = b"fhegg/fhtri004/local-row-fingerprint/v1";
const RECORD_PREFIX: &str = ".fhtri004-use-";
const RECORD_SUFFIX: &str = ".tombstone";
const STAGE_PREFIX: &str = ".fhtri004-stage-";
const MAX_STAGE_NAME_ATTEMPTS: usize = 128;

// magic + version + state/padding + batch + base session + signed row + stable
// correlation identity + party + checksum
const RESERVED_RECORD_BYTES: usize = 8 + 4 + 4 + 32 + 32 + 32 + 32 + 8 + 32;
// magic + version + state/padding + key digest + checksum
const CONSUMED_TRANSITION_BYTES: usize = 8 + 4 + 4 + 32 + 32;
const CONSUMED_RECORD_BYTES: usize = RESERVED_RECORD_BYTES + CONSUMED_TRANSITION_BYTES;

/// Exact public identity of one certified party-owned preprocessing row.
///
/// There is intentionally no public constructor. A key can only be derived by
/// revalidating an actual [`TripleMaterial`] carrying the complete FHTRI004
/// certificate and the opening of its signed row commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreprocessingUseKey {
    batch_digest: [u8; 32],
    base_session_digest: [u8; 32],
    row_commitment: [u8; 32],
    correlation_identity: [u8; 32],
    party: u64,
}

impl PreprocessingUseKey {
    pub fn batch_digest(&self) -> [u8; 32] {
        self.batch_digest
    }

    pub fn base_session_digest(&self) -> [u8; 32] {
        self.base_session_digest
    }

    pub fn row_commitment(&self) -> [u8; 32] {
        self.row_commitment
    }

    /// Protocol-stable identity of the underlying local correlation row.
    pub fn correlation_identity(&self) -> [u8; 32] {
        self.correlation_identity
    }

    pub fn party(&self) -> u64 {
        self.party
    }

    /// Content address used for the compare-and-set tombstone filename.
    pub fn digest(&self) -> [u8; 32] {
        key_digest(self)
    }

    fn from_material(material: &TripleMaterial) -> Result<Self, PreprocessingUseError> {
        material
            .validate_runtime_binding()
            .map_err(PreprocessingUseError::InvalidCertifiedMaterial)?;
        let certification = material
            .certification
            .as_ref()
            .ok_or(PreprocessingUseError::UncertifiedMaterial)?;
        let certificate = &certification.certificate;
        let row_commitment = certificate
            .row_commitments
            .get(material.party)
            .copied()
            .ok_or(PreprocessingUseError::InvalidCertifiedMaterial(
                PartyMpcError::InvalidTripleFormationCertificate,
            ))?;
        let correlation_identity = local_row_fingerprint(material);
        Self::from_verified_parts(
            certificate.digest,
            certificate.base_session_digest,
            row_commitment,
            correlation_identity,
            material.party,
        )
    }

    /// Adapter for a future independently verified certificate profile, such
    /// as dealerless FHTRI005. `correlation_identity` must be derived by that
    /// protocol from the underlying row before any re-certification salt or
    /// session wrapper; otherwise re-certification can reset custody. The
    /// constructor stays crate-private so an unverified host assertion cannot
    /// mint a durable-use identity.
    pub(crate) fn from_verified_parts(
        batch_digest: [u8; 32],
        base_session_digest: [u8; 32],
        row_commitment: [u8; 32],
        correlation_identity: [u8; 32],
        party: usize,
    ) -> Result<Self, PreprocessingUseError> {
        if batch_digest == [0; 32] {
            return Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "batch digest",
            });
        }
        if base_session_digest == [0; 32] {
            return Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "base-session digest",
            });
        }
        if row_commitment == [0; 32] {
            return Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "row commitment",
            });
        }
        if correlation_identity == [0; 32] {
            return Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "stable correlation identity",
            });
        }
        Ok(Self {
            batch_digest,
            base_session_digest,
            row_commitment,
            correlation_identity,
            party: u64::try_from(party)
                .map_err(|_| PreprocessingUseError::PartyDoesNotFitLedger)?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreprocessingUseState {
    Reserved,
    Consumed,
}

/// Durable storage failures are distinct from PartyMPC arithmetic failures so
/// a host cannot accidentally treat a failed tombstone write as a retryable
/// protocol error.
#[derive(Debug)]
pub enum PreprocessingUseError {
    LedgerRootUnavailable {
        path: PathBuf,
        source: io::Error,
    },
    LedgerRootNotDirectory {
        path: PathBuf,
    },
    LedgerRootIsSymlink {
        path: PathBuf,
    },
    LedgerRootWrongOwner {
        path: PathBuf,
        expected_uid: u32,
        actual_uid: u32,
    },
    LedgerRootUnsafePermissions {
        path: PathBuf,
        mode: u32,
    },
    LedgerRootReplaced {
        path: PathBuf,
    },
    RecordIo {
        operation: &'static str,
        path: PathBuf,
        source: io::Error,
    },
    CorruptRecord {
        path: PathBuf,
    },
    AlreadyReserved {
        key_digest: [u8; 32],
    },
    AlreadyConsumed {
        key_digest: [u8; 32],
    },
    UncertifiedMaterial,
    InvalidCertifiedMaterial(PartyMpcError),
    PartyDoesNotFitLedger,
    MissingVerifiedIdentityField {
        field: &'static str,
    },
    Runtime(PartyMpcError),
}

impl fmt::Display for PreprocessingUseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LedgerRootUnavailable { path, source } => {
                write!(
                    f,
                    "cannot inspect preprocessing-use ledger {}: {source}",
                    path.display()
                )
            }
            Self::LedgerRootNotDirectory { path } => write!(
                f,
                "preprocessing-use ledger root is not a real directory: {}",
                path.display()
            ),
            Self::LedgerRootIsSymlink { path } => write!(
                f,
                "preprocessing-use ledger root must not be a symlink: {}",
                path.display()
            ),
            Self::LedgerRootWrongOwner {
                path,
                expected_uid,
                actual_uid,
            } => write!(
                f,
                "preprocessing-use ledger {} is owned by uid {actual_uid}, expected {expected_uid}",
                path.display()
            ),
            Self::LedgerRootUnsafePermissions { path, mode } => write!(
                f,
                "preprocessing-use ledger {} has unsafe mode {mode:#o}",
                path.display()
            ),
            Self::LedgerRootReplaced { path } => write!(
                f,
                "preprocessing-use ledger pathname was replaced or detached: {}",
                path.display()
            ),
            Self::RecordIo {
                operation,
                path,
                source,
            } => write!(
                f,
                "cannot {operation} preprocessing-use record {}: {source}",
                path.display()
            ),
            Self::CorruptRecord { path } => write!(
                f,
                "preprocessing-use record is corrupt or non-canonical: {}",
                path.display()
            ),
            Self::AlreadyReserved { key_digest } => write!(
                f,
                "certified preprocessing row is already reserved ({})",
                encode_hex(key_digest)
            ),
            Self::AlreadyConsumed { key_digest } => write!(
                f,
                "certified preprocessing row is already consumed ({})",
                encode_hex(key_digest)
            ),
            Self::UncertifiedMaterial => write!(
                f,
                "durable preprocessing custody requires an FHTRI004 certified row"
            ),
            Self::InvalidCertifiedMaterial(error) => {
                write!(
                    f,
                    "certified preprocessing row failed revalidation: {error}"
                )
            }
            Self::PartyDoesNotFitLedger => {
                write!(
                    f,
                    "preprocessing party index does not fit the ledger format"
                )
            }
            Self::MissingVerifiedIdentityField { field } => {
                write!(f, "verified preprocessing identity has a zero {field}")
            }
            Self::Runtime(error) => write!(f, "reserved PartyMPC execution failed: {error}"),
        }
    }
}

impl std::error::Error for PreprocessingUseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::LedgerRootUnavailable { source, .. } | Self::RecordIo { source, .. } => {
                Some(source)
            }
            Self::InvalidCertifiedMaterial(source) | Self::Runtime(source) => Some(source),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FileIdentity {
    device: u64,
    inode: u64,
}

impl FileIdentity {
    fn from_stat(stat: &Stat) -> Self {
        Self {
            device: stat.st_dev as u64,
            inode: stat.st_ino as u64,
        }
    }
}

#[derive(Debug)]
struct LedgerInner {
    display_root: PathBuf,
    directory: File,
    identity: FileIdentity,
    authority_uid: u32,
}

/// Stable per-party authority for FHTRI004 one-shot row use.
#[derive(Clone, Debug)]
pub struct PreprocessingUseLedger {
    inner: Arc<LedgerInner>,
}

impl PreprocessingUseLedger {
    /// Open and pin an existing ledger directory. Creation and backup/rollback
    /// policy belong to the deployment; silently creating a fresh root would
    /// turn a missing ledger into a replay bypass.
    pub fn open(root: impl AsRef<Path>) -> Result<Self, PreprocessingUseError> {
        let display_root = root.as_ref().to_path_buf();
        if std::fs::symlink_metadata(&display_root)
            .map(|metadata| metadata.file_type().is_symlink())
            .unwrap_or(false)
        {
            return Err(PreprocessingUseError::LedgerRootIsSymlink { path: display_root });
        }
        let authority_uid = rustix::process::geteuid().as_raw();
        let owned = match rfs::open(
            &display_root,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        ) {
            Ok(fd) => fd,
            Err(source) if source == rustix::io::Errno::LOOP => {
                return Err(PreprocessingUseError::LedgerRootIsSymlink { path: display_root });
            }
            Err(source) => {
                return Err(PreprocessingUseError::LedgerRootUnavailable {
                    path: display_root,
                    source: source.into(),
                });
            }
        };
        let directory = File::from(owned);
        let stat = rfs::fstat(&directory).map_err(|source| {
            PreprocessingUseError::LedgerRootUnavailable {
                path: display_root.clone(),
                source: source.into(),
            }
        })?;
        validate_directory_stat(&display_root, &stat, authority_uid)?;
        let identity = FileIdentity::from_stat(&stat);
        validate_root_path_binding(&display_root, identity)?;
        Ok(Self {
            inner: Arc::new(LedgerInner {
                display_root,
                directory,
                identity,
                authority_uid,
            }),
        })
    }

    /// Diagnostic path used when the pinned namespace reports an error.
    pub fn root(&self) -> &Path {
        &self.inner.display_root
    }

    /// Revalidate and durably reserve one exact FHTRI004 row before gate zero.
    pub fn reserve(
        &self,
        material: TripleMaterial,
    ) -> Result<ReservedTripleMaterial, PreprocessingUseError> {
        self.validate_root()?;
        let key = PreprocessingUseKey::from_material(&material)?;
        let reservation = self.reserve_verified_key(key.clone())?;
        Ok(ReservedTripleMaterial {
            material,
            reservation,
        })
    }

    /// Inspect a known row's durable state. Missing records return `Ok(None)`;
    /// malformed, replaced, multiply-linked, or partially written records are
    /// errors.
    pub fn state(
        &self,
        key: &PreprocessingUseKey,
    ) -> Result<Option<PreprocessingUseState>, PreprocessingUseError> {
        self.validate_root()?;
        let name = record_name(key);
        let result = self.read_state_named(&name, key);
        self.validate_root()?;
        result
    }

    pub(crate) fn reserve_verified_key(
        &self,
        key: PreprocessingUseKey,
    ) -> Result<PreprocessingUsePermit, PreprocessingUseError> {
        self.validate_root()?;
        let final_name = record_name(&key);
        let final_path = self.inner.display_root.join(&final_name);
        let (stage_name, mut staged) = self.create_random_stage()?;
        let stage_path = self.inner.display_root.join(&stage_name);
        let staged_identity =
            validate_open_record(&staged, &stage_path, self.inner.authority_uid, 1, None)?;
        staged
            .write_all(&reserved_record(&key))
            .and_then(|_| durable_sync(&staged))
            .map_err(|source| PreprocessingUseError::RecordIo {
                operation: "durably stage reservation",
                path: stage_path.clone(),
                source,
            })?;
        ensure_named_identity(&self.inner, &stage_name, staged_identity, 1, &stage_path)?;

        // The exclusive lock starts before publication. A concurrent loser
        // that opens the final hard link waits until the winner has removed
        // the staging name and durably synced the directory.
        lock_record(&staged, FlockOperation::LockExclusive, &stage_path)?;
        match rfs::linkat(
            &self.inner.directory,
            &stage_name,
            &self.inner.directory,
            &final_name,
            AtFlags::empty(),
        ) {
            Ok(()) => {
                ensure_named_identity(&self.inner, &stage_name, staged_identity, 2, &stage_path)?;
                ensure_named_identity(&self.inner, &final_name, staged_identity, 2, &final_path)?;
                unlink_exact(&self.inner, &stage_name, staged_identity, 2, &stage_path)?;
                ensure_named_identity(&self.inner, &final_name, staged_identity, 1, &final_path)?;
                durable_sync(&self.inner.directory).map_err(|source| {
                    PreprocessingUseError::RecordIo {
                        operation: "durably sync ledger directory after reserving",
                        path: self.inner.display_root.clone(),
                        source,
                    }
                })?;
                self.validate_root()?;
                lock_record(&staged, FlockOperation::Unlock, &final_path)?;
                Ok(PreprocessingUsePermit {
                    inner: Arc::clone(&self.inner),
                    record_name: final_name,
                    record: staged,
                    record_identity: staged_identity,
                    key,
                })
            }
            Err(source) if source == rustix::io::Errno::EXIST => {
                unlink_exact(&self.inner, &stage_name, staged_identity, 1, &stage_path)?;
                durable_sync(&self.inner.directory).map_err(|sync_source| {
                    PreprocessingUseError::RecordIo {
                        operation: "durably remove losing reservation stage",
                        path: self.inner.display_root.clone(),
                        source: sync_source,
                    }
                })?;
                lock_record(&staged, FlockOperation::Unlock, &stage_path)?;
                match self.read_state_named(&final_name, &key)? {
                    Some(PreprocessingUseState::Reserved) => {
                        Err(PreprocessingUseError::AlreadyReserved {
                            key_digest: key.digest(),
                        })
                    }
                    Some(PreprocessingUseState::Consumed) => {
                        Err(PreprocessingUseError::AlreadyConsumed {
                            key_digest: key.digest(),
                        })
                    }
                    None => Err(PreprocessingUseError::CorruptRecord { path: final_path }),
                }
            }
            Err(source) => {
                let _ = unlink_exact(&self.inner, &stage_name, staged_identity, 1, &stage_path);
                Err(PreprocessingUseError::RecordIo {
                    operation: "link compare-and-set reservation",
                    path: final_path,
                    source: source.into(),
                })
            }
        }
    }

    fn create_random_stage(&self) -> Result<(String, File), PreprocessingUseError> {
        let mut random = [0u8; 16];
        for _ in 0..MAX_STAGE_NAME_ATTEMPTS {
            OsRng.fill_bytes(&mut random);
            let name = format!("{STAGE_PREFIX}{}", encode_hex(&random));
            match rfs::openat(
                &self.inner.directory,
                &name,
                OFlags::RDWR
                    | OFlags::APPEND
                    | OFlags::CREATE
                    | OFlags::EXCL
                    | OFlags::NOFOLLOW
                    | OFlags::CLOEXEC
                    | OFlags::NONBLOCK,
                Mode::RUSR | Mode::WUSR,
            ) {
                Ok(fd) => return Ok((name, File::from(fd))),
                Err(source) if source == rustix::io::Errno::EXIST => continue,
                Err(source) => {
                    return Err(PreprocessingUseError::RecordIo {
                        operation: "create random reservation staging record",
                        path: self.inner.display_root.join(name),
                        source: source.into(),
                    });
                }
            }
        }
        Err(PreprocessingUseError::RecordIo {
            operation: "allocate collision-free reservation staging name",
            path: self.inner.display_root.clone(),
            source: io::Error::new(
                io::ErrorKind::AlreadyExists,
                "exhausted random staging-name attempts",
            ),
        })
    }

    fn read_state_named(
        &self,
        name: &str,
        expected_key: &PreprocessingUseKey,
    ) -> Result<Option<PreprocessingUseState>, PreprocessingUseError> {
        let path = self.inner.display_root.join(name);
        let fd = match rfs::openat(
            &self.inner.directory,
            name,
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC | OFlags::NONBLOCK,
            Mode::empty(),
        ) {
            Ok(fd) => fd,
            Err(source) if source == rustix::io::Errno::NOENT => return Ok(None),
            Err(source) if source == rustix::io::Errno::LOOP => {
                return Err(PreprocessingUseError::CorruptRecord { path });
            }
            Err(source) => {
                return Err(PreprocessingUseError::RecordIo {
                    operation: "open descriptor-relative record",
                    path,
                    source: source.into(),
                });
            }
        };
        let mut file = File::from(fd);
        validate_open_record_kind(&file, &path)?;
        lock_record(&file, FlockOperation::LockShared, &path)?;
        let identity = validate_open_record(
            &file,
            &path,
            self.inner.authority_uid,
            1,
            Some(CONSUMED_RECORD_BYTES as u64),
        )?;
        ensure_named_identity(&self.inner, name, identity, 1, &path)?;
        let mut bytes = Vec::with_capacity(CONSUMED_RECORD_BYTES + 1);
        Read::by_ref(&mut file)
            .take((CONSUMED_RECORD_BYTES + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|source| PreprocessingUseError::RecordIo {
                operation: "read descriptor-relative record",
                path: path.clone(),
                source,
            })?;
        ensure_named_identity(&self.inner, name, identity, 1, &path)?;
        let state = parse_record(&bytes, expected_key)
            .map_err(|()| PreprocessingUseError::CorruptRecord { path: path.clone() })?;
        lock_record(&file, FlockOperation::Unlock, &path)?;
        Ok(Some(state))
    }

    fn validate_root(&self) -> Result<(), PreprocessingUseError> {
        let stat = rfs::fstat(&self.inner.directory).map_err(|source| {
            PreprocessingUseError::LedgerRootUnavailable {
                path: self.inner.display_root.clone(),
                source: source.into(),
            }
        })?;
        validate_directory_stat(&self.inner.display_root, &stat, self.inner.authority_uid)?;
        if FileIdentity::from_stat(&stat) != self.inner.identity {
            return Err(PreprocessingUseError::LedgerRootReplaced {
                path: self.inner.display_root.clone(),
            });
        }
        validate_root_path_binding(&self.inner.display_root, self.inner.identity)
    }
}

/// Certified row paired with its already-durable reservation. It intentionally
/// exposes no way to recover the bare [`TripleMaterial`].
pub struct ReservedTripleMaterial {
    material: TripleMaterial,
    reservation: PreprocessingUsePermit,
}

impl ReservedTripleMaterial {
    pub fn key(&self) -> &PreprocessingUseKey {
        self.reservation.key()
    }

    /// Recheck the transport endpoint that is about to own this reservation.
    ///
    /// This exposes no Beaver bit or recoverable material. It lets an
    /// authenticated transport reject a session/party wiring mistake before it
    /// starts any worker thread, while the only execution authority remains the
    /// private token minted by [`Self::into_parts`].
    pub(crate) fn validate_transport_binding(
        &self,
        session: &PartyMpcSession,
        party: usize,
    ) -> Result<(), PartyMpcError> {
        self.material.validate_runtime_binding()?;
        if self.material.session != *session {
            return Err(PartyMpcError::SessionMismatch);
        }
        if self.material.party != party {
            return Err(PartyMpcError::PartyMismatch {
                material: self.material.party,
                channel: party,
            });
        }
        Ok(())
    }

    fn into_parts(
        self,
    ) -> (
        TripleMaterial,
        PreprocessingUsePermit,
        DurableExecutionAuthorization,
    ) {
        (
            self.material,
            self.reservation,
            DurableExecutionAuthorization { _private: () },
        )
    }
}

/// Non-forgeable authorization consumed by the private PartyMPC core. The
/// field is private to this child module, so sibling runtime modules can name
/// but cannot construct the token.
pub(super) struct DurableExecutionAuthorization {
    _private: (),
}

/// Crate-internal permit shared by current FHTRI004 and future independently
/// verified preprocessing profiles. Dropping it retains the reservation.
pub(crate) struct PreprocessingUsePermit {
    inner: Arc<LedgerInner>,
    record_name: String,
    record: File,
    record_identity: FileIdentity,
    key: PreprocessingUseKey,
}

impl PreprocessingUsePermit {
    pub(crate) fn key(&self) -> &PreprocessingUseKey {
        &self.key
    }

    pub(crate) fn consume(mut self) -> Result<(), PreprocessingUseError> {
        let ledger = PreprocessingUseLedger {
            inner: Arc::clone(&self.inner),
        };
        ledger.validate_root()?;
        let path = self.inner.display_root.join(&self.record_name);
        lock_record(&self.record, FlockOperation::LockExclusive, &path)?;
        validate_open_record(
            &self.record,
            &path,
            self.inner.authority_uid,
            1,
            Some(CONSUMED_RECORD_BYTES as u64),
        )?;
        ensure_named_identity(
            &self.inner,
            &self.record_name,
            self.record_identity,
            1,
            &path,
        )?;

        self.record
            .seek(SeekFrom::Start(0))
            .map_err(|source| PreprocessingUseError::RecordIo {
                operation: "rewind before consuming",
                path: path.clone(),
                source,
            })?;
        let mut bytes = Vec::with_capacity(CONSUMED_RECORD_BYTES + 1);
        Read::by_ref(&mut self.record)
            .take((CONSUMED_RECORD_BYTES + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|source| PreprocessingUseError::RecordIo {
                operation: "read before consuming",
                path: path.clone(),
                source,
            })?;
        match parse_record(&bytes, &self.key) {
            Ok(PreprocessingUseState::Reserved) => {}
            Ok(PreprocessingUseState::Consumed) => {
                return Err(PreprocessingUseError::AlreadyConsumed {
                    key_digest: self.key.digest(),
                });
            }
            Err(()) => return Err(PreprocessingUseError::CorruptRecord { path }),
        }

        // O_APPEND makes this monotone even though the preceding read changed
        // the file offset. A torn append remains a corrupt fail-closed record.
        self.record
            .write_all(&consumed_transition(&self.key))
            .and_then(|_| durable_sync(&self.record))
            .map_err(|source| PreprocessingUseError::RecordIo {
                operation: "durably consume",
                path: path.clone(),
                source,
            })?;
        validate_open_record(
            &self.record,
            &path,
            self.inner.authority_uid,
            1,
            Some(CONSUMED_RECORD_BYTES as u64),
        )?;
        ensure_named_identity(
            &self.inner,
            &self.record_name,
            self.record_identity,
            1,
            &path,
        )?;
        durable_sync(&self.inner.directory).map_err(|source| PreprocessingUseError::RecordIo {
            operation: "durably sync ledger directory after consuming",
            path: self.inner.display_root.clone(),
            source,
        })?;
        ledger.validate_root()?;
        lock_record(&self.record, FlockOperation::Unlock, &path)
    }
}

/// Run the crossing circuit through the durable FHTRI004 host boundary.
pub fn run_party_with_durable_preprocessing(
    input: PartyArithmeticInput,
    preprocessing: ReservedTripleMaterial,
    channels: PartyChannels,
) -> Result<PartyReport, PreprocessingUseError> {
    let (material, reservation, authorization) = preprocessing.into_parts();
    let report = run_party_custody_authorized(input, material, channels, authorization)
        .map_err(PreprocessingUseError::Runtime)?;
    reservation.consume()?;
    Ok(report)
}

/// Run scalar equality through the durable FHTRI004 host boundary.
pub fn run_party_equality_with_durable_preprocessing(
    input: PartyEqualityInput,
    preprocessing: ReservedTripleMaterial,
    channels: PartyChannels,
) -> Result<PartyReport, PreprocessingUseError> {
    let (material, reservation, authorization) = preprocessing.into_parts();
    let report = run_party_equality_custody_authorized(input, material, channels, authorization)
        .map_err(PreprocessingUseError::Runtime)?;
    reservation.consume()?;
    Ok(report)
}

/// Run scalar comparison through the durable FHTRI004 host boundary.
pub fn run_party_comparison_with_durable_preprocessing(
    input: PartyComparisonInput,
    preprocessing: ReservedTripleMaterial,
    channels: PartyChannels,
) -> Result<PartyReport, PreprocessingUseError> {
    let (material, reservation, authorization) = preprocessing.into_parts();
    let report = run_party_comparison_custody_authorized(input, material, channels, authorization)
        .map_err(PreprocessingUseError::Runtime)?;
    reservation.consume()?;
    Ok(report)
}

fn validate_directory_stat(
    path: &Path,
    stat: &Stat,
    authority_uid: u32,
) -> Result<(), PreprocessingUseError> {
    if rfs::FileType::from_raw_mode(stat.st_mode as _) != rfs::FileType::Directory {
        return Err(PreprocessingUseError::LedgerRootNotDirectory {
            path: path.to_path_buf(),
        });
    }
    if stat.st_uid as u32 != authority_uid {
        return Err(PreprocessingUseError::LedgerRootWrongOwner {
            path: path.to_path_buf(),
            expected_uid: authority_uid,
            actual_uid: stat.st_uid as u32,
        });
    }
    let mode = stat.st_mode as u32 & 0o7777;
    if mode & 0o022 != 0 || mode & 0o700 != 0o700 || stat.st_nlink == 0 {
        return Err(PreprocessingUseError::LedgerRootUnsafePermissions {
            path: path.to_path_buf(),
            mode,
        });
    }
    Ok(())
}

fn validate_root_path_binding(
    path: &Path,
    expected: FileIdentity,
) -> Result<(), PreprocessingUseError> {
    let metadata = std::fs::symlink_metadata(path).map_err(|source| {
        PreprocessingUseError::LedgerRootUnavailable {
            path: path.to_path_buf(),
            source,
        }
    })?;
    let actual = FileIdentity {
        device: metadata.dev(),
        inode: metadata.ino(),
    };
    if metadata.file_type().is_symlink() || !metadata.is_dir() || actual != expected {
        return Err(PreprocessingUseError::LedgerRootReplaced {
            path: path.to_path_buf(),
        });
    }
    Ok(())
}

fn record_name(key: &PreprocessingUseKey) -> String {
    format!(
        "{RECORD_PREFIX}{}{RECORD_SUFFIX}",
        encode_hex(&key.digest())
    )
}

#[cfg(test)]
fn record_path(root: &Path, key: &PreprocessingUseKey) -> PathBuf {
    root.join(record_name(key))
}

fn validate_open_record_kind(file: &File, path: &Path) -> Result<(), PreprocessingUseError> {
    let stat =
        rfs::fstat(file).map_err(|_| PreprocessingUseError::CorruptRecord { path: path.into() })?;
    if rfs::FileType::from_raw_mode(stat.st_mode as _) != rfs::FileType::RegularFile {
        return Err(PreprocessingUseError::CorruptRecord { path: path.into() });
    }
    Ok(())
}

fn validate_open_record(
    file: &File,
    path: &Path,
    authority_uid: u32,
    expected_links: u64,
    maximum_size: Option<u64>,
) -> Result<FileIdentity, PreprocessingUseError> {
    let stat =
        rfs::fstat(file).map_err(|_| PreprocessingUseError::CorruptRecord { path: path.into() })?;
    let mode = stat.st_mode as u32 & 0o7777;
    if rfs::FileType::from_raw_mode(stat.st_mode as _) != rfs::FileType::RegularFile
        || stat.st_uid as u32 != authority_uid
        || mode != 0o600
        || stat.st_nlink as u64 != expected_links
        || stat.st_size < 0
        || maximum_size.is_some_and(|maximum| stat.st_size as u64 > maximum)
    {
        return Err(PreprocessingUseError::CorruptRecord { path: path.into() });
    }
    Ok(FileIdentity::from_stat(&stat))
}

fn ensure_named_identity(
    inner: &LedgerInner,
    name: &str,
    expected: FileIdentity,
    expected_links: u64,
    path: &Path,
) -> Result<(), PreprocessingUseError> {
    let stat = rfs::statat(&inner.directory, name, AtFlags::SYMLINK_NOFOLLOW)
        .map_err(|_| PreprocessingUseError::CorruptRecord { path: path.into() })?;
    if FileIdentity::from_stat(&stat) != expected
        || rfs::FileType::from_raw_mode(stat.st_mode as _) != rfs::FileType::RegularFile
        || stat.st_uid as u32 != inner.authority_uid
        || (stat.st_mode as u32 & 0o7777) != 0o600
        || stat.st_nlink as u64 != expected_links
    {
        return Err(PreprocessingUseError::CorruptRecord { path: path.into() });
    }
    Ok(())
}

fn unlink_exact(
    inner: &LedgerInner,
    name: &str,
    expected: FileIdentity,
    expected_links: u64,
    path: &Path,
) -> Result<(), PreprocessingUseError> {
    ensure_named_identity(inner, name, expected, expected_links, path)?;
    rfs::unlinkat(&inner.directory, name, AtFlags::empty()).map_err(|source| {
        PreprocessingUseError::RecordIo {
            operation: "unlink descriptor-relative staging record",
            path: path.into(),
            source: source.into(),
        }
    })
}

fn lock_record(
    file: &File,
    operation: FlockOperation,
    path: &Path,
) -> Result<(), PreprocessingUseError> {
    rfs::flock(file, operation).map_err(|source| PreprocessingUseError::RecordIo {
        operation: "lock descriptor-relative record",
        path: path.into(),
        source: source.into(),
    })
}

#[cfg(target_os = "linux")]
fn durable_sync(file: &File) -> io::Result<()> {
    rfs::fsync(file).map_err(Into::into)
}

#[cfg(target_os = "macos")]
fn durable_sync(file: &File) -> io::Result<()> {
    rfs::fsync(file).map_err(io::Error::from)?;
    rfs::fcntl_fullfsync(file).map_err(Into::into)
}

fn parse_record(
    bytes: &[u8],
    expected_key: &PreprocessingUseKey,
) -> Result<PreprocessingUseState, ()> {
    if bytes.len() != RESERVED_RECORD_BYTES && bytes.len() != CONSUMED_RECORD_BYTES {
        return Err(());
    }
    if bytes[..RESERVED_RECORD_BYTES] != reserved_record(expected_key) {
        return Err(());
    }
    if bytes.len() == RESERVED_RECORD_BYTES {
        return Ok(PreprocessingUseState::Reserved);
    }
    if bytes[RESERVED_RECORD_BYTES..] != consumed_transition(expected_key) {
        return Err(());
    }
    Ok(PreprocessingUseState::Consumed)
}

fn reserved_record(key: &PreprocessingUseKey) -> Vec<u8> {
    let mut out = Vec::with_capacity(RESERVED_RECORD_BYTES);
    out.extend_from_slice(RECORD_MAGIC);
    out.extend_from_slice(&RECORD_VERSION.to_be_bytes());
    out.extend_from_slice(&[RESERVED_STATE, 0, 0, 0]);
    out.extend_from_slice(&key.batch_digest);
    out.extend_from_slice(&key.base_session_digest);
    out.extend_from_slice(&key.row_commitment);
    out.extend_from_slice(&key.correlation_identity);
    out.extend_from_slice(&key.party.to_be_bytes());
    let checksum = checksum(RECORD_DOMAIN, &out);
    out.extend_from_slice(&checksum);
    debug_assert_eq!(out.len(), RESERVED_RECORD_BYTES);
    out
}

fn consumed_transition(key: &PreprocessingUseKey) -> Vec<u8> {
    let mut out = Vec::with_capacity(CONSUMED_TRANSITION_BYTES);
    out.extend_from_slice(TRANSITION_MAGIC);
    out.extend_from_slice(&RECORD_VERSION.to_be_bytes());
    out.extend_from_slice(&[CONSUMED_STATE, 0, 0, 0]);
    out.extend_from_slice(&key.digest());
    let checksum = checksum(TRANSITION_DOMAIN, &out);
    out.extend_from_slice(&checksum);
    debug_assert_eq!(out.len(), CONSUMED_TRANSITION_BYTES);
    out
}

fn key_digest(key: &PreprocessingUseKey) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((KEY_DOMAIN.len() as u64).to_be_bytes());
    hash.update(KEY_DOMAIN);
    hash.update(key.correlation_identity);
    hash.update(key.party.to_be_bytes());
    hash.finalize().into()
}

fn local_row_fingerprint(material: &TripleMaterial) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((LOCAL_ROW_FINGERPRINT_DOMAIN.len() as u64).to_be_bytes());
    hash.update(LOCAL_ROW_FINGERPRINT_DOMAIN);
    hash.update((material.party as u64).to_be_bytes());
    hash.update((material.triples.len() as u64).to_be_bytes());
    for triple in &material.triples {
        hash.update([triple.a, triple.b, triple.c]);
    }
    hash.finalize().into()
}

fn checksum(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((domain.len() as u64).to_be_bytes());
    hash.update(domain);
    hash.update((bytes.len() as u64).to_be_bytes());
    hash.update(bytes);
    hash.finalize().into()
}

fn encode_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use std::fs::{self, OpenOptions};
    use std::io::{Seek, SeekFrom};
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    fn key(tag: u8) -> PreprocessingUseKey {
        PreprocessingUseKey {
            batch_digest: [tag; 32],
            base_session_digest: [tag.wrapping_add(1); 32],
            row_commitment: [tag.wrapping_add(2); 32],
            correlation_identity: [tag.wrapping_add(3); 32],
            party: u64::from(tag % 3),
        }
    }

    #[test]
    fn crash_after_reservation_is_a_permanent_tombstone() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let key = key(0x11);
        let reservation = ledger.reserve_verified_key(key.clone()).unwrap();
        assert_eq!(
            ledger.state(&key).unwrap(),
            Some(PreprocessingUseState::Reserved)
        );
        drop(reservation); // model a process crash before gate zero / consume

        let reopened = PreprocessingUseLedger::open(&dir.path).unwrap();
        assert!(matches!(
            reopened.reserve_verified_key(key),
            Err(PreprocessingUseError::AlreadyReserved { .. })
        ));
    }

    #[test]
    fn consumed_transition_survives_restart_and_refuses_replay() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let key = key(0x21);
        ledger
            .reserve_verified_key(key.clone())
            .unwrap()
            .consume()
            .unwrap();
        assert_eq!(
            ledger.state(&key).unwrap(),
            Some(PreprocessingUseState::Consumed)
        );

        let reopened = PreprocessingUseLedger::open(&dir.path).unwrap();
        assert!(matches!(
            reopened.reserve_verified_key(key),
            Err(PreprocessingUseError::AlreadyConsumed { .. })
        ));
    }

    #[test]
    fn concurrent_compare_and_set_has_exactly_one_winner() {
        let dir = TestDir::new();
        let ledger = Arc::new(PreprocessingUseLedger::open(&dir.path).unwrap());
        let key = key(0x31);
        let barrier = Arc::new(Barrier::new(12));
        let threads = (0..12)
            .map(|_| {
                let ledger = Arc::clone(&ledger);
                let key = key.clone();
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    ledger.reserve_verified_key(key)
                })
            })
            .collect::<Vec<_>>();
        let results = threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
        assert_eq!(
            results
                .iter()
                .filter(|result| matches!(
                    result,
                    Err(PreprocessingUseError::AlreadyReserved { .. })
                ))
                .count(),
            11
        );
    }

    #[test]
    fn cross_process_compare_and_set_has_exactly_one_winner() {
        const CHILD_ROOT: &str = "FHEGG_USE_CAS_CHILD_ROOT";
        if let Some(root) = std::env::var_os(CHILD_ROOT) {
            let root = PathBuf::from(root);
            let ledger = PreprocessingUseLedger::open(&root).unwrap();
            let outcome = match ledger.reserve_verified_key(key(0x39)) {
                Ok(permit) => {
                    drop(permit);
                    "winner"
                }
                Err(PreprocessingUseError::AlreadyReserved { .. }) => "loser",
                Err(error) => panic!("unexpected process CAS result: {error}"),
            };
            fs::write(
                root.join(format!("cas-result-{}", std::process::id())),
                outcome,
            )
            .unwrap();
            return;
        }

        let dir = TestDir::new();
        let current = std::env::current_exe().unwrap();
        let test_name =
            "mpc_party::preprocessing_use::tests::cross_process_compare_and_set_has_exactly_one_winner";
        let mut children = (0..8)
            .map(|_| {
                Command::new(&current)
                    .args(["--exact", test_name])
                    .env(CHILD_ROOT, &dir.path)
                    .spawn()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        for child in &mut children {
            assert!(child.wait().unwrap().success());
        }
        let results = fs::read_dir(&dir.path)
            .unwrap()
            .filter_map(Result::ok)
            .filter(|entry| {
                entry
                    .file_name()
                    .to_string_lossy()
                    .starts_with("cas-result-")
            })
            .map(|entry| fs::read_to_string(entry.path()).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            results.iter().filter(|result| *result == "winner").count(),
            1
        );
        assert_eq!(
            results.iter().filter(|result| *result == "loser").count(),
            7
        );
    }

    #[test]
    fn abrupt_process_exit_after_reservation_leaves_tombstone() {
        const CHILD_ROOT: &str = "FHEGG_USE_CRASH_CHILD_ROOT";
        if let Some(root) = std::env::var_os(CHILD_ROOT) {
            let ledger = PreprocessingUseLedger::open(PathBuf::from(root)).unwrap();
            let _permit = ledger.reserve_verified_key(key(0x3a)).unwrap();
            std::process::exit(0);
        }

        let dir = TestDir::new();
        let status = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "mpc_party::preprocessing_use::tests::abrupt_process_exit_after_reservation_leaves_tombstone",
            ])
            .env(CHILD_ROOT, &dir.path)
            .status()
            .unwrap();
        assert!(status.success());
        let reopened = PreprocessingUseLedger::open(&dir.path).unwrap();
        assert!(matches!(
            reopened.reserve_verified_key(key(0x3a)),
            Err(PreprocessingUseError::AlreadyReserved { .. })
        ));
    }

    #[test]
    fn checksum_corruption_fails_closed() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let key = key(0x41);
        drop(ledger.reserve_verified_key(key.clone()).unwrap());
        let path = record_path(&dir.path, &key);
        let original = fs::read(&path).unwrap();
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        file.seek(SeekFrom::Start((RESERVED_RECORD_BYTES - 1) as u64))
            .unwrap();
        file.write_all(&[original[RESERVED_RECORD_BYTES - 1] ^ 1])
            .unwrap();
        file.sync_all().unwrap();
        assert!(matches!(
            ledger.reserve_verified_key(key),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));
    }

    #[test]
    fn torn_consumed_append_fails_closed() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let key = key(0x51);
        drop(ledger.reserve_verified_key(key.clone()).unwrap());
        let path = record_path(&dir.path, &key);
        let partial = consumed_transition(&key);
        let mut file = OpenOptions::new().append(true).open(path).unwrap();
        file.write_all(&partial[..17]).unwrap();
        file.sync_all().unwrap();
        assert!(matches!(
            ledger.reserve_verified_key(key),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));
    }

    #[test]
    fn stable_correlation_identity_prevents_recertification_reset() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let base = key(0x61);
        let mut genuinely_distinct_row = base.clone();
        genuinely_distinct_row.row_commitment[0] ^= 1;
        genuinely_distinct_row.correlation_identity[0] ^= 1;
        let mut recertified_same_row = base.clone();
        recertified_same_row.batch_digest[0] ^= 1;
        recertified_same_row.base_session_digest[0] ^= 1;
        recertified_same_row.row_commitment[0] ^= 1;
        drop(ledger.reserve_verified_key(base).unwrap());
        drop(ledger.reserve_verified_key(genuinely_distinct_row).unwrap());
        assert!(matches!(
            ledger.reserve_verified_key(recertified_same_row),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));
        assert_eq!(
            fs::read_dir(&dir.path)
                .unwrap()
                .filter_map(Result::ok)
                .count(),
            2
        );
    }

    #[test]
    fn future_verified_adapter_refuses_zero_identity_fields() {
        assert!(matches!(
            PreprocessingUseKey::from_verified_parts([0; 32], [1; 32], [2; 32], [3; 32], 0),
            Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "batch digest"
            })
        ));
        assert!(matches!(
            PreprocessingUseKey::from_verified_parts([1; 32], [0; 32], [2; 32], [3; 32], 0),
            Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "base-session digest"
            })
        ));
        assert!(matches!(
            PreprocessingUseKey::from_verified_parts([1; 32], [2; 32], [0; 32], [3; 32], 0),
            Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "row commitment"
            })
        ));
        assert!(matches!(
            PreprocessingUseKey::from_verified_parts([1; 32], [2; 32], [3; 32], [0; 32], 0),
            Err(PreprocessingUseError::MissingVerifiedIdentityField {
                field: "stable correlation identity"
            })
        ));
    }

    #[test]
    fn unsafe_root_modes_and_post_open_chmod_refuse() {
        for mode in [0o770, 0o702, 0o1777] {
            let dir = TestDir::new();
            fs::set_permissions(&dir.path, fs::Permissions::from_mode(mode)).unwrap();
            assert!(matches!(
                PreprocessingUseLedger::open(&dir.path),
                Err(PreprocessingUseError::LedgerRootUnsafePermissions {
                    mode: actual,
                    ..
                }) if actual == mode
            ));
            fs::set_permissions(&dir.path, fs::Permissions::from_mode(0o700)).unwrap();
        }

        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        fs::set_permissions(&dir.path, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(matches!(
            ledger.state(&key(0x72)),
            Err(PreprocessingUseError::LedgerRootUnsafePermissions { .. })
        ));
        fs::set_permissions(&dir.path, fs::Permissions::from_mode(0o700)).unwrap();
    }

    #[test]
    fn wrong_owner_validation_refuses() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let mut stat = rfs::fstat(&ledger.inner.directory).unwrap();
        let actual = ledger.inner.authority_uid.wrapping_add(1);
        stat.st_uid = actual as _;
        assert!(matches!(
            validate_directory_stat(&dir.path, &stat, ledger.inner.authority_uid),
            Err(PreprocessingUseError::LedgerRootWrongOwner {
                actual_uid,
                ..
            }) if actual_uid == actual
        ));
    }

    #[test]
    fn root_rename_and_replacement_refuses_pinned_ledger() {
        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let moved = dir.path.with_extension("pinned-original");
        fs::rename(&dir.path, &moved).unwrap();
        fs::create_dir(&dir.path).unwrap();
        fs::set_permissions(&dir.path, fs::Permissions::from_mode(0o700)).unwrap();
        assert!(matches!(
            ledger.state(&key(0x73)),
            Err(PreprocessingUseError::LedgerRootReplaced { .. })
        ));
        fs::remove_dir(&dir.path).unwrap();
        fs::rename(moved, &dir.path).unwrap();
    }

    #[test]
    fn record_mode_hardlink_fifo_and_replacement_refuse() {
        // Unsafe record mode.
        let mode_dir = TestDir::new();
        let mode_ledger = PreprocessingUseLedger::open(&mode_dir.path).unwrap();
        let mode_key = key(0x74);
        let mode_permit = mode_ledger.reserve_verified_key(mode_key.clone()).unwrap();
        let mode_path = record_path(&mode_dir.path, &mode_key);
        fs::set_permissions(&mode_path, fs::Permissions::from_mode(0o666)).unwrap();
        assert!(matches!(
            mode_ledger.state(&mode_key),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));
        assert!(matches!(
            mode_permit.consume(),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));

        // A second hard link destroys the single-name tombstone invariant.
        let link_dir = TestDir::new();
        let link_ledger = PreprocessingUseLedger::open(&link_dir.path).unwrap();
        let link_key = key(0x75);
        let link_permit = link_ledger.reserve_verified_key(link_key.clone()).unwrap();
        let link_path = record_path(&link_dir.path, &link_key);
        fs::hard_link(&link_path, link_dir.path.join("attacker-link")).unwrap();
        assert!(matches!(
            link_ledger.state(&link_key),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));
        assert!(matches!(
            link_permit.consume(),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));

        // NONBLOCK plus fstat rejects a FIFO without hanging.
        let fifo_dir = TestDir::new();
        let fifo_ledger = PreprocessingUseLedger::open(&fifo_dir.path).unwrap();
        let fifo_key = key(0x76);
        let fifo_path = record_path(&fifo_dir.path, &fifo_key);
        assert!(Command::new("mkfifo")
            .arg(&fifo_path)
            .status()
            .unwrap()
            .success());
        assert!(matches!(
            fifo_ledger.state(&fifo_key),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));

        // Consume retains the inode published by reserve; replacing its name
        // with a byte-identical file cannot redirect the permit.
        let replace_dir = TestDir::new();
        let replace_ledger = PreprocessingUseLedger::open(&replace_dir.path).unwrap();
        let replace_key = key(0x77);
        let replace_permit = replace_ledger
            .reserve_verified_key(replace_key.clone())
            .unwrap();
        let replace_path = record_path(&replace_dir.path, &replace_key);
        let bytes = fs::read(&replace_path).unwrap();
        fs::rename(&replace_path, replace_dir.path.join("displaced-record")).unwrap();
        fs::write(&replace_path, bytes).unwrap();
        fs::set_permissions(&replace_path, fs::Permissions::from_mode(0o600)).unwrap();
        assert!(matches!(
            replace_permit.consume(),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_record_and_ledger_root_refuse() {
        use std::os::unix::fs::symlink;

        let dir = TestDir::new();
        let ledger = PreprocessingUseLedger::open(&dir.path).unwrap();
        let key = key(0x71);
        let target = dir.path.join("attacker-target");
        fs::write(&target, reserved_record(&key)).unwrap();
        symlink(&target, record_path(&dir.path, &key)).unwrap();
        assert!(matches!(
            ledger.reserve_verified_key(key),
            Err(PreprocessingUseError::CorruptRecord { .. })
        ));

        let parent = TestDir::new();
        let link = parent.path.join("ledger-link");
        symlink(&dir.path, &link).unwrap();
        assert!(matches!(
            PreprocessingUseLedger::open(link),
            Err(PreprocessingUseError::LedgerRootIsSymlink { .. })
        ));
    }

    struct TestDir {
        path: PathBuf,
    }

    impl TestDir {
        fn new() -> Self {
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path = std::env::temp_dir().join(format!(
                "fhegg-preprocessing-use-{}-{nonce}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
            Self { path }
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}
