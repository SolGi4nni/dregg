//! Durable authority epochs for frontend-owned game-session addresses.
//!
//! [`OfferingHost`] deliberately owns game state, not deployment identity. A
//! frontend that exposes a durable `(offering, session)` route therefore needs
//! two additional pieces of routing custody:
//!
//! - one random [`GameHostIncarnation`] retained across ordinary process
//!   restarts; and
//! - one monotone generation for every game address, retained while the
//!   session is resumed and incremented whenever that address is closed and
//!   opened as a fresh world.
//!
//! This ledger is the small shared implementation of that custody. It is not a
//! lock service and does not make two processes safe to run against the same
//! session store concurrently. A deployment still has one writer. Every
//! mutation is, however, written to a temporary file, synced, atomically
//! renamed, and directory-synced before it becomes visible in memory.

use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use dreggnet_offerings::SessionId;

use crate::{GameHostIncarnation, GameSessionRef};

const INCARNATION_FILE: &str = "host-incarnation.v1";
const SESSIONS_FILE: &str = "session-generations.v1";
const SESSIONS_MAGIC: &[u8; 8] = b"DREGGE01";

/// A durable game-epoch custody failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameEpochError {
    Io {
        operation: &'static str,
        path: PathBuf,
        detail: String,
    },
    Corrupt(String),
    InvalidAddress(String),
    MissingActiveGeneration {
        offering: String,
        session: String,
    },
    GenerationExhausted {
        offering: String,
        session: String,
    },
    Poisoned,
}

impl GameEpochError {
    fn io(operation: &'static str, path: impl Into<PathBuf>, error: io::Error) -> Self {
        Self::Io {
            operation,
            path: path.into(),
            detail: error.to_string(),
        }
    }
}

impl std::fmt::Display for GameEpochError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io {
                operation,
                path,
                detail,
            } => write!(f, "could not {operation} {}: {detail}", path.display()),
            Self::Corrupt(detail) => write!(f, "corrupt game epoch ledger: {detail}"),
            Self::InvalidAddress(detail) => write!(f, "invalid game epoch address: {detail}"),
            Self::MissingActiveGeneration { offering, session } => write!(
                f,
                "durable session {offering}/{session} is live but has no active generation"
            ),
            Self::GenerationExhausted { offering, session } => write!(
                f,
                "game session generation exhausted for {offering}/{session}"
            ),
            Self::Poisoned => write!(f, "game epoch ledger lock was poisoned"),
        }
    }
}

impl std::error::Error for GameEpochError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EpochRecord {
    generation: u64,
    active: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct EpochState {
    records: BTreeMap<(String, String), EpochRecord>,
}

#[derive(Debug)]
enum Backing {
    Memory,
    Durable(PathBuf),
}

#[derive(Debug)]
struct LedgerInner {
    incarnation: GameHostIncarnation,
    backing: Backing,
    state: Mutex<EpochState>,
}

/// Cloneable custody handle for one host incarnation and its game generations.
#[derive(Clone, Debug)]
pub struct GameEpochLedger(Arc<LedgerInner>);

impl GameEpochLedger {
    /// Construct a deterministic in-memory ledger for tests and confined
    /// adapters. It carries no restart claim.
    pub fn in_memory(incarnation: GameHostIncarnation) -> Self {
        Self(Arc::new(LedgerInner {
            incarnation,
            backing: Backing::Memory,
            state: Mutex::new(EpochState::default()),
        }))
    }

    /// Construct an in-memory ledger with a fresh OS-random incarnation.
    pub fn in_memory_random() -> Result<Self, GameEpochError> {
        Ok(Self::in_memory(random_incarnation()?))
    }

    /// Open or create the durable ledger rooted at `directory`.
    ///
    /// Existing corrupt or partial authority files are refused. In particular,
    /// this never silently replaces a malformed incarnation with a new host
    /// identity or treats malformed session generations as an empty ledger.
    pub fn open(directory: impl AsRef<Path>) -> Result<Self, GameEpochError> {
        let directory = directory.as_ref().to_path_buf();
        fs::create_dir_all(&directory)
            .map_err(|error| GameEpochError::io("create epoch directory", &directory, error))?;
        let incarnation = open_incarnation(&directory)?;
        let sessions_path = directory.join(SESSIONS_FILE);
        let state = match fs::read(&sessions_path) {
            Ok(bytes) => decode_state(&bytes)?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => EpochState::default(),
            Err(error) => {
                return Err(GameEpochError::io(
                    "read session generations",
                    sessions_path,
                    error,
                ));
            }
        };
        Ok(Self(Arc::new(LedgerInner {
            incarnation,
            backing: Backing::Durable(directory),
            state: Mutex::new(state),
        })))
    }

    pub fn host_incarnation(&self) -> GameHostIncarnation {
        self.0.incarnation
    }

    /// Reconcile the result of [`OfferingHost::ensure_open`](dreggnet_offerings::OfferingHost::ensure_open)
    /// with epoch custody and return the live generation.
    ///
    /// A genuinely fresh host session always receives the next generation,
    /// even if a prior process died after the host state was forgotten but
    /// before an old `active` bit could be cleared. A resumed/existing durable
    /// session must already have an active generation. The in-memory backend
    /// may adopt an already-open session as generation one because it makes no
    /// durability claim; this keeps custom/test hosts usable without weakening
    /// the production backend.
    pub fn bind_after_ensure(
        &self,
        offering: &str,
        session: &SessionId,
        newly_opened: bool,
    ) -> Result<u64, GameEpochError> {
        validate_address(offering, session)?;
        let address = (offering.to_string(), session.0.clone());
        let mut state = self.0.state.lock().map_err(|_| GameEpochError::Poisoned)?;

        if !newly_opened {
            if let Some(record) = state.records.get(&address).filter(|record| record.active) {
                return Ok(record.generation);
            }
            if matches!(self.0.backing, Backing::Durable(_)) {
                return Err(GameEpochError::MissingActiveGeneration {
                    offering: offering.to_string(),
                    session: session.0.clone(),
                });
            }
        }

        let previous = state
            .records
            .get(&address)
            .map(|record| record.generation)
            .unwrap_or(0);
        let generation =
            previous
                .checked_add(1)
                .ok_or_else(|| GameEpochError::GenerationExhausted {
                    offering: offering.to_string(),
                    session: session.0.clone(),
                })?;
        let mut candidate = state.clone();
        candidate.records.insert(
            address,
            EpochRecord {
                generation,
                active: true,
            },
        );
        self.persist(&candidate)?;
        *state = candidate;
        Ok(generation)
    }

    /// Return the active generation, refusing absent and closed addresses.
    pub fn current_generation(
        &self,
        offering: &str,
        session: &SessionId,
    ) -> Result<u64, GameEpochError> {
        validate_address(offering, session)?;
        let state = self.0.state.lock().map_err(|_| GameEpochError::Poisoned)?;
        state
            .records
            .get(&(offering.to_string(), session.0.clone()))
            .filter(|record| record.active)
            .map(|record| record.generation)
            .ok_or_else(|| GameEpochError::MissingActiveGeneration {
                offering: offering.to_string(),
                session: session.0.clone(),
            })
    }

    /// Build the exact live bound address from current custody.
    pub fn bound_session(
        &self,
        offering: &str,
        session: &SessionId,
    ) -> Result<GameSessionRef, GameEpochError> {
        let generation = self.current_generation(offering, session)?;
        GameSessionRef::bound(
            offering,
            session.clone(),
            self.host_incarnation(),
            generation,
        )
        .map_err(|error| GameEpochError::InvalidAddress(error.to_string()))
    }

    /// Mark a successfully closed host session inactive while retaining its
    /// last generation. The next fresh open increments it.
    pub fn mark_closed(&self, offering: &str, session: &SessionId) -> Result<bool, GameEpochError> {
        validate_address(offering, session)?;
        let address = (offering.to_string(), session.0.clone());
        let mut state = self.0.state.lock().map_err(|_| GameEpochError::Poisoned)?;
        let Some(record) = state.records.get(&address) else {
            return Ok(false);
        };
        if !record.active {
            return Ok(false);
        }
        let mut candidate = state.clone();
        candidate
            .records
            .get_mut(&address)
            .expect("record was observed above")
            .active = false;
        self.persist(&candidate)?;
        *state = candidate;
        Ok(true)
    }

    fn persist(&self, state: &EpochState) -> Result<(), GameEpochError> {
        let Backing::Durable(directory) = &self.0.backing else {
            return Ok(());
        };
        let bytes = encode_state(state)?;
        atomic_replace(directory, SESSIONS_FILE, &bytes)
    }
}

fn validate_address(offering: &str, session: &SessionId) -> Result<(), GameEpochError> {
    GameSessionRef::new(offering, session.clone())
        .map(|_| ())
        .map_err(|error| GameEpochError::InvalidAddress(error.to_string()))
}

fn random_incarnation() -> Result<GameHostIncarnation, GameEpochError> {
    loop {
        let mut bytes = [0u8; 32];
        getrandom::fill(&mut bytes).map_err(|error| GameEpochError::Io {
            operation: "obtain host-incarnation entropy",
            path: PathBuf::from("<operating-system RNG>"),
            detail: error.to_string(),
        })?;
        if let Ok(incarnation) = GameHostIncarnation::new(bytes) {
            return Ok(incarnation);
        }
    }
}

fn open_incarnation(directory: &Path) -> Result<GameHostIncarnation, GameEpochError> {
    let path = directory.join(INCARNATION_FILE);
    match read_incarnation(&path) {
        Ok(incarnation) => return Ok(incarnation),
        Err(GameEpochError::Io { detail, .. }) if detail == "not found" => {}
        Err(error) => return Err(error),
    }

    let incarnation = random_incarnation()?;
    match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(mut file) => {
            file.write_all(incarnation.as_bytes())
                .map_err(|error| GameEpochError::io("write host incarnation", &path, error))?;
            file.sync_all()
                .map_err(|error| GameEpochError::io("sync host incarnation", &path, error))?;
            sync_directory(directory)?;
            Ok(incarnation)
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => read_incarnation(&path),
        Err(error) => Err(GameEpochError::io("create host incarnation", path, error)),
    }
}

fn read_incarnation(path: &Path) -> Result<GameHostIncarnation, GameEpochError> {
    let mut file = match File::open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Err(GameEpochError::Io {
                operation: "read host incarnation",
                path: path.to_path_buf(),
                detail: "not found".to_string(),
            });
        }
        Err(error) => return Err(GameEpochError::io("read host incarnation", path, error)),
    };
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)
        .map_err(|error| GameEpochError::io("read host incarnation", path, error))?;
    let exact: [u8; 32] = bytes.try_into().map_err(|bytes: Vec<u8>| {
        GameEpochError::Corrupt(format!(
            "{} must contain exactly 32 bytes, found {}",
            path.display(),
            bytes.len()
        ))
    })?;
    GameHostIncarnation::new(exact).map_err(|error| GameEpochError::Corrupt(error.to_string()))
}

fn encode_state(state: &EpochState) -> Result<Vec<u8>, GameEpochError> {
    let count = u32::try_from(state.records.len())
        .map_err(|_| GameEpochError::Corrupt("too many session-generation records".to_string()))?;
    let mut out = Vec::new();
    out.extend_from_slice(SESSIONS_MAGIC);
    out.extend_from_slice(&count.to_be_bytes());
    for ((offering, session), record) in &state.records {
        let offering_len = u16::try_from(offering.len()).map_err(|_| {
            GameEpochError::InvalidAddress("offering key exceeds u16 wire length".to_string())
        })?;
        let session_len = u16::try_from(session.len()).map_err(|_| {
            GameEpochError::InvalidAddress("session id exceeds u16 wire length".to_string())
        })?;
        out.extend_from_slice(&offering_len.to_be_bytes());
        out.extend_from_slice(&session_len.to_be_bytes());
        out.extend_from_slice(&record.generation.to_be_bytes());
        out.push(u8::from(record.active));
        out.extend_from_slice(offering.as_bytes());
        out.extend_from_slice(session.as_bytes());
    }
    Ok(out)
}

fn decode_state(bytes: &[u8]) -> Result<EpochState, GameEpochError> {
    let mut input = bytes;
    if take(&mut input, SESSIONS_MAGIC.len())? != SESSIONS_MAGIC {
        return Err(GameEpochError::Corrupt(
            "session-generation magic/version mismatch".to_string(),
        ));
    }
    let count = u32::from_be_bytes(take_array(&mut input)?) as usize;
    let mut records = BTreeMap::new();
    for _ in 0..count {
        let offering_len = u16::from_be_bytes(take_array(&mut input)?) as usize;
        let session_len = u16::from_be_bytes(take_array(&mut input)?) as usize;
        let generation = u64::from_be_bytes(take_array(&mut input)?);
        if generation == 0 {
            return Err(GameEpochError::Corrupt(
                "generation zero is reserved and cannot appear on disk".to_string(),
            ));
        }
        let active = match take(&mut input, 1)?[0] {
            0 => false,
            1 => true,
            other => {
                return Err(GameEpochError::Corrupt(format!(
                    "invalid active flag {other}"
                )));
            }
        };
        let offering = std::str::from_utf8(take(&mut input, offering_len)?)
            .map_err(|_| GameEpochError::Corrupt("offering key is not UTF-8".to_string()))?
            .to_string();
        let session = std::str::from_utf8(take(&mut input, session_len)?)
            .map_err(|_| GameEpochError::Corrupt("session id is not UTF-8".to_string()))?
            .to_string();
        validate_address(&offering, &SessionId::new(session.clone()))?;
        if records
            .insert(
                (offering.clone(), session.clone()),
                EpochRecord { generation, active },
            )
            .is_some()
        {
            return Err(GameEpochError::Corrupt(format!(
                "duplicate session-generation record for {offering}/{session}"
            )));
        }
    }
    if !input.is_empty() {
        return Err(GameEpochError::Corrupt(format!(
            "{} trailing bytes after session-generation records",
            input.len()
        )));
    }
    Ok(EpochState { records })
}

fn take<'a>(input: &mut &'a [u8], len: usize) -> Result<&'a [u8], GameEpochError> {
    if input.len() < len {
        return Err(GameEpochError::Corrupt(format!(
            "truncated session-generation record: needed {len} bytes, found {}",
            input.len()
        )));
    }
    let (head, tail) = input.split_at(len);
    *input = tail;
    Ok(head)
}

fn take_array<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], GameEpochError> {
    take(input, N)?
        .try_into()
        .map_err(|_| GameEpochError::Corrupt("invalid fixed-width field".to_string()))
}

fn atomic_replace(directory: &Path, file_name: &str, bytes: &[u8]) -> Result<(), GameEpochError> {
    let target = directory.join(file_name);
    let mut nonce = [0u8; 8];
    getrandom::fill(&mut nonce).map_err(|error| GameEpochError::Io {
        operation: "obtain epoch temporary-file entropy",
        path: directory.to_path_buf(),
        detail: error.to_string(),
    })?;
    let suffix = u64::from_be_bytes(nonce);
    let temporary = directory.join(format!(".{file_name}.{suffix:016x}.tmp"));
    let write_result = (|| {
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|error| {
                GameEpochError::io("create epoch temporary file", &temporary, error)
            })?;
        file.write_all(bytes)
            .map_err(|error| GameEpochError::io("write epoch temporary file", &temporary, error))?;
        file.sync_all()
            .map_err(|error| GameEpochError::io("sync epoch temporary file", &temporary, error))?;
        fs::rename(&temporary, &target)
            .map_err(|error| GameEpochError::io("replace epoch ledger", &target, error))?;
        sync_directory(directory)
    })();
    if write_result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    write_result
}

fn sync_directory(directory: &Path) -> Result<(), GameEpochError> {
    File::open(directory)
        .and_then(|file| file.sync_all())
        .map_err(|error| GameEpochError::io("sync epoch directory", directory, error))
}
