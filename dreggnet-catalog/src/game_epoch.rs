//! Durable authority epochs for frontend-owned game-session addresses.
//!
//! [`OfferingHost`] deliberately owns game state, not deployment identity. A
//! frontend that exposes a durable `(offering, session)` route therefore needs
//! three additional pieces of routing custody:
//!
//! - one random [`GameHostIncarnation`] retained across ordinary process
//!   restarts; and
//! - one monotone generation for every game address, retained while the
//!   session is resumed and incremented whenever that address is closed and
//!   opened as a fresh world; and
//! - a fail-closed one-shot authorization journal for private consequences
//!   whose witnesses must never be replayed after a process restart.
//!
//! This ledger is the small shared implementation of that custody. It is not a
//! lock service and does not make two processes safe to run against the same
//! session store concurrently. A deployment still has one writer. Every
//! mutation is, however, written to a temporary file, synced, atomically
//! renamed, and directory-synced before it becomes visible in memory. The
//! authorization snapshot is checksummed against accidental corruption. It is
//! presently a full-map snapshot: mutation cost grows with retained source-use
//! count, and compaction/append-log work remains a scaling follow-up.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use dreggnet_offerings::SessionId;

use crate::{GameHostIncarnation, GameSessionRef};

const INCARNATION_FILE: &str = "host-incarnation.v1";
const SESSIONS_FILE: &str = "session-generations.v1";
const SESSIONS_MAGIC: &[u8; 8] = b"DREGGE01";
const AUTHORIZATIONS_FILE: &str = "private-authorizations.v1";
const AUTHORIZATIONS_MAGIC: &[u8; 8] = b"DREGGA01";
const AUTHORIZATIONS_CHECKSUM_DOMAIN: &str = "dregg.game-authorizations.checksum.v1";

/// A durable game-epoch custody failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameEpochError {
    Io {
        operation: &'static str,
        path: PathBuf,
        detail: String,
    },
    ReplaceNotDurablySynced {
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
    InvalidAuthorization(String),
    MissingAuthorization([u8; 32]),
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

    fn replace_is_visible(&self) -> bool {
        matches!(self, Self::ReplaceNotDurablySynced { .. })
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
            Self::ReplaceNotDurablySynced { path, detail } => write!(
                f,
                "replacement of {} became visible but its directory sync failed: {detail}",
                path.display()
            ),
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
            Self::InvalidAuthorization(detail) => {
                write!(f, "invalid game authorization: {detail}")
            }
            Self::MissingAuthorization(_) => {
                write!(f, "private authorization was not reserved")
            }
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

/// Durable state of a one-shot private game authorization.
///
/// `Reserved` is deliberately replay-blocking. It means the authorization was
/// sealed before dispatch, but the process did not durably record completion.
/// A deployment must reconcile that state rather than guessing that the game
/// action did not land.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GameAuthorizationPhase {
    Reserved,
    Consumed,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AuthorizationState {
    records: BTreeMap<[u8; 32], GameAuthorizationPhase>,
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
    authorizations: Mutex<AuthorizationState>,
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
            authorizations: Mutex::new(AuthorizationState::default()),
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
        let incarnation_preexisting = path_exists(&directory.join(INCARNATION_FILE))?;
        let authorizations_path = directory.join(AUTHORIZATIONS_FILE);
        let authorizations = match fs::read(&authorizations_path) {
            Ok(bytes) => decode_authorizations(&bytes)?,
            Err(error) if error.kind() == io::ErrorKind::NotFound && !incarnation_preexisting => {
                // Initialize the replay ledger *before* minting the durable host
                // incarnation. Once an incarnation exists, absence is loss and
                // must never be reinterpreted as an empty authorization set.
                let state = AuthorizationState::default();
                atomic_replace(
                    &directory,
                    AUTHORIZATIONS_FILE,
                    &encode_authorizations(&state)?,
                )?;
                state
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return Err(GameEpochError::Corrupt(format!(
                    "{} is missing for an initialized host incarnation",
                    authorizations_path.display()
                )));
            }
            Err(error) => {
                return Err(GameEpochError::io(
                    "read private authorizations",
                    authorizations_path,
                    error,
                ));
            }
        };
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
            authorizations: Mutex::new(authorizations),
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
        if let Err(error) = self.persist(&candidate) {
            if error.replace_is_visible() {
                *state = candidate;
            }
            return Err(error);
        }
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
        if let Err(error) = self.persist(&candidate) {
            if error.replace_is_visible() {
                *state = candidate;
            }
            return Err(error);
        }
        *state = candidate;
        Ok(true)
    }

    /// Return the durable phase of a private authorization, if it has ever
    /// been sealed by this ledger.
    pub fn authorization_phase(
        &self,
        authorization_id: [u8; 32],
    ) -> Result<Option<GameAuthorizationPhase>, GameEpochError> {
        validate_authorization_id(authorization_id)?;
        let state = self
            .0
            .authorizations
            .lock()
            .map_err(|_| GameEpochError::Poisoned)?;
        Ok(state.records.get(&authorization_id).copied())
    }

    /// Seal a one-shot private authorization before dispatch.
    ///
    /// Returns `true` only for the first reservation. Both `Reserved` and
    /// `Consumed` are replay-blocking, so a crash between dispatch and the
    /// final `Consumed` write fails closed instead of reopening the witness.
    pub fn reserve_authorization(
        &self,
        authorization_id: [u8; 32],
    ) -> Result<bool, GameEpochError> {
        self.reserve_authorizations(std::slice::from_ref(&authorization_id))
    }

    /// Atomically reserve every independent source-use key, or none of them.
    /// If any key was previously reserved/consumed, returns `false` without
    /// changing the other keys. Duplicate or empty batches are refused.
    pub fn reserve_authorizations(
        &self,
        authorization_ids: &[[u8; 32]],
    ) -> Result<bool, GameEpochError> {
        validate_authorization_batch(authorization_ids)?;
        let mut state = self
            .0
            .authorizations
            .lock()
            .map_err(|_| GameEpochError::Poisoned)?;
        if authorization_ids
            .iter()
            .any(|id| state.records.contains_key(id))
        {
            return Ok(false);
        }
        let mut candidate = state.clone();
        for authorization_id in authorization_ids {
            candidate
                .records
                .insert(*authorization_id, GameAuthorizationPhase::Reserved);
        }
        if let Err(error) = self.persist_authorizations(&candidate) {
            if error.replace_is_visible() {
                *state = candidate;
            }
            return Err(error);
        }
        *state = candidate;
        Ok(true)
    }

    /// Promote a previously reserved authorization to durably consumed.
    ///
    /// Repeating the exact promotion is idempotent. A missing reservation is
    /// an error: creating `Consumed` from nothing would conceal a caller that
    /// skipped the crash-closing pre-dispatch write.
    pub fn consume_authorization(&self, authorization_id: [u8; 32]) -> Result<(), GameEpochError> {
        self.consume_authorizations(std::slice::from_ref(&authorization_id))
    }

    /// Atomically promote a batch of source-use keys from `Reserved` to
    /// `Consumed`. Every key must already exist; an all-consumed retry is
    /// idempotent.
    pub fn consume_authorizations(
        &self,
        authorization_ids: &[[u8; 32]],
    ) -> Result<(), GameEpochError> {
        validate_authorization_batch(authorization_ids)?;
        let mut state = self
            .0
            .authorizations
            .lock()
            .map_err(|_| GameEpochError::Poisoned)?;
        let mut any_reserved = false;
        for authorization_id in authorization_ids {
            match state.records.get(authorization_id) {
                Some(GameAuthorizationPhase::Consumed) => {}
                Some(GameAuthorizationPhase::Reserved) => any_reserved = true,
                None => return Err(GameEpochError::MissingAuthorization(*authorization_id)),
            }
        }
        if !any_reserved {
            return Ok(());
        }
        let mut candidate = state.clone();
        for authorization_id in authorization_ids {
            candidate
                .records
                .insert(*authorization_id, GameAuthorizationPhase::Consumed);
        }
        if let Err(error) = self.persist_authorizations(&candidate) {
            if error.replace_is_visible() {
                *state = candidate;
            }
            return Err(error);
        }
        *state = candidate;
        Ok(())
    }

    fn persist(&self, state: &EpochState) -> Result<(), GameEpochError> {
        let Backing::Durable(directory) = &self.0.backing else {
            return Ok(());
        };
        let bytes = encode_state(state)?;
        atomic_replace(directory, SESSIONS_FILE, &bytes)
    }

    fn persist_authorizations(&self, state: &AuthorizationState) -> Result<(), GameEpochError> {
        let Backing::Durable(directory) = &self.0.backing else {
            return Ok(());
        };
        let bytes = encode_authorizations(state)?;
        atomic_replace(directory, AUTHORIZATIONS_FILE, &bytes)
    }
}

fn path_exists(path: &Path) -> Result<bool, GameEpochError> {
    match fs::metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(GameEpochError::io("inspect epoch path", path, error)),
    }
}

fn validate_authorization_id(authorization_id: [u8; 32]) -> Result<(), GameEpochError> {
    if authorization_id == [0; 32] {
        return Err(GameEpochError::InvalidAuthorization(
            "the all-zero authorization id is reserved".to_string(),
        ));
    }
    Ok(())
}

fn validate_authorization_batch(authorization_ids: &[[u8; 32]]) -> Result<(), GameEpochError> {
    if authorization_ids.is_empty() {
        return Err(GameEpochError::InvalidAuthorization(
            "source-use batch is empty".to_string(),
        ));
    }
    let mut unique = BTreeSet::new();
    for authorization_id in authorization_ids {
        validate_authorization_id(*authorization_id)?;
        if !unique.insert(*authorization_id) {
            return Err(GameEpochError::InvalidAuthorization(
                "source-use batch contains a duplicate id".to_string(),
            ));
        }
    }
    Ok(())
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

fn encode_authorizations(state: &AuthorizationState) -> Result<Vec<u8>, GameEpochError> {
    let count = u32::try_from(state.records.len())
        .map_err(|_| GameEpochError::Corrupt("too many authorization records".to_string()))?;
    let mut out = Vec::with_capacity(12 + state.records.len() * 33);
    out.extend_from_slice(AUTHORIZATIONS_MAGIC);
    out.extend_from_slice(&count.to_be_bytes());
    for (authorization_id, phase) in &state.records {
        validate_authorization_id(*authorization_id)?;
        out.extend_from_slice(authorization_id);
        out.push(match phase {
            GameAuthorizationPhase::Reserved => 0,
            GameAuthorizationPhase::Consumed => 1,
        });
    }
    let checksum = blake3::derive_key(AUTHORIZATIONS_CHECKSUM_DOMAIN, &out);
    out.extend_from_slice(&checksum);
    Ok(out)
}

fn decode_authorizations(bytes: &[u8]) -> Result<AuthorizationState, GameEpochError> {
    let checksum_at = bytes.len().checked_sub(32).ok_or_else(|| {
        GameEpochError::Corrupt("authorization journal is missing its checksum".to_string())
    })?;
    let (payload, presented_checksum) = bytes.split_at(checksum_at);
    let expected_checksum = blake3::derive_key(AUTHORIZATIONS_CHECKSUM_DOMAIN, payload);
    if presented_checksum != expected_checksum {
        return Err(GameEpochError::Corrupt(
            "authorization journal checksum mismatch".to_string(),
        ));
    }
    let mut input = payload;
    if take(&mut input, AUTHORIZATIONS_MAGIC.len())? != AUTHORIZATIONS_MAGIC {
        return Err(GameEpochError::Corrupt(
            "authorization magic/version mismatch".to_string(),
        ));
    }
    let count = u32::from_be_bytes(take_array(&mut input)?) as usize;
    let mut records = BTreeMap::new();
    for _ in 0..count {
        let authorization_id = take_array(&mut input)?;
        validate_authorization_id(authorization_id)
            .map_err(|error| GameEpochError::Corrupt(error.to_string()))?;
        let phase = match take(&mut input, 1)?[0] {
            0 => GameAuthorizationPhase::Reserved,
            1 => GameAuthorizationPhase::Consumed,
            other => {
                return Err(GameEpochError::Corrupt(format!(
                    "invalid authorization phase {other}"
                )));
            }
        };
        if records.insert(authorization_id, phase).is_some() {
            return Err(GameEpochError::Corrupt(
                "duplicate private authorization record".to_string(),
            ));
        }
    }
    if !input.is_empty() {
        return Err(GameEpochError::Corrupt(format!(
            "{} trailing bytes after authorization records",
            input.len()
        )));
    }
    Ok(AuthorizationState { records })
}

fn take<'a>(input: &mut &'a [u8], len: usize) -> Result<&'a [u8], GameEpochError> {
    if input.len() < len {
        return Err(GameEpochError::Corrupt(format!(
            "truncated ledger record: needed {len} bytes, found {}",
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
        sync_directory(directory).map_err(|error| GameEpochError::ReplaceNotDurablySynced {
            path: target.clone(),
            detail: error.to_string(),
        })
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
