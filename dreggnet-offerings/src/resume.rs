//! # Session-resume — the [`OfferingHost`](crate::OfferingHost)'s durable-store seam.
//!
//! An [`OfferingHost`](crate::OfferingHost) holds each session's live state **in memory** (behind
//! the type-erased `OfferingSlot` — some sessions are `!Send`, `Rc`-backed cells). That state is
//! LOST on restart. This module closes that seam the way the rest of the platform's durable stores
//! do (the discord-bot's `CharacterStore` / the `/gallery` registry): **store only the reproducible
//! public input, and reopen by REPLAY — never a trusted serialized blob.**
//!
//! ## What a session's reproducible public input is
//!
//! A session is deterministic from its [`SessionConfig`] seed + the ordered [`advance`]s that
//! LANDED (the [`Offering`] contract: `open(cfg)` is a pure function of the seed, and
//! `verify_by_replay` guarantees re-driving the ordered landed choices from a fresh identically
//! seeded `open()` reproduces exactly the committed state chain). So a [`SessionMoveLog`] — the seed
//! + that ordered `(action, actor)` list — is a **complete, un-forgeable** description of a session:
//!
//! [`Offering`]: crate::Offering
//! [`advance`]: crate::Offering::advance
//! [`SessionConfig`]: crate::SessionConfig
//!
//! - It is not a state snapshot a peer could tamper with — it is the *inputs*, and the executor
//!   re-derives the state. A forged / ineligible advance spliced into the log is **refused on
//!   re-drive** (the same anti-ghost gate a live move hits), so a tampered log cannot reopen to a
//!   forged state — it fails to reopen at all.
//! - It is small and append-only (one row per landed turn), the natural durable shape.
//!
//! ## The seam
//!
//! [`SessionResumeStore`] is the persistence trait — [`record_open`](SessionResumeStore::record_open)
//! at open, [`record_landed`](SessionResumeStore::record_landed) after each landed advance,
//! [`forget`](SessionResumeStore::forget) on close, [`load`](SessionResumeStore::load) /
//! [`all`](SessionResumeStore::all) on boot. [`InMemoryResumeStore`] is the reference impl the tests
//! drive; the durable **sqlite** impl is the discord-bot's follow-up (exactly as `SqliteGalleryStore`
//! / `SqliteCharacterStore` back their sync traits). The host writes THROUGH an attached store on
//! open/advance and reopens with [`OfferingHost::resume`](crate::OfferingHost::resume) /
//! [`resume_all`](crate::OfferingHost::resume_all) — replaying the log to the identical committed
//! state.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::{Action, DreggIdentity, SessionConfig, SessionId};

/// **One recorded LANDED advance** — the reproducible public input of a single committed turn: the
/// typed [`Action`] that was resolved and the [`DreggIdentity`] it was attributed to (for a
/// collective turn, the decision's carrier — the mover of record). Only landed advances are logged:
/// a refused move commits nothing and records nothing, so replaying the log re-lands exactly the
/// committed steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoggedMove {
    /// The typed action the executor resolved on this turn (the `{turn, arg, text}` the frontend
    /// collected).
    pub action: Action,
    /// The actor the landed turn was attributed to (the collective carrier for a crowd turn).
    pub actor: DreggIdentity,
}

impl LoggedMove {
    /// A logged move — an `action` that landed, attributed to `actor`.
    pub fn new(action: Action, actor: DreggIdentity) -> Self {
        LoggedMove { action, actor }
    }
}

/// **A session's reproducible public input** — its [`SessionConfig`] seed plus the ordered
/// [`LoggedMove`]s that landed. This is the ENTIRE durable footprint of a session: reopen it by
/// re-driving these moves from a fresh [`open`](crate::Offering::open) under the same `cfg`
/// ([`OfferingHost::resume`](crate::OfferingHost::resume)). It is not trusted — the executor
/// re-checks every logged move on re-drive, so a tampered log is refused, never replayed to a forged
/// state.
#[derive(Clone, Debug)]
pub struct SessionMoveLog {
    /// The offering the session belongs to (the host registry key).
    pub key: String,
    /// The session's id (the surface slot it reopens under).
    pub id: SessionId,
    /// The deterministic config the session was opened with (the seed the world is re-derived from).
    pub cfg: SessionConfig,
    /// The ordered landed advances — replaying these from a fresh `open(cfg)` reproduces the exact
    /// committed state chain.
    pub moves: Vec<LoggedMove>,
}

impl SessionMoveLog {
    /// A fresh (moveless) log for a just-opened session under `key`/`id`/`cfg`.
    pub fn new(key: impl Into<String>, id: SessionId, cfg: SessionConfig) -> Self {
        SessionMoveLog {
            key: key.into(),
            id,
            cfg,
            moves: Vec::new(),
        }
    }

    /// Append a landed advance to the log (the host calls this on each `Outcome::Landed`).
    pub fn record(&mut self, action: Action, actor: DreggIdentity) {
        self.moves.push(LoggedMove::new(action, actor));
    }

    /// The number of landed advances recorded (the replayable turns; genesis is implicit in `cfg`).
    pub fn len(&self) -> usize {
        self.moves.len()
    }

    /// Whether no advance has landed yet (a session at genesis).
    pub fn is_empty(&self) -> bool {
        self.moves.is_empty()
    }
}

/// **The session-resume persistence seam** — where an [`OfferingHost`](crate::OfferingHost)'s
/// per-session [`SessionMoveLog`]s are durably kept so a session survives restart. It is a SYNC
/// trait over `&self` (interior mutability), matching the discord-bot's `GalleryStore` /
/// `CharacterStore`: an attached store is written through on open/advance and read back on boot to
/// [`resume_all`](crate::OfferingHost::resume_all).
///
/// The reference impl is [`InMemoryResumeStore`] (the tests); the durable **sqlite** impl is the
/// discord-bot's follow-up (the same shape as `SqliteGalleryStore` — an async `Database` bridged to
/// this sync trait). Records are keyed by `(key, id)` and are idempotent: re-recording an open or a
/// landed move for an already-known `(key, id, index)` is a no-op the durable impl gets from an
/// `INSERT OR IGNORE` on the PK.
pub trait SessionResumeStore {
    /// Record a session's OPEN — its config (the replay seed). Establishes the log for `(key, id)`.
    fn record_open(&self, key: &str, id: &SessionId, cfg: &SessionConfig);

    /// Append a LANDED advance to `(key, id)`'s log (called after each `Outcome::Landed`). A refused
    /// move records nothing (it committed nothing).
    fn record_landed(&self, key: &str, id: &SessionId, action: &Action, actor: &DreggIdentity);

    /// Drop `(key, id)`'s log (on session close) — it will not be resumed on the next boot.
    fn forget(&self, key: &str, id: &SessionId);

    /// Load `(key, id)`'s recorded log, if any (the reproducible public input to
    /// [`resume`](crate::OfferingHost::resume)).
    fn load(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog>;

    /// Every recorded log (for [`resume_all`](crate::OfferingHost::resume_all) on boot).
    fn all(&self) -> Vec<SessionMoveLog>;
}

/// **The in-memory reference [`SessionResumeStore`]** — the tests' backing (and the shape the
/// durable sqlite impl mirrors). Interior-mutable and cheaply [`Clone`]able (an `Rc` share of one
/// map), so a caller can hand one clone to the host (`with_resume_store`) and keep another to read
/// back across a simulated restart. Keyed by `(key, id)`; append-only per session.
#[derive(Clone, Default)]
pub struct InMemoryResumeStore {
    inner: Rc<RefCell<BTreeMap<(String, String), SessionMoveLog>>>,
}

impl InMemoryResumeStore {
    /// A fresh, empty store.
    pub fn new() -> Self {
        InMemoryResumeStore::default()
    }

    /// How many session logs are currently held.
    pub fn len(&self) -> usize {
        self.inner.borrow().len()
    }

    /// Whether the store holds no logs.
    pub fn is_empty(&self) -> bool {
        self.inner.borrow().is_empty()
    }

    fn map_key(key: &str, id: &SessionId) -> (String, String) {
        (key.to_string(), id.0.clone())
    }
}

impl SessionResumeStore for InMemoryResumeStore {
    fn record_open(&self, key: &str, id: &SessionId, cfg: &SessionConfig) {
        self.inner
            .borrow_mut()
            .entry(Self::map_key(key, id))
            // Idempotent: a re-open of a known session keeps its existing (possibly non-empty) log.
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), cfg.clone()));
    }

    fn record_landed(&self, key: &str, id: &SessionId, action: &Action, actor: &DreggIdentity) {
        let mut map = self.inner.borrow_mut();
        let entry = map
            .entry(Self::map_key(key, id))
            // A landed move on a session we never saw opened still establishes a log (default cfg);
            // in practice `record_open` always precedes it (the host opens before it advances).
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), SessionConfig::default()));
        entry.record(action.clone(), actor.clone());
    }

    fn forget(&self, key: &str, id: &SessionId) {
        self.inner.borrow_mut().remove(&Self::map_key(key, id));
    }

    fn load(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        self.inner.borrow().get(&Self::map_key(key, id)).cloned()
    }

    fn all(&self) -> Vec<SessionMoveLog> {
        self.inner.borrow().values().cloned().collect()
    }
}
