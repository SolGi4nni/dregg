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
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::signed::Attribution;
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
    /// **The attribution's trust level** ([`Attribution`]) — was `actor` a VERIFIED signer
    /// (`Signed`, the [`crate::OfferingHost::advance_signed`] path) or a frontend-asserted label
    /// (`Asserted`, every legacy path)? Provenance beside the replayed inputs — replay itself
    /// still re-drives `(action, actor)` only. A log persisted before this field existed decodes
    /// as `Asserted` (which is exactly what every pre-signed-seam attribution was).
    pub attribution: Attribution,
}

impl LoggedMove {
    /// A logged move — an `action` that landed, attributed to `actor`. The attribution defaults
    /// to [`Attribution::Asserted`] (the legacy trust level); a verified move is recorded with
    /// [`LoggedMove::attributed`].
    pub fn new(action: Action, actor: DreggIdentity) -> Self {
        let attribution = Attribution::from(actor.clone());
        LoggedMove {
            action,
            actor,
            attribution,
        }
    }

    /// A logged move with an explicit [`Attribution`] trust level (the signed-advance path
    /// records [`Attribution::Signed`] here).
    pub fn attributed(action: Action, actor: DreggIdentity, attribution: Attribution) -> Self {
        LoggedMove {
            action,
            actor,
            attribution,
        }
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

    /// Append a landed advance with an explicit [`Attribution`] trust level (the signed-advance
    /// path records [`Attribution::Signed`]).
    pub fn record_attributed(
        &mut self,
        action: Action,
        actor: DreggIdentity,
        attribution: Attribution,
    ) {
        self.moves
            .push(LoggedMove::attributed(action, actor, attribution));
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

    /// Append a LANDED advance **with its [`Attribution`] trust level** — the provenance-aware
    /// twin of [`record_landed`](SessionResumeStore::record_landed), which the host calls so a
    /// store that understands attribution (the in-memory and file stores here) can persist it.
    /// **Default: drops the attribution and delegates to `record_landed`** — additive, so an
    /// existing external implementor keeps compiling and behaving exactly as before (its logs
    /// simply decode with the legacy `Asserted` level).
    fn record_landed_attributed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        attribution: &Attribution,
    ) {
        let _ = attribution;
        self.record_landed(key, id, action, actor);
    }

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
        self.record_landed_attributed(key, id, action, actor, &Attribution::from(actor.clone()));
    }

    fn record_landed_attributed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        attribution: &Attribution,
    ) {
        let mut map = self.inner.borrow_mut();
        let entry = map
            .entry(Self::map_key(key, id))
            // A landed move on a session we never saw opened still establishes a log (default cfg);
            // in practice `record_open` always precedes it (the host opens before it advances).
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), SessionConfig::default()));
        entry.record_attributed(action.clone(), actor.clone(), attribution.clone());
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

// ═══════════════════════════════════════════════════════════════════════════════
// The durable file-backed store — the shared durable seam every frontend can mount.
// ═══════════════════════════════════════════════════════════════════════════════

/// **A durable, file-backed [`SessionResumeStore`]** — the core's own durable store, so a frontend
/// (telegram / wechat / web) no longer has to reinvent one. It persists each session's
/// [`SessionMoveLog`] to **one append-only text file per session** under a directory: the header
/// line is the session's `(key, id, seed)`, and each subsequent line is one landed advance. A
/// session survives a real process restart by [`OfferingHost::resume_all`](crate::OfferingHost::resume_all)
/// re-driving these logs — the state is never serialized, only the reproducible public input, so a
/// tampered file is refused on re-drive exactly as a tampered in-memory log is.
///
/// Why a file store and not sqlite: the move-log is small and append-only (the natural file shape),
/// and the whole workspace is bound to ONE `links="sqlite3"` (deos-matrix's `rusqlite`) — a second
/// sqlite in this hub crate would fight that single-link constraint. A dependency-light file store
/// gives every frontend a shared durable store with no link-heavy dependency and no feature gate.
///
/// The encoding escapes `\`, tab, newline and CR in every string field, so an [`Action::text`]
/// payload carrying tabs / newlines round-trips losslessly. Records are keyed by a content hash of
/// `(key, id)` (the file name), so any `(key, id)` maps to a stable file. Cheaply [`Clone`]able (it
/// holds only the root path), so a caller can hand one clone to the host and keep another to read
/// back across a restart.
#[derive(Clone, Debug)]
pub struct FileResumeStore {
    root: PathBuf,
}

impl FileResumeStore {
    /// Open (creating if needed) a file store rooted at `dir`. Each session's log is a `*.log` file
    /// directly under `dir`.
    pub fn open(dir: impl Into<PathBuf>) -> io::Result<Self> {
        let root = dir.into();
        fs::create_dir_all(&root)?;
        Ok(FileResumeStore { root })
    }

    /// The directory this store persists under.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// How many session logs are currently persisted (the `*.log` files under the root).
    pub fn len(&self) -> usize {
        self.log_files().len()
    }

    /// Whether the store persists no logs.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The stable file path for `(key, id)` — a content hash of the pair, so an arbitrary key/id
    /// (which may hold path-hostile characters) maps to a safe, collision-resistant file name.
    fn path_for(&self, key: &str, id: &SessionId) -> PathBuf {
        let mut h = blake3::Hasher::new();
        h.update(key.as_bytes());
        h.update(&[0]); // domain separator between key and id
        h.update(id.0.as_bytes());
        self.root.join(format!("{}.log", h.finalize().to_hex()))
    }

    /// Every `*.log` file path under the root (sorted, for deterministic enumeration).
    fn log_files(&self) -> Vec<PathBuf> {
        let mut out = Vec::new();
        if let Ok(entries) = fs::read_dir(&self.root) {
            for e in entries.flatten() {
                let p = e.path();
                if p.extension().and_then(|s| s.to_str()) == Some("log") {
                    out.push(p);
                }
            }
        }
        out.sort();
        out
    }

    /// Write the header line for a just-opened session iff the file does not already exist
    /// (idempotent — a re-open keeps the existing file and its recorded advances).
    fn write_header_if_absent(&self, key: &str, id: &SessionId, cfg: &SessionConfig) {
        let path = self.path_for(key, id);
        // `create_new` succeeds only if the file did not exist — the atomic "insert or ignore".
        if let Ok(mut f) = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
        {
            let _ = writeln!(f, "{}", encode_header(key, id, cfg));
        }
    }
}

impl SessionResumeStore for FileResumeStore {
    fn record_open(&self, key: &str, id: &SessionId, cfg: &SessionConfig) {
        self.write_header_if_absent(key, id, cfg);
    }

    fn record_landed(&self, key: &str, id: &SessionId, action: &Action, actor: &DreggIdentity) {
        self.record_landed_attributed(key, id, action, actor, &Attribution::from(actor.clone()));
    }

    fn record_landed_attributed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        attribution: &Attribution,
    ) {
        // A landed move on a session we never saw opened still establishes a file (default cfg);
        // in practice `record_open` always precedes it (the host opens before it advances).
        self.write_header_if_absent(key, id, &SessionConfig::default());
        let path = self.path_for(key, id);
        if let Ok(mut f) = fs::OpenOptions::new().append(true).open(&path) {
            let _ = writeln!(f, "{}", encode_move(action, actor, attribution));
        }
    }

    fn forget(&self, key: &str, id: &SessionId) {
        let _ = fs::remove_file(self.path_for(key, id));
    }

    fn load(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        let text = fs::read_to_string(self.path_for(key, id)).ok()?;
        decode_log(&text)
    }

    fn all(&self) -> Vec<SessionMoveLog> {
        self.log_files()
            .iter()
            .filter_map(|p| fs::read_to_string(p).ok().and_then(|t| decode_log(&t)))
            .collect()
    }
}

// ── The line codec: tab-separated, escaped string fields, one file per session ──

/// Escape a string field so it holds no delimiter (`\t`) or record (`\n` / `\r`) bytes — backslash
/// first, so the escape is reversible. An [`Action::text`] carrying tabs/newlines round-trips.
fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out
}

/// Reverse [`esc`].
fn unesc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('\\') => out.push('\\'),
                Some('t') => out.push('\t'),
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// The header line: `key \t id \t seed` (seed = the `u64` or `-` for the offering default).
fn encode_header(key: &str, id: &SessionId, cfg: &SessionConfig) -> String {
    let seed = cfg
        .seed
        .map(|s| s.to_string())
        .unwrap_or_else(|| "-".into());
    format!("{}\t{}\t{}", esc(key), esc(&id.0), seed)
}

/// One landed advance: `label \t turn \t arg \t enabled \t has_text \t text \t actor \t trust`.
/// The 8th `trust` column is the [`Attribution`] level — `s` (signed: `actor` is a VERIFIED
/// pubkey hex) or `a` (asserted). It carries no payload of its own (a signed attribution's
/// pubkey and an asserted attribution's label are both exactly the `actor` column), so old
/// 7-column lines decode losslessly as `a` — see [`decode_log`].
fn encode_move(action: &Action, actor: &DreggIdentity, attribution: &Attribution) -> String {
    let trust = match attribution {
        Attribution::Signed { .. } => "s",
        Attribution::Asserted { .. } => "a",
    };
    format!(
        "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        esc(&action.label),
        esc(&action.turn),
        action.arg,
        action.enabled as u8,
        action.text.is_some() as u8,
        esc(action.text.as_deref().unwrap_or("")),
        esc(&actor.0),
        trust,
    )
}

/// Parse a whole session file back into a [`SessionMoveLog`] — the header plus the ordered landed
/// advances. Returns `None` on a structurally corrupt file (a missing / malformed header), so a
/// damaged file is treated as absent rather than resumed to a wrong state.
fn decode_log(text: &str) -> Option<SessionMoveLog> {
    let mut lines = text.lines();
    let header = lines.next()?;
    let h: Vec<&str> = header.split('\t').collect();
    if h.len() != 3 {
        return None;
    }
    let key = unesc(h[0]);
    let id = SessionId::new(unesc(h[1]));
    let seed = match h[2] {
        "-" => None,
        n => Some(n.parse::<u64>().ok()?),
    };
    let cfg = SessionConfig { seed };

    let mut log = SessionMoveLog::new(key, id, cfg);
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        // 7 columns = the pre-attribution format (every such log was asserted-only);
        // 8 columns = the current format with the trailing trust column.
        if f.len() != 7 && f.len() != 8 {
            return None;
        }
        let label = unesc(f[0]);
        let turn = unesc(f[1]);
        let arg = f[2].parse::<i64>().ok()?;
        let enabled = f[3] == "1";
        let has_text = f[4] == "1";
        let text = unesc(f[5]);
        let actor = DreggIdentity(unesc(f[6]));
        let attribution = match f.get(7).copied() {
            // A signed move's actor IS its verified pubkey hex (verify_signed's postcondition).
            Some("s") => Attribution::Signed {
                pubkey_hex: actor.0.clone(),
            },
            // Explicitly asserted, or the legacy 7-column line (which was always asserted).
            Some("a") | None => Attribution::from(actor.clone()),
            // An unknown trust tag is a corrupt file — treat as absent, never mis-labeled.
            Some(_) => return None,
        };
        let mut action = Action::new(label, turn, arg, enabled);
        if has_text {
            action = action.with_text(text);
        }
        log.record_attributed(action, actor, attribution);
    }
    Some(log)
}

#[cfg(test)]
mod file_store_tests {
    use super::*;

    /// A unique scratch directory for one test (process id + a monotone counter), created fresh.
    fn scratch_dir(tag: &str) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static N: AtomicU64 = AtomicU64::new(0);
        let n = N.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "offerings-filestore-{}-{}-{}",
            std::process::id(),
            tag,
            n
        ));
        let _ = fs::remove_dir_all(&dir);
        dir
    }

    /// A move-log round-trips through the durable file store: record open + two landed advances,
    /// load it back byte-for-byte, and an `Action::text` payload carrying tabs/newlines survives.
    #[test]
    fn a_move_log_round_trips_through_the_file_store() {
        let dir = scratch_dir("roundtrip");
        let store = FileResumeStore::open(&dir).expect("open store");
        let key = "dungeon";
        let id = SessionId::new("sess-1");
        let cfg = SessionConfig::with_seed(0xABCD_1234);

        store.record_open(key, &id, &cfg);
        store.record_landed(
            key,
            &id,
            &Action::new("press on", "choose", 3, true),
            &DreggIdentity("web:alice".into()),
        );
        // A text-bearing action whose payload holds a tab and a newline (the escaping tooth).
        store.record_landed(
            key,
            &id,
            &Action::new("edit", "insert", 0, false).with_text("line one\twith tab\nline two"),
            &DreggIdentity("web:bob".into()),
        );

        let log = store.load(key, &id).expect("the log persisted");
        assert_eq!(log.key, "dungeon");
        assert_eq!(log.id, id);
        assert_eq!(log.cfg.seed, Some(0xABCD_1234));
        assert_eq!(log.moves.len(), 2);
        assert_eq!(log.moves[0].action.label, "press on");
        assert_eq!(log.moves[0].action.arg, 3);
        assert!(log.moves[0].action.enabled);
        assert_eq!(log.moves[0].actor.0, "web:alice");
        assert_eq!(
            log.moves[1].action.text.as_deref(),
            Some("line one\twith tab\nline two"),
            "a tab/newline text payload survives the round-trip"
        );
        assert!(!log.moves[1].action.enabled);

        let _ = fs::remove_dir_all(&dir);
    }

    /// The store enumerates ALL sessions, is idempotent on re-open (keeps recorded moves), and
    /// forgets a session on request.
    #[test]
    fn the_store_enumerates_and_forgets() {
        let dir = scratch_dir("enumerate");
        let store = FileResumeStore::open(&dir).expect("open store");
        let a = SessionId::new("a");
        let b = SessionId::new("b");
        let cfg = SessionConfig::with_seed(7);

        store.record_open("dungeon", &a, &cfg);
        store.record_landed(
            "dungeon",
            &a,
            &Action::new("m", "choose", 1, true),
            &DreggIdentity("x".into()),
        );
        store.record_open("dungeon", &b, &cfg);

        // A RE-open of `a` must NOT drop its recorded advance (idempotent header).
        store.record_open("dungeon", &a, &cfg);
        assert_eq!(store.load("dungeon", &a).unwrap().moves.len(), 1);

        assert_eq!(store.len(), 2, "two sessions persisted");
        assert_eq!(store.all().len(), 2);

        store.forget("dungeon", &b);
        assert_eq!(store.len(), 1, "b forgotten");
        assert!(store.load("dungeon", &b).is_none());
        assert!(store.load("dungeon", &a).is_some());

        let _ = fs::remove_dir_all(&dir);
    }

    /// ATTRIBUTION PROVENANCE round-trips through the file store — a signed move reloads as
    /// `Signed`, an asserted one as `Asserted` — and a LEGACY 7-column log line (persisted
    /// before the trust column existed) still decodes, as `Asserted` (which is exactly what
    /// every pre-signed-seam attribution was). The existing wire format is never broken.
    #[test]
    fn attribution_round_trips_and_legacy_seven_column_lines_still_decode() {
        let dir = scratch_dir("attribution");
        let store = FileResumeStore::open(&dir).expect("open store");
        let id = SessionId::new("s");
        let cfg = SessionConfig::with_seed(11);
        let pubkey_hex = "ab".repeat(32); // a 64-char stand-in pubkey hex
        store.record_open("dungeon", &id, &cfg);
        store.record_landed_attributed(
            "dungeon",
            &id,
            &Action::new("m", "choose", 1, true),
            &DreggIdentity(pubkey_hex.clone()),
            &Attribution::Signed {
                pubkey_hex: pubkey_hex.clone(),
            },
        );
        store.record_landed(
            "dungeon",
            &id,
            &Action::new("m", "choose", 2, true),
            &DreggIdentity("web:alice".into()),
        );
        let log = store.load("dungeon", &id).expect("log persisted");
        assert_eq!(
            log.moves[0].attribution,
            Attribution::Signed {
                pubkey_hex: pubkey_hex.clone()
            },
            "a signed move reloads as Signed"
        );
        assert!(
            !log.moves[1].attribution.is_signed(),
            "a plain record_landed reloads as Asserted"
        );

        // A LEGACY file: header + one 7-column move line (no trust column) decodes as Asserted.
        let legacy = "dungeon\told-sess\t42\npress on\tchoose\t3\t1\t0\t\tweb:bob\n";
        let old = decode_log(legacy).expect("a pre-attribution log still decodes");
        assert_eq!(old.moves.len(), 1);
        assert_eq!(old.moves[0].actor.0, "web:bob");
        assert_eq!(
            old.moves[0].attribution,
            Attribution::Asserted {
                label: "web:bob".into()
            },
            "a legacy line is honestly Asserted"
        );

        let _ = fs::remove_dir_all(&dir);
    }

    /// A second store instance opened on the SAME directory sees the first's logs — the durability
    /// a real process restart relies on (the file outlives the store handle).
    #[test]
    fn a_fresh_store_on_the_same_dir_sees_persisted_logs() {
        let dir = scratch_dir("restart");
        {
            let store = FileResumeStore::open(&dir).expect("open store");
            store.record_open(
                "dungeon",
                &SessionId::new("s"),
                &SessionConfig::with_seed(42),
            );
            store.record_landed(
                "dungeon",
                &SessionId::new("s"),
                &Action::new("m", "choose", 2, true),
                &DreggIdentity("p".into()),
            );
        }
        // A brand-new handle (a simulated restart) reads the persisted log.
        let reopened = FileResumeStore::open(&dir).expect("reopen store");
        let all = reopened.all();
        assert_eq!(all.len(), 1);
        assert_eq!(all[0].cfg.seed, Some(42));
        assert_eq!(all[0].moves.len(), 1);

        let _ = fs::remove_dir_all(&dir);
    }
}
