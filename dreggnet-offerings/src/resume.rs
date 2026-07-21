//! # Session-resume — the [`OfferingHost`](crate::OfferingHost)'s durable-store seam.
//!
//! An [`OfferingHost`](crate::OfferingHost) holds each session's live state **in memory** (behind
//! the type-erased `OfferingSlot` — some sessions are `!Send`, `Rc`-backed cells). That state is
//! LOST on restart. This module closes that seam the way the rest of the platform's durable stores
//! do (the discord-bot's `CharacterStore` / the `/gallery` registry): **store only the reproducible
//! public input, and reopen by REPLAY — never a trusted serialized session blob.**
//!
//! ## What a session's reproducible public input is
//!
//! A session is deterministic from its [`SessionConfig`] seed plus its ordered landed turns and
//! successfully applied binary operations. Ordinary turns retain `(action, actor)` and re-drive
//! through the executor. Each opaque operation retains its name/actor/request digest/public receipt
//! plus only the concrete offering's explicitly approved replay representation; it is decoded,
//! verified, reapplied, and receipt-compared on restart. A timeline cursor preserves interleaving.
//! Thus a [`SessionMoveLog`] is a complete reproducible description without a trusted state blob:
//!
//! [`Offering`]: crate::Offering
//! [`advance`]: crate::Offering::advance
//! [`SessionConfig`]: crate::SessionConfig
//!
//! - It is not a state snapshot a peer could tamper with — it is the *inputs*, and the executor
//!   re-derives the state. A forged / ineligible advance spliced into the log is **refused on
//!   re-drive** (the same anti-ghost gate a live move hits), so a tampered log cannot reopen to a
//!   forged state — it fails to reopen at all.
//! - It is append-only. Potentially large approved operation evidence lives in a content-addressed
//!   sidecar rather than being expanded into the text log.
//! - The host never assumes an upload is safe to retain. The concrete offering must disclose and
//!   select replay material; a durable host refuses before mutation when it declines.
//!
//! ## The seam
//!
//! [`SessionResumeStore`] is the persistence trait — [`record_open`](SessionResumeStore::record_open)
//! at open, [`record_landed`](SessionResumeStore::record_landed) after each landed advance,
//! [`record_binary_operation`](SessionResumeStore::record_binary_operation) after each successful
//! durable opaque operation,
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
use crate::{Action, BinaryOperationReceipt, DreggIdentity, SessionConfig, SessionId};

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

/// One successfully applied transport-bearing operation in the session's
/// durable replay timeline.
///
/// The host never journals an arbitrary upload body. `replay_material` is the
/// concrete offering's explicit safe representation, accompanied by its exact
/// disclosure. `payload_digest` still commits to the original request, while
/// `replay_digest` detects corruption of the retained representation before it
/// reaches an offering decoder. `after_moves` preserves ordering with ordinary
/// landed turns without changing their legacy wire format.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoggedBinaryOperation {
    /// Stable wire cursor into the ordinary-move timeline.
    pub after_moves: u64,
    pub name: String,
    pub actor: DreggIdentity,
    pub payload_digest: [u8; 32],
    pub replay_digest: [u8; 32],
    pub replay_material: Vec<u8>,
    pub replay_disclosure: String,
    pub replay_is_canonical_request: bool,
    pub receipt: BinaryOperationReceipt,
}

/// **A session's reproducible input** — its [`SessionConfig`] seed plus the landed
/// [`LoggedMove`]s and [`LoggedBinaryOperation`]s in timeline order. Reopen it by re-driving both
/// from a fresh [`open`](crate::Offering::open) under the same `cfg`
/// ([`OfferingHost::resume`](crate::OfferingHost::resume)). It is not trusted: the executor checks
/// each move, while each operation's safe representation is digest-checked, decoded, verified,
/// reapplied, and compared with its journaled public receipt.
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
    /// Successful opaque operations, ordered relative to `moves` by each
    /// entry's `after_moves` cursor. Legacy logs decode with an empty vector.
    pub operations: Vec<LoggedBinaryOperation>,
}

impl SessionMoveLog {
    /// A fresh (moveless) log for a just-opened session under `key`/`id`/`cfg`.
    pub fn new(key: impl Into<String>, id: SessionId, cfg: SessionConfig) -> Self {
        SessionMoveLog {
            key: key.into(),
            id,
            cfg,
            moves: Vec::new(),
            operations: Vec::new(),
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
        self.moves.is_empty() && self.operations.is_empty()
    }

    /// Append one successfully applied opaque operation. The host constructs
    /// the entry so the original request and safe replay representation remain
    /// separately committed.
    pub fn record_binary_operation(&mut self, operation: LoggedBinaryOperation) {
        self.operations.push(operation);
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

    /// **Persist the signed-advance replay floors** for `(key, id)` — the last consumed
    /// [`SignedAction::counter`](crate::SignedAction::counter) per signer pubkey (hex). The host
    /// writes a floor through the moment
    /// [`advance_signed`](crate::OfferingHost::advance_signed) consumes it, and re-records the
    /// whole set at lifecycle eviction, so the floors survive eviction AND a process restart —
    /// wiping them would re-admit a captured envelope (a counter-reset replay). A store MUST
    /// merge **max-wise** (never lower a recorded floor).
    ///
    /// Returns whether the floors were durably recorded. **Default: `false`** (unsupported) —
    /// additive, an existing external implementor keeps compiling; the host then RETAINS the
    /// floors in memory at eviction instead of dropping them (fail-closed: a small map, never a
    /// replay hole).
    fn record_signed_counters(&self, key: &str, id: &SessionId, floors: &[(String, u64)]) -> bool {
        let _ = (key, id, floors);
        false
    }

    /// The persisted signed-advance replay floors for `(key, id)` — `(signer pubkey hex, last
    /// consumed counter)` pairs, loaded on [`resume`](crate::OfferingHost::resume) and merged
    /// max-wise into the host's live ledger. Default: empty (a store that never recorded any).
    fn load_signed_counters(&self, key: &str, id: &SessionId) -> Vec<(String, u64)> {
        let _ = (key, id);
        Vec::new()
    }

    /// Whether this store can durably retain offering-selected binary-operation
    /// replay material. The default is fail-closed so attaching an older store
    /// cannot silently make a successful opaque mutation disappear on restart.
    fn supports_binary_operations(&self) -> bool {
        false
    }

    /// Append one successfully applied opaque operation. Returns `true` only
    /// when both its public journal row and safe replay material were retained.
    fn record_binary_operation(
        &self,
        key: &str,
        id: &SessionId,
        operation: &LoggedBinaryOperation,
    ) -> bool {
        let _ = (key, id, operation);
        false
    }

    /// Drop `(key, id)`'s log (on session close) — it will not be resumed on the next boot.
    /// An implementor that persists signed-counter floors drops those too (the log is gone;
    /// nothing remains to resume, so nothing remains to guard).
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
    /// The persisted signed-advance replay floors, `(key, id) → (pubkey hex → last consumed
    /// counter)` — the counter-survival seam lifecycle eviction/resume rides (merge-max).
    counters: Rc<RefCell<BTreeMap<(String, String), BTreeMap<String, u64>>>>,
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

    fn record_signed_counters(&self, key: &str, id: &SessionId, floors: &[(String, u64)]) -> bool {
        let mut map = self.counters.borrow_mut();
        let entry = map.entry(Self::map_key(key, id)).or_default();
        for (pk, c) in floors {
            // Merge MAX-wise: a floor is never lowered (lowering one re-admits a replay).
            let slot = entry.entry(pk.clone()).or_insert(*c);
            *slot = (*slot).max(*c);
        }
        true
    }

    fn load_signed_counters(&self, key: &str, id: &SessionId) -> Vec<(String, u64)> {
        self.counters
            .borrow()
            .get(&Self::map_key(key, id))
            .map(|m| m.iter().map(|(pk, c)| (pk.clone(), *c)).collect())
            .unwrap_or_default()
    }

    fn supports_binary_operations(&self) -> bool {
        true
    }

    fn record_binary_operation(
        &self,
        key: &str,
        id: &SessionId,
        operation: &LoggedBinaryOperation,
    ) -> bool {
        let mut map = self.inner.borrow_mut();
        let entry = map
            .entry(Self::map_key(key, id))
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), SessionConfig::default()));
        entry.record_binary_operation(operation.clone());
        true
    }

    fn forget(&self, key: &str, id: &SessionId) {
        self.inner.borrow_mut().remove(&Self::map_key(key, id));
        self.counters.borrow_mut().remove(&Self::map_key(key, id));
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
        self.root.join(format!("{}.log", Self::name_for(key, id)))
    }

    /// The **signed-counter sidecar** path for `(key, id)` — the same content-hash name with a
    /// `.counters` extension, one `pubkey \t counter` line per signer floor. A sidecar (not extra
    /// lines in the `.log`) keeps the move-log wire format untouched: an old reader still decodes
    /// every log, and [`log_files`](FileResumeStore::log_files)'s `.log` filter never sees it.
    fn counters_path_for(&self, key: &str, id: &SessionId) -> PathBuf {
        self.root
            .join(format!("{}.counters", Self::name_for(key, id)))
    }

    /// Content-addressed sidecar for one offering-selected replay object. Raw
    /// bytes live here rather than being hex-expanded into the append-only text
    /// log (an fhEgg evidence bundle may be large).
    fn operation_path_for(&self, key: &str, id: &SessionId, replay_digest: &[u8; 32]) -> PathBuf {
        self.root.join(format!(
            "{}.op.{}",
            Self::name_for(key, id),
            hex32(replay_digest)
        ))
    }

    /// The collision-resistant file stem for `(key, id)`.
    fn name_for(key: &str, id: &SessionId) -> String {
        let mut h = blake3::Hasher::new();
        h.update(key.as_bytes());
        h.update(&[0]); // domain separator between key and id
        h.update(id.0.as_bytes());
        h.finalize().to_hex().to_string()
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

    fn load_path(&self, path: &Path) -> Option<SessionMoveLog> {
        let text = fs::read_to_string(path).ok()?;
        let mut log = decode_log(&text)?;
        // A renamed/spliced file must not claim a different `(key,id)` than its
        // content-addressed filename.
        if self.path_for(&log.key, &log.id) != path {
            return None;
        }
        for operation in &mut log.operations {
            // Preserve a missing/corrupt sidecar as a replayable *refusal*, not
            // an absent session. OfferingHost checks `replay_digest` and reports
            // `OperationRefused`, so lazy resume cannot mistake corruption for
            // "no durable session" and fresh-mint over it.
            operation.replay_material =
                fs::read(self.operation_path_for(&log.key, &log.id, &operation.replay_digest))
                    .unwrap_or_default();
        }
        Some(log)
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

    fn record_signed_counters(&self, key: &str, id: &SessionId, floors: &[(String, u64)]) -> bool {
        // Merge MAX-wise over whatever is already persisted (a floor is never lowered), then
        // rewrite the small sidecar whole. Report honestly: `false` on any IO failure, so the
        // host retains the floors in memory instead of trusting a write that did not land.
        let mut merged: BTreeMap<String, u64> = self
            .load_signed_counters(key, id)
            .into_iter()
            .collect::<BTreeMap<_, _>>();
        for (pk, c) in floors {
            let slot = merged.entry(pk.clone()).or_insert(*c);
            *slot = (*slot).max(*c);
        }
        let mut text = String::new();
        for (pk, c) in &merged {
            text.push_str(&format!("{}\t{}\n", esc(pk), c));
        }
        fs::write(self.counters_path_for(key, id), text).is_ok()
    }

    fn load_signed_counters(&self, key: &str, id: &SessionId) -> Vec<(String, u64)> {
        let Ok(text) = fs::read_to_string(self.counters_path_for(key, id)) else {
            return Vec::new();
        };
        text.lines()
            .filter(|l| !l.is_empty())
            .filter_map(|l| {
                let (pk, c) = l.split_once('\t')?;
                Some((unesc(pk), c.parse::<u64>().ok()?))
            })
            .collect()
    }

    fn supports_binary_operations(&self) -> bool {
        true
    }

    fn record_binary_operation(
        &self,
        key: &str,
        id: &SessionId,
        operation: &LoggedBinaryOperation,
    ) -> bool {
        if *blake3::hash(&operation.replay_material).as_bytes() != operation.replay_digest {
            return false;
        }
        self.write_header_if_absent(key, id, &SessionConfig::default());

        // Write the potentially large safe replay object first. An interrupted
        // write cannot become a journaled operation; an orphan sidecar is inert.
        let sidecar = self.operation_path_for(key, id, &operation.replay_digest);
        if sidecar.exists() {
            if fs::read(&sidecar).ok().as_deref() != Some(operation.replay_material.as_slice()) {
                return false;
            }
        } else {
            let Ok(mut file) = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&sidecar)
            else {
                return false;
            };
            if file.write_all(&operation.replay_material).is_err() || file.sync_data().is_err() {
                return false;
            }
        }

        let encoded = encode_operation(operation);
        let log_path = self.path_for(key, id);
        if fs::read_to_string(&log_path)
            .ok()
            .is_some_and(|text| text.lines().any(|line| line == encoded))
        {
            return true;
        }
        let Ok(mut file) = fs::OpenOptions::new().append(true).open(log_path) else {
            return false;
        };
        writeln!(file, "{encoded}").is_ok() && file.sync_data().is_ok()
    }

    fn forget(&self, key: &str, id: &SessionId) {
        let _ = fs::remove_file(self.path_for(key, id));
        let _ = fs::remove_file(self.counters_path_for(key, id));
        let prefix = format!("{}.op.", Self::name_for(key, id));
        if let Ok(entries) = fs::read_dir(&self.root) {
            for entry in entries.flatten() {
                if entry
                    .file_name()
                    .to_str()
                    .is_some_and(|name| name.starts_with(&prefix))
                {
                    let _ = fs::remove_file(entry.path());
                }
            }
        }
    }

    fn load(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        self.load_path(&self.path_for(key, id))
    }

    fn all(&self) -> Vec<SessionMoveLog> {
        self.log_files()
            .iter()
            .filter_map(|path| self.load_path(path))
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

/// One opaque operation metadata row. The safe replay bytes live in a
/// content-addressed `.op.<digest>` sidecar; this line retains only commitments,
/// attribution, the public receipt, and the exact persistence disclosure.
fn encode_operation(operation: &LoggedBinaryOperation) -> String {
    let mut fields = vec![
        "@op".to_string(),
        operation.after_moves.to_string(),
        esc(&operation.name),
        esc(&operation.actor.0),
        hex32(&operation.payload_digest),
        hex32(&operation.replay_digest),
        esc(&operation.receipt.operation),
        hex32(&operation.receipt.receipt_id),
        esc(&operation.replay_disclosure),
        (operation.replay_is_canonical_request as u8).to_string(),
        operation.receipt.public_fields.len().to_string(),
    ];
    for (key, value) in &operation.receipt.public_fields {
        fields.push(esc(key));
        fields.push(esc(value));
    }
    fields.join("\t")
}

fn decode_operation(fields: &[&str]) -> Option<LoggedBinaryOperation> {
    if fields.len() < 11 || fields[0] != "@op" {
        return None;
    }
    let replay_is_canonical_request = match fields[9] {
        "0" => false,
        "1" => true,
        _ => return None,
    };
    let count = fields[10].parse::<usize>().ok()?;
    if fields.len() != 11 + count.checked_mul(2)? {
        return None;
    }
    let mut public_fields = Vec::with_capacity(count);
    for pair in fields[11..].chunks_exact(2) {
        public_fields.push((unesc(pair[0]), unesc(pair[1])));
    }
    Some(LoggedBinaryOperation {
        after_moves: fields[1].parse::<u64>().ok()?,
        name: unesc(fields[2]),
        actor: DreggIdentity(unesc(fields[3])),
        payload_digest: decode_hex32(fields[4])?,
        replay_digest: decode_hex32(fields[5])?,
        replay_material: Vec::new(),
        replay_disclosure: unesc(fields[8]),
        replay_is_canonical_request,
        receipt: BinaryOperationReceipt {
            operation: unesc(fields[6]),
            receipt_id: decode_hex32(fields[7])?,
            public_fields,
        },
    })
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn decode_hex32(value: &str) -> Option<[u8; 32]> {
    if value.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).ok()?;
    }
    Some(out)
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
        if f.first().copied() == Some("@op") {
            log.record_binary_operation(decode_operation(&f)?);
            continue;
        }
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

    /// Opaque-operation replay bytes live in a content-addressed sidecar, not
    /// the text log, and corruption is refused before the offering sees them.
    #[test]
    fn binary_operation_journal_round_trips_and_refuses_sidecar_tamper() {
        let dir = scratch_dir("binary-operation");
        let store = FileResumeStore::open(&dir).expect("open store");
        let key = "market";
        let id = SessionId::new("shielded");
        let cfg = SessionConfig::with_seed(41);
        let replay_material = b"public proof material; no private witness".to_vec();
        let replay_digest = *blake3::hash(&replay_material).as_bytes();
        let operation = LoggedBinaryOperation {
            after_moves: u64::MAX,
            name: "settle.private.v1".to_string(),
            actor: DreggIdentity("worker-key".to_string()),
            payload_digest: replay_digest,
            replay_digest,
            replay_material: replay_material.clone(),
            replay_disclosure: "public proof and result only".to_string(),
            replay_is_canonical_request: true,
            receipt: BinaryOperationReceipt {
                operation: "settle.private.v1".to_string(),
                receipt_id: [0xA5; 32],
                public_fields: vec![("price".to_string(), "7".to_string())],
            },
        };

        store.record_open(key, &id, &cfg);
        assert!(store.record_binary_operation(key, &id, &operation));
        let loaded = store.load(key, &id).expect("journal loads");
        assert_eq!(loaded.operations, vec![operation.clone()]);

        let sidecar = store.operation_path_for(key, &id, &replay_digest);
        fs::write(&sidecar, b"tampered public proof").expect("tamper fixture");
        let corrupt = store
            .load(key, &id)
            .expect("corrupt operation remains visible to fail-closed resume");
        assert_ne!(
            *blake3::hash(&corrupt.operations[0].replay_material).as_bytes(),
            corrupt.operations[0].replay_digest,
            "the host's replay gate will reject the corrupt sidecar"
        );

        store.forget(key, &id);
        assert!(!sidecar.exists(), "forget removes operation sidecars");
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

    /// Signed-counter floors round-trip through BOTH stores, merge MAX-wise (a stale re-record
    /// never lowers a floor), and are dropped with the log on `forget`.
    #[test]
    fn signed_counter_floors_round_trip_and_never_lower() {
        let dir = scratch_dir("counters");
        let file = FileResumeStore::open(&dir).expect("open store");
        let mem = InMemoryResumeStore::new();
        let id = SessionId::new("s");
        let pk = "ab".repeat(32);

        for store in [&file as &dyn SessionResumeStore, &mem] {
            assert!(store.load_signed_counters("dungeon", &id).is_empty());
            assert!(store.record_signed_counters("dungeon", &id, &[(pk.clone(), 3)]));
            // A STALE (lower) re-record must not lower the floor — merge is max-wise.
            assert!(store.record_signed_counters("dungeon", &id, &[(pk.clone(), 1)]));
            assert_eq!(
                store.load_signed_counters("dungeon", &id),
                vec![(pk.clone(), 3)],
                "the floor held at its maximum"
            );
            store.forget("dungeon", &id);
            assert!(
                store.load_signed_counters("dungeon", &id).is_empty(),
                "forget drops the floors with the log"
            );
        }
        // The sidecar never pollutes the move-log enumeration.
        assert_eq!(file.len(), 0, "no .log files — sidecars are not logs");

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
