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

use crate::signed::{Attribution, Custody};
use crate::{Action, BinaryOperationReceipt, DreggIdentity, SessionConfig, SessionId};

/// **The re-verifiable envelope of a signed advance** — everything
/// [`verify_signed`](crate::verify_signed) consumed to admit the turn, persisted BESIDE the
/// [`LoggedMove`] so its `Signed` provenance survives a restart as a CHECKABLE fact rather than a
/// bare trust tag over a fully-controllable actor string.
///
/// A `Signed` [`LoggedMove`] used to reload from just its `actor` string + a one-byte `s` tag, so
/// anyone who could write the (unauthenticated) durable store forged a "verified-signer" turn no
/// key ever signed. With this envelope persisted,
/// [`OfferingHost::resume`](crate::OfferingHost::resume) RE-RUNS `verify_signed` over
/// `(pubkey, counter, signature, action, offering, session)` before honoring the `Signed`
/// attribution — a forged store line (a victim pubkey tagged `s` with no/wrong signature) fails
/// that check and the session refuses to resume (fail-closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedProvenance {
    /// The signer's Ed25519 public key, canonical lowercase hex — the key the signature verifies
    /// under and (by [`verify_signed`](crate::verify_signed)'s postcondition) the exact string the
    /// signed move's `actor` carries.
    pub pubkey_hex: String,
    /// The replay counter that was signed — part of the canonical
    /// [`signing_message`](crate::signing_message), so re-verification must use this exact value.
    pub counter: u64,
    /// The Ed25519 signature over the canonical signing message — the 64 bytes `verify_signed`
    /// checked at land time and re-checks on resume. Bound to [`epoch`](SignedProvenance::epoch)
    /// when that is `Some`.
    pub signature: [u8; 64],
    /// **The custody grade** — did a USER-held key sign, or a SERVER-held (custodial) one? Not part
    /// of the re-verified crypto; it is *provenance* (where the key lived), persisted so a resumed
    /// or displayed `Signed` receipt can say WHICH — a bare `Signed` used to collapse them. A line
    /// persisted before the custody column existed decodes as [`Custody::Custodial`] (the honest
    /// floor, never the stronger `UserHeld` claim).
    pub custody: Custody,
    /// **The host incarnation the signature is bound to**, if any ([`crate::OfferingHost::signing_epoch`]).
    /// `Some` for a turn admitted through
    /// [`advance_signed_attributed`](crate::OfferingHost::advance_signed_attributed) under a live
    /// epoch — the message was [`signing_message_in_epoch`](crate::signing_message_in_epoch), so
    /// resume MUST re-verify under this exact epoch (the live host now carries a fresh one). `None`
    /// for an epoch-free signature (the game spine's inner action signature, whose replay binding is
    /// its separate authority signature, and any pre-epoch persisted line).
    pub epoch: Option<[u8; 32]>,
}

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
    /// **The re-verifiable signature envelope** for a `Signed` move ([`SignedProvenance`]) — the
    /// `(counter, signature)` [`verify_signed`](crate::verify_signed) consumed, persisted so the
    /// `Signed` provenance is INDEPENDENTLY re-checkable on resume. `Some` iff `attribution` is
    /// [`Attribution::Signed`]: an `Asserted` (or legacy) move carries `None` and needs no
    /// signature. A durably-decoded `Signed` move ALWAYS carries `Some` (a bare `s` tag with no
    /// envelope is refused as a corrupt/forged line — see [`decode_log`]).
    pub signature: Option<SignedProvenance>,
}

impl LoggedMove {
    /// A logged move — an `action` that landed, attributed to `actor`. The attribution defaults
    /// to [`Attribution::Asserted`] (the legacy trust level); a verified move is recorded with
    /// [`LoggedMove::signed`].
    pub fn new(action: Action, actor: DreggIdentity) -> Self {
        let attribution = Attribution::from(actor.clone());
        LoggedMove {
            action,
            actor,
            attribution,
            signature: None,
        }
    }

    /// A logged move with an explicit [`Attribution`] trust level, carrying NO signature envelope
    /// — the asserted / legacy path. (A `Signed` trust level is only durably re-verifiable via
    /// [`LoggedMove::signed`], which persists the [`SignedProvenance`] beside it.)
    pub fn attributed(action: Action, actor: DreggIdentity, attribution: Attribution) -> Self {
        LoggedMove {
            action,
            actor,
            attribution,
            signature: None,
        }
    }

    /// A logged SIGNATURE-VERIFIED move — the signed-advance path records this, threading the
    /// [`SignedProvenance`] ([`verify_signed`](crate::verify_signed)'s consumed
    /// `(counter, signature)`) so the `Signed` attribution reloads as a re-verifiable fact. The
    /// `actor` and the attribution's pubkey are both `provenance.pubkey_hex` (the verified signer).
    pub fn signed(action: Action, actor: DreggIdentity, provenance: SignedProvenance) -> Self {
        let attribution = Attribution::Signed {
            pubkey_hex: provenance.pubkey_hex.clone(),
        };
        LoggedMove {
            action,
            actor,
            attribution,
            signature: Some(provenance),
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

    /// Append a landed advance with an explicit [`Attribution`] trust level and NO signature
    /// envelope — the asserted / legacy path. (The signed-advance path uses
    /// [`record_signed`](SessionMoveLog::record_signed).)
    pub fn record_attributed(
        &mut self,
        action: Action,
        actor: DreggIdentity,
        attribution: Attribution,
    ) {
        self.moves
            .push(LoggedMove::attributed(action, actor, attribution));
    }

    /// Append a landed SIGNATURE-VERIFIED advance, persisting the [`SignedProvenance`] beside it
    /// (the signed-advance path records this) so its `Signed` provenance is re-verifiable on resume.
    pub fn record_signed(
        &mut self,
        action: Action,
        actor: DreggIdentity,
        provenance: SignedProvenance,
    ) {
        self.moves
            .push(LoggedMove::signed(action, actor, provenance));
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
    ///
    /// Returns whether the advance was **durably recorded** — `true` only when the line is on stable
    /// storage (synced). A `false` means the committed turn did NOT reach the durable log, so the host
    /// must QUARANTINE the session (a landed-but-not-durable turn would resume as a silently-omitted or
    /// bricking replay), mirroring [`record_binary_operation`](SessionResumeStore::record_binary_operation).
    fn record_landed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
    ) -> bool;

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
    ) -> bool {
        let _ = attribution;
        self.record_landed(key, id, action, actor)
    }

    /// Append a LANDED signature-VERIFIED advance **with the re-verifiable envelope**
    /// ([`SignedProvenance`] — the replay counter and Ed25519 signature
    /// [`verify_signed`](crate::verify_signed) consumed), so the `Signed` provenance survives a
    /// restart as a CHECKABLE fact rather than a bare `actor` string + trust tag. A store that
    /// persists it lets [`OfferingHost::resume`](crate::OfferingHost::resume) RE-RUN `verify_signed`
    /// on reload; a forged store line (a victim pubkey tagged `s` with no/wrong signature) then
    /// fails re-verification and the session refuses to resume (fail-closed), instead of
    /// reconstructing a `Signed` turn no key ever signed.
    ///
    /// **Default: records the move as ASSERTED** (delegates to
    /// [`record_landed`](SessionResumeStore::record_landed)) — an implementor that cannot persist
    /// the signature MUST NOT persist an unverifiable `Signed` tag; it fails closed to the trust it
    /// can prove. Additive, so an existing external implementor keeps compiling.
    fn record_landed_signed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        provenance: &SignedProvenance,
    ) -> bool {
        let _ = provenance;
        self.record_landed(key, id, action, actor)
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

    /// **RETIRE `(key, id)`'s log without destroying it** — the finished-game seam.
    ///
    /// [`forget`](SessionResumeStore::forget) is a DELETE, and on a product whose claim is "a
    /// finished game can be replayed by anyone" a delete is the wrong direction: the moment a match
    /// ends is the moment its log becomes the artifact. `archive` moves the log OUT of the live
    /// resume set (so [`all`](SessionResumeStore::all) / boot-resume never reopen a finished match
    /// as if it were still being played) and INTO a retained set readable by
    /// [`load_archived`](SessionResumeStore::load_archived) /
    /// [`archived_logs`](SessionResumeStore::archived_logs), from which
    /// [`OfferingHost::replay_archived`](crate::OfferingHost::replay_archived) re-executes it
    /// through the real executor.
    ///
    /// Returns whether the log is now RETAINED. An implementor is allowed to answer `false` — and
    /// two honest cases do:
    ///
    /// * a store that cannot archive (the **default**, which delegates to `forget`): the log is
    ///   gone, exactly as it was before this method existed, and the `false` says so instead of
    ///   letting a caller believe an archive exists;
    /// * a log with NOTHING IN IT (no landed move, no operation). A session that was opened and
    ///   closed without being played is not a finished game; retaining its genesis would fill the
    ///   archive with rows that describe nothing. Such a log is DELETED and `false` is returned.
    ///
    /// Default: `forget` + `false` — additive, so an existing external implementor keeps compiling
    /// and keeps its current behaviour verbatim.
    fn archive(&self, key: &str, id: &SessionId) -> bool {
        self.forget(key, id);
        false
    }

    /// Load `(key, id)`'s ARCHIVED log ([`archive`](SessionResumeStore::archive)), if this store
    /// retained one. Default: `None` (a store that cannot archive has nothing archived).
    fn load_archived(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        let _ = (key, id);
        None
    }

    /// Every ARCHIVED log — the finished games this store retained. **Never** part of
    /// [`all`](SessionResumeStore::all): a finished match must not boot-resume into the live set.
    /// Default: empty.
    fn archived_logs(&self) -> Vec<SessionMoveLog> {
        Vec::new()
    }

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
    /// **The retired logs** ([`SessionResumeStore::archive`]) — finished games, held OUT of `inner`
    /// so [`all`](SessionResumeStore::all) and boot-resume never reopen one, and readable so
    /// [`OfferingHost::replay_archived`](crate::OfferingHost::replay_archived) can re-execute it.
    archived: Rc<RefCell<BTreeMap<(String, String), SessionMoveLog>>>,
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

    fn record_landed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
    ) -> bool {
        self.record_landed_attributed(key, id, action, actor, &Attribution::from(actor.clone()))
    }

    fn record_landed_attributed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        attribution: &Attribution,
    ) -> bool {
        let mut map = self.inner.borrow_mut();
        let entry = map
            .entry(Self::map_key(key, id))
            // A landed move on a session we never saw opened still establishes a log (default cfg);
            // in practice `record_open` always precedes it (the host opens before it advances).
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), SessionConfig::default()));
        entry.record_attributed(action.clone(), actor.clone(), attribution.clone());
        true
    }

    fn record_landed_signed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        provenance: &SignedProvenance,
    ) -> bool {
        let mut map = self.inner.borrow_mut();
        let entry = map
            .entry(Self::map_key(key, id))
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), SessionConfig::default()));
        entry.record_signed(action.clone(), actor.clone(), provenance.clone());
        true
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
        // `forget` is a TOTAL delete, archive included. Anything less would leave a "forgotten but
        // still archived" ghost that a finished-matches page would keep showing.
        self.archived.borrow_mut().remove(&Self::map_key(key, id));
    }

    fn archive(&self, key: &str, id: &SessionId) -> bool {
        let map_key = Self::map_key(key, id);
        let retired = self.inner.borrow_mut().remove(&map_key);
        match retired {
            // An UNPLAYED session is not a finished game — see the trait doc. It is dropped (it was
            // already removed above), and NOTHING else is: a stray re-open of a finished match's url
            // mints an empty session under that id, and destroying the archive or the replay floor
            // here would let that stray request wipe the artifact.
            Some(log) if log.is_empty() => self.archived.borrow().contains_key(&map_key),
            // Retire it. The counter FLOORS stay where they are (not moved, not dropped): they guard
            // this id against a captured signed envelope replaying onto a fresh mint, and that
            // hazard outlives the match.
            Some(log) => {
                self.archived.borrow_mut().insert(map_key, log);
                true
            }
            // Nothing live to retire — report the archive that already exists (idempotent, so
            // `replay_archived`'s resume→verify→re-close round trip cannot destroy what it replayed)
            // and touch NOTHING else.
            None => self.archived.borrow().contains_key(&map_key),
        }
    }

    fn load_archived(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        self.archived.borrow().get(&Self::map_key(key, id)).cloned()
    }

    fn archived_logs(&self) -> Vec<SessionMoveLog> {
        self.archived.borrow().values().cloned().collect()
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

/// The subdirectory a [`FileResumeStore`] retires finished sessions into
/// ([`SessionResumeStore::archive`]). It holds files with the SAME content-addressed stems as the
/// live root, which is what lets the archive be read back through the identical codec
/// ([`FileResumeStore::archive_view`]) instead of a second, drifting decoder — and it is a
/// DIRECTORY, so [`FileResumeStore::log_files`]'s `.log` extension filter skips it and a finished
/// match can never boot-resume into the live set.
const ARCHIVE_DIR: &str = "archive";

impl FileResumeStore {
    /// Open (creating if needed) a file store rooted at `dir`. Each session's log is a `*.log` file
    /// directly under `dir`.
    pub fn open(dir: impl Into<PathBuf>) -> io::Result<Self> {
        let root = dir.into();
        fs::create_dir_all(&root)?;
        Ok(FileResumeStore { root })
    }

    /// **The archive, viewed as a store of its own** — the same struct rooted at
    /// [`ARCHIVE_DIR`]. Every path helper, the whole line codec, the operation sidecar resolution
    /// and the filename↔content self-check are therefore SHARED with the live root rather than
    /// re-implemented for archived logs (a second decoder is where the divergence would live).
    ///
    /// The returned view is read-only *by use*, not by type: nothing calls a `record_*` method on
    /// it. It does not create the directory — an absent archive simply reads as empty.
    fn archive_view(&self) -> FileResumeStore {
        FileResumeStore {
            root: self.root.join(ARCHIVE_DIR),
        }
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

    /// **Every operation sidecar belonging to `(key, id)`** under this root. Shared by
    /// [`forget`](SessionResumeStore::forget) (which deletes them) and
    /// [`archive`](SessionResumeStore::archive) (which moves them), so the two cannot disagree about
    /// which files are part of a session — the divergence that would leave an archived log pointing
    /// at evidence still sitting in the live root.
    fn operation_sidecars(&self, key: &str, id: &SessionId) -> Vec<PathBuf> {
        let prefix = format!("{}.op.", Self::name_for(key, id));
        let mut out = Vec::new();
        if let Ok(entries) = fs::read_dir(&self.root) {
            for entry in entries.flatten() {
                if entry
                    .file_name()
                    .to_str()
                    .is_some_and(|name| name.starts_with(&prefix))
                {
                    out.push(entry.path());
                }
            }
        }
        out.sort();
        out
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

    fn record_landed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
    ) -> bool {
        self.record_landed_attributed(key, id, action, actor, &Attribution::from(actor.clone()))
    }

    fn record_landed_attributed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        attribution: &Attribution,
    ) -> bool {
        // The ASSERTED path — an asserted line's trust is implicit (no signature to persist), so
        // the attribution level rides only in the omission of the signed columns. A `Signed`
        // attribution never reaches here (the host routes it to `record_landed_signed`, which
        // persists the re-verifiable envelope); were one to, it is fail-closed to asserted rather
        // than written as an unverifiable `s`.
        let _ = attribution;
        // A landed move on a session we never saw opened still establishes a file (default cfg);
        // in practice `record_open` always precedes it (the host opens before it advances).
        self.write_header_if_absent(key, id, &SessionConfig::default());
        let path = self.path_for(key, id);
        // Durable-or-quarantine: report `true` only when the line is both written AND synced to
        // stable storage. A swallowed error here (the old best-effort append) would let a committed
        // turn vanish on a transient ENOSPC while the host reported `Landed` — a bricking/omitting
        // replay on the next boot. The host quarantines the session on `false`.
        match fs::OpenOptions::new().append(true).open(&path) {
            Ok(mut f) => {
                writeln!(f, "{}", encode_move(action, actor, None)).is_ok() && f.sync_data().is_ok()
            }
            Err(_) => false,
        }
    }

    fn record_landed_signed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        provenance: &SignedProvenance,
    ) -> bool {
        self.write_header_if_absent(key, id, &SessionConfig::default());
        let path = self.path_for(key, id);
        // Durable-or-quarantine (see `record_landed_attributed`): `true` only when written AND synced.
        match fs::OpenOptions::new().append(true).open(&path) {
            Ok(mut f) => {
                writeln!(f, "{}", encode_move(action, actor, Some(provenance))).is_ok()
                    && f.sync_data().is_ok()
            }
            Err(_) => false,
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
        for path in self.operation_sidecars(key, id) {
            let _ = fs::remove_file(path);
        }
        // `forget` is a TOTAL delete, archive included — anything less would leave a "forgotten but
        // still archived" ghost that a finished-matches page would keep showing. The view shares the
        // codec AND the path helpers, so this is the same removal one directory down.
        let view = self.archive_view();
        let _ = fs::remove_file(view.path_for(key, id));
        for path in view.operation_sidecars(key, id) {
            let _ = fs::remove_file(path);
        }
    }

    /// **Retire the log into the archive subdirectory instead of deleting it.** The move is a
    /// `rename` inside one directory tree, so it is atomic on every platform this runs on: the log is
    /// either live or archived, never half of both.
    ///
    /// Four things are deliberate here:
    ///
    /// * **the counter sidecar STAYS in the live root.** It is the signed-advance replay floor, and
    ///   what it guards — a captured envelope re-verifying against a fresh mint of the same id —
    ///   outlives the match. `forget` used to delete it on the argument "the log is gone, so nothing
    ///   remains to guard"; with the log RETAINED and the id still re-mintable, keeping the floor is
    ///   strictly the safer of the two, and it is also what lets
    ///   [`OfferingHost::replay_archived`](crate::OfferingHost::replay_archived) reload the floors
    ///   when it re-drives the archived tape;
    /// * **the operation sidecars MOVE with the log**, because the archived log's `replay_digest`
    ///   entries are resolved relative to whichever root loaded them;
    /// * **an already-archived id is idempotent.** Re-archiving reports the archive that exists
    ///   rather than reporting a loss, so `replay_archived`'s resume→verify→re-close round trip does
    ///   not destroy the thing it just replayed;
    /// * ⚑ **an unplayed genesis is deleted WITHOUT touching the archive.** A finished match's url
    ///   stays reachable, so a later visit (or a bound command that accidentally mints a fresh
    ///   session under that id and immediately closes it) produces an EMPTY live log over an existing
    ///   archive. Routing that through `forget` — a total delete — would let a stray request destroy
    ///   the artifact it came to look at.
    fn archive(&self, key: &str, id: &SessionId) -> bool {
        let live = self.path_for(key, id);
        let view = self.archive_view();
        let archived = view.path_for(key, id);
        if !live.exists() {
            // Nothing live to retire. Either it was already archived (report that) or there was
            // never a log at all.
            return archived.exists();
        }
        // A session that was opened and closed without being PLAYED is not a finished game. Remove
        // the genesis and its own sidecars; the archive (if any) and the replay floor are untouched.
        if self.load_path(&live).is_none_or(|log| log.is_empty()) {
            let _ = fs::remove_file(&live);
            for sidecar in self.operation_sidecars(key, id) {
                let _ = fs::remove_file(sidecar);
            }
            return archived.exists();
        }
        if fs::create_dir_all(&view.root).is_err() {
            // Fail HONEST, not loud: report that nothing is retained and leave the live log exactly
            // where it is. A caller that believed a false `true` would show a "finished match" row
            // pointing at a log nobody kept.
            return false;
        }
        for sidecar in self.operation_sidecars(key, id) {
            if let Some(name) = sidecar.file_name() {
                let _ = fs::rename(&sidecar, view.root.join(name));
            }
        }
        if fs::rename(&live, &archived).is_err() {
            return false;
        }
        true
    }

    fn load_archived(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        self.archive_view().load(key, id)
    }

    fn archived_logs(&self) -> Vec<SessionMoveLog> {
        self.archive_view().all()
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

/// One landed advance. An ASSERTED (or legacy) move is 8 columns:
/// `label \t turn \t arg \t enabled \t has_text \t text \t actor \t a`. A SIGNED move is 12
/// columns — the `s` trust tag PLUS the re-verifiable envelope AND its provenance grade:
/// `… \t actor \t s \t counter \t signature_hex \t custody \t epoch`: the `(counter, signature)`
/// [`verify_signed`](crate::verify_signed) consumed, the `custody` grade (`c` custodial / `u`
/// user-held), and the `epoch` the signature is bound to (64-hex host incarnation, or `-` for an
/// epoch-free signature). So [`decode_log`] reloads a `Signed` move as a fact
/// [`OfferingHost::resume`](crate::OfferingHost::resume) can RE-CHECK — not a bare tag over a
/// fully-controllable `actor` string — AND can say WHOSE key signed and under which incarnation.
/// The signer pubkey is the `actor` column itself (`verify_signed`'s postcondition: a signed move's
/// actor IS its verified pubkey hex), so it is not duplicated on the wire. A `Signed` trust level
/// with no persisted envelope is never written as `s` (it would be an unverifiable, forgeable
/// claim) — `provenance = None` yields an `a` line.
///
/// **Backward-compatible, additively:** old 7-column lines decode losslessly as `a`; a 10-column
/// `s` line (the pre-custody/epoch signed format) decodes as `Signed` with custody `Custodial` and
/// no epoch — the honest floor, never a wrong grade; a bare 8-column `s` (a signed tag with NO
/// envelope) is refused as corrupt — see [`decode_log`].
fn encode_move(
    action: &Action,
    actor: &DreggIdentity,
    provenance: Option<&SignedProvenance>,
) -> String {
    let base = format!(
        "{}\t{}\t{}\t{}\t{}\t{}\t{}",
        esc(&action.label),
        esc(&action.turn),
        action.arg,
        action.enabled as u8,
        action.text.is_some() as u8,
        esc(action.text.as_deref().unwrap_or("")),
        esc(&actor.0),
    );
    match provenance {
        Some(prov) => format!(
            "{base}\ts\t{}\t{}\t{}\t{}",
            prov.counter,
            hex64(&prov.signature),
            prov.custody.wire_tag(),
            prov.epoch
                .map(|e| hex32(&e))
                .unwrap_or_else(|| "-".to_string()),
        ),
        None => format!("{base}\ta"),
    }
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

fn hex64(bytes: &[u8; 64]) -> String {
    let mut out = String::with_capacity(128);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn decode_hex64(value: &str) -> Option<[u8; 64]> {
    if value.len() != 128 {
        return None;
    }
    let mut out = [0u8; 64];
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
        // Column count fixes the trust shape:
        //   7  = the pre-attribution legacy format (every such log was asserted-only);
        //   8  = an explicit trust tag (`a` asserted — an `s` here is a bare signed CLAIM with NO
        //        envelope and is REFUSED, never reconstructed Signed-without-a-signature);
        //   10 = a pre-custody/epoch signed move (the `s` tag + `counter` + `signature`) — decodes
        //        as Custodial + epoch-free (the honest floor, never a wrong grade);
        //   12 = a signed move carrying its custody grade + bound epoch too.
        if !matches!(f.len(), 7 | 8 | 10 | 12) {
            return None;
        }
        let label = unesc(f[0]);
        let turn = unesc(f[1]);
        let arg = f[2].parse::<i64>().ok()?;
        let enabled = f[3] == "1";
        let has_text = f[4] == "1";
        let text = unesc(f[5]);
        let actor = DreggIdentity(unesc(f[6]));
        let mut action = Action::new(label, turn, arg, enabled);
        if has_text {
            action = action.with_text(text);
        }
        match (f.len(), f.get(7).copied()) {
            // Legacy 7-column, or an explicit asserted 8-column tag — always ASSERTED.
            (7, _) | (8, Some("a")) => {
                let attribution = Attribution::from(actor.clone());
                log.record_attributed(action, actor, attribution);
            }
            // A pre-custody/epoch SIGNED move (10 columns): the `s` tag + the re-verifiable
            // `(counter, signature)`. The actor column IS the signer pubkey hex. Custody defaults
            // to the honest floor (Custodial) and the signature is epoch-free (verified under the
            // legacy message on resume). The signature is NOT verified here (decode is a pure codec)
            // — `OfferingHost::resume` re-runs the verifier before honoring the `Signed` attribution.
            (10, Some("s")) => {
                let counter = f[8].parse::<u64>().ok()?;
                let signature = decode_hex64(f[9])?;
                let provenance = SignedProvenance {
                    pubkey_hex: actor.0.clone(),
                    counter,
                    signature,
                    custody: Custody::Custodial,
                    epoch: None,
                };
                log.record_signed(action, actor, provenance);
            }
            // A full SIGNED move (12 columns): the envelope PLUS its custody grade and bound epoch.
            (12, Some("s")) => {
                let counter = f[8].parse::<u64>().ok()?;
                let signature = decode_hex64(f[9])?;
                let custody = Custody::from_wire_tag(f[10])?;
                let epoch = match f[11] {
                    "-" => None,
                    hexed => Some(decode_hex32(hexed)?),
                };
                let provenance = SignedProvenance {
                    pubkey_hex: actor.0.clone(),
                    counter,
                    signature,
                    custody,
                    epoch,
                };
                log.record_signed(action, actor, provenance);
            }
            // A bare `s` with no envelope (8-column signed), or any unknown tag / column shape:
            // a corrupt or forged line — refuse the whole file (never a mislabeled Signed).
            _ => return None,
        }
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

    /// ⚑ **ARCHIVE RETAINS, `forget` DELETES — and the two must not be confused.** The finished
    /// match's log survives, is readable through the archive, and is held OUT of the live resume set
    /// so it never boots back as a game in progress. Non-vacuous on every clause: the same store is
    /// asked for the same session both ways.
    #[test]
    fn an_archived_session_is_retained_out_of_the_live_resume_set() {
        let dir = scratch_dir("archive");
        let store = FileResumeStore::open(&dir).expect("open store");
        let key = "automatafl";
        let played = SessionId::new("af1-played");
        let deleted = SessionId::new("af1-deleted");
        let cfg = SessionConfig::with_seed(0x5EED);

        for id in [&played, &deleted] {
            store.record_open(key, id, &cfg);
            assert!(store.record_landed(
                key,
                id,
                &Action::new("seal", "seal", 4, true),
                &DreggIdentity("afs1-a-secret".into()),
            ));
        }
        assert_eq!(
            store.all().len(),
            2,
            "both are live before anything retires"
        );

        // THE DELETE, for contrast — this is what `close` used to do to a finished match.
        store.forget(key, &deleted);
        assert!(store.load(key, &deleted).is_none());
        assert!(
            store.load_archived(key, &deleted).is_none(),
            "a forgotten log is GONE — `forget` is not a quiet archive"
        );

        // THE ARCHIVE.
        assert!(store.archive(key, &played), "a played log is retained");
        assert!(
            store.load(key, &played).is_none(),
            "an archived match must not be resumable as a live session"
        );
        assert!(
            store.all().is_empty(),
            "…and must not be boot-resumed: `all` is the live set only"
        );
        let archived = store
            .load_archived(key, &played)
            .expect("the finished match's log is retained");
        assert_eq!(archived.key, key);
        assert_eq!(archived.id, played);
        assert_eq!(
            archived.cfg.seed,
            Some(0x5EED),
            "the seed the replay re-derives the world from survives"
        );
        assert_eq!(archived.moves.len(), 1);
        assert_eq!(archived.moves[0].actor.0, "afs1-a-secret");
        assert_eq!(
            store.archived_logs().len(),
            1,
            "the archive enumerates exactly the finished match"
        );

        // IDEMPOTENT: replaying an archived match re-closes it, which re-archives it. That must not
        // be the thing that destroys the artifact.
        assert!(
            store.archive(key, &played),
            "re-archiving reports the archive"
        );
        assert!(store.load_archived(key, &played).is_some());

        let _ = fs::remove_dir_all(&dir);
    }

    /// A session that was OPENED and closed without being PLAYED is not a finished game, and filling
    /// the archive with rows that describe nothing would make "your finished matches" meaningless.
    /// Such a log is deleted and `archive` says so by answering `false`.
    #[test]
    fn an_unplayed_session_is_deleted_rather_than_archived() {
        let dir = scratch_dir("archive-empty");
        let store = FileResumeStore::open(&dir).expect("open store");
        let id = SessionId::new("af1-never-played");
        store.record_open("automatafl", &id, &SessionConfig::with_seed(3));

        assert!(
            !store.archive("automatafl", &id),
            "an unplayed session reports NOTHING retained"
        );
        assert!(store.load("automatafl", &id).is_none());
        assert!(store.load_archived("automatafl", &id).is_none());
        assert!(store.archived_logs().is_empty());

        // …and an id the store never saw at all is `false` too, not a phantom archive.
        assert!(!store.archive("automatafl", &SessionId::new("af1-unknown")));

        let _ = fs::remove_dir_all(&dir);
    }

    /// ⚑ **A STRAY RE-OPEN MUST NOT WIPE A FINISHED MATCH.** A finished match's url stays reachable,
    /// so a later visit (or a bound command that mints a fresh session under that id and immediately
    /// closes it) leaves an EMPTY live log sitting over an existing archive. If the unplayed-genesis
    /// path routed through `forget` — a total delete — that stray request would destroy the artifact
    /// it came to look at. Driven on both stores, because they had to agree about this.
    #[test]
    fn an_empty_re_open_over_an_archived_match_does_not_destroy_it() {
        let dir = scratch_dir("archive-reopen");
        let file = FileResumeStore::open(&dir).expect("open store");
        let memory = InMemoryResumeStore::new();
        let key = "automatafl";
        let id = SessionId::new("af1-revisited");
        let cfg = SessionConfig::with_seed(23);

        for store in [
            &file as &dyn SessionResumeStore,
            &memory as &dyn SessionResumeStore,
        ] {
            store.record_open(key, &id, &cfg);
            assert!(store.record_landed(
                key,
                &id,
                &Action::new("seal", "seal", 2, true),
                &DreggIdentity("afs1-a".into()),
            ));
            assert!(store.archive(key, &id), "the played match is retained");

            // THE STRAY: a fresh genesis under the same id, closed with nothing played.
            store.record_open(key, &id, &cfg);
            assert!(
                store.archive(key, &id),
                "the empty re-open must report the archive that still exists"
            );
            let kept = store
                .load_archived(key, &id)
                .expect("the finished match survived a stray re-open");
            assert_eq!(kept.moves.len(), 1, "…with its moves intact");
            assert!(
                store.load(key, &id).is_none(),
                "…and the stray genesis itself is gone from the live set"
            );
        }

        let _ = fs::remove_dir_all(&dir);
    }

    /// The in-memory reference store carries the SAME archive contract as the durable one — the
    /// committed in-RAM suites drive it, so a divergence here is a divergence nobody would see until
    /// a deployment with a session dir behaved differently from every test.
    #[test]
    fn the_in_memory_store_archives_on_the_same_contract() {
        let store = InMemoryResumeStore::new();
        let key = "tug";
        let played = SessionId::new("tug1-played");
        let empty = SessionId::new("tug1-empty");
        let cfg = SessionConfig::with_seed(19);

        store.record_open(key, &played, &cfg);
        store.record_landed(
            key,
            &played,
            &Action::new("pull", "pull", 1, true),
            &DreggIdentity("tugs1-b-secret".into()),
        );
        store.record_open(key, &empty, &cfg);

        assert!(store.archive(key, &played));
        assert!(
            !store.archive(key, &empty),
            "an unplayed session is deleted"
        );
        assert!(store.load(key, &played).is_none());
        assert!(store.all().is_empty(), "the live set is empty");
        assert_eq!(store.archived_logs().len(), 1);
        assert_eq!(
            store
                .load_archived(key, &played)
                .expect("retained")
                .moves
                .len(),
            1
        );
        assert!(store.archive(key, &played), "idempotent");
    }

    /// ⚑ The signed-replay FLOOR survives an archive. `forget` drops it on the argument "the log is
    /// gone, so nothing remains to guard" — but an archived id is still re-mintable, so the floor is
    /// exactly what stops a captured envelope from replaying onto a fresh session of the same name.
    #[test]
    fn archiving_keeps_the_signed_replay_floor_that_forget_drops() {
        let dir = scratch_dir("archive-counters");
        let store = FileResumeStore::open(&dir).expect("open store");
        let key = "automatafl";
        let id = SessionId::new("af1-signed");
        let pubkey_hex = "cd".repeat(32);
        store.record_open(key, &id, &SessionConfig::with_seed(5));
        store.record_landed(
            key,
            &id,
            &Action::new("seal", "seal", 1, true),
            &DreggIdentity("afs1-a".into()),
        );
        assert!(store.record_signed_counters(key, &id, &[(pubkey_hex.clone(), 9)]));

        assert!(store.archive(key, &id));
        assert_eq!(
            store.load_signed_counters(key, &id),
            vec![(pubkey_hex.clone(), 9)],
            "the replay floor outlives the match it guarded"
        );

        // NON-VACUOUS: `forget` really does drop it, which is why the archive path had to differ.
        store.forget(key, &id);
        assert!(store.load_signed_counters(key, &id).is_empty());

        let _ = fs::remove_dir_all(&dir);
    }

    /// ATTRIBUTION PROVENANCE round-trips through the file store — a signed move reloads as
    /// `Signed` **carrying its re-verifiable `(counter, signature)` envelope**, an asserted one as
    /// `Asserted` — and a LEGACY 7-column log line (persisted before the trust column existed)
    /// still decodes, as `Asserted` (which is exactly what every pre-signed-seam attribution was).
    /// The existing wire format is never broken. A bare `s` tag with NO signature envelope (an old
    /// 8-column signed line, or a hand-forged one) is REFUSED as corrupt — never reconstructed as
    /// a `Signed` turn no signature backs.
    #[test]
    fn attribution_round_trips_and_legacy_seven_column_lines_still_decode() {
        let dir = scratch_dir("attribution");
        let store = FileResumeStore::open(&dir).expect("open store");
        let id = SessionId::new("s");
        let cfg = SessionConfig::with_seed(11);
        let pubkey_hex = "ab".repeat(32); // a 64-char stand-in pubkey hex
        let signature = [0x11u8; 64]; // an opaque signature blob (the store is a pure codec)
        let epoch = [0x22u8; 32]; // a stand-in host incarnation
        store.record_open("dungeon", &id, &cfg);
        // A USER-HELD, epoch-bound signed move — exercises BOTH new columns.
        store.record_landed_signed(
            "dungeon",
            &id,
            &Action::new("m", "choose", 1, true),
            &DreggIdentity(pubkey_hex.clone()),
            &SignedProvenance {
                pubkey_hex: pubkey_hex.clone(),
                counter: 4,
                signature,
                custody: Custody::UserHeld,
                epoch: Some(epoch),
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
        assert_eq!(
            log.moves[0].signature,
            Some(SignedProvenance {
                pubkey_hex: pubkey_hex.clone(),
                counter: 4,
                signature,
                custody: Custody::UserHeld,
                epoch: Some(epoch),
            }),
            "the envelope PLUS its custody grade and bound epoch survive the round-trip"
        );
        assert!(
            !log.moves[1].attribution.is_signed(),
            "a plain record_landed reloads as Asserted"
        );
        assert!(
            log.moves[1].signature.is_none(),
            "an asserted move carries no signature envelope"
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
        assert!(old.moves[0].signature.is_none());

        // A PRE-CUSTODY/EPOCH signed line (10 columns: … actor s counter signature) decodes as
        // Signed with custody Custodial and NO epoch — the honest floor, never a wrong grade.
        let ten_col = format!(
            "dungeon\ttcol\t42\nm\tchoose\t1\t1\t0\t\t{pubkey_hex}\ts\t4\t{}\n",
            hex64(&signature)
        );
        let old_signed = decode_log(&ten_col).expect("a pre-custody signed log still decodes");
        assert_eq!(old_signed.moves.len(), 1);
        let prov = old_signed.moves[0]
            .signature
            .as_ref()
            .expect("the 10-column envelope survives");
        assert_eq!(
            prov.custody,
            Custody::Custodial,
            "a pre-custody signed line defaults to the honest Custodial floor"
        );
        assert!(
            prov.epoch.is_none(),
            "a pre-epoch signed line is honestly epoch-free"
        );

        // THE FORGE, at the codec layer: a bare 8-column `s` tag with NO signature envelope is
        // NOT reconstructed as Signed — it is a corrupt/forged line and the whole file is refused.
        let bare_signed = format!("dungeon\tforged\t42\nm\tchoose\t1\t1\t0\t\t{pubkey_hex}\ts\n");
        assert!(
            decode_log(&bare_signed).is_none(),
            "a signed tag with no persisted signature is corrupt — never a reconstructed Signed"
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
