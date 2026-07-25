//! **The generic DreggNet-offering → Discord adapter.**
//!
//! `/dungeon` (`commands::fiction`) proved one offering can be played in Discord. This module
//! is the *shape* of that proof, extracted: ANY [`dreggnet_offerings::Offering`] —
//! [`dreggnet_council::CouncilOffering`], [`dreggnet_market::MarketOffering`], a hosted-Hermes
//! or grain offering later — becomes a Discord command surface by implementing
//! [`DiscordOffering`] (a key, a title, a session store, and which turns take a typed value).
//!
//! The bot is the offering core's **Discord `Frontend`** in the sense
//! `dreggnet_offerings`'s doc names:
//!
//! * **present** — an offering's [`Offering::render`] returns a deos
//!   [`Surface`](dreggnet_offerings::Surface) (a
//!   `deos_view::ViewNode`). We paint it through the SAME `deos_view::discord` backend the
//!   desktop/web/seL4 renderers are peers of ([`embed_of`]) — the card is authored once by the
//!   offering and rendered by the platform. We keep only the *embed* from that render and mint
//!   the *components* ourselves ([`action_rows`]) from the typed [`Offering::actions`], because
//!   a Discord custom-id must carry **which offering** the press belongs to (`deos_view`'s
//!   `deosturn:<turn>:<arg>` id is already the `viewnode_applet` card route) and because some
//!   affordances need a **typed value** the user supplies in a modal.
//! * **collect** — a press decodes back into the typed `(SessionId, Action, DreggIdentity)`:
//!   [`parse_press`] → [`drive`] / [`drive_value`].
//! * **the actor is a real dregg identity** — never a Discord nickname. The presser's
//!   [`DreggIdentity`] is their derived Ed25519 public key hex
//!   (`UserCipherclerk::derive(bot_secret, user_id, federation)`), exactly as `/dungeon`'s
//!   ballots are attributed ([`identity_of`]).
//! * **the executor is the sole referee** — a press is ONE [`Offering::advance`]: a legal move
//!   lands a real `TurnReceipt` ([`Outcome::Landed`]), an illegal/ineligible/forged one is a
//!   real [`Outcome::Refused`] that commits nothing. A currently-ineligible affordance is
//!   rendered **locked but still pressable** (`🔒`, danger-styled) — the cap tooth is *shown,
//!   not hidden*, and pressing it surfaces the executor's own refusal honestly, rather than the
//!   frontend pretending to be the gate.
//!
//! ## The custom-id wire
//!
//! | id | meaning |
//! |----|---------|
//! | `offering:fire:<key>:<generation>:<head>:<turn>:<arg>` | exact-head press → one `advance` |
//! | `offering:ask:<key>:<generation>:<head>:<turn>` | exact-head press → typed-value modal |
//! | `offering:submit:<key>:<generation>:<head>:<turn>` | same-head modal submit → `advance` |
//!
//! `<key>` is [`DiscordOffering::KEY`] (`council`, `market`, …). The public generation/head stamp
//! is freshness, not authority: Discord authenticates the interaction and the executor remains
//! the referee. It prevents controls left on an old message from crossing a session replacement,
//! landed direct turn, or closed collective round.
//!
//! ## What is logic-driven vs what needs a live Discord token
//!
//! [`drive`] / [`drive_value`] are the **sync core** of a press: decode the custom-id, resolve
//! the actor, run the real offering turn, hand back the [`Outcome`]. The async handlers
//! ([`handle_component`], [`handle_modal`], [`handle_status`], [`handle_verify`]) are thin
//! serenity wrappers around them. So the tests drive the SAME path a live button press takes —
//! only the HTTP round-trip to Discord is absent.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{SyncSender, sync_channel};
use std::time::{SystemTime, UNIX_EPOCH};

use serenity::all::{
    ActionRowComponent, ButtonStyle, CommandInteraction, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateEmbed, CreateEmbedFooter, CreateInputText,
    CreateInteractionResponse, CreateInteractionResponseMessage, CreateModal,
    EditInteractionResponse, InputTextStyle, ModalInteraction,
};

use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::{
    Action, Attribution, Audience, AudienceProjection, CollectiveDecision, DreggIdentity,
    FileResumeStore, Offering, Outcome, SessionConfig, SessionId, SessionMoveLog,
    SessionResumeStore, Tally, VerifyReport, VoteCount, project_for_audience,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::commands::ack;

/// The custom-id namespace every offering component press lives in (`main.rs` routes on it).
pub const PREFIX: &str = "offering";
/// The modal input field carrying an affordance's typed value (a reserve price, a sealed bid).
pub const VALUE_FIELD: &str = "value";

/// Public, unforgeable-by-accident identity of the exact surface that minted a
/// Discord control. `generation` changes whenever a channel opens/replaces a
/// session; `head` changes whenever a direct turn lands (or a collective round
/// advances). Both ride every component and modal id and are compared inside
/// the store-thread mutation job.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ControlStamp {
    pub generation: u64,
    pub head: u64,
}

impl ControlStamp {
    /// Unbound wire sentinel retained for parser/render fixtures. Production
    /// routers must mint an exact live or persistent-world stamp instead.
    pub const PERSISTENT: Self = Self {
        generation: 0,
        head: 0,
    };
}

static OPEN_GENERATION_COUNTER: AtomicU64 = AtomicU64::new(1);

fn fresh_generation(channel: u64) -> u64 {
    let counter = OPEN_GENERATION_COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let mut h = blake3::Hasher::new();
    h.update(b"dregg.discord.offering-generation.v1\0");
    h.update(&channel.to_le_bytes());
    h.update(&counter.to_le_bytes());
    h.update(&nanos.to_le_bytes());
    h.update(&std::process::id().to_le_bytes());
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&h.finalize().as_bytes()[..8]);
    let generation = u64::from_le_bytes(bytes);
    if generation == 0 {
        counter.max(1)
    } else {
        generation
    }
}

/// A **live offering in a channel** — the offering value itself (a council carries its
/// electorate/catalog/quorum; a market its pricing) plus its open session. Both are needed to
/// advance, so both are stored.
pub struct Live<O: Offering> {
    /// The offering (the stateless-ish factory that also carries the session-shaping config).
    pub offering: O,
    /// The live confined session (the real receipt chain).
    pub session: O::Session,
    /// The live collective ballot round — `Some` iff this offering runs in **collective mode**
    /// ([`DiscordOffering::collective`]): many pressers cast write-once votes per round, and the
    /// plurality winner drives ONE [`Offering::advance_collective`]. `None` for a direct
    /// (1-press-1-turn) offering, whose presses resolve immediately through [`drive`].
    pub round: Option<CollectiveRound>,
    /// Fresh for every open/replacement in this process, and time/counter-bound
    /// so controls left in Discord across a restart do not alias a new session.
    pub generation: u64,
    /// Monotonic direct-state head. Collective surfaces use their round number
    /// as the control head instead (votes must not stale one another).
    pub control_head: u64,
    /// OfferingHost-compatible replay journal for this exact live session.
    /// Ordinary landed moves and safe opaque operations share one relative
    /// timeline; a frontend restart replays this log rather than trusting a
    /// serialized session blob.
    pub journal: SessionMoveLog,
    /// Optional write-through persistence for [`Self::journal`]. Constructed
    /// on this store's owning thread because implementations may be `!Send`.
    pub resume_store: Option<Box<dyn SessionResumeStore>>,
}

impl<O: Offering> Live<O> {
    /// The exact incarnation/head a newly rendered control must carry.
    pub fn control_stamp(&self) -> ControlStamp {
        ControlStamp {
            generation: self.generation,
            head: self
                .round
                .as_ref()
                .map_or(self.control_head, |round| round.round),
        }
    }

    /// Record one ordinary or crowd turn iff the executor actually landed it.
    /// This is the typed-store twin of `OfferingHost::record_landed`.
    ///
    /// Returns whether the record is **durable**. `true` when nothing needed persisting (a
    /// refused move commits nothing; a session with no attached store never claimed durability)
    /// or when the attached store confirmed the line reached stable storage. `false` is the one
    /// dangerous case the [`SessionResumeStore::record_landed`] contract names: the turn LANDED
    /// on the substrate but its line did not reach the log, so a later replay would silently omit
    /// a committed turn — or brick on the next one. The caller QUARANTINES the session on
    /// `false`; before this the boolean was discarded and that divergence was invisible.
    #[must_use]
    pub fn record_landed(&mut self, action: Action, actor: DreggIdentity, outcome: &Outcome) -> bool
    where
        O: DiscordOffering,
    {
        if !outcome.landed() {
            return true;
        }
        self.journal.record(action.clone(), actor.clone());
        match self.resume_store.as_deref() {
            None => true,
            Some(store) => store.record_landed(O::KEY, &self.journal.id, &action, &actor),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE DURABLE SESSION STORE — what survives a restart, and what deliberately does not.
//
// A live offering session is a real confined world plus a hash-linked receipt chain, and it
// lived ONLY in `Store<O>`'s thread-owned `HashMap`. Every game in flight died with the process.
//
// What is persisted is NOT the session: it is the session's REPRODUCIBLE PUBLIC INPUT — the
// `SessionConfig` seed plus the ordered landed `(action, actor)` pairs ([`SessionMoveLog`]).
// A resume RE-DRIVES those through the real executor from a fresh `open(cfg)`, so the receipt
// chain is REBUILT rather than restored: the resumed session can take the next turn because the
// turns behind it genuinely re-landed. A serialized state blob would have produced the exact
// fake this avoids — a board that renders and refuses every move.
//
// The store is the offering core's own [`FileResumeStore`] (append-only text, one file per
// session, `sync_data` per line). It is not a second implementation: the bot supplies the root
// and the core does the persisting.
//
// DELIBERATELY EPHEMERAL, per store:
//   * an in-flight COLLECTIVE ROUND (the ballots cast but not yet closed) — a ballot commits
//     nothing to the substrate, so there is nothing to reproduce; the round re-opens over the
//     resumed state.
//   * `crate::throttle` token buckets — a restart forgiving a rate limit is correct. The
//     limiter is explicitly not a security boundary (the executor is the referee), and its
//     buckets are pure recovery state: a persisted one only ever punishes.
//   * `crate::viewnode_applet` tally cards — a per-user toy counter with no external claim.
// ─────────────────────────────────────────────────────────────────────────────

/// Where the durable session logs live, or `None` when session persistence is OFF. Installed
/// once at boot by [`install_resume_store`]; unset in unit tests that never install one.
static RESUME_ROOT: OnceLock<Option<PathBuf>> = OnceLock::new();

/// **Main-loop entry point.** Point every offering session store at `root` (or `None` to run
/// sessions purely in RAM, the pre-existing behaviour). First install wins; call once at boot,
/// BEFORE any offering command is served.
pub fn install_resume_store(root: Option<PathBuf>) {
    let _ = RESUME_ROOT.set(root);
}

/// The installed durable root, if session persistence is on.
fn resume_root() -> Option<&'static PathBuf> {
    RESUME_ROOT.get().and_then(|r| r.as_ref())
}

/// Build a durable store handle on the CALLING thread (which, for every use below, is the
/// session store's own thread — `SessionResumeStore` is deliberately not `Send`-bound).
/// `None` when persistence is off, or when the directory cannot be opened — in which case the
/// session still runs, in RAM, exactly as it did before, and says so in the log.
fn durable_store() -> Option<Box<dyn SessionResumeStore>> {
    let root = resume_root()?;
    match FileResumeStore::open(root) {
        Ok(store) => Some(Box::new(store)),
        Err(e) => {
            tracing::warn!(
                "offering session persistence is UNAVAILABLE ({}): {e} — sessions in this \
                 process will not survive a restart",
                root.display(),
            );
            None
        }
    }
}

/// The durable log id of `channel`'s session of this offering at `generation`. The generation
/// rides the id so a resume can restore the EXACT incarnation a Discord button was minted
/// against (see [`resume_in`]); the `(key, channel)` prefix is what a cold lookup scans for.
fn journal_id(key: &str, channel: u64, generation: u64) -> SessionId {
    SessionId::new(format!("discord:{key}:{channel}:{generation:016x}"))
}

/// The `(key, channel)` prefix every durable log id for this channel starts with.
fn journal_prefix(key: &str, channel: u64) -> String {
    format!("discord:{key}:{channel}:")
}

/// The generation stamped into a durable log id, or `None` for an id this build does not mint.
fn generation_of(id: &SessionId) -> Option<u64> {
    u64::from_str_radix(id.0.rsplit(':').next()?, 16).ok()
}

/// The channel's persisted log, if one is on disk. There is **at most one per `(key, channel)`**:
/// an open forgets the channel's previous logs before recording its own ([`open_core`]), so a
/// replaced session leaves nothing behind to alias. If more than one is somehow present the
/// lookup refuses rather than guessing which incarnation a stranger's button belonged to.
fn stored_log(store: &dyn SessionResumeStore, key: &str, channel: u64) -> Option<SessionMoveLog> {
    let prefix = journal_prefix(key, channel);
    let mut found: Vec<SessionMoveLog> = store
        .all()
        .into_iter()
        .filter(|log| log.key == key && log.id.0.starts_with(&prefix))
        .collect();
    match found.len() {
        1 => found.pop(),
        0 => None,
        n => {
            tracing::warn!(
                "{n} durable {key} logs for channel {channel} — refusing to guess which \
                 incarnation to resume",
            );
            None
        }
    }
}

/// A turn whose [`Action::arg`] is a **number the user supplies** rather than a fixed index —
/// rendered as a button that opens a Discord modal (the market's reserve price / sealed bid).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValuePrompt {
    /// The modal title.
    pub title: &'static str,
    /// The input field's label.
    pub label: &'static str,
    /// The input field's placeholder.
    pub placeholder: &'static str,
}

/// A turn whose [`Action::text`] is a **free-text string the user supplies** (a Hermes prompt, a
/// document edit's text) rather than a numeric arg — rendered as a button that opens a Discord
/// modal collecting text. Where a [`ValuePrompt`]'s modal value is parsed to `i64` and fired via
/// [`drive_value`], a text prompt's raw string rides the first-class [`Action::text`] payload and
/// fires via [`drive_text`]. It never rides the label: a label is DISPLAY, and an offering that
/// reads it as content commits the button's own caption as if it were the user's input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TextPrompt {
    /// The modal title.
    pub title: &'static str,
    /// The input field's label.
    pub label: &'static str,
    /// The input field's placeholder.
    pub placeholder: &'static str,
    /// A multi-line paragraph input (a document paragraph) vs a single line (a short prompt).
    pub paragraph: bool,
}

/// A unit of work against an offering's live session table, run ON the store's owning thread.
type Job<O> = Box<dyn FnOnce(&mut HashMap<u64, Live<O>>) + Send + 'static>;

/// **The per-offering session store — a dedicated thread that OWNS the live sessions.**
///
/// Not a `Mutex<HashMap<…>>`, and for a load-bearing reason: an offering session is not
/// necessarily `Send`. [`dreggnet_council::CouncilSession`] holds `collective_choice::BallotCap`s,
/// each carrying a `Mandate` whose non-amplification predicate is an `Rc<dyn Fn(u64) -> bool>`
/// (`dregg-intent`'s `agent_mandate`) — so a council session cannot cross a thread boundary at
/// all, and a `static Mutex<…>` (which needs `Sync`, hence `Send` contents) will not hold one.
///
/// So the sessions are **confined to their store's thread** (fittingly: an offering session IS a
/// confined thing). Every access is a job shipped to that thread and awaited; the session itself
/// never moves. Only `Send` job closures (the offering itself is BUILT on the store's thread by
/// [`open_in`]'s factory, so a world-backed offering holding an `Rc` never crosses either) and the
/// job's *result* (an embed, an [`Outcome`], a [`VerifyReport`] — all plain data) cross.
///
/// A job is short and CPU-bound (one real executor turn), and the call blocks the caller until it
/// returns — the same cost profile as `/dungeon`'s `sessions()` mutex, which likewise resolves a
/// real turn while holding the lock. Nothing awaits inside a job, so no deadlock is reachable.
///
/// (Were `Mandate::admits` an `Arc<dyn Fn + Send + Sync>`, this could collapse back to a plain
/// `Mutex<HashMap<…>>`. That is a cross-crate change to `dregg-intent`, deliberately not made
/// here.)
pub struct Store<O: DiscordOffering> {
    jobs: SyncSender<Job<O>>,
}

/// Why a store job did not return a value. BOTH cases used to abort the caller with a panic
/// (`send`/`recv` `.expect`), and a job that panicked killed the store thread outright — bricking
/// the whole offering subsystem until process restart. Now a panicking job is CONTAINED (the
/// thread lives on) and the fault is returned to the ONE caller, which degrades gracefully.
#[derive(Debug)]
enum StoreError {
    /// The store thread's channel is closed — it never spawned, or has gone away unrecoverably.
    ThreadGone,
    /// This job panicked; the panic was contained on the store thread, which survives.
    JobPanicked,
}

impl<O: DiscordOffering> Store<O> {
    /// Spawn the store's owning thread (called once, from the offering's `store()` `OnceLock`).
    pub fn spawn() -> Store<O> {
        let (jobs, rx) = sync_channel::<Job<O>>(64);
        std::thread::Builder::new()
            .name(format!("offering-{}", O::KEY))
            .spawn(move || {
                let mut sessions: HashMap<u64, Live<O>> = HashMap::new();
                while let Ok(job) = rx.recv() {
                    // A panicking job is contained per-job by `run`; this loop-level guard is the
                    // structural net so NO job can ever unwind out of the loop and kill the thread
                    // (which would brick the whole subsystem for every later caller).
                    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        job(&mut sessions)
                    }));
                }
            })
            .expect("spawn the offering session thread");
        Store { jobs }
    }

    /// Run `f` against the session table on the owning thread and hand back its result. A panic
    /// inside `f` is caught on the store thread and returned to THIS caller as
    /// [`StoreError::JobPanicked`]; the thread returns from the job normally and lives on to serve
    /// the next. The happy path is unchanged.
    fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut HashMap<u64, Live<O>>) -> R + Send + 'static,
    ) -> Result<R, StoreError> {
        let (tx, rx) = sync_channel::<std::thread::Result<R>>(1);
        self.jobs
            .send(Box::new(move |sessions| {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(sessions)));
                let _ = tx.send(result);
            }))
            .map_err(|_| StoreError::ThreadGone)?;
        match rx.recv() {
            Ok(Ok(value)) => Ok(value),
            Ok(Err(_panic)) => Err(StoreError::JobPanicked),
            Err(_) => Err(StoreError::ThreadGone),
        }
    }
}

/// **An offering the bot serves as a Discord surface.** Implement this on any
/// [`Offering`] and the whole Discord frontend (embed, buttons, modals, press→turn, verify)
/// comes from this module.
pub trait DiscordOffering: Offering + Sized + 'static
where
    Self::Session: 'static,
{
    /// The offering's key in the generation/head-bound custom-id wire (`council`, `market`).
    const KEY: &'static str;
    /// The embed title.
    const TITLE: &'static str;
    /// The embed colour.
    const COLOR: u32;
    /// The honest footer tagline (what the surface actually guarantees).
    const TAGLINE: &'static str;

    /// The per-channel session store for this offering (one live session per channel), owned by
    /// its own thread. Implementors hand back a `OnceLock`-initialised [`Store::spawn`].
    fn store() -> &'static Store<Self>;

    /// **How this offering's VALUE is rebuilt when a persisted session is resumed** — called on
    /// the store's own thread, so a `!Send` world-backed offering is born where it lives.
    ///
    /// A [`SessionMoveLog`] describes the session's inputs (the seed + the landed turns); it does
    /// NOT describe the offering value those turns were played against. An offering whose
    /// constructor is deterministic and argument-free can hand one back here and its channels
    /// survive a restart. An offering whose value carries runtime configuration the log cannot
    /// reproduce — a council's electorate, a market's pricing table, a Hermes brain, a shared
    /// world handle — MUST leave this `None`: replaying its moves into a differently-configured
    /// world would rebuild a state that never existed. Default: `None` (not resumable), so an
    /// offering opts IN to resume rather than inheriting a wrong one.
    fn rebuild() -> Option<Self> {
        None
    }

    /// Which turns take a user-supplied numeric arg (a modal), rather than a fixed one.
    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    /// Which turns take a user-supplied **free-text string** (a modal), carried on the
    /// [`Action::label`]. Default: none (the offering is all fixed-arg buttons).
    fn text_prompt(_turn: &str) -> Option<TextPrompt> {
        None
    }

    /// The EXACT invocation that opens a fresh session of this offering — the hint a stale
    /// press gets. `/play`-mounted offerings override this (`/play offering:<key>`); bespoke
    /// commands keep the `/<key> open` default.
    fn open_hint() -> String {
        format!("/{} open", Self::KEY)
    }

    /// Whether this offering runs as a **collective ballot** — many write-once voters per round,
    /// the plurality winner driving ONE [`Offering::advance_collective`] — rather than a direct
    /// 1-press-1-turn offering. Default: direct (`false`). A collective offering's session opens
    /// with a live [`CollectiveRound`]; a press casts a write-once vote ([`cast_vote`]) and a
    /// round close resolves the plurality winner as a real crowd turn ([`close_round`]).
    fn collective() -> bool {
        false
    }

    /// For a [`collective`](DiscordOffering::collective) offering, the identity the resolved
    /// plurality turn is **carried by** (the mover of record on the substrate). A plurality is a
    /// crowd decision with no single mover, so the default is the "party" pseudo-identity the
    /// dungeon uses; the real electorate is recorded in the [`CollectiveDecision`] beside it.
    fn collective_carrier() -> DreggIdentity {
        DreggIdentity("party".to_string())
    }

    /// A one-line honest status ribbon (verified turns, phase, quorum) for the footer.
    fn status_line(&self, session: &Self::Session) -> String;
}

// ─────────────────────────────────────────────────────────────────────────────
// The session store.
// ─────────────────────────────────────────────────────────────────────────────

/// Open a fresh session for `channel` (fail-closed: an offering that refuses to deploy is
/// surfaced, never faked). Takes a **factory** rather than an offering value: the offering (and
/// its session) is BUILT on the store's thread, where both then live — so an offering that is not
/// `Send` (a world-backed RPG surface holding an `Rc`-shared [`dreggnet_surfaces::SharedWorld`])
/// never crosses a thread boundary at all. Replaces any session already open in the channel.
pub fn open_in<O: DiscordOffering>(
    channel: u64,
    make: impl FnOnce() -> O + Send + 'static,
    cfg: SessionConfig,
) -> Result<(), dreggnet_offerings::OfferingError> {
    // The PRODUCTION open. It attaches the installed durable store (`None` when persistence is
    // off), so every offering command in the bot writes its move-log through without a single
    // call site changing. This used to hardcode `resume_store: None` while the store-attaching
    // constructor beside it had only `#[cfg(test)]` callers: persistence was built, tested, and
    // never reached a running bot.
    open_core::<O>(channel, make, cfg, || Ok(durable_store()))
        .map_err(dreggnet_offerings::OfferingError::Deploy)
}

/// Open a fresh live session with an OfferingHost-compatible durable replay
/// store. Both the offering and store factories run on the owning thread, so
/// neither the offering session nor a `!Send` store crosses thread boundaries.
pub fn open_in_with_resume_store<O: DiscordOffering>(
    channel: u64,
    make: impl FnOnce() -> O + Send + 'static,
    cfg: SessionConfig,
    make_store: impl FnOnce() -> Result<Box<dyn SessionResumeStore>, String> + Send + 'static,
) -> Result<(), String> {
    open_core::<O>(channel, make, cfg, move || make_store().map(Some))
}

/// The ONE open path: build the offering and its optional durable store on the store's owning
/// thread, forget any earlier durable log for this channel (an open REPLACES the channel's
/// session, so the record it would resume from must go with it), record the new open, and insert
/// the live session. Both public constructors are thin wrappers.
fn open_core<O: DiscordOffering>(
    channel: u64,
    make: impl FnOnce() -> O + Send + 'static,
    cfg: SessionConfig,
    make_store: impl FnOnce() -> Result<Option<Box<dyn SessionResumeStore>>, String> + Send + 'static,
) -> Result<(), String> {
    O::store()
        .run(move |sessions| {
            let offering = make();
            let session = offering
                .open(cfg.clone())
                .map_err(|error| error.to_string())?;
            // A collective offering opens with a live round over the session's first actions (an open
            // crowd — a restricted electorate is set with [`open_round`]); a direct offering has none.
            let round = if O::collective() {
                Some(CollectiveRound::new(0, offering.actions(&session), None))
            } else {
                None
            };
            let generation = fresh_generation(channel);
            let id = journal_id(O::KEY, channel, generation);
            let store = make_store()?;
            if let Some(store) = store.as_deref() {
                // AT MOST ONE durable log per (key, channel). A replacement open (or a fresh open
                // after a restart that never resumed) drops the channel's earlier record here, so
                // a cold lookup can never find two incarnations and have to guess.
                let prefix = journal_prefix(O::KEY, channel);
                for old in store.all() {
                    if old.key == O::KEY && old.id.0.starts_with(&prefix) {
                        store.forget(O::KEY, &old.id);
                    }
                }
                store.record_open(O::KEY, &id, &cfg);
            }
            sessions.insert(
                channel,
                Live {
                    offering,
                    session,
                    round,
                    generation,
                    control_head: 0,
                    journal: SessionMoveLog::new(O::KEY, id, cfg),
                    resume_store: store,
                },
            );
            Ok(())
        })
        .unwrap_or_else(|_| Err("the offering session thread is unavailable".to_string()))
}

/// Why a channel's persisted session could not be brought back. Every arm is fail-closed:
/// nothing is inserted, and the channel keeps behaving exactly as it did with no session — the
/// one thing that must never happen is a surface that renders and then refuses every move.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResumeRefusal {
    /// Session persistence is off, or this channel has no durable log.
    NoRecord,
    /// This offering cannot be rebuilt from a log alone — its VALUE carries runtime
    /// configuration the log does not describe (a council's electorate, a market's pricing, a
    /// Hermes brain). Named rather than guessed: reopening it under a DIFFERENT configuration
    /// would replay the moves into a world that is not the one they landed in.
    NotRebuildable,
    /// A fresh `open(cfg)` under the recorded seed refused.
    Deploy(String),
    /// A recorded move did not re-land. The log is not trusted — the executor re-checks every
    /// turn on the way back in — so a tampered or foreign line fails HERE and the session simply
    /// does not come back.
    Refused { index: usize, reason: String },
    /// The log carries a durable opaque operation (an uploaded proof bundle). Replaying one
    /// needs the offering's own decoder + receipt comparison, which lives in
    /// `OfferingHost::resume` and is not reimplemented here. Refused rather than replayed
    /// without it — dropping a committed operation would resume a state that never existed.
    HasOperations(usize),
    /// A line claims a verified signer. This adapter records only `Asserted` attributions, so a
    /// `Signed` line in one of ITS logs is a foreign or forged line, not a stronger claim.
    ForeignAttribution(usize),
}

impl std::fmt::Display for ResumeRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResumeRefusal::NoRecord => write!(f, "no durable session record for this channel"),
            ResumeRefusal::NotRebuildable => write!(
                f,
                "this offering's value is not reconstructible from its move log"
            ),
            ResumeRefusal::Deploy(why) => write!(f, "the session did not redeploy: {why}"),
            ResumeRefusal::Refused { index, reason } => {
                write!(f, "recorded move #{index} did not re-land: {reason}")
            }
            ResumeRefusal::HasOperations(n) => write!(
                f,
                "{n} journaled opaque operation(s) need the host's replay path"
            ),
            ResumeRefusal::ForeignAttribution(index) => write!(
                f,
                "recorded move #{index} claims a signature this surface never records"
            ),
        }
    }
}

/// **Bring `channel`'s persisted session back — by REPLAY, never by deserializing a state blob.**
///
/// Opens a fresh session under the log's recorded seed and re-drives every landed
/// `(action, actor)` through the real [`Offering::advance`]. Each one must LAND: the executor is
/// the referee on the way back in exactly as it was on the way out, so a spliced or tampered log
/// fails here and nothing is inserted. What comes back is therefore a session that can take the
/// next turn, with a receipt chain it genuinely re-built — not a rendering of one.
///
/// The **generation is restored from the log id**, so the buttons a player left in Discord before
/// the restart still address this session and still fire. That is deliberate: the generation
/// exists to stop a control from crossing into a *different* session, and this is the same one.
///
/// The in-flight collective round is NOT restored (a ballot commits nothing); a collective
/// offering re-opens its round over the resumed state.
pub fn resume_in<O: DiscordOffering>(channel: u64) -> Result<usize, ResumeRefusal> {
    O::store()
        .run(move |sessions| {
            // A live session won the race (a concurrent open, or another cold press that got
            // here first). Never overwrite it: the replayed one would discard turns the live
            // one has already landed.
            if let Some(live) = sessions.get(&channel) {
                return Ok(live.journal.moves.len());
            }
            let Some(store) = durable_store() else {
                return Err(ResumeRefusal::NoRecord);
            };
            let Some(log) = stored_log(store.as_ref(), O::KEY, channel) else {
                return Err(ResumeRefusal::NoRecord);
            };
            if !log.operations.is_empty() {
                return Err(ResumeRefusal::HasOperations(log.operations.len()));
            }
            let Some(offering) = O::rebuild() else {
                return Err(ResumeRefusal::NotRebuildable);
            };
            let mut session = offering
                .open(log.cfg.clone())
                .map_err(|e| ResumeRefusal::Deploy(e.to_string()))?;
            for (index, m) in log.moves.iter().enumerate() {
                if matches!(m.attribution, Attribution::Signed { .. }) {
                    return Err(ResumeRefusal::ForeignAttribution(index));
                }
                let outcome = offering.advance(&mut session, m.action.clone(), m.actor.clone());
                if !outcome.landed() {
                    let reason = match outcome {
                        Outcome::Refused(why) => why,
                        Outcome::Landed { .. } => unreachable!("landed() is false"),
                    };
                    return Err(ResumeRefusal::Refused { index, reason });
                }
            }
            let landed = log.moves.len();
            // The direct-surface head is exactly the count of landed turns (`open` starts it at
            // 0 and `note_direct_landing` bumps it once per landed direct turn), so restoring it
            // this way reproduces the stamp the pre-restart buttons carry, byte for byte.
            //
            // That identity holds ONLY because a log carrying opaque operations was refused
            // above: `commands::binary_operation` bumps `control_head` for a successful
            // operation WITHOUT recording an ordinary move, so a move count would under-count
            // the head for such a session. If operation replay is ever wired here, the head must
            // become `moves + operations`, not `moves` — the refusal above is what makes this
            // line correct today, not an accident that happens to line up.
            //
            // A collective surface's head is its ROUND number, which a move count cannot
            // reproduce — its stale ballot buttons are refused, which is right: the round they
            // belonged to is gone.
            let control_head = landed as u64;
            let round = if O::collective() {
                Some(CollectiveRound::new(
                    control_head,
                    offering.actions(&session),
                    None,
                ))
            } else {
                None
            };
            let generation = generation_of(&log.id).unwrap_or_else(|| fresh_generation(channel));
            sessions.insert(
                channel,
                Live {
                    offering,
                    session,
                    round,
                    generation,
                    control_head,
                    journal: log,
                    resume_store: Some(store),
                },
            );
            Ok(landed)
        })
        .unwrap_or(Err(ResumeRefusal::Deploy(
            "the offering session thread is unavailable".to_string(),
        )))
}

/// **The cold-press path**: if `channel` has no live session, try to bring its persisted one
/// back before answering "no session open". Returns whether a session is live afterwards.
///
/// This is what makes the persistence reachable without a boot-time registry of every offering
/// type: the router already resolves a press to its concrete `O`, so the resume happens exactly
/// when somebody touches the channel, and never for a channel nobody returns to.
pub fn ensure_live<O: DiscordOffering>(channel: u64) -> bool {
    if O::store()
        .run(move |sessions| sessions.contains_key(&channel))
        .unwrap_or(false)
    {
        return true;
    }
    match resume_in::<O>(channel) {
        Ok(turns) => {
            tracing::info!(
                "resumed the {} session in channel {channel} by replaying {turns} landed turn(s)",
                O::KEY,
            );
            true
        }
        Err(ResumeRefusal::NoRecord) => false,
        Err(why) => {
            tracing::warn!(
                "the persisted {} session in channel {channel} did NOT resume: {why}",
                O::KEY,
            );
            false
        }
    }
}

/// Whether `channel` has a session of this offering — **resuming a persisted one if it has not
/// been touched since the restart**.
///
/// The resume is deliberate here and not a surprising side effect of a query: this is what the
/// re-open guard (`commands::open_guard`) asks before it lets `/play` replace a channel's
/// session. Answering "no session" for a game that is merely cold would silently wipe a match
/// that was one press from being resumable — exactly the loss this whole path exists to stop.
pub fn is_open<O: DiscordOffering>(channel: u64) -> bool {
    ensure_live::<O>(channel)
}

/// Run `f` against the channel's live session (`None` when no session is open). `f` runs on the
/// store's thread; only its result comes back.
pub fn with_live<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&mut Live<O>) -> R + Send + 'static,
) -> Option<R> {
    O::store()
        .run(move |sessions| sessions.get_mut(&channel).map(f))
        .unwrap_or(None)
}

/// Run one transaction against a live session and optionally quarantine it.
/// The callback result and removal decision are made on the owning thread;
/// removal happens before the caller can observe the result.
pub(crate) fn with_live_transaction<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&mut Live<O>) -> (R, bool) + Send + 'static,
) -> Option<R> {
    O::store()
        .run(move |sessions| {
            let (result, quarantine) = {
                let live = sessions.get_mut(&channel)?;
                f(live)
            };
            if quarantine {
                // A quarantined session must not be resurrectable from disk either — see
                // `mutate_live`.
                forget_channel_log::<O>(sessions.get(&channel), channel);
                sessions.remove(&channel);
            }
            Some(result)
        })
        .unwrap_or(None)
}

/// Read the exact control incarnation/head of a live channel session.
pub fn control_stamp_in<O: DiscordOffering>(channel: u64) -> Option<ControlStamp> {
    with_live::<O, _>(channel, |live| live.control_stamp())
}

/// Mint a fixed-argument test/adapter control from the current live head.
/// Production renders obtain the same stamp atomically in [`surface_of`].
pub fn fire_id_in<O: DiscordOffering>(channel: u64, turn: &str, arg: i64) -> Option<String> {
    let turn = turn.to_string();
    control_stamp_in::<O>(channel).map(|stamp| fire_id_at(O::KEY, stamp, &turn, arg))
}

/// Mint a numeric-modal control from the current live head.
pub fn ask_id_in<O: DiscordOffering>(channel: u64, turn: &str) -> Option<String> {
    let turn = turn.to_string();
    control_stamp_in::<O>(channel).map(|stamp| ask_id_at(O::KEY, stamp, &turn))
}

/// Drop the channel's session **and its durable record**. A close is a decision that the session
/// is OVER, so leaving the log behind would let the very next press resurrect what was just
/// closed. Part of the adapter's session API (a `/<offering> close` subcommand is the obvious
/// next consumer); today the driven tests are what exercise it.
#[allow(dead_code)]
pub fn close_in<O: DiscordOffering>(channel: u64) {
    let _ = O::store().run(move |sessions| {
        forget_channel_log::<O>(sessions.get(&channel), channel);
        sessions.remove(&channel);
    });
}

/// Drop `channel`'s durable log — on the store's own thread, so the `!Send` store handle never
/// travels. Uses the live session's own attached store when there is one (the exact handle that
/// wrote the log), and otherwise opens one to clear a record left by an earlier process.
fn forget_channel_log<O: DiscordOffering>(live: Option<&Live<O>>, channel: u64) {
    if let Some(live) = live {
        if let Some(store) = live.resume_store.as_deref() {
            store.forget(O::KEY, &live.journal.id);
            return;
        }
    }
    let Some(store) = durable_store() else {
        return;
    };
    let prefix = journal_prefix(O::KEY, channel);
    for log in store.all() {
        if log.key == O::KEY && log.id.0.starts_with(&prefix) {
            store.forget(O::KEY, &log.id);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Identity — the actor is a derived dregg key, never a Discord nickname.
// ─────────────────────────────────────────────────────────────────────────────

/// The presser's **derived dregg identity** — their Ed25519 public key hex, deterministic in
/// `(bot_secret, discord_user_id, federation)`. The SAME derivation `/dungeon` attributes its
/// ballots to, and the SAME hex `CouncilOffering::member_identity` builds an electorate from.
pub fn identity_of(state: &BotState, discord_user_id: u64) -> DreggIdentity {
    DreggIdentity(
        UserCipherclerk::derive(
            &state.config.bot_secret,
            discord_user_id,
            state.federation_id_bytes,
        )
        .public_key_hex()
        .to_string(),
    )
}

/// The presser's raw Ed25519 public key (what a council electorate is built from).
pub fn public_key_of(state: &BotState, discord_user_id: u64) -> [u8; 32] {
    UserCipherclerk::derive(
        &state.config.bot_secret,
        discord_user_id,
        state.federation_id_bytes,
    )
    .app
    .public_key()
    .0
}

/// **Display-time cross-platform identity resolution.** Map a custodial pubkey hex to the stable
/// ACCOUNT ID of the root key K it linked to (via `/link-prove`, recorded in the shared
/// `$DREGG_LINK_DIR/links.tsv`), falling back to the custodial key ITSELF when it was never linked.
/// So a Discord-you and a Telegram-you (different custodial keys) that both linked to the same K
/// collapse to ONE human wherever a board / leaderboard groups or shows players.
///
/// The join key is the rotation-ready account id
/// ([`webauth_core::link_registry::LinkStore::resolve_root_account`], via
/// [`RootResolver`](webauth_core::identity_resolve::RootResolver)), NOT the raw root pubkey: it is
/// byte-identical to the identity CELL's id, so the shallow TSV and the coming cell agree, and the
/// resolution survives a future signing-key rotation.
///
/// This is a DISPLAY / RANK concern only. Attribution is UNCHANGED: the turn (and its proof /
/// receipt) is still signed by, and attributed to, the custodial key — only the label a board
/// groups and shows under resolves to the account. Additive by construction: an unlinked key
/// resolves to itself, so the common unlinked case is byte-identical to today.
///
/// **Per-call** — it re-reads the link store each time. A board render should build ONE
/// [`RootResolver`](webauth_core::identity_resolve::RootResolver) snapshot and resolve every row
/// against it (the boards here do); this stays for the one-off single-identity sites.
pub fn resolve_display_root(custodial_pubkey_hex: &str) -> String {
    webauth_core::identity_resolve::RootResolver::load().resolve(custodial_pubkey_hex)
}

// ─────────────────────────────────────────────────────────────────────────────
// COLLECTIVE MODE — an optional per-offering write-once ballot.
//
// A DIRECT offering resolves each press as one turn (1-press-1-turn, [`drive`]). A COLLECTIVE
// offering ([`DiscordOffering::collective`]) instead runs a round: many pressers cast write-once
// votes (keyed by derived dregg identity), and a round *close* resolves the plurality winner as
// ONE real [`Offering::advance_collective`] carrying the whole [`CollectiveDecision`] (the
// electorate + the offering core's [`Tally`] + the carrier). The `/dungeon` crowd is the shape
// this generalises: the crowd decides, the world disposes, the receipt records who decided.
// ─────────────────────────────────────────────────────────────────────────────

/// The outcome of casting one collective ballot ([`CollectiveRound::cast`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cast {
    /// The ballot was recorded (the voter's first vote this round).
    Recorded,
    /// The voter already voted this round — refused (write-once per derived identity).
    AlreadyVoted,
    /// The voter is not in this round's electorate — refused (a restricted collective).
    NotEligible,
    /// The chosen option is not on this round's ballot.
    BadOption,
    /// No round is open (either not a collective offering, or no session).
    NoRound,
    /// No session of this offering is open in the channel.
    NoSession,
    /// The control was minted by a replaced session or an earlier round.
    StaleSurface,
}

/// **A live voting round** over an offering's cap-gated [`Action`]s. A ballot is keyed by the
/// voter's **derived dregg public-key hex** (never a Discord nickname), and is **write-once**: a
/// second vote from the same identity is refused. The plurality winner ([`winner_position`]) is
/// resolved as one real crowd turn by [`close_round`]; ties break toward the lowest option index
/// (deterministic, reproducible — the SAME rule `/dungeon`'s bespoke ballot uses).
pub struct CollectiveRound {
    /// The round number (monotonic per session).
    pub round: u64,
    /// The candidate moves, in stable order (the offering's actions at round open). The option
    /// position is the ballot id; the option's [`Action::arg`] is what the [`Tally`] carries.
    pub options: Vec<Action>,
    /// The ballots cast: voter public-key hex → chosen option position (write-once).
    pub ballots: HashMap<String, usize>,
    /// The eligible voters (public-key hex), or `None` for an **open crowd** (anyone may vote —
    /// the `/dungeon` default). A restricted electorate (a council-shaped crowd) refuses an
    /// outsider's ballot at [`Cast::NotEligible`]; the substrate is still the referee of the
    /// resolved turn.
    pub electorate: Option<Vec<String>>,
}

impl CollectiveRound {
    /// A fresh round over `options`, restricted to `electorate` (or an open crowd if `None`).
    pub fn new(round: u64, options: Vec<Action>, electorate: Option<Vec<DreggIdentity>>) -> Self {
        Self::with_electorate(
            round,
            options,
            electorate.map(|e| e.into_iter().map(|i| i.0).collect()),
        )
    }

    /// The internal constructor (electorate already reduced to hex), so a round can preserve its
    /// electorate restriction across close→re-open without re-wrapping.
    fn with_electorate(round: u64, options: Vec<Action>, electorate: Option<Vec<String>>) -> Self {
        CollectiveRound {
            round,
            options,
            ballots: HashMap::new(),
            electorate,
        }
    }

    /// The option position carrying [`Action::arg`] `arg` (the wire fires by arg — see
    /// [`cast_vote`]), or `None` if no option carries it.
    pub fn position_of_arg(&self, arg: i64) -> Option<usize> {
        self.options.iter().position(|a| a.arg == arg)
    }

    /// **Cast a write-once ballot by option position.** Refuses a non-member ([`Cast::NotEligible`]),
    /// an out-of-range option ([`Cast::BadOption`]), and a repeat vote ([`Cast::AlreadyVoted`]).
    pub fn cast(&mut self, voter: &DreggIdentity, option: usize) -> Cast {
        if let Some(elec) = &self.electorate {
            if !elec.iter().any(|e| e == &voter.0) {
                return Cast::NotEligible;
            }
        }
        if option >= self.options.len() {
            return Cast::BadOption;
        }
        if self.ballots.contains_key(&voter.0) {
            return Cast::AlreadyVoted;
        }
        self.ballots.insert(voter.0.clone(), option);
        Cast::Recorded
    }

    /// Cast a write-once ballot by the option's [`Action::arg`] (the custom-id wire's shape).
    pub fn cast_arg(&mut self, voter: &DreggIdentity, arg: i64) -> Cast {
        match self.position_of_arg(arg) {
            Some(pos) => self.cast(voter, pos),
            None => Cast::BadOption,
        }
    }

    /// The vote count per option position, in option order.
    pub fn counts(&self) -> Vec<usize> {
        let mut c = vec![0usize; self.options.len()];
        for &p in self.ballots.values() {
            if p < c.len() {
                c[p] += 1;
            }
        }
        c
    }

    /// The plurality winner's option position — most votes, ties to the lowest index. `None` only
    /// when the round has no options; a round with options but zero ballots resolves to option 0.
    pub fn winner_position(&self) -> Option<usize> {
        if self.options.is_empty() {
            return None;
        }
        let counts = self.counts();
        (0..self.options.len()).max_by_key(|&i| (counts[i], std::cmp::Reverse(i)))
    }

    /// The offering core's [`Tally`] for this round — the per-option [`VoteCount`] distribution
    /// (arg + votes) and the winning arg the crowd carried onto the substrate. `None` only when
    /// there are no options.
    pub fn tally(&self) -> Option<Tally> {
        let pos = self.winner_position()?;
        let counts = self.counts();
        let vote_counts = self
            .options
            .iter()
            .enumerate()
            .map(|(i, a)| VoteCount::new(a.arg, counts[i] as u32))
            .collect();
        Some(Tally::new(vote_counts, self.options[pos].arg))
    }

    /// The electorate of record — everyone who actually cast a ballot this round (sorted, so the
    /// recorded [`CollectiveDecision`] is deterministic). These are the voters the crowd turn is
    /// attributed to, NOT the eligible set.
    pub fn voter_ids(&self) -> Vec<DreggIdentity> {
        let mut v: Vec<String> = self.ballots.keys().cloned().collect();
        v.sort();
        v.into_iter().map(DreggIdentity).collect()
    }
}

/// The plurality-resolved facts of a closed collective round.
pub struct CollectiveResolved {
    /// The round number that closed.
    pub round: u64,
    /// The winning option (the [`Action`] carried onto the substrate).
    pub winner: Action,
    /// The crowd's [`Tally`] (the ballot distribution + the winning arg).
    pub tally: Tally,
    /// The electorate of record (everyone who voted).
    pub electorate: Vec<DreggIdentity>,
    /// The real substrate outcome of the resolved crowd turn — a landed [`Outcome::Landed`]
    /// (a genuine `TurnReceipt`) or the executor's own [`Outcome::Refused`] (anti-ghost).
    pub outcome: Outcome,
    /// Whether the landed crowd turn reached the durable session log. `false` means the round
    /// resolved for real but this session can no longer be resumed truthfully.
    pub durable: bool,
}

/// The result of [`close_round`].
#[allow(clippy::large_enum_variant)]
pub enum CollectiveClose {
    /// The plurality winner resolved as a real crowd turn (and the next round opened).
    Resolved(CollectiveResolved),
    /// The round has no options — nothing to resolve (a re-open, not a turn).
    Empty,
    /// No round is open (not a collective offering, or none opened yet).
    NoRound,
    /// No session of this offering is open in the channel.
    NoSession,
}

/// Open (or replace) a collective round for `channel`, restricted to `electorate` (or an open
/// crowd if `None`). The candidate options are the offering's current [`Offering::actions`]. Used
/// to attach a restricted electorate to a collective session (a council-shaped crowd); an open
/// crowd already gets a round at [`open_in`]. Returns `false` if no session is open.
#[allow(dead_code)]
pub fn open_round<O: DiscordOffering>(
    channel: u64,
    electorate: Option<Vec<DreggIdentity>>,
) -> bool {
    O::store()
        .run(move |sessions| match sessions.get_mut(&channel) {
            Some(live) => {
                let options = live.offering.actions(&live.session);
                live.control_head = live.control_head.saturating_add(1);
                live.round = Some(CollectiveRound::new(live.control_head, options, electorate));
                true
            }
            None => false,
        })
        .unwrap_or(false)
}

/// **Cast one write-once collective ballot**, keyed by `voter`'s derived dregg identity, for the
/// option carrying `arg` — the SAME path a live vote-button press takes. This is the collective
/// analogue of [`drive`]: it records a vote rather than resolving a turn (the plurality winner is
/// resolved later by [`close_round`]).
pub fn cast_vote<O: DiscordOffering>(channel: u64, voter: DreggIdentity, arg: i64) -> Cast {
    O::store()
        .run(move |sessions| match sessions.get_mut(&channel) {
            None => Cast::NoSession,
            Some(live) => match live.round.as_mut() {
                None => Cast::NoRound,
                Some(round) => round.cast_arg(&voter, arg),
            },
        })
        .unwrap_or(Cast::NoSession)
}

/// Cast a ballot only if the button belongs to this exact session generation
/// and collective round. The comparison and write-once mutation share one
/// store-thread job, so a close/reopen cannot race between them.
pub fn cast_vote_at<O: DiscordOffering>(
    channel: u64,
    stamp: ControlStamp,
    voter: DreggIdentity,
    arg: i64,
) -> Cast {
    O::store()
        .run(move |sessions| match sessions.get_mut(&channel) {
            None => Cast::NoSession,
            Some(live) if live.control_stamp() != stamp => Cast::StaleSurface,
            Some(live) => match live.round.as_mut() {
                None => Cast::NoRound,
                Some(round) => round.cast_arg(&voter, arg),
            },
        })
        .unwrap_or(Cast::NoSession)
}

/// **Close the collective round: resolve its plurality winner as ONE real crowd turn.** Tallies
/// the write-once ballots, drives the winning [`Action`] through [`Offering::advance_collective`]
/// carrying the full [`CollectiveDecision`] (the voters of record + the [`Tally`] + the carrier),
/// and opens the next round over the resulting state (preserving the electorate restriction). A
/// landed move records a real `TurnReceipt`; a refused one commits nothing (anti-ghost). This is
/// the collective analogue of a single-press resolution — many pressers, one refereed turn.
pub fn close_round<O: DiscordOffering>(channel: u64) -> CollectiveClose {
    let carrier = O::collective_carrier();
    ensure_live::<O>(channel);
    O::store()
        .run(move |sessions| {
            let Some(live) = sessions.get_mut(&channel) else {
                return CollectiveClose::NoSession;
            };
            let Some(round) = live.round.take() else {
                return CollectiveClose::NoRound;
            };
            let Some(pos) = round.winner_position() else {
                // An option-less round: nothing to resolve — put it back and report empty.
                live.round = Some(round);
                return CollectiveClose::Empty;
            };
            let winner = round.options[pos].clone();
            let tally = round.tally().expect("a winner implies a tally");
            let electorate = round.voter_ids();
            let restrict = round.electorate.clone();
            let round_no = round.round;

            // THE CROWD DECIDES, THE WORLD DISPOSES — one real cap-bounded turn carrying the whole
            // decision (the substrate still admits exactly one typed Action; the tally is provenance).
            let decision =
                CollectiveDecision::new(electorate.clone(), carrier.clone(), tally.clone());
            let outcome =
                live.offering
                    .advance_collective(&mut live.session, winner.clone(), decision);
            // A crowd turn is journaled like any other; a non-durable one is reported to the
            // caller so the surface can say the round landed but is no longer resumable. (The
            // session is not dropped mid-round here — the next direct mutation quarantines it.)
            let durable = live.record_landed(winner.clone(), carrier, &outcome);

            // Open the next round over the new state, keeping any electorate restriction.
            let next_options = live.offering.actions(&live.session);
            live.control_head = round_no.saturating_add(1);
            live.round = Some(CollectiveRound::with_electorate(
                live.control_head,
                next_options,
                restrict,
            ));

            CollectiveClose::Resolved(CollectiveResolved {
                round: round_no,
                winner,
                tally,
                electorate,
                outcome,
                durable,
            })
        })
        .unwrap_or(CollectiveClose::NoSession)
}

/// Read the channel's live collective round (`None` when no round is open). Runs on the store's
/// thread; only the result comes back. The driven tests + a future `/<offering>` collective
/// surface use it to render the live tally.
#[allow(dead_code)]
pub fn with_round<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&CollectiveRound) -> R + Send + 'static,
) -> Option<R> {
    O::store()
        .run(move |sessions| sessions.get(&channel).and_then(|l| l.round.as_ref()).map(f))
        .unwrap_or(None)
}

/// An honest one-line note for a cast ballot (the ephemeral ack a live vote gets).
fn cast_note(cast: Cast) -> String {
    match cast {
        Cast::Recorded => {
            "**Ballot recorded.** One write-once vote per dregg identity.".to_string()
        }
        Cast::AlreadyVoted => "You already voted this round. One ballot per identity.".to_string(),
        Cast::NotEligible => {
            "You are not in this round's electorate — your ballot is refused.".to_string()
        }
        Cast::BadOption => "That option is no longer on the ballot.".to_string(),
        Cast::NoRound => "No collective round is open here.".to_string(),
        Cast::NoSession => "No session is open in this channel.".to_string(),
        Cast::StaleSurface => {
            "That ballot belongs to a replaced session or closed round — nothing was recorded."
                .to_string()
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The custom-id wire.
// ─────────────────────────────────────────────────────────────────────────────

/// A decoded component press.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Press {
    /// Fire affordance `turn` with the fixed `arg` — one real offering turn.
    Fire {
        /// The offering key ([`DiscordOffering::KEY`]).
        key: String,
        /// Exact session incarnation and state/round head that minted the button.
        stamp: ControlStamp,
        /// The affordance verb.
        turn: String,
        /// The affordance argument.
        arg: i64,
    },
    /// The affordance needs a typed **numeric** value: open the value modal for `turn`. The value
    /// the user types IS the arg (a market reserve / a sealed bid), so no pre-arg is carried.
    Ask {
        /// The offering key.
        key: String,
        /// Exact session incarnation and state head that minted the button.
        stamp: ControlStamp,
        /// The affordance verb whose value the modal collects.
        turn: String,
    },
    /// The affordance needs a **free-text** value AND carries its own `arg`: open the text modal
    /// for `(turn, arg)`. Unlike [`Ask`](Press::Ask), a text affordance's `arg` is distinct from
    /// its text (a document insert's anchor position + its prose), so the wire carries both.
    AskText {
        /// The offering key.
        key: String,
        /// Exact session incarnation and state head that minted the button.
        stamp: ControlStamp,
        /// The affordance verb whose text the modal collects.
        turn: String,
        /// The affordance argument (the anchor/cell the text applies to).
        arg: i64,
    },
}

/// The exact-session/head custom-id of a fixed-arg affordance button.
pub fn fire_id_at(key: &str, stamp: ControlStamp, turn: &str, arg: i64) -> String {
    format!(
        "{PREFIX}:fire:{key}:{:x}:{:x}:{turn}:{arg}",
        stamp.generation, stamp.head
    )
}

/// Unbound fixed-arg id retained for parser/render fixtures. Production live
/// controls use [`fire_id_at`] or [`fire_id_in`].
pub fn fire_id(key: &str, turn: &str, arg: i64) -> String {
    fire_id_at(key, ControlStamp::PERSISTENT, turn, arg)
}

/// The custom-id of a numeric-value-taking affordance button (opens the value modal).
pub fn ask_id_at(key: &str, stamp: ControlStamp, turn: &str) -> String {
    format!(
        "{PREFIX}:ask:{key}:{:x}:{:x}:{turn}",
        stamp.generation, stamp.head
    )
}

pub fn ask_id(key: &str, turn: &str) -> String {
    ask_id_at(key, ControlStamp::PERSISTENT, turn)
}

/// The custom-id of a text-taking affordance button carrying its `arg` (opens the text modal).
pub fn askt_id_at(key: &str, stamp: ControlStamp, turn: &str, arg: i64) -> String {
    format!(
        "{PREFIX}:askt:{key}:{:x}:{:x}:{turn}:{arg}",
        stamp.generation, stamp.head
    )
}

pub fn askt_id(key: &str, turn: &str, arg: i64) -> String {
    askt_id_at(key, ControlStamp::PERSISTENT, turn, arg)
}

/// The custom-id of the modal that collects `turn`'s numeric value.
pub fn submit_id(key: &str, stamp: ControlStamp, turn: &str) -> String {
    format!(
        "{PREFIX}:submit:{key}:{:x}:{:x}:{turn}",
        stamp.generation, stamp.head
    )
}

/// The custom-id of the modal that collects `turn`'s free text, carrying its `arg` back.
pub fn subt_id(key: &str, stamp: ControlStamp, turn: &str, arg: i64) -> String {
    format!(
        "{PREFIX}:subt:{key}:{:x}:{:x}:{turn}:{arg}",
        stamp.generation, stamp.head
    )
}

fn stamp(generation: &str, head: &str) -> Option<ControlStamp> {
    Some(ControlStamp {
        generation: u64::from_str_radix(generation, 16).ok()?,
        head: u64::from_str_radix(head, 16).ok()?,
    })
}

/// Decode a component press. `None` for any id that is not ours.
pub fn parse_press(custom_id: &str) -> Option<Press> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "fire", key, generation, head, turn, arg] => Some(Press::Fire {
            key: (*key).to_string(),
            stamp: stamp(generation, head)?,
            turn: (*turn).to_string(),
            arg: arg.parse().ok()?,
        }),
        [PREFIX, "ask", key, generation, head, turn] => Some(Press::Ask {
            key: (*key).to_string(),
            stamp: stamp(generation, head)?,
            turn: (*turn).to_string(),
        }),
        [PREFIX, "askt", key, generation, head, turn, arg] => Some(Press::AskText {
            key: (*key).to_string(),
            stamp: stamp(generation, head)?,
            turn: (*turn).to_string(),
            arg: arg.parse().ok()?,
        }),
        _ => None,
    }
}

/// Decode a **numeric** modal submit id into `(key, turn)`. `None` for any id that is not ours.
pub fn parse_submit(custom_id: &str) -> Option<(String, ControlStamp, String)> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "submit", key, generation, head, turn] => Some((
            (*key).to_string(),
            stamp(generation, head)?,
            (*turn).to_string(),
        )),
        _ => None,
    }
}

/// Decode a **text** modal submit id into `(key, turn, arg)`. `None` for any id that is not ours.
pub fn parse_text_submit(custom_id: &str) -> Option<(String, ControlStamp, String, i64)> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "subt", key, generation, head, turn, arg] => Some((
            (*key).to_string(),
            stamp(generation, head)?,
            (*turn).to_string(),
            arg.parse().ok()?,
        )),
        _ => None,
    }
}

/// The offering key a press/submit id belongs to (what the router dispatches on).
pub fn key_of(custom_id: &str) -> Option<String> {
    match parse_press(custom_id) {
        Some(Press::Fire { key, .. })
        | Some(Press::Ask { key, .. })
        | Some(Press::AskText { key, .. }) => Some(key),
        None => parse_submit(custom_id)
            .map(|(k, _, _)| k)
            .or_else(|| parse_text_submit(custom_id).map(|(k, _, _, _)| k)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — the offering's own deos Surface → a Discord embed + affordance buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// The offering's [`Surface`](dreggnet_offerings::Surface) (its deos `ViewNode`) rendered to a
/// Discord embed through the
/// `deos_view::discord` backend — the SAME renderer the desktop/web/framebuffer backends are
/// peers of. We take the embed only: the components come from [`action_rows`] (see the module
/// doc — a Discord custom-id must carry the offering key and route a value-taking affordance to
/// its modal, which the generic `deosturn:` card id cannot).
fn embed_projection<O: DiscordOffering>(
    live: &Live<O>,
    projection: &AudienceProjection,
) -> CreateEmbed {
    let card = deos_view::discord::render_card(O::TITLE, projection.surface.view(), &[]);
    clamp_description(card.embed)
        .color(O::COLOR)
        .footer(CreateEmbedFooter::new(truncate(
            &format!(
                "{} · {}",
                live.offering.status_line(&live.session),
                O::TAGLINE
            ),
            2040,
        )))
}

/// Discord's hard cap on an embed description. Exceed it and the WHOLE message is refused with a
/// 400 — so a board that grew one line too long does not render "mostly"; it does not render AT
/// ALL, and the player is left holding the previous turn's board with its previous turn's buttons.
const DESCRIPTION_CAP: usize = 4000;

/// **Clamp a rendered card's description to what Discord will actually accept.**
///
/// `deos_view::discord::render_card` composes the description by appending a line per view node
/// and never bounds it — correct for that crate (its other backends have no such cap), and a live
/// hazard here. A Descent board sits comfortably under the cap today, but nothing HOLDS it there:
/// the pressure lines, one banked-relic note per relic, and a `Host` sub-view all grow it, and the
/// generic adapter renders offerings whose content is typed by users (a document, a market listing).
/// The failure mode is the worst kind — the turn commits, the edit 400s, and the surface freezes
/// silently — so the frontend truncates rather than hands Discord something it will reject.
fn clamp_description(embed: CreateEmbed) -> CreateEmbed {
    let Ok(value) = serde_json::to_value(&embed) else {
        return embed;
    };
    let Some(description) = value.get("description").and_then(|d| d.as_str()) else {
        return embed;
    };
    if description.chars().count() <= DESCRIPTION_CAP {
        return embed;
    }
    let clamped = truncate(description, DESCRIPTION_CAP);
    embed.description(clamped)
}

pub fn embed_of<O: DiscordOffering>(live: &Live<O>) -> CreateEmbed {
    let projection = project_for_audience(&live.offering, &live.session, &Audience::Shared);
    embed_projection(live, &projection)
}

/// The affordance buttons for the session's current [`Offering::actions`], chunked into Discord
/// rows (≤5 × ≤5).
///
/// * an **eligible** action → a primary button firing `(turn, arg)`;
/// * an action whose turn takes a **typed value** → a button that opens its modal;
/// * an **ineligible** action → `🔒`, danger-styled, and **still pressable**: the cap tooth is
///   shown, not hidden, and the press surfaces the executor's own [`Outcome::Refused`] rather
///   than the frontend pretending to be the gate.
pub fn action_rows_at<O: DiscordOffering>(
    actions: &[Action],
    stamp: ControlStamp,
) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for chunk in actions.chunks(5).take(5) {
        let mut buttons: Vec<CreateButton> = Vec::new();
        for a in chunk {
            let id = if O::text_prompt(&a.turn).is_some() {
                // A text affordance carries its own arg (a doc insert's anchor) beside the text.
                askt_id_at(O::KEY, stamp, &a.turn, a.arg)
            } else if O::value_prompt(&a.turn).is_some() {
                ask_id_at(O::KEY, stamp, &a.turn)
            } else {
                fire_id_at(O::KEY, stamp, &a.turn, a.arg)
            };
            let label = if a.enabled {
                truncate(&a.label, 78)
            } else {
                truncate(&format!("🔒 {}", a.label), 78)
            };
            let style = if a.enabled {
                ButtonStyle::Primary
            } else {
                ButtonStyle::Danger
            };
            buttons.push(CreateButton::new(id).label(label).style(style));
        }
        rows.push(CreateActionRow::Buttons(buttons));
    }
    // The standing verify-don't-trust affordance (backlog Tier-2 #10): every offering
    // surface carries the "⛓ re-verify chain" press (`commands::verify_chain`); a press
    // re-derives the session's receipt hash-chain live. Skipped only when the surface
    // already fills Discord's 5-row cap.
    if rows.len() < 5 {
        rows.push(crate::commands::verify_chain::row(O::KEY));
    }
    rows
}

/// Unbound rows retained for parser/render fixtures. Generic live surfaces and
/// persistent-world surfaces must use [`action_rows_at`] with their exact stamp.
pub fn action_rows<O: DiscordOffering>(actions: &[Action]) -> Vec<CreateActionRow> {
    action_rows_at::<O>(actions, ControlStamp::PERSISTENT)
}

/// The full surface of a channel's live session: embed + affordance rows.
pub fn surface_of<O: DiscordOffering>(live: &Live<O>) -> (CreateEmbed, Vec<CreateActionRow>) {
    let projection = project_for_audience(&live.offering, &live.session, &Audience::Shared);
    let embed = embed_projection(live, &projection);
    (
        embed,
        action_rows_at::<O>(&projection.actions, live.control_stamp()),
    )
}

/// The session's embed rendered **AS `viewer` sees it** — the viewer-aware
/// [`Offering::render_for`] projection (a multiway-tug seat's own hidden hand revealed, a document's
/// per-region cap surfaced), where [`embed_of`] paints the one viewer-blind surface everyone shared.
/// A full-information offering inherits `render_for`'s default (== `render`), so nothing changes for
/// it; only an offering with genuinely per-viewer state paints differently here.
pub fn embed_for<O: DiscordOffering>(live: &Live<O>, viewer: &DreggIdentity) -> CreateEmbed {
    let audience = Audience::private(viewer.clone());
    let projection = project_for_audience(&live.offering, &live.session, &audience);
    embed_projection(live, &projection)
}

/// The full surface of a channel's live session **AS `viewer` sees it** — the viewer-aware embed
/// ([`embed_for`]) + the viewer-aware affordances ([`Offering::actions_for`], so an actor is never
/// offered a cap they lack). This is the render the live press path takes (it holds the presser's
/// derived dregg identity), so the tug hidden hand + the doc cap-dimming reach the Discord surface.
pub fn surface_for<O: DiscordOffering>(
    live: &Live<O>,
    viewer: &DreggIdentity,
) -> (CreateEmbed, Vec<CreateActionRow>) {
    let audience = Audience::private(viewer.clone());
    let projection = project_for_audience(&live.offering, &live.session, &audience);
    let embed = embed_projection(live, &projection);
    (
        embed,
        action_rows_at::<O>(&projection.actions, live.control_stamp()),
    )
}

/// The field name on a private view's **where-to-act plaque** ([`private_act_plaque`]). A stable
/// marker so a test can pin "the private view explains itself" without matching on prose.
pub const PRIVATE_ACT_FIELD: &str = "🔒 Yours alone — act on the board above";

/// The pair a Discord **channel** is allowed to receive for one viewer.
///
/// The first surface is always safe to publish into the shared channel. For a
/// hidden-information offering it is the viewer-blind fog and the second value
/// is the viewer projection that must be sent ephemerally. The companion has
/// no controls: all actions stay on the shared board, so pressing a private
/// ephemeral can never leave the public board stale. For a public offering the
/// existing viewer-aware surface remains the shared one and there is no
/// companion. Keeping this decision pure lets hostile tests inspect the exact
/// objects the async handlers publish without a live Discord token.
pub fn channel_surfaces<O: DiscordOffering>(
    live: &Live<O>,
    viewer: &DreggIdentity,
) -> (
    (CreateEmbed, Vec<CreateActionRow>),
    Option<(CreateEmbed, Vec<CreateActionRow>)>,
) {
    if live.offering.hidden_information() {
        let (private_embed, _private_rows) = surface_for::<O>(live, viewer);
        (surface_of::<O>(live), Some((private_embed, Vec::new())))
    } else {
        (surface_for::<O>(live, viewer), None)
    }
}

/// The modal that collects a value-taking affordance's typed arg.
pub fn value_modal<O: DiscordOffering>(
    stamp: ControlStamp,
    turn: &str,
    prompt: ValuePrompt,
) -> CreateModal {
    CreateModal::new(submit_id(O::KEY, stamp, turn), prompt.title).components(vec![
        CreateActionRow::InputText(
            CreateInputText::new(InputTextStyle::Short, prompt.label, VALUE_FIELD)
                .placeholder(prompt.placeholder)
                .required(true)
                .max_length(20),
        ),
    ])
}

/// The modal that collects a text-taking affordance's free-text [`Action::label`] (a Hermes
/// prompt, a document paragraph), carrying its `arg` (the anchor) back on the submit id. A
/// paragraph prompt uses a multi-line input.
pub fn text_modal<O: DiscordOffering>(
    stamp: ControlStamp,
    turn: &str,
    arg: i64,
    prompt: TextPrompt,
) -> CreateModal {
    let style = if prompt.paragraph {
        InputTextStyle::Paragraph
    } else {
        InputTextStyle::Short
    };
    CreateModal::new(subt_id(O::KEY, stamp, turn, arg), prompt.title).components(vec![
        CreateActionRow::InputText(
            CreateInputText::new(style, prompt.label, VALUE_FIELD)
                .placeholder(prompt.placeholder)
                .required(true)
                .max_length(300),
        ),
    ])
}

/// An honest account of a resolved move: a landed receipt (with its complete `receipt_hash`) or
/// the executor's own refusal reason — never laundered.
pub fn outcome_note(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Landed { receipt, ended } => {
            let card = PlayerTurnReceipt::from_landed(receipt, *ended);
            // "Landed" is the executor's fact and is always true here — `Outcome::Landed`
            // means the turn was ADMITTED. "Verified" is a claim about the ACTOR, and this
            // header used to assert it unconditionally while the card printed one line below
            // it says otherwise: `compact_text` calls `lead_phrase()`, whose `Asserted` grade
            // renders "Recorded (asserted …)" under a doc-comment reading, in as many words,
            // `"Verified" would be a lie here`. So the surface contradicted its own body, and
            // the honest half was the one nobody read.
            //
            // The grade ladder — Asserted / Signed / Signed (custodial) / Verified turn — is
            // exactly the distinction this project sells. Overriding it with the top rung on
            // every turn does not merely overstate one message; it makes the ladder unreadable,
            // because if everything says "verified" then nothing does.
            format!(
                "**The turn landed.**\n> {}\n> This complete id is the copyable join into \
                 the session's hash-linked receipt chain; every later turn commits to the \
                 record before it.",
                card.compact_text(PlayerReplaySurface::Discord)
            )
        }
        Outcome::Refused(why) => format!(
            "**Refused — nothing committed, no receipt.**\n> The executor refused the move: {why}"
        ),
    }
}

/// A verify report as an honest line.
pub fn verify_note(report: &VerifyReport) -> String {
    if report.verified {
        format!(
            "✓ **{} verified turns re-verify.** {}",
            report.turns, report.detail
        )
    } else {
        format!(
            "✗ **The chain does NOT re-verify** over {} turns:\n> {}",
            report.turns, report.detail
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The SYNC core of a press — what the tests drive and the async handlers wrap.
// ─────────────────────────────────────────────────────────────────────────────

/// The result of driving a component press through the offering.
///
/// (`Fired` is the big variant — it carries a real `TurnReceipt`. That is the payload, and a
/// `Driven` is built exactly once per press, so the size difference buys nothing to box away.)
#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Driven {
    /// The press resolved on the substrate — a real landed receipt or a real refusal.
    Fired(Outcome),
    /// The affordance takes a typed value: the frontend must open this modal.
    NeedsValue {
        /// Exact surface incarnation carried into the modal submit id.
        stamp: ControlStamp,
        /// The affordance verb whose value the modal collects.
        turn: String,
        /// The prompt to render.
        prompt: ValuePrompt,
    },
    /// The affordance takes free text: the frontend must open this text modal (carrying `arg`).
    NeedsText {
        /// Exact surface incarnation carried into the modal submit id.
        stamp: ControlStamp,
        /// The affordance verb whose text the modal collects.
        turn: String,
        /// The affordance argument (the anchor/cell the text applies to).
        arg: i64,
        /// The text prompt to render.
        prompt: TextPrompt,
    },
    /// No session of this offering is open in the channel.
    NoSession,
    /// The control belongs to a replaced session or an earlier state/round.
    StaleSurface,
    /// The custom-id is not this offering's.
    NotOurs,
    /// The turn LANDED but its durable log line did not, so the session was quarantined. The
    /// receipt is real; the resumability is not, and the surface says both.
    LandedNotDurable(Outcome),
}

/// **Drive one component press.** Decodes the custom-id and, for a fixed-arg affordance, runs
/// ONE real [`Offering::advance`] attributed to `actor`. This is the whole logic of a live
/// button press; [`handle_component`] only adds the serenity round-trip.
pub fn drive<O: DiscordOffering>(channel: u64, custom_id: &str, actor: DreggIdentity) -> Driven {
    let press = match parse_press(custom_id) {
        Some(p) => p,
        None => return Driven::NotOurs,
    };
    // THE COLD PRESS. A button that outlived the process finds its channel empty; bring the
    // persisted session back by replay before deciding this press has nowhere to land. The
    // restored session carries the SAME generation the button was minted against, so the stamp
    // check below passes and the press fires — which is the whole point: a restart must not turn
    // a live board into a wall of dead buttons.
    ensure_live::<O>(channel);
    match press {
        Press::Ask { key, stamp, turn } if key == O::KEY => match O::value_prompt(&turn) {
            Some(prompt) if stamp_is_current::<O>(channel, stamp) => Driven::NeedsValue {
                stamp,
                turn,
                prompt,
            },
            Some(_) => Driven::StaleSurface,
            // A value-less turn addressed as `ask` — fire it with arg 0 rather than dead-ending.
            None => drive_value_at::<O>(channel, stamp, &turn, 0, actor),
        },
        Press::AskText {
            key,
            stamp,
            turn,
            arg,
        } if key == O::KEY => match O::text_prompt(&turn) {
            Some(prompt) if stamp_is_current::<O>(channel, stamp) => Driven::NeedsText {
                stamp,
                turn,
                arg,
                prompt,
            },
            Some(_) => Driven::StaleSurface,
            // A text-less turn addressed as `askt` — fire it with its arg rather than dead-ending.
            None => drive_value_at::<O>(channel, stamp, &turn, arg, actor),
        },
        Press::Fire {
            key,
            stamp,
            turn,
            arg,
        } if key == O::KEY => drive_value_at::<O>(channel, stamp, &turn, arg, actor),
        _ => Driven::NotOurs,
    }
}

fn stamp_is_current<O: DiscordOffering>(channel: u64, stamp: ControlStamp) -> bool {
    O::store()
        .run(move |sessions| {
            sessions
                .get(&channel)
                .is_some_and(|live| live.control_stamp() == stamp)
        })
        .unwrap_or(false)
}

enum MutationAttempt {
    Fired(Outcome),
    NoSession,
    StaleSurface,
    /// The turn LANDED on the substrate but its line did not reach the durable log. The session
    /// was quarantined (dropped from the live table) rather than left to resume as a
    /// silently-omitted or bricking replay — the fail-closed half of the
    /// [`SessionResumeStore::record_landed`] contract.
    LandedNotDurable(Outcome),
}

/// Run one mutation against the channel's live session and quarantine it if a landed turn did
/// not reach the durable log. The mutation, the durability verdict and the removal all happen in
/// ONE store-thread job, so no caller can observe (or press against) a session whose log has
/// already diverged from its state.
fn mutate_live<O: DiscordOffering>(
    channel: u64,
    stamp: Option<ControlStamp>,
    f: impl FnOnce(&mut Live<O>) -> (Outcome, bool) + Send + 'static,
) -> MutationAttempt {
    // THE COLD PRESS, for every mutation entry point — including a modal submit, which reaches
    // `drive_text_at` / `drive_value_at` without passing through `drive`. A form a player opened
    // before the restart must still commit.
    ensure_live::<O>(channel);
    O::store()
        .run(move |sessions| {
            let (attempt, quarantine) = {
                let Some(live) = sessions.get_mut(&channel) else {
                    return MutationAttempt::NoSession;
                };
                if stamp.is_some_and(|s| live.control_stamp() != s) {
                    return MutationAttempt::StaleSurface;
                }
                let (outcome, durable) = f(live);
                if durable {
                    (MutationAttempt::Fired(outcome), false)
                } else {
                    (MutationAttempt::LandedNotDurable(outcome), true)
                }
            };
            if quarantine {
                // FORGET the log too. A log that is missing a turn its session DID land is the
                // one thing more dangerous than no log at all: resuming from it would rebuild a
                // plausible board that diverged from the committed history — a session that
                // renders and lies. Better no record than a wrong one.
                forget_channel_log::<O>(sessions.get(&channel), channel);
                sessions.remove(&channel);
            }
            attempt
        })
        .unwrap_or(MutationAttempt::NoSession)
}

/// The honest note a quarantined session gets. The turn is REAL — it landed on the executor —
/// but this process can no longer offer to resume it, and saying so beats a surface that quietly
/// diverges from its own log.
fn not_durable_note<O: DiscordOffering>(outcome: &Outcome) -> String {
    format!(
        "{}\n\n⚠ **This turn did not reach durable storage, so the session was closed.** The \
         move landed on the executor and its receipt above is real; what failed is the write \
         that would let it be resumed after a restart. Rather than keep a session whose record \
         no longer matches its state, it is dropped here. Open a fresh one with `{}`.",
        outcome_note(outcome),
        O::open_hint(),
    )
}

fn note_direct_landing<O: DiscordOffering>(live: &mut Live<O>, outcome: &Outcome) {
    if !O::collective() && matches!(outcome, Outcome::Landed { .. }) {
        live.control_head = live.control_head.saturating_add(1);
    }
}

fn drive_value_at<O: DiscordOffering>(
    channel: u64,
    stamp: ControlStamp,
    turn: &str,
    arg: i64,
    actor: DreggIdentity,
) -> Driven {
    let turn = turn.to_string();
    driven_of(mutate_live::<O>(channel, Some(stamp), move |live| {
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        let durable = live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        (outcome, durable)
    }))
}

fn driven_of(attempt: MutationAttempt) -> Driven {
    match attempt {
        MutationAttempt::Fired(outcome) => Driven::Fired(outcome),
        MutationAttempt::NoSession => Driven::NoSession,
        MutationAttempt::StaleSurface => Driven::StaleSurface,
        MutationAttempt::LandedNotDurable(outcome) => Driven::LandedNotDurable(outcome),
    }
}

/// **Drive an affordance with an explicit arg** — the modal-submit path (and the fixed-arg
/// path's own body). ONE real offering turn, attributed to the presser's dregg identity.
pub fn drive_value<O: DiscordOffering>(
    channel: u64,
    turn: &str,
    arg: i64,
    actor: DreggIdentity,
) -> Driven {
    // The action is resolved on the store's own thread (where the session lives), so it owns
    // its strings.
    let turn = turn.to_string();
    driven_of(mutate_live::<O>(channel, None, move |live| {
        // The label is decoration; the executor resolves the TYPED (turn, arg) — and `enabled`
        // is a decoration too (we pass `true`), because the substrate is the sole referee: a
        // move it does not admit comes back as a real `Refused`, not a frontend veto.
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        let durable = live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        (outcome, durable)
    }))
}

fn drive_text_at<O: DiscordOffering>(
    channel: u64,
    stamp: ControlStamp,
    turn: &str,
    arg: i64,
    text: &str,
    actor: DreggIdentity,
) -> Driven {
    let turn = turn.to_string();
    let text = text.to_string();
    driven_of(mutate_live::<O>(channel, Some(stamp), move |live| {
        let action = Action::new(turn.clone(), turn, arg, true).with_text(text);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        let durable = live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        (outcome, durable)
    }))
}

/// **Drive a text-taking affordance** — the free-text modal-submit path. The typed string rides
/// the first-class [`Action::text`] payload; ONE real offering turn, attributed to the presser's
/// dregg identity. (A Hermes prompt, a document edit's text.)
pub fn drive_text<O: DiscordOffering>(
    channel: u64,
    turn: &str,
    arg: i64,
    text: &str,
    actor: DreggIdentity,
) -> Driven {
    let turn = turn.to_string();
    let text = text.to_string();
    driven_of(mutate_live::<O>(channel, None, move |live| {
        // The typed text rides `Action::text` and ONLY that. The label is the affordance VERB —
        // the same display-only string every other frontend path sends. We deliberately do NOT
        // duplicate the user's text into the label: a label is decoration, and an offering that
        // reads it as CONTENT is a bug (it let a bare press register the literal name "register").
        // Keeping content out of the label means such a regression fails LOUDLY here instead of
        // being silently propped up by this path. `arg` is the affordance's own (a doc insert's
        // anchor); `enabled` is decoration — the substrate is the sole referee of what lands.
        let action = Action::new(turn.clone(), turn, arg, true).with_text(text);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        let durable = live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        (outcome, durable)
    }))
}

/// Re-verify the channel's committed chain through [`Offering::verify`] — resuming the
/// channel's persisted session first if this process has not seen it yet.
pub fn verify_live<O: DiscordOffering>(channel: u64) -> Option<VerifyReport> {
    ensure_live::<O>(channel);
    with_live::<O, _>(channel, |live| live.offering.verify(&live.session))
}

// ─────────────────────────────────────────────────────────────────────────────
// The async Discord handlers — thin wrappers over the sync core.
// ─────────────────────────────────────────────────────────────────────────────

/// Post the channel's live surface (embed + affordance buttons) as the command response, projected
/// **AS the requesting user sees it** — their derived dregg identity is threaded to [`surface_for`],
/// so a seated tug player's `/tug status` shows their own hidden hand (and a document's per-region
/// cap dimming reaches the read path), not the viewer-blind public projection.
pub async fn handle_status<O: DiscordOffering>(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
) {
    let channel = command.channel_id.get();
    let viewer = identity_of(state, command.user.id.get());
    // Bring the channel's persisted session back if this process has not touched it yet, so
    // `/… status` after a restart shows the board it left rather than "nothing open here".
    ensure_live::<O>(channel);
    let rendered = with_live::<O, _>(channel, move |live| {
        (
            surface_for::<O>(live, &viewer),
            live.offering.hidden_information(),
        )
    });
    match rendered {
        Some(((embed, rows), hidden_information)) => {
            let rows = if hidden_information { Vec::new() } else { rows };
            let msg = CreateInteractionResponseMessage::new()
                .embed(embed)
                .components(rows)
                // A viewer projection which may contain a hand / sealed move
                // is never posted into the channel. Public offerings keep the
                // familiar channel-visible status response.
                .ephemeral(hidden_information);
            let _ = command
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        None => ephemeral(ctx, command, &no_session_text::<O>()).await,
    }
}

/// Re-verify the channel's chain and post the honest report.
pub async fn handle_verify<O: DiscordOffering>(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    // ACK inside Discord's 3s window BEFORE the (possibly slow) chain re-derivation — the report
    // lands as an EDIT of this deferred response. The verifier runs on the offering's store
    // thread; move the blocking wait OFF the async worker so a long chain never parks it.
    ack::defer_slash(ctx, command, false).await;
    let report = tokio::task::spawn_blocking(move || verify_live::<O>(channel))
        .await
        .ok()
        .flatten();
    match report {
        Some(report) => {
            // AUDIT the verify: the report verdict is the outcome (read-only, but a
            // failed re-verification is exactly the finding the envelope exists for).
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::Actor {
                        platform_id: command.user.id.get().to_string(),
                        dregg_identity: None,
                        grade: "custodial".to_string(),
                    },
                    crate::audit::Surface::Command,
                    crate::audit::Input {
                        kind: format!("offering:verify:{}", O::KEY),
                        detail: serde_json::Value::Null,
                    },
                )
                .with_session(channel.to_string())
                .with_offering(O::KEY)
                .with_outcome(crate::audit::AuditOutcome::Verified {
                    verified: report.verified,
                    turns: u64::try_from(report.turns).unwrap_or(u64::MAX),
                }),
            );
            let embed = CreateEmbed::new()
                .title(format!("{} — verify", O::TITLE))
                .description(verify_note(&report))
                .color(if report.verified { O::COLOR } else { 0xE63946 });
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
        }
        None => {
            let embed = CreateEmbed::new()
                .title(format!("{} — verify", O::TITLE))
                .description(no_session_text::<O>())
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
        }
    }
}

/// Route a component press: fire it as a real turn (and re-render the surface with the outcome),
/// or open the modal a value-taking affordance needs.
pub async fn handle_component<O: DiscordOffering>(
    ctx: &Context,
    component: &ComponentInteraction,
    state: &BotState,
) {
    let channel = component.channel_id.get();
    let actor = identity_of(state, component.user.id.get());

    // COLLECTIVE MODE: a press is a write-once VOTE, not an immediate turn. ACK inside the 3s
    // window BEFORE the ballot records, then follow up ephemerally; the plurality winner is
    // resolved later by a round close ([`handle_close`]). Direct offerings fall through to the
    // 1-press-1-turn path.
    if O::collective() {
        match parse_press(&component.data.custom_id) {
            Some(Press::Fire { stamp, arg, .. }) => {
                // ACK, then cast — and the cast goes to the blocking pool, because it is a
                // write-once ballot resolved on the offering's store thread.
                let ballot_actor = actor.clone();
                let cast = ack::ack_component_then(ctx, component, move || {
                    cast_vote_at::<O>(channel, stamp, ballot_actor, arg)
                })
                .await
                // A dropped job is NOT a recorded ballot. `NoSession` is the honest floor here:
                // it tells the presser nothing was cast, which is the only safe reading.
                .unwrap_or(Cast::NoSession);
                // AUDIT: a collective ballot is a decision too — record the cast verdict
                // (the resolved crowd turn is enveloped by `handle_close`).
                crate::audit::log().emit(
                    crate::audit::AuditEvent::new(
                        "discord",
                        crate::audit::actor_of(component.user.id.get(), &actor),
                        crate::audit::Surface::Component,
                        crate::audit::Input {
                            kind: format!("offering:vote:{}", O::KEY),
                            detail: serde_json::json!({
                                "custom_id": component.data.custom_id,
                                "arg": arg,
                                "cast": format!("{cast:?}"),
                            }),
                        },
                    )
                    .decided(
                        if matches!(cast, Cast::Recorded) {
                            "routed"
                        } else {
                            "refused"
                        },
                        match cast {
                            Cast::Recorded => "",
                            Cast::AlreadyVoted => "already_voted",
                            Cast::NotEligible => "not_eligible",
                            Cast::BadOption => "bad_option",
                            Cast::NoRound => "no_round",
                            Cast::NoSession => "no_session",
                            Cast::StaleSurface => "stale_surface",
                        },
                    )
                    .with_session(channel.to_string())
                    .with_offering(O::KEY),
                );
                ack::followup_ephemeral(ctx, component, &cast_note(cast)).await;
            }
            // Never a silent drop: a non-ballot press on a collective surface says so.
            _ => {
                component_ephemeral(
                    ctx,
                    component,
                    "This surface runs in collective mode — that press is not one of the \
                     round's ballot options.",
                )
                .await;
            }
        }
        return;
    }

    // DEFER-SAFETY on the direct path: a committing press is ACKed INSIDE the 3s window,
    // BEFORE the store-thread turn resolves (a slow offering can no longer blow the window
    // on a move that permanently landed). A modal must be the FIRST response, so the shapes
    // that open one are decided here — mirroring `drive`'s own dispatch — and left un-ACKed.
    let will_commit = match parse_press(&component.data.custom_id) {
        Some(Press::Fire { key, .. }) => key == O::KEY,
        Some(Press::Ask { key, turn, .. }) => key == O::KEY && O::value_prompt(&turn).is_none(),
        Some(Press::AskText { key, turn, .. }) => key == O::KEY && O::text_prompt(&turn).is_none(),
        _ => false,
    };
    if will_commit {
        ack::ack_component(ctx, component).await;
    }

    // THE HOT PATH LEAVES THE ASYNC WORKER. `drive` is a real executor turn behind a blocking
    // `sync_channel` `recv()` on the offering's store thread — the one thread every player in
    // every channel of this offering queues on. Awaiting it inline parked a Tokio worker for the
    // whole turn, so under load the store's latency landed on EVERY in-flight interaction's
    // 3-second clock at once (`verify_chain.rs` and `handle_verify` already knew this; the
    // 1-press-1-turn path, which is the one under load, did not).
    let id = component.data.custom_id.clone();
    let driving = {
        let actor = actor.clone();
        tokio::task::spawn_blocking(move || drive::<O>(channel, &id, actor)).await
    };
    let Ok(driven) = driving else {
        // The blocking pool dropped the job. This is NOT a refusal and NOT a receipt.
        let text = "The offering service did not run your press, so nothing here says whether \
             it landed. Re-open the board before playing on.";
        if will_commit {
            ack::followup_ephemeral(ctx, component, text).await;
        } else {
            component_ephemeral(ctx, component, text).await;
        }
        return;
    };
    match driven {
        Driven::NeedsValue {
            stamp,
            turn,
            prompt,
        } => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Modal(value_modal::<O>(stamp, &turn, prompt)),
                )
                .await;
        }
        Driven::NeedsText {
            stamp,
            turn,
            arg,
            prompt,
        } => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Modal(text_modal::<O>(stamp, &turn, arg, prompt)),
                )
                .await;
        }
        Driven::Fired(outcome) => {
            // AUDIT the resolved press: the landed `turn_hash` (the receipt-chain
            // join) or the executor's own refusal reason — never laundered.
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(component.user.id.get(), &actor),
                    crate::audit::Surface::Component,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({ "custom_id": component.data.custom_id }),
                    },
                )
                .with_session(channel.to_string())
                .with_offering(O::KEY)
                .with_outcome(crate::audit::outcome_of(&outcome)),
            );
            update_surface::<O>(
                ctx,
                component,
                channel,
                &actor,
                &outcome_note(&outcome),
                will_commit,
            )
            .await;
            // 👑 THE CROWN: the moment a crowned game's match ENDS on a landed turn, offer to
            // fold the whole match into ONE proof (`commands::crown` — the proof-carrying board).
            if matches!(&outcome, Outcome::Landed { ended: true, .. })
                && crate::commands::crown::foldable_key(O::KEY)
            {
                crate::commands::crown::offer_fold(ctx, component.channel_id, O::KEY).await;
            }
        }
        Driven::LandedNotDurable(outcome) => {
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(component.user.id.get(), &actor),
                    crate::audit::Surface::Component,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({
                            "custom_id": component.data.custom_id,
                            "durable": false,
                        }),
                    },
                )
                .with_session(channel.to_string())
                .with_offering(O::KEY)
                .with_outcome(crate::audit::outcome_of(&outcome)),
            );
            let note = not_durable_note::<O>(&outcome);
            if will_commit {
                ack::followup_ephemeral(ctx, component, &note).await;
            } else {
                component_ephemeral(ctx, component, &note).await;
            }
        }
        Driven::NoSession => {
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(component.user.id.get(), &actor),
                    crate::audit::Surface::Component,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({ "custom_id": component.data.custom_id }),
                    },
                )
                .decided("refused", "no_session")
                .with_session(channel.to_string())
                .with_offering(O::KEY),
            );
            if will_commit {
                ack::followup_ephemeral(ctx, component, &no_session_text::<O>()).await;
            } else {
                component_ephemeral(ctx, component, &no_session_text::<O>()).await;
            }
        }
        Driven::NotOurs => {
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(component.user.id.get(), &actor),
                    crate::audit::Surface::Component,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({ "custom_id": component.data.custom_id }),
                    },
                )
                .decided("refused", "stale_surface")
                .with_session(channel.to_string())
                .with_offering(O::KEY),
            );
            component_ephemeral(
                ctx,
                component,
                "That button belongs to a stale or different surface — nothing was fired.",
            )
            .await;
        }
        Driven::StaleSurface => {
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(component.user.id.get(), &actor),
                    crate::audit::Surface::Component,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({ "custom_id": component.data.custom_id }),
                    },
                )
                .decided("refused", "stale_surface")
                .with_session(channel.to_string())
                .with_offering(O::KEY),
            );
            if will_commit {
                ack::followup_ephemeral(
                    ctx,
                    component,
                    "That control belongs to a replaced session or earlier state — nothing was fired.",
                )
                .await;
            } else {
                component_ephemeral(
                    ctx,
                    component,
                    "That control belongs to a replaced session or earlier state — nothing was fired.",
                )
                .await;
            }
        }
    }
}

/// Route a modal submit: parse the typed value/text and fire the affordance as a real turn. A
/// **text** submit (`subt:<key>:<turn>:<arg>`) carries its string on the label + its `arg` on the
/// id ([`drive_text`]); a **numeric** submit (`submit:<key>:<turn>`) parses the value the user
/// typed AS the arg ([`drive_value`], reporting a non-number honestly).
pub async fn handle_modal<O: DiscordOffering>(
    ctx: &Context,
    modal: &ModalInteraction,
    state: &BotState,
) {
    let channel = modal.channel_id.get();
    let actor = identity_of(state, modal.user.id.get());
    let raw = modal_value(modal, VALUE_FIELD);

    // A TEXT submit: (key, turn, arg) on the id, the free text on the label.
    if let Some((key, stamp, turn, arg)) = parse_text_submit(&modal.data.custom_id) {
        if key != O::KEY {
            return modal_unrouted(ctx, modal).await;
        }
        // ACK FIRST. A MODAL SUBMIT IS AN INTERACTION, ON THE SAME 3-SECOND CLOCK — and this one
        // was answering LAST. `drive_text_at` is a real executor turn on the offering's store
        // thread (a sealed bid, a reserve price, a document paragraph), and it ran, then
        // `channel_surfaces` blocked on the same thread AGAIN to re-render, and only then did
        // `finish_modal` send the first response. A typed move that outran the window therefore
        // COMMITTED, and the player was shown "This interaction failed" over a board still
        // painted with the pre-move state.
        let text = raw.trim().to_string();
        let (actor_job, turn_job) = (actor.clone(), turn.clone());
        let driven = ack::defer_modal_then(ctx, modal, move || {
            drive_text_at::<O>(channel, stamp, &turn_job, arg, &text, actor_job)
        })
        .await;
        finish_modal::<O>(ctx, modal, channel, &actor, driven).await;
        return;
    }

    // A NUMERIC submit: the typed value IS the arg.
    let Some((key, stamp, turn)) = parse_submit(&modal.data.custom_id) else {
        // NEVER a silent drop: a submit id this build cannot decode says so.
        return modal_unrouted(ctx, modal).await;
    };
    if key != O::KEY {
        return modal_unrouted(ctx, modal).await;
    }
    // A non-number is decided BEFORE anything is ACKed and before any work — nothing fired, so
    // the honest answer is a plain ephemeral on an unanswered interaction.
    let Ok(value) = raw.trim().parse::<i64>() else {
        let _ = modal
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content(format!("`{raw}` is not a whole number."))
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    };
    let (actor_job, turn_job) = (actor.clone(), turn.clone());
    let driven = ack::defer_modal_then(ctx, modal, move || {
        drive_value_at::<O>(channel, stamp, &turn_job, value, actor_job)
    })
    .await;
    finish_modal::<O>(ctx, modal, channel, &actor, driven).await;
}

/// A submit this build cannot route — answered, never dropped.
async fn modal_unrouted(ctx: &Context, modal: &ModalInteraction) {
    let _ = modal
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(
                        "That form is from a surface this bot build no longer decodes — nothing \
                         was fired.",
                    )
                    .ephemeral(true),
            ),
        )
        .await;
}

/// The shared tail of a modal submit: post the move's honest outcome + the re-rendered surface (a
/// landed receipt / a real refusal), or the no-session note.
///
/// Every answer here is an EDIT of the [`ack::defer_modal`] the caller already sent (rule 1: the
/// typed move mutates the board it was typed on). `driven: None` is the blocking pool dropping
/// the job — reported as the unknown it is, never as a refusal.
async fn finish_modal<O: DiscordOffering>(
    ctx: &Context,
    modal: &ModalInteraction,
    channel: u64,
    viewer: &DreggIdentity,
    driven: Option<Driven>,
) {
    let Some(driven) = driven else {
        ack::note_modal(
            ctx,
            modal,
            "The offering service did not run your move, so this is NOT a refusal and NOT a \
             receipt — nothing here says whether it landed. Re-open the board (its controls carry \
             the state that minted them) before playing on.",
        )
        .await;
        return;
    };
    match driven {
        Driven::Fired(outcome) => {
            // AUDIT the modal-driven advance (the typed value already rode the modal
            // funnel line, secret-redacted): the landed `turn_hash` or the refusal.
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(modal.user.id.get(), viewer),
                    crate::audit::Surface::Modal,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({ "custom_id": modal.data.custom_id }),
                    },
                )
                .with_session(channel.to_string())
                .with_offering(O::KEY)
                .with_outcome(crate::audit::outcome_of(&outcome)),
            );
            let note = outcome_note(&outcome);
            let viewer_id = viewer.clone();
            let rendered = tokio::task::spawn_blocking(move || {
                with_live::<O, _>(channel, move |live| channel_surfaces::<O>(live, &viewer_id))
            })
            .await
            .ok()
            .flatten();
            match rendered {
                // ── THE BOARD IS ONE MESSAGE. A typed move (a reserve price, a sealed bid, a
                //    document paragraph) is an ORDINARY TURN, and an ordinary turn MUTATES the
                //    board it was played on — it does not append a second board beneath it.
                //
                //    A modal opened from a component press carries that component's message
                //    (`modal.message`), so `UpdateMessage` is legal here and edits the very board
                //    the player pressed. Before this, every modal turn answered with a NEW
                //    message: the channel filled with one full board per bid, and the board
                //    ABOVE kept its buttons — buttons the head-stamp would then refuse, so the
                //    surface a player was looking at was dead and said nothing about it.
                Some(((embed, rows), private_surface)) if modal.message.is_some() => {
                    ack::edit_modal(ctx, modal, &truncate(&note, 1900), Some(embed), rows).await;
                    // A hidden-information game's shared board carries only the fog; the presser's
                    // own projection rides a single-reader followup, exactly as the button path
                    // does. It must never be what the board edit puts on the channel surface.
                    if let Some((private_embed, _private_rows)) = private_surface {
                        let _ = modal
                            .create_followup(
                                &ctx.http,
                                serenity::all::CreateInteractionResponseFollowup::new()
                                    .content(
                                        "**Your private view** — only you can read this hand / \
                                         sealed move. Use the shared board's controls to act.",
                                    )
                                    .embed(private_embed)
                                    .ephemeral(true),
                            )
                            .await;
                    }
                }
                // No board to mutate (a modal reached us without its origin message, or the
                // session closed underneath): answer honestly rather than dropping the submit.
                other => match other {
                    Some(((embed, rows), _)) => {
                        ack::edit_modal(ctx, modal, &truncate(&note, 1900), Some(embed), rows)
                            .await;
                    }
                    // No surface to paint (the session closed underneath). Never wipe the board
                    // a player may still be looking at — the outcome goes to them privately.
                    None => ack::note_modal(ctx, modal, &note).await,
                },
            }
            // 👑 THE CROWN (modal path): a crowned game's match ending on a modal-landed
            // turn gets the same fold offer as the component path above.
            if matches!(&outcome, Outcome::Landed { ended: true, .. })
                && crate::commands::crown::foldable_key(O::KEY)
            {
                crate::commands::crown::offer_fold(ctx, modal.channel_id, O::KEY).await;
            }
        }
        Driven::LandedNotDurable(outcome) => {
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(modal.user.id.get(), viewer),
                    crate::audit::Surface::Modal,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({
                            "custom_id": modal.data.custom_id,
                            "durable": false,
                        }),
                    },
                )
                .with_session(channel.to_string())
                .with_offering(O::KEY)
                .with_outcome(crate::audit::outcome_of(&outcome)),
            );
            ack::note_modal(
                ctx,
                modal,
                &truncate(&not_durable_note::<O>(&outcome), 1900),
            )
            .await;
        }
        Driven::StaleSurface => {
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::actor_of(modal.user.id.get(), viewer),
                    crate::audit::Surface::Modal,
                    crate::audit::Input {
                        kind: format!("offering:advance:{}", O::KEY),
                        detail: serde_json::json!({
                            "custom_id": modal.data.custom_id,
                        }),
                    },
                )
                .decided("refused", "stale_surface")
                .with_session(channel.to_string())
                .with_offering(O::KEY),
            );
            ack::note_modal(
                ctx,
                modal,
                "That form belongs to a replaced session or earlier state — nothing was fired.",
            )
            .await;
        }
        Driven::NoSession | Driven::NotOurs => {
            ack::note_modal(ctx, modal, &no_session_text::<O>()).await;
        }
        Driven::NeedsValue { .. } | Driven::NeedsText { .. } => {
            ack::note_modal(
                ctx,
                modal,
                "That form did not resolve to a typed move — nothing was fired.",
            )
            .await;
        }
    }
}

/// The honest one-line note a resolved round close posts — the round, the plurality winner, the
/// ballot split, the electorate of record, and the resolved turn's real outcome. Pure, so the
/// driven tests read exactly what [`handle_close`] posts.
pub fn close_note(resolved: &CollectiveResolved) -> String {
    format!(
        "**Round {} closed.** The party chose **{}** ({}/{} ballot(s) · {} voter(s) of record).\n{}{}",
        resolved.round,
        truncate(&resolved.winner.label, 120),
        resolved.tally.winning_votes(),
        resolved.tally.total_votes(),
        resolved.electorate.len(),
        outcome_note(&resolved.outcome),
        // The crowd turn is real either way; what a non-durable write costs is the ABILITY TO
        // RESUME this session after a restart, and that is said out loud rather than swallowed.
        if resolved.durable {
            ""
        } else {
            "\n\n⚠ **This round did not reach durable storage** — the turn landed, but this \
             session can no longer be resumed after a restart."
        },
    )
}

/// **Close a collective round** (a `/<offering> close`): resolve the plurality winner as ONE real
/// crowd turn and post the honest outcome + the next round's surface. The collective analogue of
/// [`handle_component`]'s single-press resolution. Registered as the `close` subcommand on the
/// generic wrappers (`/council close`, `/market close`, …); a DIRECT offering answers honestly
/// that its presses already resolve one-by-one, so there is no round to close.
pub async fn handle_close<O: DiscordOffering>(ctx: &Context, command: &CommandInteraction) {
    if !O::collective() {
        ephemeral(
            ctx,
            command,
            &format!(
                "`/{key}` runs in DIRECT mode — every press already resolves as its own \
                 verified turn, so there is no collective round to close.",
                key = O::KEY
            ),
        )
        .await;
        return;
    }
    let channel = command.channel_id.get();
    match close_round::<O>(channel) {
        CollectiveClose::Resolved(resolved) => {
            // AUDIT the resolved crowd turn: the closer is the presser of record here;
            // the substrate mover is the collective carrier, and the electorate + tally
            // ride the detail (the receipt-chain join is the landed `turn_hash`).
            crate::audit::log().emit(
                crate::audit::AuditEvent::new(
                    "discord",
                    crate::audit::Actor {
                        platform_id: command.user.id.get().to_string(),
                        dregg_identity: None,
                        grade: "custodial".to_string(),
                    },
                    crate::audit::Surface::Command,
                    crate::audit::Input {
                        kind: format!("offering:close:{}", O::KEY),
                        detail: serde_json::json!({
                            "round": resolved.round,
                            "winner": resolved.winner.label,
                            "winning_votes": resolved.tally.winning_votes(),
                            "total_votes": resolved.tally.total_votes(),
                            "electorate": resolved.electorate.len(),
                            "carrier": O::collective_carrier().0,
                        }),
                    },
                )
                .with_session(channel.to_string())
                .with_offering(O::KEY)
                .with_outcome(crate::audit::outcome_of(&resolved.outcome)),
            );
            let note = close_note(&resolved);
            let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
            let msg = match rendered {
                Some((embed, rows)) => CreateInteractionResponseMessage::new()
                    .content(truncate(&note, 1900))
                    .embed(embed)
                    .components(rows),
                None => CreateInteractionResponseMessage::new().content(truncate(&note, 1900)),
            };
            let _ = command
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        CollectiveClose::Empty => {
            ephemeral(ctx, command, "There is nothing to vote on this round.").await
        }
        CollectiveClose::NoRound => {
            ephemeral(ctx, command, "No collective round is open here.").await
        }
        CollectiveClose::NoSession => ephemeral(ctx, command, &no_session_text::<O>()).await,
    }
}

/// Re-render the shared channel surface with the move's honest outcome. A
/// public offering keeps its viewer-aware render. A hidden-information offering
/// edits only its viewer-blind fog into the shared message and sends the
/// presser's [`surface_for`] projection as an ephemeral companion.
async fn update_surface<O: DiscordOffering>(
    ctx: &Context,
    component: &ComponentInteraction,
    channel: u64,
    viewer: &DreggIdentity,
    note: &str,
    acked: bool,
) {
    let viewer = viewer.clone();
    // The re-render is a SECOND blocking store round-trip; it runs after the ACK, but it is the
    // same worker-parking cost, so it goes to the blocking pool too.
    let rendered = tokio::task::spawn_blocking(move || {
        with_live::<O, _>(channel, move |live| channel_surfaces::<O>(live, &viewer))
    })
    .await
    .ok()
    .flatten();
    let Some(((embed, rows), private_surface)) = rendered else {
        if acked {
            ack::followup_ephemeral(ctx, component, &no_session_text::<O>()).await;
        } else {
            component_ephemeral(ctx, component, &no_session_text::<O>()).await;
        }
        return;
    };
    if acked {
        // The press was deferred inside the 3s window ([`ack_component`]); EDIT
        // the pressed message into the post-turn render. For a hidden game this
        // is the viewer-blind public fog, never the presser's private projection.
        let result = component
            .edit_response(
                &ctx.http,
                EditInteractionResponse::new()
                    .content(truncate(note, 1900))
                    .embed(embed)
                    .components(rows),
            )
            .await;
        // A refused edit here means the turn LANDED and the board never showed it. Never silent.
        ack::warn_dropped_edit(&result, "offering", &component.data.custom_id);
        if let Some((private_embed, _private_rows)) = private_surface {
            ack::followup_ephemeral_surface(
                ctx,
                component,
                "**Your private view** — only you can read this hand / sealed move. Use the shared board's controls to act.",
                private_embed,
                vec![],
            )
            .await;
        }
        return;
    }
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::UpdateMessage(
                CreateInteractionResponseMessage::new()
                    .content(truncate(note, 1900))
                    .embed(embed)
                    .components(rows),
            ),
        )
        .await;
    if let Some((private_embed, _private_rows)) = private_surface {
        ack::followup_ephemeral_surface(
            ctx,
            component,
            "**Your private view** — only you can read this hand / sealed move. Use the shared board's controls to act.",
            private_embed,
            vec![],
        )
        .await;
    }
}

fn no_session_text<O: DiscordOffering>() -> String {
    format!(
        "No {} session is open in this channel — sessions live in bot memory and do NOT \
         survive a bot restart. Start a fresh one with `{}`.",
        O::KEY,
        O::open_hint()
    )
}

async fn ephemeral(ctx: &Context, command: &CommandInteraction, text: &str) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(text)
                    .ephemeral(true),
            ),
        )
        .await;
}

pub(crate) async fn component_ephemeral(
    ctx: &Context,
    component: &ComponentInteraction,
    text: &str,
) {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(text)
                    .ephemeral(true),
            ),
        )
        .await;
}

/// Read a modal text field by id.
fn modal_value(modal: &ModalInteraction, id: &str) -> String {
    for row in &modal.data.components {
        for component in &row.components {
            if let ActionRowComponent::InputText(input) = component
                && input.custom_id == id
            {
                return input.value.clone().unwrap_or_default();
            }
        }
    }
    String::new()
}

/// Truncate `s` to at most `max` characters (char-safe).
pub fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The routers — `main.rs` sends every `offering:` press/modal here; we dispatch on the key.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE one Discord mounting table** — every offering the generic per-type adapter serves.
/// Both routers ([`route_component`] / [`route_modal`]) and [`generic_offering_keys`] expand
/// from THIS list, so "which offerings the routers dispatch" is one statement that cannot
/// drift into three (the old shape: two hand-maintained 15-ish-arm matches plus a folklore
/// count). The offering SET itself is pinned to the shared registrar: the parity test below
/// checks this table (plus the rpg-world route and the bespoke `/dungeon` crowd surface)
/// serves exactly the LIVE `dreggnet_catalog::full_catalog_host` — the same 23 web, Telegram,
/// and WeChat register (docs/BOT-SHARED-BACKEND-DESIGN.md).
///
/// Component presses for the eight identity-owned RPG feature-surface keys never reach this table's arms
/// (they are intercepted for the per-identity persistent world, `commands::rpg_world`); their
/// rows here serve the modal router and the key census. Offerings whose affordances are all
/// fixed-arg buttons never mint a modal, so their modal arms are inert — present for
/// uniformity, and so a value-taking turn added later is routed the day it exists.
macro_rules! for_each_generic_offering {
    ($per:ident) => {
        $per!(dreggnet_council::CouncilOffering);
        $per!(dreggnet_market::MarketOffering);
        $per!(dreggnet_market::DarkBazaarOffering);
        #[cfg(feature = "private-bazaar-live")]
        $per!(dreggnet_market::private_bazaar_live_host::PrivateBazaarRaidOffering);
        $per!(dreggnet_hermes::HermesOffering);
        $per!(dreggnet_grain::GrainOffering);
        $per!(dreggnet_doc::DocOffering);
        $per!(dreggnet_offerings::native_descent::NativeDescentOffering);
        $per!(dreggnet_offerings::campaign::DescentCampaignOffering);
        $per!(crate::commands::portfolio::SeatedTug);
        $per!(dregg_automatafl::AutomataflOffering);
        $per!(dreggnet_surfaces::HostedProofAssignedRaidOffering);
        $per!(dreggnet_names::NamesOffering);
        $per!(dreggnet_compute::ComputeOffering);
        $per!(dreggnet_surfaces::TradeOffering);
        $per!(dreggnet_surfaces::InventoryOffering);
        $per!(dreggnet_surfaces::CheevoShowcase);
        $per!(dreggnet_surfaces::GuildPage);
        $per!(dreggnet_surfaces::CraftOffering);
        $per!(dreggnet_surfaces::CompanionOffering);
        $per!(dreggnet_surfaces::AshenmoorErrandOffering);
        $per!(dreggnet_surfaces::TavernOffering);
        $per!(dreggnet_surfaces::PartyOffering);
        $per!(dreggnet_gear::LoadoutOffering);
        $per!(dreggnet_gear::TalentTreeOffering);
        $per!(crate::commands::overworld::OverworldPlay);
    };
}

// The table is the crate's, not this module's. `commands::verify_chain` mounts the standing
// "⛓ re-verify chain" press for EVERY key this table serves, and it used to do so from a
// second hand-kept list — which drifted, leaving eight shipped buttons that answered a press
// with nothing at all. One table, every router.
pub(crate) use for_each_generic_offering;

/// The keys the generic adapter's routers dispatch — expanded from the ONE mounting table
/// ([`for_each_generic_offering`]), never a second hand-kept list. The catalog parity test
/// pins this census to the live shared registrar. (Runtime-unused until the Phase-C host
/// bridge routes by key string — docs/BOT-SHARED-BACKEND-DESIGN.md; today the tests consume it.)
#[allow(dead_code)]
pub fn generic_offering_keys() -> Vec<&'static str> {
    let mut keys = Vec::new();
    macro_rules! push_key {
        ($ty:ty) => {
            keys.push(<$ty as DiscordOffering>::KEY);
        };
    }
    for_each_generic_offering!(push_key);
    keys
}

/// Dispatch an `offering:` component press to the offering that owns the key.
pub async fn route_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let Some(key) = key_of(&component.data.custom_id) else {
        component_ephemeral(
            ctx,
            component,
            "That button is from a stale surface this bot build no longer decodes.",
        )
        .await;
        return;
    };
    // ── The eight identity-owned RPG feature surfaces route to the PER-IDENTITY PERSISTENT world
    //    (`commands::rpg_world`): the press is one real turn in the PRESSER's own
    //    sqlite-persisted world (backlog #15/#24), not a per-channel demo store. ──
    if crate::commands::rpg_world::is_rpg_key(&key) {
        crate::commands::rpg_world::handle_component(ctx, component, state).await;
        return;
    }
    // ── The native Descent takes the ordinary adapter path, then publishes a run that just
    //    ENDED. The generic adapter has no notion of "this run is over and belongs on the web as a
    //    card", and the Descent is the one offering whose finished runs are the product's share
    //    surface, so the extra step is named here rather than smuggled into `handle_component`.
    //    Keyed off the offering's own `KEY` constant, so it cannot drift into a second key string.
    if key == <dreggnet_offerings::native_descent::NativeDescentOffering as DiscordOffering>::KEY {
        handle_component::<dreggnet_offerings::native_descent::NativeDescentOffering>(
            ctx, component, state,
        )
        .await;
        crate::commands::native_descent::share_finished_run(ctx, component).await;
        return;
    }
    // ── Everything else: the ONE mounting table, in order. ──
    macro_rules! try_component {
        ($ty:ty) => {
            if key == <$ty as DiscordOffering>::KEY {
                return handle_component::<$ty>(ctx, component, state).await;
            }
        };
    }
    for_each_generic_offering!(try_component);
    component_ephemeral(
        ctx,
        component,
        &format!("No offering with key `{key}` is mounted in this bot build."),
    )
    .await;
}

/// Dispatch an `offering:` modal submit to the offering that owns the key.
pub async fn route_modal(ctx: &Context, modal: &ModalInteraction, state: &BotState) {
    let Some(key) = key_of(&modal.data.custom_id) else {
        let _ = modal
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content(
                            "That form is from a stale surface this bot build no longer decodes.",
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    };
    // The ONE mounting table again — a modal-less offering's arm is inert (it never mints a
    // modal), but a forged/stale submit id still resolves to the honest adapter path (the
    // substrate is the sole referee) instead of a misleading "not mounted".
    macro_rules! try_modal {
        ($ty:ty) => {
            if key == <$ty as DiscordOffering>::KEY {
                return handle_modal::<$ty>(ctx, modal, state).await;
            }
        };
    }
    for_each_generic_offering!(try_modal);
    let _ = modal
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(format!(
                        "No offering with key `{key}` is mounted in this bot build."
                    ))
                    .ephemeral(true),
            ),
        )
        .await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the wire codec + the rendering contract, driven with no live Discord.
// (The offering-driving tests live beside each offering: `commands::council`,
// `commands::market`.)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// **A MODAL SUBMIT IS AN INTERACTION, ON THE SAME 3-SECOND CLOCK — and it was answering
    /// LAST.** `handle_modal` ran `drive_text_at` / `drive_value_at` — a real executor turn on the
    /// offering store thread: a sealed bid, a reserve price, a document paragraph — then blocked
    /// on that same thread AGAIN to re-render, and only then sent its FIRST response. A typed move
    /// that outran the window had COMMITTED, and the player was shown "This interaction failed"
    /// over a board still painted with the pre-move state.
    ///
    /// This drives the REAL `drive_value_at` against a REAL live council through the REAL
    /// ordering helper `handle_modal` now uses. The trace is the assertion, and the turn is
    /// checked to have genuinely landed — so this cannot pass by not doing the work.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_typed_move_is_answered_before_the_turn_commits() {
        use dreggnet_council::{CouncilOffering, TURN_PROPOSE};
        use std::sync::{Arc, Mutex};

        let channel = 90_941;
        close_in::<CouncilOffering>(channel);
        let members: Vec<[u8; 32]> = vec![[11u8; 32], [22u8; 32], [33u8; 32]];
        let voter = CouncilOffering::member_identity(&members[0]);
        open_in::<CouncilOffering>(
            channel,
            move || {
                CouncilOffering::new(
                    members,
                    vec![dreggnet_council::CandidateProposal::new(
                        "Fund the commons",
                        1,
                    )],
                    2,
                )
            },
            SessionConfig::with_seed(channel),
        )
        .expect("the council cell comes alive");
        let stamp = control_stamp_in::<CouncilOffering>(channel).expect("a live stamp");

        let trace: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));
        let ack_trace = Arc::clone(&trace);
        let work_trace = Arc::clone(&trace);
        let driven = crate::commands::ack::testing::ack_then_blocking_for_test(
            async move {
                tokio::task::yield_now().await;
                ack_trace.lock().unwrap().push("acked");
            },
            move || {
                let out = drive_value_at::<CouncilOffering>(channel, stamp, TURN_PROPOSE, 0, voter);
                work_trace.lock().unwrap().push("committed");
                out
            },
        )
        .await;

        assert!(
            matches!(driven, Some(Driven::Fired(ref o)) if o.landed()),
            "the typed move must genuinely land, or this test proves nothing: {driven:?}"
        );
        assert_eq!(
            trace.lock().unwrap().as_slice(),
            ["acked", "committed"],
            "the turn committed before the modal submit was answered"
        );
        close_in::<CouncilOffering>(channel);
    }

    #[test]
    fn the_custom_id_wire_round_trips() {
        let stamp = ControlStamp {
            generation: 0xabc,
            head: 3,
        };
        let fire = fire_id_at("council", stamp, "approve", 2);
        assert_eq!(fire, "offering:fire:council:abc:3:approve:2");
        assert_eq!(
            parse_press(&fire),
            Some(Press::Fire {
                key: "council".into(),
                stamp,
                turn: "approve".into(),
                arg: 2
            })
        );

        let ask = ask_id_at("market", stamp, "bid");
        assert_eq!(ask, "offering:ask:market:abc:3:bid");
        assert_eq!(
            parse_press(&ask),
            Some(Press::Ask {
                key: "market".into(),
                stamp,
                turn: "bid".into()
            })
        );

        assert_eq!(
            parse_submit(&submit_id("market", stamp, "list")),
            Some(("market".into(), stamp, "list".into()))
        );

        assert_eq!(key_of(&fire).as_deref(), Some("council"));
        assert_eq!(key_of(&ask).as_deref(), Some("market"));
        assert_eq!(
            key_of(&submit_id("market", stamp, "list")).as_deref(),
            Some("market")
        );
    }

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    // ─────────────────────────────────────────────────────────────────────────
    // PERSISTENCE — the restart gate.
    // ─────────────────────────────────────────────────────────────────────────

    /// Point this test process's session store at a scratch directory. The install is a
    /// `OnceLock`, so calling it from several tests is fine — the first one wins and the rest
    /// see the same root.
    fn install_test_resume_store() -> PathBuf {
        static ROOT: OnceLock<PathBuf> = OnceLock::new();
        let root = ROOT
            .get_or_init(|| {
                let dir = std::env::temp_dir()
                    .join(format!("dregg-bot-test-sessions-{}", std::process::id()));
                let _ = std::fs::remove_dir_all(&dir);
                std::fs::create_dir_all(&dir).expect("the scratch session directory");
                dir
            })
            .clone();
        install_resume_store(Some(root.clone()));
        root
    }

    /// **THE RESTART GATE: the bot forgets, comes back, and LANDS THE NEXT TURN.**
    ///
    /// The failure this is written against is the plausible one, not the obvious one. Persisting
    /// a *rendering* would produce a board that looks resumable and refuses every move — a new
    /// fake, worse than the honest amnesia. So this test does not check that a board comes back;
    /// it checks that the thing that comes back **can still be played**:
    ///
    ///   1. open a real offering and land two real turns through the SAME `drive` path a live
    ///      button press takes (with their real receipts);
    ///   2. DROP the whole in-RAM session — the offering value, the session, the receipt chain —
    ///      exactly as a process restart does (`quench`, which removes the live entry and leaves
    ///      the durable log alone);
    ///   3. press a button minted BEFORE the drop, and require it to LAND a third turn.
    ///
    /// The third turn landing is the whole assertion. It can only happen if the resumed session
    /// re-drove turns 1 and 2 through the real executor: an offering advances against committed
    /// state, so a fake would refuse here. The pre-drop button firing is the second half — the
    /// resumed session carries the same generation and head stamp, so controls a player left in
    /// the channel are still live rather than a wall of "that control belongs to a replaced
    /// session".
    #[test]
    fn a_session_survives_a_restart_and_lands_the_next_turn() {
        use dreggnet_names::NamesOffering;

        install_test_resume_store();
        let channel = 99_501;
        close_in::<NamesOffering>(channel);

        open_in(channel, NamesOffering::new, SessionConfig::with_seed(11))
            .expect("the offering opens");

        // The registration affordance — a text-taking turn, so the log's `Action::text` payload
        // is on the replay path too (a name that did not survive persistence would resume into a
        // world with different names in it, and the executor would notice).
        let register = with_live::<NamesOffering, _>(channel, |live| {
            live.offering
                .actions(&live.session)
                .into_iter()
                .find(|a| a.enabled)
                .expect("the names surface offers a registration")
        })
        .expect("the session is live");

        // Two real turns, through the SAME sync core a live modal submit takes.
        for name in ["alpha-before", "beta-before"] {
            let stamp = control_stamp_in::<NamesOffering>(channel).expect("a live stamp");
            let driven = drive_text_at::<NamesOffering>(
                channel,
                stamp,
                &register.turn,
                register.arg,
                name,
                actor("a1"),
            );
            assert!(
                matches!(driven, Driven::Fired(Outcome::Landed { .. })),
                "the pre-restart turn `{name}` must land: {driven:?}",
            );
        }

        // The stamp a control left in the channel carries, minted BEFORE the crash.
        let pre_restart_stamp = control_stamp_in::<NamesOffering>(channel).expect("a live stamp");

        // ── THE RESTART. Everything in RAM goes; only the durable log survives. ──
        quench::<NamesOffering>(channel);
        assert!(
            !live_entry_exists::<NamesOffering>(channel),
            "the in-RAM session is genuinely gone"
        );

        // ── THE PRESS. A form carrying the PRE-RESTART stamp must commit a third turn. ──
        let driven = drive_text_at::<NamesOffering>(
            channel,
            pre_restart_stamp,
            &register.turn,
            register.arg,
            "gamma-after",
            actor("a1"),
        );
        assert!(
            matches!(driven, Driven::Fired(Outcome::Landed { .. })),
            "a control minted before the restart must land a REAL turn on the resumed \
             session — got {driven:?}",
        );

        // The resumed session CONTINUED the committed chain rather than starting a new one …
        let journal_len =
            with_live::<NamesOffering, _>(channel, |live| live.journal.moves.len()).unwrap();
        assert_eq!(
            journal_len, 3,
            "two pre-restart turns plus the one that landed after it"
        );
        // … and it is the SAME state, not a same-shaped one: the names registered before the
        // crash are still registered, which is only true if their turns genuinely re-landed.
        let names = with_live::<NamesOffering, _>(channel, |live| {
            let mut n: Vec<String> = live
                .session
                .registered()
                .into_iter()
                .map(|(name, _owner)| name)
                .collect();
            n.sort();
            n
        })
        .expect("the session is live");
        assert_eq!(
            names,
            vec![
                "alpha-before".to_string(),
                "beta-before".to_string(),
                "gamma-after".to_string()
            ],
            "the pre-restart registrations came back through the executor, and the post-restart \
             one joined them",
        );
        // The offering's own verifier re-derives the whole chain over the resumed session.
        let report = verify_live::<NamesOffering>(channel).expect("the resumed session verifies");
        assert!(
            report.verified,
            "the resumed chain must re-verify: {}",
            report.detail
        );

        close_in::<NamesOffering>(channel);
    }

    /// A tampered durable log does NOT resume. The executor re-checks every recorded move on the
    /// way back in, so a line nobody could have played fails there — and the channel is left with
    /// no session rather than a forged one.
    #[test]
    fn a_tampered_log_refuses_to_resume() {
        use dreggnet_names::NamesOffering;
        use dreggnet_offerings::FileResumeStore;

        let root = install_test_resume_store();
        let channel = 99_502;
        close_in::<NamesOffering>(channel);
        open_in(channel, NamesOffering::new, SessionConfig::with_seed(12))
            .expect("the offering opens");
        let id = with_live::<NamesOffering, _>(channel, |live| live.journal.id.clone())
            .expect("a live journal id");

        // Splice a move no player made and no executor would admit.
        let store = FileResumeStore::open(&root).expect("the scratch store");
        assert!(store.record_landed(
            <NamesOffering as DiscordOffering>::KEY,
            &id,
            &Action::new("forged", "no-such-turn", 4_242, true),
            &actor("ff"),
        ));

        quench::<NamesOffering>(channel);
        let refused = resume_in::<NamesOffering>(channel);
        assert!(
            matches!(refused, Err(ResumeRefusal::Refused { .. })),
            "a spliced move must fail on re-drive, not reopen a forged state — got {refused:?}",
        );
        assert!(
            !live_entry_exists::<NamesOffering>(channel),
            "nothing is left live after a refused resume"
        );
        close_in::<NamesOffering>(channel);
    }

    /// An offering that declines [`DiscordOffering::rebuild`] is honestly NOT resumable, rather
    /// than being reopened under a guessed configuration.
    #[test]
    fn an_unrebuildable_offering_refuses_to_resume() {
        use dreggnet_offerings::native_descent::NativeDescentOffering;

        install_test_resume_store();
        let channel = 99_503;
        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            NativeDescentOffering::new,
            SessionConfig::with_seed(3),
        )
        .expect("the offering opens");
        quench::<NativeDescentOffering>(channel);
        assert_eq!(
            resume_in::<NativeDescentOffering>(channel),
            Err(ResumeRefusal::NotRebuildable),
            "a day-bound offering names its own irreproducibility instead of guessing",
        );
        close_in::<NativeDescentOffering>(channel);
    }

    /// Drop the channel's LIVE session while leaving its durable record intact — a faithful
    /// in-process stand-in for the process dying. Deliberately not `close_in`, which forgets the
    /// record too (a close is a decision; a crash is not).
    fn quench<O: DiscordOffering>(channel: u64) {
        let _ = O::store().run(move |sessions| {
            sessions.remove(&channel);
        });
    }

    fn live_entry_exists<O: DiscordOffering>(channel: u64) -> bool {
        O::store()
            .run(move |sessions| sessions.contains_key(&channel))
            .unwrap_or(false)
    }

    /// **Panic isolation**: a job that panics on the store thread does NOT brick the subsystem.
    /// Before this hardening a panicking job killed the store thread and every later access
    /// panicked at `send`/`recv`'s `.expect`; now the panic is contained (the caller gets a clean
    /// `None`) and a subsequent job on the SAME store still succeeds. (A "thread … panicked at
    /// 'store-panic-isolation-canary'" line on stderr during this test is EXPECTED — the point is
    /// that it is contained, not fatal.)
    #[test]
    fn a_panicking_job_does_not_brick_the_store() {
        use dreggnet_offerings::native_descent::NativeDescentOffering;

        let channel = 99_207;
        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            NativeDescentOffering::new,
            SessionConfig::with_seed(1),
        )
        .unwrap();

        // A job that panics comes back as a graceful `None`, not a process abort.
        let panicked = with_live::<NativeDescentOffering, ()>(channel, |_live| {
            panic!("store-panic-isolation-canary")
        });
        assert!(
            panicked.is_none(),
            "a panicking job must return None, not abort the caller"
        );

        // The store thread SURVIVED: the very next job against the same store still answers.
        let revision =
            with_live::<NativeDescentOffering, _>(channel, |live| live.session.revision());
        assert_eq!(
            revision,
            Some(0),
            "the store thread must survive a panicking job and keep serving"
        );
        close_in::<NativeDescentOffering>(channel);
    }

    #[test]
    fn a_replaced_direct_session_refuses_its_old_control_without_mutation() {
        use dreggnet_offerings::native_descent::NativeDescentOffering;

        let channel = 99_201;
        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            NativeDescentOffering::new,
            SessionConfig::with_seed(1),
        )
        .unwrap();
        let action = with_live::<NativeDescentOffering, _>(channel, |live| {
            live.offering.actions(&live.session)[0].clone()
        })
        .unwrap();
        let old = fire_id_in::<NativeDescentOffering>(channel, &action.turn, action.arg).unwrap();

        open_in(
            channel,
            NativeDescentOffering::new,
            SessionConfig::with_seed(1),
        )
        .unwrap();
        assert!(matches!(
            drive::<NativeDescentOffering>(channel, &old, actor("old")),
            Driven::StaleSurface
        ));
        assert_eq!(
            with_live::<NativeDescentOffering, _>(channel, |live| live.session.revision()),
            Some(0),
            "an S1 button cannot mutate replacement S2"
        );

        let fresh = fire_id_in::<NativeDescentOffering>(channel, &action.turn, action.arg).unwrap();
        assert!(matches!(
            drive::<NativeDescentOffering>(channel, &fresh, actor("fresh")),
            Driven::Fired(Outcome::Landed { .. })
        ));
        close_in::<NativeDescentOffering>(channel);
    }

    #[test]
    fn a_modal_submit_is_bound_to_the_session_that_opened_it() {
        use dreggnet_market::{DarkBazaarOffering, TURN_LIST};

        let channel = 99_202;
        close_in::<DarkBazaarOffering>(channel);
        open_in(
            channel,
            DarkBazaarOffering::new,
            SessionConfig::with_seed(2),
        )
        .unwrap();
        let old_stamp = control_stamp_in::<DarkBazaarOffering>(channel).unwrap();
        let old_submit = submit_id(DarkBazaarOffering::KEY, old_stamp, TURN_LIST);

        open_in(
            channel,
            DarkBazaarOffering::new,
            SessionConfig::with_seed(2),
        )
        .unwrap();
        let (_, stamp, turn) = parse_submit(&old_submit).unwrap();
        assert!(matches!(
            drive_value_at::<DarkBazaarOffering>(channel, stamp, &turn, 100, actor("seller")),
            Driven::StaleSurface
        ));
        assert_eq!(
            with_live::<DarkBazaarOffering, _>(channel, |live| {
                live.session.market().receipts_len()
            }),
            Some(0)
        );
        close_in::<DarkBazaarOffering>(channel);
    }

    /// A foreign custom-id (the `/dungeon` ballot, the ViewNode card route, the dashboard) is
    /// NOT ours — the router must ignore it rather than mis-fire a turn.
    #[test]
    fn a_foreign_custom_id_is_not_ours() {
        for id in [
            "fiction:vote:0:1",
            "deosturn:increment:1",
            "deos:abc12345:grant",
            "dregg:panel:identity",
            "start:menu",
            "offering:bogus:market:bid",
        ] {
            assert_eq!(parse_press(id), None, "{id} must not decode as a press");
            assert_eq!(parse_submit(id), None, "{id} must not decode as a submit");
        }
        assert_eq!(key_of("fiction:vote:0:1"), None);
    }

    /// **BOTH-POLARITY catalog parity** (the Discord half of `dreggnet-catalog`'s contract —
    /// docs/BOT-SHARED-BACKEND-DESIGN.md): every offering the LIVE shared registrar
    /// (`full_catalog_host`, the same builder web/Telegram/WeChat register through) serves is
    /// reachable on Discord — through the ONE mounting table, the rpg-world route, or the
    /// bespoke `/dungeon` crowd surface — and every mounted key is either a catalog offering
    /// or a declared Discord extra. Registering a new catalog offering fails this test until
    /// its Discord route exists; mounting a phantom key fails it too.
    #[test]
    fn the_mounted_offerings_are_exactly_the_shared_catalog() {
        let host = dreggnet_catalog::full_catalog_host(&dreggnet_catalog::CatalogConfig::default());
        let live: Vec<String> = host.list_offerings().into_iter().map(|o| o.key).collect();
        assert_eq!(
            live.len(),
            dreggnet_catalog::CATALOG_KEYS.len(),
            "the live registrar serves the full catalog"
        );

        let mounted = generic_offering_keys();
        // No duplicate mounting (two table rows claiming one key would shadow each other).
        let unique: std::collections::BTreeSet<_> = mounted.iter().copied().collect();
        assert_eq!(unique.len(), mounted.len(), "mounted keys are unique");

        for key in &live {
            let served = mounted.contains(&key.as_str())
                || crate::commands::rpg_world::is_rpg_key(key)
                // `dungeon` is served by the bespoke `/dungeon` crowd surface
                // (`commands::fiction`, its own `fiction:` custom-id namespace); its
                // generic-adapter mounting is the staged `commands::dungeon_offering`.
                || key == "dungeon";
            assert!(
                served,
                "catalog offering `{key}` must be reachable on Discord"
            );
        }
        for key in &mounted {
            let known = dreggnet_catalog::CATALOG_KEYS.contains(key)
                || crate::commands::portfolio::DISCORD_EXTRA_PLAY_KEYS.contains(key)
                || crate::commands::portfolio::DISCORD_OPT_IN_PLAY_KEYS.contains(key);
            assert!(
                known,
                "mounted key `{key}` is neither a catalog offering nor a declared Discord extra"
            );
        }
    }

    #[test]
    fn an_outcome_is_reported_honestly() {
        let refused = Outcome::Refused("below quorum: the proposal has not passed".into());
        let note = outcome_note(&refused);
        assert!(note.contains("Refused"), "{note}");
        assert!(note.contains("nothing committed, no receipt"), "{note}");
        assert!(
            note.contains("below quorum"),
            "the executor's own reason survives: {note}"
        );

        let mut receipt = dregg_app_framework::TurnReceipt {
            turn_hash: [0x11; 32],
            post_state_hash: [0x22; 32],
            ..Default::default()
        };
        let landed = Outcome::Landed {
            receipt: receipt.clone(),
            ended: false,
        };
        let note = outcome_note(&landed);
        let first_id = PlayerTurnReceipt::from_landed(&receipt, false).receipt_hex();
        assert!(
            note.contains(&first_id),
            "complete receipt id missing: {note}"
        );
        assert!(note.contains("Session continues"), "{note}");

        // The card is the receipt-chain join, not merely the stable turn id.
        receipt.post_state_hash = [0x33; 32];
        let second_id = PlayerTurnReceipt::from_landed(&receipt, false).receipt_hex();
        assert_ne!(first_id, second_id);
    }
}
