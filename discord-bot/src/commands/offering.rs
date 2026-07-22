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
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{SyncSender, sync_channel};
use std::time::{SystemTime, UNIX_EPOCH};

use serenity::all::{
    ActionRowComponent, ButtonStyle, CommandInteraction, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateEmbed, CreateEmbedFooter, CreateInputText,
    CreateInteractionResponse, CreateInteractionResponseMessage, CreateModal,
    EditInteractionResponse, InputTextStyle, ModalInteraction,
};

use dreggnet_offerings::{
    Action, Audience, AudienceProjection, CollectiveDecision, DreggIdentity, Offering, Outcome,
    SessionConfig, SessionId, SessionMoveLog, SessionResumeStore, Tally, VerifyReport, VoteCount,
    project_for_audience,
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
    pub fn record_landed(&mut self, action: Action, actor: DreggIdentity, outcome: &Outcome)
    where
        O: DiscordOffering,
    {
        if !outcome.landed() {
            return;
        }
        self.journal.record(action.clone(), actor.clone());
        if let Some(store) = self.resume_store.as_deref() {
            store.record_landed(O::KEY, &self.journal.id, &action, &actor);
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

impl<O: DiscordOffering> Store<O> {
    /// Spawn the store's owning thread (called once, from the offering's `store()` `OnceLock`).
    pub fn spawn() -> Store<O> {
        let (jobs, rx) = sync_channel::<Job<O>>(64);
        std::thread::Builder::new()
            .name(format!("offering-{}", O::KEY))
            .spawn(move || {
                let mut sessions: HashMap<u64, Live<O>> = HashMap::new();
                while let Ok(job) = rx.recv() {
                    job(&mut sessions);
                }
            })
            .expect("spawn the offering session thread");
        Store { jobs }
    }

    /// Run `f` against the session table on the owning thread and hand back its result.
    fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut HashMap<u64, Live<O>>) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |sessions| {
                let _ = tx.send(f(sessions));
            }))
            .expect("the offering session thread is alive");
        rx.recv().expect("the offering session thread answered")
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
    O::store().run(move |sessions| {
        let offering = make();
        let session = offering.open(cfg.clone())?;
        // A collective offering opens with a live round over the session's first actions (an open
        // crowd — a restricted electorate is set with [`open_round`]); a direct offering has none.
        let round = if O::collective() {
            Some(CollectiveRound::new(0, offering.actions(&session), None))
        } else {
            None
        };
        let generation = fresh_generation(channel);
        let journal_id = SessionId::new(format!("discord:{}:{channel}:{generation:016x}", O::KEY));
        sessions.insert(
            channel,
            Live {
                offering,
                session,
                round,
                generation,
                control_head: 0,
                journal: SessionMoveLog::new(O::KEY, journal_id, cfg),
                resume_store: None,
            },
        );
        Ok(())
    })
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
    O::store().run(move |sessions| {
        let offering = make();
        let session = offering
            .open(cfg.clone())
            .map_err(|error| error.to_string())?;
        let round = if O::collective() {
            Some(CollectiveRound::new(0, offering.actions(&session), None))
        } else {
            None
        };
        let generation = fresh_generation(channel);
        let journal_id = SessionId::new(format!("discord:{}:{channel}:{generation:016x}", O::KEY));
        let store = make_store()?;
        store.record_open(O::KEY, &journal_id, &cfg);
        sessions.insert(
            channel,
            Live {
                offering,
                session,
                round,
                generation,
                control_head: 0,
                journal: SessionMoveLog::new(O::KEY, journal_id, cfg),
                resume_store: Some(store),
            },
        );
        Ok(())
    })
}

/// Whether `channel` has a live session of this offering.
pub fn is_open<O: DiscordOffering>(channel: u64) -> bool {
    O::store().run(move |sessions| sessions.contains_key(&channel))
}

/// Run `f` against the channel's live session (`None` when no session is open). `f` runs on the
/// store's thread; only its result comes back.
pub fn with_live<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&mut Live<O>) -> R + Send + 'static,
) -> Option<R> {
    O::store().run(move |sessions| sessions.get_mut(&channel).map(f))
}

/// Run one transaction against a live session and optionally quarantine it.
/// The callback result and removal decision are made on the owning thread;
/// removal happens before the caller can observe the result.
pub(crate) fn with_live_transaction<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&mut Live<O>) -> (R, bool) + Send + 'static,
) -> Option<R> {
    O::store().run(move |sessions| {
        let (result, quarantine) = {
            let live = sessions.get_mut(&channel)?;
            f(live)
        };
        if quarantine {
            sessions.remove(&channel);
        }
        Some(result)
    })
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

/// Drop the channel's session. Part of the adapter's session API (a `/<offering> close`
/// subcommand is the obvious next consumer); today the driven tests are what exercise it.
#[allow(dead_code)]
pub fn close_in<O: DiscordOffering>(channel: u64) {
    O::store().run(move |sessions| {
        sessions.remove(&channel);
    });
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
    O::store().run(move |sessions| match sessions.get_mut(&channel) {
        Some(live) => {
            let options = live.offering.actions(&live.session);
            live.control_head = live.control_head.saturating_add(1);
            live.round = Some(CollectiveRound::new(live.control_head, options, electorate));
            true
        }
        None => false,
    })
}

/// **Cast one write-once collective ballot**, keyed by `voter`'s derived dregg identity, for the
/// option carrying `arg` — the SAME path a live vote-button press takes. This is the collective
/// analogue of [`drive`]: it records a vote rather than resolving a turn (the plurality winner is
/// resolved later by [`close_round`]).
pub fn cast_vote<O: DiscordOffering>(channel: u64, voter: DreggIdentity, arg: i64) -> Cast {
    O::store().run(move |sessions| match sessions.get_mut(&channel) {
        None => Cast::NoSession,
        Some(live) => match live.round.as_mut() {
            None => Cast::NoRound,
            Some(round) => round.cast_arg(&voter, arg),
        },
    })
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
    O::store().run(move |sessions| match sessions.get_mut(&channel) {
        None => Cast::NoSession,
        Some(live) if live.control_stamp() != stamp => Cast::StaleSurface,
        Some(live) => match live.round.as_mut() {
            None => Cast::NoRound,
            Some(round) => round.cast_arg(&voter, arg),
        },
    })
}

/// **Close the collective round: resolve its plurality winner as ONE real crowd turn.** Tallies
/// the write-once ballots, drives the winning [`Action`] through [`Offering::advance_collective`]
/// carrying the full [`CollectiveDecision`] (the voters of record + the [`Tally`] + the carrier),
/// and opens the next round over the resulting state (preserving the electorate restriction). A
/// landed move records a real `TurnReceipt`; a refused one commits nothing (anti-ghost). This is
/// the collective analogue of a single-press resolution — many pressers, one refereed turn.
pub fn close_round<O: DiscordOffering>(channel: u64) -> CollectiveClose {
    let carrier = O::collective_carrier();
    O::store().run(move |sessions| {
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
        let decision = CollectiveDecision::new(electorate.clone(), carrier.clone(), tally.clone());
        let outcome = live
            .offering
            .advance_collective(&mut live.session, winner.clone(), decision);
        live.record_landed(winner.clone(), carrier, &outcome);

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
        })
    })
}

/// Read the channel's live collective round (`None` when no round is open). Runs on the store's
/// thread; only the result comes back. The driven tests + a future `/<offering>` collective
/// surface use it to render the live tally.
#[allow(dead_code)]
pub fn with_round<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&CollectiveRound) -> R + Send + 'static,
) -> Option<R> {
    O::store().run(move |sessions| sessions.get(&channel).and_then(|l| l.round.as_ref()).map(f))
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
    card.embed
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

/// An honest account of a resolved move: a landed receipt (with its real `turn_hash`) or the
/// executor's own refusal reason — never laundered.
pub fn outcome_note(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Landed { receipt, ended } => {
            let h = hex::encode(&receipt.turn_hash[..8]);
            let tail = if *ended {
                " — the session ended."
            } else {
                ""
            };
            format!(
                "**A verified turn landed.** `turn_hash {h}…`{tail}\n> This hash seals the \
                 move into the session's hash-linked receipt chain — every later turn commits \
                 to it, so mutating ANY past move changes every hash after it. Press ⛓ \
                 **re-verify chain** and the bot recomputes the whole chain from the move \
                 history in front of you."
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
}

/// **Drive one component press.** Decodes the custom-id and, for a fixed-arg affordance, runs
/// ONE real [`Offering::advance`] attributed to `actor`. This is the whole logic of a live
/// button press; [`handle_component`] only adds the serenity round-trip.
pub fn drive<O: DiscordOffering>(channel: u64, custom_id: &str, actor: DreggIdentity) -> Driven {
    let press = match parse_press(custom_id) {
        Some(p) => p,
        None => return Driven::NotOurs,
    };
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
    O::store().run(move |sessions| {
        sessions
            .get(&channel)
            .is_some_and(|live| live.control_stamp() == stamp)
    })
}

enum MutationAttempt {
    Fired(Outcome),
    NoSession,
    StaleSurface,
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
    match O::store().run(move |sessions| {
        let Some(live) = sessions.get_mut(&channel) else {
            return MutationAttempt::NoSession;
        };
        if live.control_stamp() != stamp {
            return MutationAttempt::StaleSurface;
        }
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        MutationAttempt::Fired(outcome)
    }) {
        MutationAttempt::Fired(outcome) => Driven::Fired(outcome),
        MutationAttempt::NoSession => Driven::NoSession,
        MutationAttempt::StaleSurface => Driven::StaleSurface,
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
    let outcome = with_live::<O, _>(channel, move |live| {
        // The label is decoration; the executor resolves the TYPED (turn, arg) — and `enabled`
        // is a decoration too (we pass `true`), because the substrate is the sole referee: a
        // move it does not admit comes back as a real `Refused`, not a frontend veto.
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        outcome
    });
    match outcome {
        Some(o) => Driven::Fired(o),
        None => Driven::NoSession,
    }
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
    match O::store().run(move |sessions| {
        let Some(live) = sessions.get_mut(&channel) else {
            return MutationAttempt::NoSession;
        };
        if live.control_stamp() != stamp {
            return MutationAttempt::StaleSurface;
        }
        let action = Action::new(turn.clone(), turn, arg, true).with_text(text);
        let outcome = live
            .offering
            .advance(&mut live.session, action.clone(), actor.clone());
        live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        MutationAttempt::Fired(outcome)
    }) {
        MutationAttempt::Fired(outcome) => Driven::Fired(outcome),
        MutationAttempt::NoSession => Driven::NoSession,
        MutationAttempt::StaleSurface => Driven::StaleSurface,
    }
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
    let outcome = with_live::<O, _>(channel, move |live| {
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
        live.record_landed(action, actor, &outcome);
        note_direct_landing::<O>(live, &outcome);
        outcome
    });
    match outcome {
        Some(o) => Driven::Fired(o),
        None => Driven::NoSession,
    }
}

/// Re-verify the channel's committed chain through [`Offering::verify`].
pub fn verify_live<O: DiscordOffering>(channel: u64) -> Option<VerifyReport> {
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
    match verify_live::<O>(channel) {
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
            let msg = CreateInteractionResponseMessage::new().embed(embed);
            let _ = command
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        None => ephemeral(ctx, command, &no_session_text::<O>()).await,
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
                ack::ack_component(ctx, component).await;
                let cast = cast_vote_at::<O>(channel, stamp, actor.clone(), arg);
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

    match drive::<O>(channel, &component.data.custom_id, actor.clone()) {
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
            return;
        }
        let driven = drive_text_at::<O>(channel, stamp, &turn, arg, raw.trim(), actor.clone());
        finish_modal::<O>(ctx, modal, channel, &actor, driven).await;
        return;
    }

    // A NUMERIC submit: the typed value IS the arg.
    let Some((key, stamp, turn)) = parse_submit(&modal.data.custom_id) else {
        return;
    };
    if key != O::KEY {
        return;
    }
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
    let driven = drive_value_at::<O>(channel, stamp, &turn, value, actor.clone());
    finish_modal::<O>(ctx, modal, channel, &actor, driven).await;
}

/// The shared tail of a modal submit: post the move's honest outcome + the re-rendered surface (a
/// landed receipt / a real refusal), or the no-session note.
async fn finish_modal<O: DiscordOffering>(
    ctx: &Context,
    modal: &ModalInteraction,
    channel: u64,
    viewer: &DreggIdentity,
    driven: Driven,
) {
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
            let viewer = viewer.clone();
            let rendered = with_live::<O, _>(channel, move |live| {
                (
                    surface_for::<O>(live, &viewer),
                    live.offering.hidden_information(),
                )
            });
            let msg = match rendered {
                Some(((embed, rows), hidden_information)) => {
                    let rows = if hidden_information { Vec::new() } else { rows };
                    CreateInteractionResponseMessage::new()
                        .content(note)
                        .embed(embed)
                        .components(rows)
                        .ephemeral(hidden_information)
                }
                None => CreateInteractionResponseMessage::new().content(note),
            };
            let _ = modal
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
            // 👑 THE CROWN (modal path): a crowned game's match ending on a modal-landed
            // turn gets the same fold offer as the component path above.
            if matches!(&outcome, Outcome::Landed { ended: true, .. })
                && crate::commands::crown::foldable_key(O::KEY)
            {
                crate::commands::crown::offer_fold(ctx, modal.channel_id, O::KEY).await;
            }
        }
        Driven::StaleSurface => {
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
                .decided("refused", "stale_surface")
                .with_session(channel.to_string())
                .with_offering(O::KEY),
            );
            let _ = modal
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(
                                "That form belongs to a replaced session or earlier state — nothing was fired.",
                            )
                            .ephemeral(true),
                    ),
                )
                .await;
        }
        Driven::NoSession | Driven::NotOurs => {
            let _ = modal
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(no_session_text::<O>())
                            .ephemeral(true),
                    ),
                )
                .await;
        }
        Driven::NeedsValue { .. } | Driven::NeedsText { .. } => {
            let _ = modal
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(
                                "That form did not resolve to a typed move — nothing was fired.",
                            )
                            .ephemeral(true),
                    ),
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
        "**Round {} closed.** The party chose **{}** ({}/{} ballot(s) · {} voter(s) of record).\n{}",
        resolved.round,
        truncate(&resolved.winner.label, 120),
        resolved.tally.winning_votes(),
        resolved.tally.total_votes(),
        resolved.electorate.len(),
        outcome_note(&resolved.outcome),
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
    let rendered = with_live::<O, _>(channel, move |live| channel_surfaces::<O>(live, &viewer));
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
        let _ = component
            .edit_response(
                &ctx.http,
                EditInteractionResponse::new()
                    .content(truncate(note, 1900))
                    .embed(embed)
                    .components(rows),
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
                || crate::commands::portfolio::DISCORD_EXTRA_PLAY_KEYS.contains(key);
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
    }
}
