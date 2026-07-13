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
//! * **present** — an offering's [`Offering::render`] returns a deos [`Surface`] (a
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
//! | id                                | meaning                                            |
//! |-----------------------------------|----------------------------------------------------|
//! | `offering:fire:<key>:<turn>:<arg>`| press → one `advance(Action{turn,arg}, actor)`      |
//! | `offering:ask:<key>:<turn>`       | press → open a modal for the turn's typed value     |
//! | `offering:submit:<key>:<turn>`    | the modal's submit → `advance` with the typed value |
//!
//! `<key>` is [`DiscordOffering::KEY`] (`council`, `market`, …) — the router in `main.rs` sends
//! every `offering:` press here, and [`route_component`] / [`route_modal`] dispatch on the key.
//!
//! ## What is logic-driven vs what needs a live Discord token
//!
//! [`drive`] / [`drive_value`] are the **sync core** of a press: decode the custom-id, resolve
//! the actor, run the real offering turn, hand back the [`Outcome`]. The async handlers
//! ([`handle_component`], [`handle_modal`], [`handle_status`], [`handle_verify`]) are thin
//! serenity wrappers around them. So the tests drive the SAME path a live button press takes —
//! only the HTTP round-trip to Discord is absent.

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    ActionRowComponent, ButtonStyle, CommandInteraction, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateEmbed, CreateEmbedFooter, CreateInputText,
    CreateInteractionResponse, CreateInteractionResponseMessage, CreateModal, InputTextStyle,
    ModalInteraction,
};

use dreggnet_offerings::{
    Action, CollectiveDecision, DreggIdentity, Offering, Outcome, SessionConfig, Surface, Tally,
    VerifyReport, VoteCount,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;

/// The custom-id namespace every offering component press lives in (`main.rs` routes on it).
pub const PREFIX: &str = "offering";
/// The modal input field carrying an affordance's typed value (a reserve price, a sealed bid).
pub const VALUE_FIELD: &str = "value";

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

/// A turn whose [`Action::label`] is a **free-text string the user supplies** (a Hermes prompt, a
/// document edit's text) rather than a numeric arg — rendered as a button that opens a Discord
/// modal collecting text. Where a [`ValuePrompt`]'s modal value is parsed to `i64` and fired via
/// [`drive_value`], a text prompt's raw string rides the [`Action::label`] and fires via
/// [`drive_text`] (the affordance wire carries no string payload, so the label is where it goes).
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
/// never moves. Only the *offering* (`O: Send` — a council's electorate/catalog/quorum) and the
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
pub trait DiscordOffering: Offering + Send + Sized + 'static
where
    Self::Session: 'static,
{
    /// The offering's key in the custom-id wire (`council`, `market`).
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
/// surfaced, never faked). The session is BORN on the store's thread, where it then lives.
/// Replaces any session already open in the channel.
pub fn open_in<O: DiscordOffering>(
    channel: u64,
    offering: O,
    cfg: SessionConfig,
) -> Result<(), dreggnet_offerings::OfferingError> {
    O::store().run(move |sessions| {
        let session = offering.open(cfg)?;
        // A collective offering opens with a live round over the session's first actions (an open
        // crowd — a restricted electorate is set with [`open_round`]); a direct offering has none.
        let round = if O::collective() {
            Some(CollectiveRound::new(0, offering.actions(&session), None))
        } else {
            None
        };
        sessions.insert(
            channel,
            Live {
                offering,
                session,
                round,
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
            live.round = Some(CollectiveRound::new(0, options, electorate));
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

/// **Close the collective round: resolve its plurality winner as ONE real crowd turn.** Tallies
/// the write-once ballots, drives the winning [`Action`] through [`Offering::advance_collective`]
/// carrying the full [`CollectiveDecision`] (the voters of record + the [`Tally`] + the carrier),
/// and opens the next round over the resulting state (preserving the electorate restriction). A
/// landed move records a real `TurnReceipt`; a refused one commits nothing (anti-ghost). This is
/// the collective analogue of a single-press resolution — many pressers, one refereed turn.
#[allow(dead_code)]
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
        let decision = CollectiveDecision::new(electorate.clone(), carrier, tally.clone());
        let outcome = live
            .offering
            .advance_collective(&mut live.session, winner.clone(), decision);

        // Open the next round over the new state, keeping any electorate restriction.
        let next_options = live.offering.actions(&live.session);
        live.round = Some(CollectiveRound::with_electorate(
            round_no + 1,
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
        /// The affordance verb whose value the modal collects.
        turn: String,
    },
    /// The affordance needs a **free-text** value AND carries its own `arg`: open the text modal
    /// for `(turn, arg)`. Unlike [`Ask`](Press::Ask), a text affordance's `arg` is distinct from
    /// its text (a document insert's anchor position + its prose), so the wire carries both.
    AskText {
        /// The offering key.
        key: String,
        /// The affordance verb whose text the modal collects.
        turn: String,
        /// The affordance argument (the anchor/cell the text applies to).
        arg: i64,
    },
}

/// The custom-id of a fixed-arg affordance button.
pub fn fire_id(key: &str, turn: &str, arg: i64) -> String {
    format!("{PREFIX}:fire:{key}:{turn}:{arg}")
}

/// The custom-id of a numeric-value-taking affordance button (opens the value modal).
pub fn ask_id(key: &str, turn: &str) -> String {
    format!("{PREFIX}:ask:{key}:{turn}")
}

/// The custom-id of a text-taking affordance button carrying its `arg` (opens the text modal).
pub fn askt_id(key: &str, turn: &str, arg: i64) -> String {
    format!("{PREFIX}:askt:{key}:{turn}:{arg}")
}

/// The custom-id of the modal that collects `turn`'s numeric value.
pub fn submit_id(key: &str, turn: &str) -> String {
    format!("{PREFIX}:submit:{key}:{turn}")
}

/// The custom-id of the modal that collects `turn`'s free text, carrying its `arg` back.
pub fn subt_id(key: &str, turn: &str, arg: i64) -> String {
    format!("{PREFIX}:subt:{key}:{turn}:{arg}")
}

/// Decode a component press. `None` for any id that is not ours.
pub fn parse_press(custom_id: &str) -> Option<Press> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "fire", key, turn, arg] => Some(Press::Fire {
            key: (*key).to_string(),
            turn: (*turn).to_string(),
            arg: arg.parse().ok()?,
        }),
        [PREFIX, "ask", key, turn] => Some(Press::Ask {
            key: (*key).to_string(),
            turn: (*turn).to_string(),
        }),
        [PREFIX, "askt", key, turn, arg] => Some(Press::AskText {
            key: (*key).to_string(),
            turn: (*turn).to_string(),
            arg: arg.parse().ok()?,
        }),
        _ => None,
    }
}

/// Decode a **numeric** modal submit id into `(key, turn)`. `None` for any id that is not ours.
pub fn parse_submit(custom_id: &str) -> Option<(String, String)> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "submit", key, turn] => Some(((*key).to_string(), (*turn).to_string())),
        _ => None,
    }
}

/// Decode a **text** modal submit id into `(key, turn, arg)`. `None` for any id that is not ours.
pub fn parse_text_submit(custom_id: &str) -> Option<(String, String, i64)> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "subt", key, turn, arg] => {
            Some(((*key).to_string(), (*turn).to_string(), arg.parse().ok()?))
        }
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
            .map(|(k, _)| k)
            .or_else(|| parse_text_submit(custom_id).map(|(k, _, _)| k)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — the offering's own deos Surface → a Discord embed + affordance buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// The offering's [`Surface`] (its deos `ViewNode`) rendered to a Discord embed through the
/// `deos_view::discord` backend — the SAME renderer the desktop/web/framebuffer backends are
/// peers of. We take the embed only: the components come from [`action_rows`] (see the module
/// doc — a Discord custom-id must carry the offering key and route a value-taking affordance to
/// its modal, which the generic `deosturn:` card id cannot).
pub fn embed_of<O: DiscordOffering>(live: &Live<O>) -> CreateEmbed {
    let surface: Surface = live.offering.render(&live.session);
    let card = deos_view::discord::render_card(O::TITLE, surface.view(), &[]);
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

/// The affordance buttons for the session's current [`Offering::actions`], chunked into Discord
/// rows (≤5 × ≤5).
///
/// * an **eligible** action → a primary button firing `(turn, arg)`;
/// * an action whose turn takes a **typed value** → a button that opens its modal;
/// * an **ineligible** action → `🔒`, danger-styled, and **still pressable**: the cap tooth is
///   shown, not hidden, and the press surfaces the executor's own [`Outcome::Refused`] rather
///   than the frontend pretending to be the gate.
pub fn action_rows<O: DiscordOffering>(actions: &[Action]) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for chunk in actions.chunks(5).take(5) {
        let mut buttons: Vec<CreateButton> = Vec::new();
        for a in chunk {
            let id = if O::text_prompt(&a.turn).is_some() {
                // A text affordance carries its own arg (a doc insert's anchor) beside the text.
                askt_id(O::KEY, &a.turn, a.arg)
            } else if O::value_prompt(&a.turn).is_some() {
                ask_id(O::KEY, &a.turn)
            } else {
                fire_id(O::KEY, &a.turn, a.arg)
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
    rows
}

/// The full surface of a channel's live session: embed + affordance rows.
pub fn surface_of<O: DiscordOffering>(live: &Live<O>) -> (CreateEmbed, Vec<CreateActionRow>) {
    let actions = live.offering.actions(&live.session);
    (embed_of(live), action_rows::<O>(&actions))
}

/// The modal that collects a value-taking affordance's typed arg.
pub fn value_modal<O: DiscordOffering>(turn: &str, prompt: ValuePrompt) -> CreateModal {
    CreateModal::new(submit_id(O::KEY, turn), prompt.title).components(vec![
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
pub fn text_modal<O: DiscordOffering>(turn: &str, arg: i64, prompt: TextPrompt) -> CreateModal {
    let style = if prompt.paragraph {
        InputTextStyle::Paragraph
    } else {
        InputTextStyle::Short
    };
    CreateModal::new(subt_id(O::KEY, turn, arg), prompt.title).components(vec![
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
            format!("**A verified turn landed.** `turn_hash {h}…`{tail}")
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
        /// The affordance verb whose value the modal collects.
        turn: String,
        /// The prompt to render.
        prompt: ValuePrompt,
    },
    /// The affordance takes free text: the frontend must open this text modal (carrying `arg`).
    NeedsText {
        /// The affordance verb whose text the modal collects.
        turn: String,
        /// The affordance argument (the anchor/cell the text applies to).
        arg: i64,
        /// The text prompt to render.
        prompt: TextPrompt,
    },
    /// No session of this offering is open in the channel.
    NoSession,
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
        Press::Ask { key, turn } if key == O::KEY => match O::value_prompt(&turn) {
            Some(prompt) => Driven::NeedsValue { turn, prompt },
            // A value-less turn addressed as `ask` — fire it with arg 0 rather than dead-ending.
            None => drive_value::<O>(channel, &turn, 0, actor),
        },
        Press::AskText { key, turn, arg } if key == O::KEY => match O::text_prompt(&turn) {
            Some(prompt) => Driven::NeedsText { turn, arg, prompt },
            // A text-less turn addressed as `askt` — fire it with its arg rather than dead-ending.
            None => drive_value::<O>(channel, &turn, arg, actor),
        },
        Press::Fire { key, turn, arg } if key == O::KEY => {
            drive_value::<O>(channel, &turn, arg, actor)
        }
        _ => Driven::NotOurs,
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
        live.offering.advance(&mut live.session, action, actor)
    });
    match outcome {
        Some(o) => Driven::Fired(o),
        None => Driven::NoSession,
    }
}

/// **Drive a text-taking affordance** — the free-text modal-submit path. The typed string rides
/// the [`Action::label`] (the affordance wire carries no string payload); ONE real offering turn,
/// attributed to the presser's dregg identity. (A Hermes prompt, a document edit's text.)
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
        // The typed text is the label; `arg` is the affordance's own (a doc insert's anchor), and
        // `enabled` is decoration — the substrate is the sole referee of what lands.
        let action = Action::new(text, turn, arg, true);
        live.offering.advance(&mut live.session, action, actor)
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

/// Post the channel's live surface (embed + affordance buttons) as the command response.
pub async fn handle_status<O: DiscordOffering>(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
    match rendered {
        Some((embed, rows)) => {
            let msg = CreateInteractionResponseMessage::new()
                .embed(embed)
                .components(rows);
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

    // COLLECTIVE MODE: a press is a write-once VOTE, not an immediate turn. Cast the ballot for
    // the pressed option's arg and ack it ephemerally; the plurality winner is resolved later by
    // a round close ([`handle_close`]). Direct offerings fall through to the 1-press-1-turn path.
    if O::collective() {
        if let Some(Press::Fire { arg, .. }) = parse_press(&component.data.custom_id) {
            let cast = cast_vote::<O>(channel, actor, arg);
            component_ephemeral(ctx, component, &cast_note(cast)).await;
        }
        return;
    }

    match drive::<O>(channel, &component.data.custom_id, actor) {
        Driven::NeedsValue { turn, prompt } => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Modal(value_modal::<O>(&turn, prompt)),
                )
                .await;
        }
        Driven::NeedsText { turn, arg, prompt } => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Modal(text_modal::<O>(&turn, arg, prompt)),
                )
                .await;
        }
        Driven::Fired(outcome) => {
            update_surface::<O>(ctx, component, channel, &outcome_note(&outcome)).await;
        }
        Driven::NoSession => {
            component_ephemeral(ctx, component, &no_session_text::<O>()).await;
        }
        Driven::NotOurs => {}
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
    if let Some((key, turn, arg)) = parse_text_submit(&modal.data.custom_id) {
        if key != O::KEY {
            return;
        }
        let driven = drive_text::<O>(channel, &turn, arg, raw.trim(), actor);
        finish_modal::<O>(ctx, modal, channel, driven).await;
        return;
    }

    // A NUMERIC submit: the typed value IS the arg.
    let Some((key, turn)) = parse_submit(&modal.data.custom_id) else {
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
    let driven = drive_value::<O>(channel, &turn, value, actor);
    finish_modal::<O>(ctx, modal, channel, driven).await;
}

/// The shared tail of a modal submit: post the move's honest outcome + the re-rendered surface (a
/// landed receipt / a real refusal), or the no-session note.
async fn finish_modal<O: DiscordOffering>(
    ctx: &Context,
    modal: &ModalInteraction,
    channel: u64,
    driven: Driven,
) {
    match driven {
        Driven::Fired(outcome) => {
            let note = outcome_note(&outcome);
            let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
            let msg = match rendered {
                Some((embed, rows)) => CreateInteractionResponseMessage::new()
                    .content(note)
                    .embed(embed)
                    .components(rows),
                None => CreateInteractionResponseMessage::new().content(note),
            };
            let _ = modal
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        _ => {
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
    }
}

/// **Close a collective round** (a `/<offering> close`): resolve the plurality winner as ONE real
/// crowd turn and post the honest outcome + the next round's surface. The collective analogue of
/// [`handle_component`]'s single-press resolution. Reachable once a collective offering registers
/// a close subcommand; today the driven tests + the dungeon adapter exercise [`close_round`].
#[allow(dead_code)]
pub async fn handle_close<O: DiscordOffering>(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    match close_round::<O>(channel) {
        CollectiveClose::Resolved(resolved) => {
            let note = format!(
                "**Round {} closed.** The party chose **{}** ({}/{} ballot(s)).\n{}",
                resolved.round,
                truncate(&resolved.winner.label, 120),
                resolved.tally.winning_votes(),
                resolved.tally.total_votes(),
                outcome_note(&resolved.outcome),
            );
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
        CollectiveClose::NoRound | CollectiveClose::NoSession => {
            ephemeral(ctx, command, &no_session_text::<O>()).await
        }
    }
}

/// Re-render the channel's surface into the pressed message, with the move's honest outcome.
async fn update_surface<O: DiscordOffering>(
    ctx: &Context,
    component: &ComponentInteraction,
    channel: u64,
    note: &str,
) {
    let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
    let Some((embed, rows)) = rendered else {
        component_ephemeral(ctx, component, &no_session_text::<O>()).await;
        return;
    };
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
}

fn no_session_text<O: DiscordOffering>() -> String {
    format!(
        "No {} session is open in this channel. Start one with `/{} open`.",
        O::KEY,
        O::KEY
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

async fn component_ephemeral(ctx: &Context, component: &ComponentInteraction, text: &str) {
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

/// Dispatch an `offering:` component press to the offering that owns the key.
pub async fn route_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let Some(key) = key_of(&component.data.custom_id) else {
        return;
    };
    match key.as_str() {
        k if k == <dreggnet_council::CouncilOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_council::CouncilOffering>(ctx, component, state).await
        }
        k if k == <dreggnet_market::MarketOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_market::MarketOffering>(ctx, component, state).await
        }
        k if k == <dreggnet_hermes::HermesOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_hermes::HermesOffering>(ctx, component, state).await
        }
        k if k == <dreggnet_grain::GrainOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_grain::GrainOffering>(ctx, component, state).await
        }
        k if k == <dreggnet_doc::DocOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_doc::DocOffering>(ctx, component, state).await
        }
        _ => {}
    }
}

/// Dispatch an `offering:` modal submit to the offering that owns the key.
pub async fn route_modal(ctx: &Context, modal: &ModalInteraction, state: &BotState) {
    let Some(key) = key_of(&modal.data.custom_id) else {
        return;
    };
    match key.as_str() {
        k if k == <dreggnet_council::CouncilOffering as DiscordOffering>::KEY => {
            handle_modal::<dreggnet_council::CouncilOffering>(ctx, modal, state).await
        }
        k if k == <dreggnet_market::MarketOffering as DiscordOffering>::KEY => {
            handle_modal::<dreggnet_market::MarketOffering>(ctx, modal, state).await
        }
        k if k == <dreggnet_hermes::HermesOffering as DiscordOffering>::KEY => {
            handle_modal::<dreggnet_hermes::HermesOffering>(ctx, modal, state).await
        }
        k if k == <dreggnet_doc::DocOffering as DiscordOffering>::KEY => {
            handle_modal::<dreggnet_doc::DocOffering>(ctx, modal, state).await
        }
        _ => {}
    }
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
        let fire = fire_id("council", "approve", 2);
        assert_eq!(fire, "offering:fire:council:approve:2");
        assert_eq!(
            parse_press(&fire),
            Some(Press::Fire {
                key: "council".into(),
                turn: "approve".into(),
                arg: 2
            })
        );

        let ask = ask_id("market", "bid");
        assert_eq!(ask, "offering:ask:market:bid");
        assert_eq!(
            parse_press(&ask),
            Some(Press::Ask {
                key: "market".into(),
                turn: "bid".into()
            })
        );

        assert_eq!(
            parse_submit(&submit_id("market", "list")),
            Some(("market".into(), "list".into()))
        );

        assert_eq!(key_of(&fire).as_deref(), Some("council"));
        assert_eq!(key_of(&ask).as_deref(), Some("market"));
        assert_eq!(
            key_of(&submit_id("market", "list")).as_deref(),
            Some("market")
        );
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
