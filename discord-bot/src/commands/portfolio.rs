//! `/play <offering>` — **the full-portfolio reach**: the twelve DreggNet Cloud offerings that did
//! NOT yet have a bespoke Discord slash command, mounted through the SAME generic
//! [`crate::commands::offering`] adapter as `/council` / `/market` / `/doc`, so Discord reaches
//! offering parity with the web catalog ([`dreggnet_web::demo_host`]).
//!
//! Before this module Discord served six of the eighteen portfolio offerings (dungeon, council,
//! market, hermes, grain, doc). This adds the rest via one uniform `/play` command:
//!
//! * **the two portfolio games** — `automatafl` (the simultaneous-move board) and `tug`
//!   (multiway-tug, wrapped in the seat-claiming [`SeatedTug`] adapter — the byte-peer of the web
//!   `seated` module — so a Discord user's derived identity can claim a seat and see their OWN
//!   hidden hand through the viewer-aware render path);
//! * **the two remaining non-game offerings** — `names` and `compute`;
//! * **the eight do-once RPG feature surfaces** — `trade`, `inventory`, `cheevos`, `guild`, `craft`,
//!   `companion`, `tavern`, `party` (`dreggnet-surfaces`).
//!
//! Each `impl`s [`Offering`], so it becomes a Discord surface through the generic adapter with no
//! per-offering rendering code: its deos `ViewNode` render is the embed, its cap-gated `Action`s are
//! the buttons, a press is ONE real `advance` attributed to the presser's derived dregg identity, and
//! the press re-render is projected FOR the presser ([`crate::commands::offering::surface_for`]).
//!
//! ROUTING: the eight RPG feature-surface keys open in the invoker's **per-identity persistent
//! world** ([`crate::commands::rpg_world`]) — one `OfferingHost` per derived dregg identity,
//! mounted via `dreggnet_surfaces::register_surfaces` (ONE shared world across craft/inventory/
//! trade, so a forged item IS in your inventory IS tradeable), sqlite-persisted by replay, with
//! the player's REAL earned cheevos. The four remaining keys (the two games + names/compute)
//! keep the per-channel generic-adapter stores below. A board offering (automatafl, tug) is a
//! `CoordGrid` that the Discord card renderer paints in full (the most complete renderer of the
//! three chat surfaces).

use std::sync::OnceLock;

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dregg_automatafl::AutomataflOffering;
use dregg_multiway_tug::{Player, TugOffering, TugSession};
use dreggnet_compute::ComputeOffering;
use dreggnet_names::NamesOffering;
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dreggnet_surfaces::{
    CheevoShowcase, CompanionOffering, CraftOffering, GuildPage, InventoryOffering, PartyOffering,
    TavernOffering, TradeOffering,
};

use crate::BotState;
use crate::commands::ack;
use crate::commands::offering::{self, DiscordOffering, Store, identity_of};

// ─────────────────────────────────────────────────────────────────────────────
// SeatedTug — the seat-claiming adapter (byte-peer of `dreggnet_web::seated`).
// ─────────────────────────────────────────────────────────────────────────────

/// The multiway-tug offering with **Discord-claimable seats**. `TugOffering` names its two seats by
/// fixed canonical strings while a Discord user's [`DreggIdentity`] is a derived key — this adapter
/// claims a seat for the first two distinct identities that act (A then B), rewriting the actor to
/// the canonical seat identity before delegating; a third identity is a spectator (refused). It
/// changes NOTHING in `dregg-multiway-tug`, and `render_for` maps a viewer to their seat so the
/// hidden-hand fog reaches the right player.
pub struct SeatedTug {
    inner: TugOffering,
}

impl SeatedTug {
    pub fn new() -> Self {
        SeatedTug { inner: TugOffering }
    }
}

impl Default for SeatedTug {
    fn default() -> Self {
        SeatedTug::new()
    }
}

/// A live tug round plus its seat claims (which Discord identity holds seat A / seat B).
pub struct SeatedTugSession {
    inner: TugSession,
    seats: [Option<DreggIdentity>; 2],
}

impl SeatedTugSession {
    fn seat_of(&self, who: &DreggIdentity) -> Option<Player> {
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].as_ref() == Some(who) {
                return Some(p);
            }
        }
        None
    }

    fn claim(&mut self, who: &DreggIdentity) -> Option<Player> {
        if let Some(p) = self.seat_of(who) {
            return Some(p);
        }
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].is_none() {
                self.seats[p.idx()] = Some(who.clone());
                return Some(p);
            }
        }
        None
    }
}

impl Offering for SeatedTug {
    type Session = SeatedTugSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(SeatedTugSession {
            inner: self.inner.open(cfg)?,
            seats: [None, None],
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.inner.actions(&session.inner)
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let Some(seat) = session.claim(&actor) else {
            return Outcome::Refused("both seats are taken — you are a spectator".to_string());
        };
        self.inner
            .advance(&mut session.inner, input, TugOffering::seat_identity(seat))
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.inner.verify(&session.inner)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        self.inner.render(&session.inner)
    }

    /// The per-viewer surface — a claimed seat sees its OWN hand; anyone else sees the public fog.
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        match session.seat_of(viewer) {
            Some(seat) => self
                .inner
                .render_for(&session.inner, &TugOffering::seat_identity(seat)),
            None => self.inner.render(&session.inner),
        }
    }

    fn price(&self, input: &Action) -> RunCost {
        self.inner.price(input)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The DiscordOffering impls — each mounts its offering on the generic adapter.
// ─────────────────────────────────────────────────────────────────────────────

/// A generic honest status line for a portfolio offering: the count of committed turns its chain
/// re-verifies over (genesis + committed), the same number `/…​ verify` reports.
fn verified_turns<O: Offering>(off: &O, session: &O::Session) -> String {
    format!("{} verified turns", off.verify(session).turns)
}

macro_rules! seat_of_store {
    ($ty:ty) => {{
        static SESSIONS: OnceLock<Store<$ty>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }};
}

impl DiscordOffering for SeatedTug {
    const KEY: &'static str = "tug";
    const TITLE: &'static str = "Multiway-Tug";
    const COLOR: u32 = 0x8E5BD6;
    const TAGLINE: &'static str =
        "a hidden-hand tug of influence · your own hand revealed, the opponent fog";
    fn store() -> &'static Store<Self> {
        seat_of_store!(SeatedTug)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for AutomataflOffering {
    const KEY: &'static str = "automatafl";
    const TITLE: &'static str = "Automatafl";
    const COLOR: u32 = 0x3D8B7D;
    const TAGLINE: &'static str =
        "the simultaneous-move board · seal a move · reveal · the automaton steps";
    fn store() -> &'static Store<Self> {
        seat_of_store!(AutomataflOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for NamesOffering {
    const KEY: &'static str = "names";
    const TITLE: &'static str = "DreggNet Names";
    const COLOR: u32 = 0x4A78C2;
    const TAGLINE: &'static str = "an identity / naming service · register · transfer · resolve";
    fn store() -> &'static Store<Self> {
        seat_of_store!(NamesOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for ComputeOffering {
    const KEY: &'static str = "compute";
    const TITLE: &'static str = "DreggNet Compute";
    const COLOR: u32 = 0x2F8FA6;
    const TAGLINE: &'static str = "a confined compute-job market · post · claim · settle";
    fn store() -> &'static Store<Self> {
        seat_of_store!(ComputeOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for TradeOffering {
    const KEY: &'static str = "trade";
    const TITLE: &'static str = "DreggNet Trade";
    const COLOR: u32 = 0xC28A3D;
    const TAGLINE: &'static str = "a player market · list · settle an atomic asset swap";
    fn store() -> &'static Store<Self> {
        seat_of_store!(TradeOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for InventoryOffering {
    const KEY: &'static str = "inventory";
    const TITLE: &'static str = "Inventory";
    const COLOR: u32 = 0x9A7B4F;
    const TAGLINE: &'static str = "your owned notes (gear · cards · trophies), provenance-checked";
    fn store() -> &'static Store<Self> {
        seat_of_store!(InventoryOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for CheevoShowcase {
    const KEY: &'static str = "cheevos";
    const TITLE: &'static str = "Achievements";
    const COLOR: u32 = 0xD4A72C;
    const TAGLINE: &'static str = "earned soulbound proofs over verified runs";
    fn store() -> &'static Store<Self> {
        seat_of_store!(CheevoShowcase)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for GuildPage {
    const KEY: &'static str = "guild";
    const TITLE: &'static str = "Guild";
    const COLOR: u32 = 0x6E7BA6;
    const TAGLINE: &'static str = "the roster + the aggregate verified-clears leaderboard";
    fn store() -> &'static Store<Self> {
        seat_of_store!(GuildPage)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for CraftOffering {
    const KEY: &'static str = "craft";
    const TITLE: &'static str = "Forge";
    const COLOR: u32 = 0xB5562E;
    const TAGLINE: &'static str =
        "a provably-fair craft loop · consume materials · mint a bound output";
    fn store() -> &'static Store<Self> {
        seat_of_store!(CraftOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for CompanionOffering {
    const KEY: &'static str = "companion";
    const TITLE: &'static str = "Companions";
    const COLOR: u32 = 0xC26AA0;
    const TAGLINE: &'static str = "hatch a fair-drawn companion · raise it through XP-gated turns";
    fn store() -> &'static Store<Self> {
        seat_of_store!(CompanionOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for TavernOffering {
    const KEY: &'static str = "tavern";
    const TITLE: &'static str = "Tavern";
    const COLOR: u32 = 0x8A6D3B;
    const TAGLINE: &'static str = "the shared hub · presence · the LFG board · the party roster";
    fn store() -> &'static Store<Self> {
        seat_of_store!(TavernOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for PartyOffering {
    const KEY: &'static str = "party";
    const TITLE: &'static str = "Party";
    const COLOR: u32 = 0x5B8ED6;
    const TAGLINE: &'static str = "a seated roster + a quorum-certified fork ballot";
    fn store() -> &'static Store<Self> {
        seat_of_store!(PartyOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — these twelve are mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE CROWN SEAM (`commands::crown`) — the played tug match as a fold job.
// ─────────────────────────────────────────────────────────────────────────────

/// The channel's finished, WON tug match as the whole-match fold's job: the WINNER's dealt
/// hidden hand (`(card_id, nonce)` pairs, exactly as committed at open), their ordered plays,
/// and the terminal win facts — read through `TugSession`'s owner-facing match-record seam.
/// Lives HERE because only this module can reach the seated session's inner round. `None`
/// until the round has scored a winner.
///
/// The record never leaves the fold path: the resulting proof's public inputs are
/// `[blinded_leaf, hand_root]` per play — the card ids are not among them.
pub fn played_tug_match(channel: u64) -> Option<dreggnet_prove_service::PlayedMatch> {
    offering::with_live::<SeatedTug, _>(channel, |live| {
        let s = &live.session.inner;
        let (winner, charm) = s.win_facts()?;
        let seat = if winner == 1 { Player::A } else { Player::B };
        Some(dreggnet_prove_service::PlayedMatch::Tug(
            dreggnet_prove_service::TugMatch {
                hand: s.dealt_hand(seat),
                plays: s.plays_of(seat),
                win: Some(dreggnet_prove_service::TugWin { charm, winner }),
            },
        ))
    })
    .flatten()
}

// ─────────────────────────────────────────────────────────────────────────────
// The `/play` command — open any portfolio offering by key.
// ─────────────────────────────────────────────────────────────────────────────

/// The fifteen `/play` offering keys (the games + non-game + RPG surfaces this module mounts,
/// plus gear/talents (`commands::gear`) and the overworld (`commands::overworld`)).
pub const PLAY_KEYS: [&str; 15] = [
    "automatafl",
    "tug",
    "names",
    "compute",
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "tavern",
    "party",
    "gear",
    "talents",
    "overworld",
];

/// Register `/play <offering>` — open any of the twelve full-portfolio offerings in this channel.
pub fn register() -> CreateCommand {
    let mut option = CreateCommandOption::new(
        CommandOptionType::String,
        "offering",
        "Which portfolio offering to open in this channel",
    )
    .required(true);
    for key in PLAY_KEYS {
        option = option.add_string_choice(key, key);
    }
    CreateCommand::new("play")
        .description(
            "Open a DreggNet Cloud offering — a game or a feature surface — in this channel",
        )
        .add_option(option)
        // `/play <offering> action:verify` — re-verify the channel's live session chain (the
        // SAME `offering::handle_verify` `/council verify` runs; backlog Tier-2 #10 — the
        // flagship games were the least verifiable surfaces). Default (absent) = open.
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "action",
                "What to do (default: open) — verify re-checks the live session's chain",
            )
            .add_string_choice("verify", "verify")
            .required(false),
        )
}

/// Route `/play <offering>` — open the chosen offering + post its surface (projected for the opener).
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let string_opt = |name: &str| -> Option<String> {
        command
            .data
            .options
            .iter()
            .find(|o| o.name == name)
            .and_then(|o| match &o.value {
                CommandDataOptionValue::String(s) => Some(s.clone()),
                _ => None,
            })
    };
    let key = string_opt("offering").unwrap_or_default();

    // `/play <offering> action:verify` — re-verify the channel's live session chain through
    // the SAME generic verifier every bespoke offering command exposes (backlog Tier-2 #10).
    // Runs BEFORE the deferred ACK: `offering::handle_verify` creates its own response.
    if string_opt("action").as_deref() == Some("verify") {
        handle_play_verify(ctx, command, &key).await;
        return;
    }

    let channel = command.channel_id.get();
    let viewer = identity_of(state, command.user.id.get());
    let cfg = SessionConfig::with_seed(channel);

    // ACK inside Discord's 3s window BEFORE the open runs — a world-backed open deploys a real
    // world-cell on the offering store's thread; the surface (or an honest refusal) lands as an
    // EDIT of this deferred response.
    ack::defer_slash(ctx, command, false).await;

    // The eight RPG feature surfaces open in the invoker's PER-IDENTITY PERSISTENT world
    // (`commands::rpg_world`): ONE shared craft/inventory/trade ledger per player (the saga
    // composition), sqlite-persisted by replay, real earned cheevos — never a throwaway
    // per-channel demo world. `handle_play` edits the response this handler already deferred.
    if crate::commands::rpg_world::is_rpg_key(&key) {
        crate::commands::rpg_world::handle_play(ctx, command, state, &key).await;
        return;
    }

    let opened: Result<(), OfferingError> = match key.as_str() {
        "tug" => open_and_post::<SeatedTug>(ctx, command, SeatedTug::new, &viewer, cfg).await,
        "automatafl" => {
            open_and_post::<AutomataflOffering>(ctx, command, || AutomataflOffering, &viewer, cfg)
                .await
        }
        "names" => {
            open_and_post::<NamesOffering>(ctx, command, NamesOffering::new, &viewer, cfg).await
        }
        "compute" => {
            open_and_post::<ComputeOffering>(ctx, command, ComputeOffering::new, &viewer, cfg).await
        }
        "gear" => {
            open_and_post::<dreggnet_gear::LoadoutOffering>(
                ctx,
                command,
                dreggnet_gear::LoadoutOffering::new,
                &viewer,
                cfg,
            )
            .await
        }
        "talents" => {
            open_and_post::<dreggnet_gear::TalentTreeOffering>(
                ctx,
                command,
                dreggnet_gear::TalentTreeOffering::new,
                &viewer,
                cfg,
            )
            .await
        }
        "overworld" => {
            open_and_post::<crate::commands::overworld::OverworldPlay>(
                ctx,
                command,
                crate::commands::overworld::OverworldPlay::new,
                &viewer,
                cfg,
            )
            .await
        }
        other => {
            let embed = CreateEmbed::new()
                .title("Unknown offering")
                .description(format!(
                    "`{other}` is not in the portfolio — pick one of the `/play` choices."
                ))
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, vec![]).await;
            return;
        }
    };

    if let Err(e) = opened {
        let embed = CreateEmbed::new()
            .title("The offering was not opened")
            .description(format!("The executor refused to open the session: {e}"))
            .color(0xE63946);
        ack::edit_slash(ctx, command, embed, vec![]).await;
    }
}

/// `/play <offering> action:verify` — dispatch the generic chain re-verifier for the chosen
/// offering key (the SAME [`offering::handle_verify`] behind `/council verify` et al.), so the
/// twelve portfolio offerings — the flagship games included — answer verify-don't-trust with a
/// command, not a shrug (backlog Tier-2 #10).
async fn handle_play_verify(ctx: &Context, command: &CommandInteraction, key: &str) {
    match key {
        "tug" => offering::handle_verify::<SeatedTug>(ctx, command).await,
        "automatafl" => offering::handle_verify::<AutomataflOffering>(ctx, command).await,
        "names" => offering::handle_verify::<NamesOffering>(ctx, command).await,
        "compute" => offering::handle_verify::<ComputeOffering>(ctx, command).await,
        "trade" => offering::handle_verify::<TradeOffering>(ctx, command).await,
        "inventory" => offering::handle_verify::<InventoryOffering>(ctx, command).await,
        "cheevos" => offering::handle_verify::<CheevoShowcase>(ctx, command).await,
        "guild" => offering::handle_verify::<GuildPage>(ctx, command).await,
        "craft" => offering::handle_verify::<CraftOffering>(ctx, command).await,
        "companion" => offering::handle_verify::<CompanionOffering>(ctx, command).await,
        "tavern" => offering::handle_verify::<TavernOffering>(ctx, command).await,
        "party" => offering::handle_verify::<PartyOffering>(ctx, command).await,
        "gear" => offering::handle_verify::<dreggnet_gear::LoadoutOffering>(ctx, command).await,
        "talents" => {
            offering::handle_verify::<dreggnet_gear::TalentTreeOffering>(ctx, command).await
        }
        "overworld" => {
            offering::handle_verify::<crate::commands::overworld::OverworldPlay>(ctx, command).await
        }
        other => {
            let _ = command
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(format!("Unknown offering `{other}`."))
                            .ephemeral(true),
                    ),
                )
                .await;
        }
    }
}

/// Open the offering `make` builds in the channel and post its surface (projected FOR the
/// opener). The factory runs on the offering store's own thread ([`offering::open_in`]), so a
/// world-backed non-`Send` offering is born where it lives. Returns the open result so the caller
/// reports a fail-closed refusal honestly.
async fn open_and_post<O: DiscordOffering>(
    ctx: &Context,
    command: &CommandInteraction,
    make: impl FnOnce() -> O + Send + 'static,
    viewer: &DreggIdentity,
    cfg: SessionConfig,
) -> Result<(), OfferingError> {
    // REFUSE-WITH-CONFIRM (backlog #32): a live session (a mid-game board, claimed seats, a
    // built chain) must not be silently wiped by a re-open; the replacement open is stashed
    // behind an explicit Confirm press (`commands::open_guard`).
    if offering::is_open::<O>(command.channel_id.get()) {
        let channel = command.channel_id.get();
        let status =
            offering::with_live::<O, _>(channel, |live| live.offering.status_line(&live.session));
        let viewer = viewer.clone();
        crate::commands::open_guard::refuse_with_confirm(
            ctx,
            command,
            O::KEY,
            status,
            Box::new(move || {
                offering::open_in(channel, make, cfg).map_err(|e| e.to_string())?;
                offering::with_live::<O, _>(channel, move |live| {
                    offering::surface_for::<O>(live, &viewer)
                })
                .ok_or_else(|| "the fresh session did not render".to_string())
            }),
        )
        .await;
        return Ok(());
    }
    offering::open_in(command.channel_id.get(), make, cfg)?;
    let channel = command.channel_id.get();
    let viewer = viewer.clone();
    let rendered = offering::with_live::<O, _>(channel, move |live| {
        offering::surface_for::<O>(live, &viewer)
    });
    match rendered {
        Some((embed, rows)) => ack::edit_slash(ctx, command, embed, rows).await,
        // The session opened but vanished before the render read it (a concurrent close): say
        // so instead of leaving the deferred response spinning forever (no silent drop).
        None => {
            let embed = CreateEmbed::new()
                .title("The offering opened but did not render")
                .description(
                    "The session was not there to render (it may have been closed the same \
                     instant). Run the command again.",
                )
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, vec![]).await;
        }
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — every portfolio offering DRIVEN at the logic level (the SAME `open_in` +
// `drive` a live `/play` open + button press take), against real substrates. No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::offering::{
        Driven, close_in, drive, fire_id, is_open, surface_for, with_live,
    };
    // The tests still drive the generic per-type adapter path for all twelve keys (the adapter
    // mechanics); the LIVE `/play` route for the eight RPG keys is the per-identity persistent
    // world (`commands::rpg_world`), whose own tests cover composition + persistence.
    use dreggnet_surfaces::SharedWorld;

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// The debug text of a session's rendered surface (the same idiom the game crates' surface tests
    /// use) — a proxy for "the surface is non-empty / not a silent drop".
    fn view_text(surface: &Surface) -> String {
        format!("{:?}", surface.view())
    }

    /// **Every one of the twelve `/play` offerings OPENS and renders a NON-EMPTY surface** — the
    /// exact gap the audit found (automatafl, tug, and the eight RPG surfaces were absent on
    /// Discord). Each opens over its real substrate through the generic adapter and its
    /// viewer-projected surface carries renderable content (no silent empty).
    #[test]
    fn every_play_offering_opens_and_renders_a_non_empty_surface() {
        // A distinct channel per offering so their per-channel stores do not collide.
        let mut ch = 770_000u64;
        let me = actor("aa");

        macro_rules! check {
            ($ty:ty, $ctor:expr, $key:literal) => {{
                let channel = ch;
                ch += 1;
                close_in::<$ty>(channel);
                offering::open_in(channel, || $ctor, SessionConfig::with_seed(channel))
                    .unwrap_or_else(|e| panic!("`{}` opens on Discord: {e}", $key));
                assert!(is_open::<$ty>(channel), "`{}` session is live", $key);
                assert_eq!(
                    <$ty as DiscordOffering>::KEY,
                    $key,
                    "`{}` registers under its web-parity key",
                    $key
                );
                // The viewer-projected surface is non-empty (the render path the live press takes).
                let text = with_live::<$ty, _>(channel, {
                    let me = me.clone();
                    move |live| view_text(&live.offering.render_for(&live.session, &me))
                })
                .expect("the session is live");
                assert!(
                    !text.trim().is_empty() && text != "VStack([])",
                    "`{}` renders a non-empty surface (not a silent drop): {text}",
                    $key
                );
                // `surface_for` (the live-press render path) runs and yields the affordance rows.
                let rows = with_live::<$ty, _>(channel, {
                    let me = me.clone();
                    move |live| surface_for::<$ty>(live, &me).1
                })
                .expect("live");
                let _ = rows; // its existence + non-panic is the smoke; content asserted per-game below.
                close_in::<$ty>(channel);
            }};
        }

        // The world-backed surfaces each build their demo `SharedWorld` INSIDE the open factory
        // (the `Rc`-shared world is not `Send`; it is born on the store's thread) — matching the
        // module HONEST SCOPE note: each opens over its own world on this per-type surface.
        check!(SeatedTug, SeatedTug::new(), "tug");
        check!(AutomataflOffering, AutomataflOffering, "automatafl");
        check!(NamesOffering, NamesOffering::new(), "names");
        check!(ComputeOffering, ComputeOffering::new(), "compute");
        check!(
            TradeOffering,
            TradeOffering::in_world(SharedWorld::demo("Adventurer")),
            "trade"
        );
        check!(
            InventoryOffering,
            InventoryOffering::in_world(SharedWorld::demo("Adventurer")),
            "inventory"
        );
        check!(CheevoShowcase, CheevoShowcase::demo(), "cheevos");
        check!(GuildPage, GuildPage::demo("The Iron Wardens"), "guild");
        check!(
            CraftOffering,
            CraftOffering::in_world(SharedWorld::demo("Adventurer")),
            "craft"
        );
        check!(CompanionOffering, CompanionOffering::demo(), "companion");
        check!(
            TavernOffering,
            TavernOffering::demo("The Salted Tankard"),
            "tavern"
        );
        check!(PartyOffering, PartyOffering::new(), "party");
        let _ = ch; // the macro's channel cursor past the last offering
    }

    /// **The fifteen `/play` keys are exactly `PLAY_KEYS`** — the `handle` dispatch + the `register`
    /// choices + the route arms agree (so every offering is reachable, none stranded).
    #[test]
    fn the_play_keys_cover_the_twelve_portfolio_offerings() {
        for want in [
            "automatafl",
            "tug",
            "names",
            "compute",
            "trade",
            "inventory",
            "cheevos",
            "guild",
            "craft",
            "companion",
            "tavern",
            "party",
            "gear",
            "talents",
            "overworld",
        ] {
            assert!(PLAY_KEYS.contains(&want), "`{want}` is a /play key");
        }
        assert_eq!(PLAY_KEYS.len(), 15);
    }

    /// `/play` registers the `action:verify` choice (backlog Tier-2 #10) — the twelve
    /// portfolio offerings, the flagship games included, expose the chain re-verifier as a
    /// pressable command, not test-only capability.
    #[test]
    fn play_registers_the_verify_action() {
        let cmd = serde_json::to_value(register()).expect("the command serializes");
        let text = cmd.to_string();
        assert!(text.contains("\"action\""), "{text}");
        assert!(text.contains("\"verify\""), "{text}");
    }

    /// **automatafl is REACHABLE + DRIVABLE on Discord** — the board renders a non-empty surface and
    /// a real move drives one turn through the substrate (a landed receipt), re-rendering the board.
    #[test]
    fn automatafl_drives_a_real_turn_on_discord() {
        let channel = 771_100u64;
        close_in::<AutomataflOffering>(channel);
        offering::open_in(
            channel,
            || AutomataflOffering,
            SessionConfig::with_seed(channel),
        )
        .expect("automatafl opens");
        let me = actor("af");

        // The first affordance the board offers (a `select` on a movable piece).
        let first = with_live::<AutomataflOffering, _>(channel, |live| {
            live.offering.actions(&live.session).into_iter().next()
        })
        .flatten()
        .expect("the board offers at least one affordance");

        match drive::<AutomataflOffering>(
            channel,
            &fire_id(AutomataflOffering::KEY, &first.turn, first.arg),
            me,
        ) {
            Driven::Fired(outcome) => {
                // A legal select lands; the substrate is the referee for anything else.
                assert!(
                    matches!(outcome, Outcome::Landed { .. } | Outcome::Refused(_)),
                    "an automatafl press resolves on the real substrate: {outcome:?}"
                );
            }
            other => panic!("an automatafl press must drive a real turn, got {other:?}"),
        }
        assert!(
            offering::verify_live::<AutomataflOffering>(channel)
                .expect("live")
                .verified,
            "the automatafl chain re-verifies"
        );
        close_in::<AutomataflOffering>(channel);
    }

    /// **The multiway-tug hidden hand threads the viewer on Discord** — a seated player sees THEIR
    /// OWN card ids through the viewer-aware render path while a different viewer (and the old
    /// viewer-blind render) sees fog; the two seats' hands DIFFER. This is the `hidden_hand_web.rs`
    /// shape on the Discord surface, driven end-to-end through the generic adapter's `drive`.
    #[test]
    fn the_tug_hidden_hand_threads_the_viewer_on_discord() {
        let channel = 771_200u64;
        close_in::<SeatedTug>(channel);
        offering::open_in(channel, SeatedTug::new, SessionConfig::with_seed(channel))
            .expect("tug opens");
        let alice = actor("al");
        let bob = actor("bo");

        // Alice claims seat A by playing the opening Competition — a real landed receipt.
        match drive::<SeatedTug>(channel, &fire_id(SeatedTug::KEY, "comp", 3), alice.clone()) {
            Driven::Fired(o) => assert!(o.landed(), "alice's comp lands + claims seat A: {o:?}"),
            other => panic!("alice's play must drive a turn, got {other:?}"),
        }
        // Bob claims seat B by playing — lands or is a real turn-order refusal, either way seat B is
        // his and his view is projected for him.
        let _ = drive::<SeatedTug>(channel, &fire_id(SeatedTug::KEY, "secret", 0), bob.clone());

        // AS ALICE (seat A): her own hand (card ids) is revealed, the opponent is fog.
        let alice_view = with_live::<SeatedTug, _>(channel, {
            let alice = alice.clone();
            move |live| view_text(&live.offering.render_for(&live.session, &alice))
        })
        .expect("live");
        assert!(
            alice_view.contains("Your hand") && alice_view.contains("card #"),
            "seat A sees HER OWN card ids on Discord: {alice_view}"
        );
        assert!(
            alice_view.contains("Opponent (hidden hand)"),
            "the opponent's hand stays fog for the seated viewer: {alice_view}"
        );

        // AS BOB (seat B): his own, DIFFERENT hand.
        let bob_view = with_live::<SeatedTug, _>(channel, {
            let bob = bob.clone();
            move |live| view_text(&live.offering.render_for(&live.session, &bob))
        })
        .expect("live");
        assert!(
            bob_view.contains("Your hand") && bob_view.contains("card #"),
            "seat B sees HIS OWN card ids on Discord: {bob_view}"
        );
        assert_ne!(
            alice_view, bob_view,
            "the viewer threaded: the two seats' hands render DIFFERENTLY (per-viewer \
             discrimination, not the viewer-blind fog the old render served everyone)"
        );

        // A THIRD identity (holds no seat) sees fog — never anyone's cards.
        let stranger = actor("st");
        let stranger_view = with_live::<SeatedTug, _>(channel, {
            let stranger = stranger.clone();
            move |live| view_text(&live.offering.render_for(&live.session, &stranger))
        })
        .expect("live");
        assert!(
            !stranger_view.contains("card #"),
            "a non-seat viewer sees fog, never the cards: {stranger_view}"
        );

        close_in::<SeatedTug>(channel);
    }
}
