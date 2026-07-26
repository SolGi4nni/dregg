//! `/play <offering>` — **the full-portfolio reach**: the catalog offerings that did
//! NOT yet have a bespoke Discord slash command, mounted through the SAME generic
//! [`crate::commands::offering`] adapter as `/council` / `/market` / `/doc`, so Discord reaches
//! offering parity with the web catalog ([`dreggnet_web::demo_host`]).
//!
//! Discord historically served only six of the catalog offerings (dungeon, council, market,
//! hermes, grain, doc). The shared portfolio now has 23 entries; `/play` serves the seventeen
//! without bespoke commands, plus three Discord-native surfaces:
//!
//! * **six portfolio games** — native `descent`, its durable `descent-campaign`, the shielded
//!   `bazaar`, the proof-assigned `private-raid`, `automatafl` (the simultaneous-move board), and `tug`
//!   (multiway-tug, wrapped in the seat-claiming [`SeatedTug`] adapter — the ONE shared
//!   `dreggnet_catalog::seated` copy every frontend uses — so a Discord user's derived identity
//!   can claim a seat and see their OWN hidden hand through the viewer-aware render path);
//! * **the two remaining non-game offerings** — `names` and `compute`;
//! * **the nine do-once RPG feature surfaces** — `trade`, `inventory`, `cheevos`, `guild`, `craft`,
//!   `companion`, `quest`, `tavern`, `party` (`dreggnet-surfaces`).
//!
//! Each `impl`s [`Offering`], so it becomes a Discord surface through the generic adapter with no
//! per-offering rendering code: its deos `ViewNode` render is the embed, its cap-gated `Action`s are
//! the buttons, and a press is ONE real `advance` attributed to the presser's derived dregg
//! identity. Hidden games keep the channel card viewer-blind and deliver
//! [`crate::commands::offering::surface_for`] only as an ephemeral companion.
//!
//! ROUTING: the eight identity-owned RPG feature-surface keys open in the invoker's **per-identity persistent
//! world** ([`crate::commands::rpg_world`]) — one `OfferingHost` per derived dregg identity,
//! mounted via `dreggnet_surfaces::register_surfaces` (ONE shared world across craft/inventory/
//! trade, so a forged item IS in your inventory IS tradeable), sqlite-persisted by replay, with
//! the player's REAL earned cheevos. `party` joins the shared games + names/compute on the shared
//! per-channel generic-adapter stores below. A board offering (automatafl, tug) is a
//! `CoordGrid` that the Discord card renderer paints in full (the most complete renderer of the
//! three chat surfaces).

use std::sync::OnceLock;

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dregg_automatafl::AutomataflOffering;
use dregg_multiway_tug::Player;
use dreggnet_compute::ComputeOffering;
use dreggnet_market::DarkBazaarOffering;
#[cfg(feature = "private-bazaar-live")]
use dreggnet_market::private_bazaar_live_host::PrivateBazaarRaidOffering;
use dreggnet_names::NamesOffering;
use dreggnet_offerings::campaign::DescentCampaignOffering;
use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{DreggIdentity, Offering, OfferingError, SessionConfig};
use dreggnet_surfaces::{
    AshenmoorErrandOffering, CheevoShowcase, CompanionOffering, CraftOffering, GuildPage,
    HostedProofAssignedRaidOffering, InventoryOffering, PartyOffering, TavernOffering,
    TradeOffering,
};

use crate::BotState;
use crate::commands::ack;
use crate::commands::offering::{self, DiscordOffering, Store, TextPrompt, identity_of};

// ─────────────────────────────────────────────────────────────────────────────
// SeatedTug — THE shared seat-claiming adapter (`dreggnet_catalog::seated`).
// ─────────────────────────────────────────────────────────────────────────────

/// The multiway-tug offering with **claimable seats** — the ONE shared adapter from
/// `dreggnet-catalog` (docs/BOT-SHARED-BACKEND-DESIGN.md collapsed the four byte-peer copies;
/// this module held the fourth). `TugOffering` names its two seats by fixed canonical strings
/// while a Discord user's [`DreggIdentity`] is a derived key — the adapter claims a seat for the
/// first two distinct identities that act (A then B) and `render_for` maps a viewer to their seat
/// so the hidden-hand fog reaches the right player. Re-exported so every existing consumer
/// (`offering::route_component`, `verify_chain`, the crown) keeps its `portfolio::SeatedTug` path;
/// the [`DiscordOffering`] impl below is the Discord-specific mounting, which stays here. (The
/// session type is `dreggnet_catalog::seated::SeatedTugSession`; no Discord code names it.)
pub use dreggnet_catalog::seated::SeatedTug;

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

impl DiscordOffering for DescentCampaignOffering {
    const KEY: &'static str = DescentCampaignOffering::KEY;
    const TITLE: &'static str = "The Deepening Ways";
    const COLOR: u32 = 0xB58B4A;
    const TAGLINE: &'static str =
        "player-driven native expeditions · replay-verified Crowns open real region roads";

    /// **Deliberately not resumable**, for the same reason as `NativeDescentOffering`: it wraps
    /// the day-bound native offering, so a rebuild on a later day is a different world.
    fn rebuild() -> Option<Self> {
        None
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(DescentCampaignOffering)
    }

    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }

    fn status_line(&self, session: &Self::Session) -> String {
        format!(
            "{} verified turns · {} locations crowned · campaign revision {}",
            self.verify(session).turns,
            session.cleared_count(),
            session.revision()
        )
    }
}

impl DiscordOffering for SeatedTug {
    const KEY: &'static str = "tug";
    const TITLE: &'static str = "Multiway-Tug";
    const COLOR: u32 = 0x8E5BD6;
    const TAGLINE: &'static str =
        "a hidden-hand tug of influence · your own hand revealed, the opponent fog";
    /// Rebuilt from a deterministic, argument-free constructor — identical to the
    /// factory production opens it with — so a persisted session of this offering
    /// resumes by replay into the SAME world its turns landed in.
    fn rebuild() -> Option<Self> {
        Some(SeatedTug::new())
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(SeatedTug)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    /// Rebuilt from a deterministic, argument-free constructor — identical to the
    /// factory production opens it with — so a persisted session of this offering
    /// resumes by replay into the SAME world its turns landed in.
    fn rebuild() -> Option<Self> {
        Some(AutomataflOffering)
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(AutomataflOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

#[cfg(feature = "private-bazaar-live")]
impl DiscordOffering for PrivateBazaarRaidOffering {
    const KEY: &'static str = PrivateBazaarRaidOffering::KEY;
    const TITLE: &'static str = "The Dark Bazaar raid";
    const COLOR: u32 = 0x4B3F72;
    const TAGLINE: &'static str =
        "viewer-blind allocation · exact private settlement · one receipted game consequence";

    fn store() -> &'static Store<Self> {
        seat_of_store!(PrivateBazaarRaidOffering)
    }

    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }

    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for HostedProofAssignedRaidOffering {
    const KEY: &'static str = dreggnet_surfaces::private_raid::KEY;
    const TITLE: &'static str = "The Ash Gate Raid";
    const COLOR: u32 = 0x7A5AA6;
    const TAGLINE: &'static str =
        "four public identities · one shielded optimal role proof · real party capabilities";

    /// Rebuilt from a deterministic, argument-free constructor — identical to the
    /// factory production opens it with — so a persisted session of this offering
    /// resumes by replay into the SAME world its turns landed in.
    fn rebuild() -> Option<Self> {
        Some(HostedProofAssignedRaidOffering::new())
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(HostedProofAssignedRaidOffering)
    }

    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }

    fn text_prompt(turn: &str) -> Option<TextPrompt> {
        (turn == dreggnet_surfaces::private_raid::TURN_STREAM_ASSIGNMENT).then_some(TextPrompt {
            title: "Append raid proof chunk",
            label: "Lowercase hex (up to 240 characters)",
            placeholder: "00…",
            paragraph: false,
        })
    }

    fn status_line(&self, session: &Self::Session) -> String {
        let proof = if session.assignment().is_some() {
            "assignment verified"
        } else if session.roster().len() == 4 {
            "awaiting seat-0 proof upload"
        } else {
            "mustering"
        };
        format!(
            "{} verified turns · {}/4 public seats · {proof}",
            self.verify(session).turns,
            session.roster().len(),
        )
    }
}

impl DiscordOffering for NamesOffering {
    const KEY: &'static str = "names";
    const TITLE: &'static str = "DreggNet Names";
    const COLOR: u32 = 0x4A78C2;
    const TAGLINE: &'static str = "an identity / naming service · register · transfer · resolve";
    /// Rebuilt from a deterministic, argument-free constructor — identical to the
    /// factory production opens it with — so a persisted session of this offering
    /// resumes by replay into the SAME world its turns landed in.
    fn rebuild() -> Option<Self> {
        Some(NamesOffering::new())
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(NamesOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    /// Rebuilt from a deterministic, argument-free constructor — identical to the
    /// factory production opens it with — so a persisted session of this offering
    /// resumes by replay into the SAME world its turns landed in.
    fn rebuild() -> Option<Self> {
        Some(ComputeOffering::new())
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(ComputeOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
    fn open_hint() -> String {
        format!("/play offering:{}", Self::KEY)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for AshenmoorErrandOffering {
    const KEY: &'static str = dreggnet_surfaces::quest::KEY;
    const TITLE: &'static str = "The Ashenmoor Errand";
    const COLOR: u32 = 0xB06B3C;
    const TAGLINE: &'static str =
        "earn committed faction standing · unlock and complete an ordered quest";
    fn store() -> &'static Store<Self> {
        seat_of_store!(AshenmoorErrandOffering)
    }
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
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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
    /// Rebuilt from a deterministic, argument-free constructor — identical to the
    /// factory production opens it with — so a persisted session of this offering
    /// resumes by replay into the SAME world its turns landed in.
    fn rebuild() -> Option<Self> {
        Some(PartyOffering::new())
    }

    fn store() -> &'static Store<Self> {
        seat_of_store!(PartyOffering)
    }
    // The REAL invocation that opens this offering (backlog #29): the stale-session hint
    // must be typeable — this offering is mounted by `/play`, not a bespoke `/<key> open`.
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

/// The channel's finished, WON tug match as the whole-match fold's job: the WINNER's private
/// full-round inventory (`(card_id, nonce)` pairs: opening hand + four draws), every exact card
/// consumed by their four actions, and the terminal win facts — read through `TugSession`'s
/// owner-facing match-record seam.
/// Lives HERE because only this module can reach the seated session's inner round. `None`
/// until the round has scored a winner.
///
/// The record never leaves the fold path: the resulting proof's public inputs are
/// `[blinded_leaf, hand_root]` per play — the card ids are not among them.
pub fn played_tug_match(channel: u64) -> Option<dreggnet_prove_service::PlayedMatch> {
    offering::with_live::<SeatedTug, _>(channel, |live| {
        let s = live.session.inner();
        let (winner, charm) = s.win_facts()?;
        let seat = if winner == 1 { Player::A } else { Player::B };
        let private = s.terminal_match_record(seat)?;
        Some(dreggnet_prove_service::PlayedMatch::Tug(
            dreggnet_prove_service::TugMatch {
                hand: private.hand,
                plays: private.plays,
                win: Some(dreggnet_prove_service::TugWin { charm, winner }),
            },
        ))
    })
    .flatten()
}

// ─────────────────────────────────────────────────────────────────────────────
// The `/play` command — open any portfolio offering by key.
// ─────────────────────────────────────────────────────────────────────────────

/// The catalog keys served by their own **bespoke slash commands** (`/dungeon`, `/council`,
/// `/market`, `/doc`, `/grain`, `/hermes`) rather than `/play` — the complement of `/play`'s
/// reach within the shared catalog. Each name is asserted registered in
/// `REGISTERED_COMMAND_NAMES` by the parity test below.
pub const BESPOKE_COMMAND_KEYS: [&str; 6] =
    ["dungeon", "council", "market", "doc", "grain", "hermes"];

/// The **Discord-only `/play` extras** beyond the shared catalog: gear/talents
/// (`commands::gear`) and the overworld (`commands::overworld`) are not (yet) registered in
/// `dreggnet-catalog`, so they are declared here explicitly instead of riding the derived list.
pub const DISCORD_EXTRA_PLAY_KEYS: [&str; 3] = ["gear", "talents", "overworld"];

/// Deployment-backed routes which are intentionally not part of the ordinary
/// synthetic catalog. Their feature gates pull the real verifier/policy stack;
/// the running bot additionally requires a complete deployment record.
#[cfg(feature = "private-bazaar-live")]
pub const DISCORD_OPT_IN_PLAY_KEYS: [&str; 1] = [PrivateBazaarRaidOffering::KEY];
#[cfg(not(feature = "private-bazaar-live"))]
pub const DISCORD_OPT_IN_PLAY_KEYS: [&str; 0] = [];

/// The `/play` offering CHOICES — **derived from the shared catalog**
/// ([`dreggnet_catalog::CATALOG_KEYS`], the ONE statement of what the DreggNet portfolio is)
/// minus the [`BESPOKE_COMMAND_KEYS`], plus the [`DISCORD_EXTRA_PLAY_KEYS`], and finally
/// **narrowed to the SHIP LIST** (`dreggnet_catalog::SHIPPED_KEYS`).
///
/// ⚑ The discord-bot builds no `OfferingHost` — it drives per-type `Store<O>`s — so it cannot
/// inherit the host-level shelf every other frontend gets from `apply_ship_list`. It reads the
/// same array directly instead, which is what keeps Discord from advertising a set the web and
/// the bots do not. To re-list something on Discord, add it to `SHIPPED_KEYS`; nothing here needs
/// touching.
///
/// ⚠ **This narrows the `/play` picker only, and Discord enforces its own choice list**, so an
/// unshipped key cannot be typed into `/play` even though it is still mounted. Its per-type
/// component/modal routes (`commands::offering::route_component`, which covers every mounted
/// type) and its bespoke subcommand, where it has one, are untouched — this is the one host where
/// "unlisted is still reachable" is narrower than elsewhere, and it is Discord's constraint, not
/// the ship list's.
pub fn play_keys() -> Vec<&'static str> {
    dreggnet_catalog::CATALOG_KEYS
        .iter()
        .copied()
        .filter(|k| !BESPOKE_COMMAND_KEYS.contains(k))
        .chain(DISCORD_EXTRA_PLAY_KEYS)
        .chain(DISCORD_OPT_IN_PLAY_KEYS)
        .filter(|k| dreggnet_catalog::is_shipped(k))
        .collect()
}

/// Register `/play <offering>` — open any SHIPPED offering (`play_keys`) in this channel.
pub fn register() -> CreateCommand {
    let mut option = CreateCommandOption::new(
        CommandOptionType::String,
        "offering",
        "Which portfolio offering to open in this channel",
    )
    .required(true);
    for key in play_keys() {
        option = option.add_string_choice(key, key);
    }
    CreateCommand::new("play")
        .description("Open one receipted game, market, or engine offering in this channel")
        .add_option(option)
        // `/play <offering> action:verify` — re-verify the channel's live session chain (the
        // SAME `offering::handle_verify` `/council verify` runs; backlog Tier-2 #10 — the
        // flagship games were the least verifiable surfaces). Default (absent) = open.
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "action",
                "Open by default; verify a chain or submit the Ash Gate's proof receipt",
            )
            .add_string_choice("verify", "verify")
            .add_string_choice("submit raid proof", "submit-raid-proof")
            .required(false),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Attachment,
                "proof",
                "Canonical private-raid HidingFri receipt (for submit raid proof)",
            )
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

    // `/play <offering> action:verify` — re-verify the live session chain through the SAME
    // generic verifier every bespoke offering command exposes (backlog Tier-2 #10). Runs
    // BEFORE the deferred ACK: each verify route owns its own response (the generic path
    // responds directly; the RPG path defers itself — a first-touch replay can exceed 3s).
    if string_opt("action").as_deref() == Some("verify") {
        handle_play_verify(ctx, command, state, &key).await;
        return;
    }
    if string_opt("action").as_deref() == Some("submit-raid-proof") {
        handle_raid_proof_upload(ctx, command, state, &key).await;
        return;
    }

    let channel = command.channel_id.get();
    let viewer = identity_of(state, command.user.id.get());
    let cfg = SessionConfig::with_seed(channel);

    // ACK inside Discord's 3s window BEFORE the open runs — a world-backed open deploys a real
    // world-cell on the offering store's thread; the surface (or an honest refusal) lands as an
    // EDIT of this deferred response.
    ack::defer_slash(ctx, command, false).await;

    // The eight identity-owned RPG feature surfaces open in the invoker's PER-IDENTITY PERSISTENT world
    // (`commands::rpg_world`): ONE shared craft/inventory/trade ledger per player (the saga
    // composition), sqlite-persisted by replay, real earned cheevos — never a throwaway
    // per-channel demo world. `handle_play` edits the response this handler already deferred.
    if crate::commands::rpg_world::is_rpg_key(&key) {
        crate::commands::rpg_world::handle_play(ctx, command, state, &key).await;
        return;
    }

    // ⚑ THE LIVE DESCENT OPENS ON TODAY'S VERIFIED BEACON DAY. Both Descent surfaces are built
    // through `commands::native_descent::live_offering`, whose day is re-resolved at every open
    // (this process outlives many UTC days), so a run's banked relics mint under a provenance
    // root that could not exist before that day's drand round was revealed. Fail-closed: no
    // verified day, no session — never the pre-computable deploy-seed-derived root.
    let opened: Result<(), OfferingError> = match key.as_str() {
        DescentCampaignOffering::KEY => {
            open_and_post::<DescentCampaignOffering>(
                ctx,
                command,
                || {
                    DescentCampaignOffering::with_native(
                        crate::commands::native_descent::live_offering(),
                    )
                },
                &viewer,
                cfg,
            )
            .await
        }
        "descent" => {
            // ⚑ TODAY'S DAY, NOT THIS CHANNEL. The native Descent opens on the committed day's own
            // seed — the same number `/descent/play` hands the browser as `nativeSeed` — so every
            // channel and the web tab descend the SAME drawn dungeon, and the run's record is one
            // the board's native lane will admit (`commands::native_descent::open_config_on_todays_day`).
            // With the channel id as the seed each channel got its own map and no run could ever
            // be shared.
            open_and_post::<NativeDescentOffering>(
                ctx,
                command,
                crate::commands::native_descent::live_offering,
                &viewer,
                crate::commands::native_descent::open_config_on_todays_day(channel),
            )
            .await
        }
        "bazaar" => {
            open_and_post::<DarkBazaarOffering>(ctx, command, DarkBazaarOffering::new, &viewer, cfg)
                .await
        }
        "tug" => open_and_post::<SeatedTug>(ctx, command, SeatedTug::new, &viewer, cfg).await,
        "automatafl" => {
            open_and_post::<AutomataflOffering>(ctx, command, || AutomataflOffering, &viewer, cfg)
                .await
        }
        #[cfg(feature = "private-bazaar-live")]
        PrivateBazaarRaidOffering::KEY => match state.private_bazaar_deployment.clone() {
            Some(deployment) => {
                open_and_post::<PrivateBazaarRaidOffering>(
                    ctx,
                    command,
                    move || deployment.offering(),
                    &viewer,
                    cfg,
                )
                .await
            }
            None => Err(OfferingError::Deploy(
                "this bot build has no configured private Bazaar deployment".to_owned(),
            )),
        },
        dreggnet_surfaces::private_raid::KEY => {
            open_and_post::<HostedProofAssignedRaidOffering>(
                ctx,
                command,
                HostedProofAssignedRaidOffering::new,
                &viewer,
                cfg,
            )
            .await
        }
        "names" => {
            open_and_post::<NamesOffering>(ctx, command, NamesOffering::new, &viewer, cfg).await
        }
        "compute" => {
            open_and_post::<ComputeOffering>(ctx, command, ComputeOffering::new, &viewer, cfg).await
        }
        "party" => {
            open_and_post::<PartyOffering>(ctx, command, PartyOffering::new, &viewer, cfg).await
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

/// `/play <offering> action:verify` — dispatch the chain re-verifier for the chosen offering
/// key, so the portfolio offerings — the flagship games included — answer verify-don't-trust
/// with a command, not a shrug (backlog Tier-2 #10). The eight identity-owned RPG keys verify the INVOKER's
/// per-identity persistent world chain (`commands::rpg_world` — where their sessions actually
/// live); the rest go through the generic per-channel verifier ([`offering::handle_verify`],
/// the SAME one behind `/council verify` et al.).
async fn handle_play_verify(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
    key: &str,
) {
    if crate::commands::rpg_world::is_rpg_key(key) {
        crate::commands::rpg_world::handle_verify(ctx, command, state, key).await;
        return;
    }
    match key {
        DescentCampaignOffering::KEY => {
            offering::handle_verify::<DescentCampaignOffering>(ctx, command).await
        }
        "descent" => offering::handle_verify::<NativeDescentOffering>(ctx, command).await,
        "bazaar" => offering::handle_verify::<DarkBazaarOffering>(ctx, command).await,
        "tug" => offering::handle_verify::<SeatedTug>(ctx, command).await,
        "automatafl" => offering::handle_verify::<AutomataflOffering>(ctx, command).await,
        #[cfg(feature = "private-bazaar-live")]
        PrivateBazaarRaidOffering::KEY => {
            offering::handle_verify::<PrivateBazaarRaidOffering>(ctx, command).await
        }
        dreggnet_surfaces::private_raid::KEY => {
            offering::handle_verify::<HostedProofAssignedRaidOffering>(ctx, command).await
        }
        "names" => offering::handle_verify::<NamesOffering>(ctx, command).await,
        "compute" => offering::handle_verify::<ComputeOffering>(ctx, command).await,
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

/// Upload the canonical HidingFri receipt into the exact live channel raid. The
/// offering remains the only decoder/verifier and enforces that the submitter is
/// public proof seat zero; Discord only bounds and transports the opaque bytes.
async fn handle_raid_proof_upload(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
    key: &str,
) {
    ack::defer_slash(ctx, command, false).await;
    if key != dreggnet_surfaces::private_raid::KEY {
        let embed = CreateEmbed::new()
            .title("That proof does not belong to this offering")
            .description("`submit raid proof` is only valid with `offering:private-raid`.")
            .color(0xE63946);
        ack::edit_slash(ctx, command, embed, vec![]).await;
        return;
    }
    let channel = command.channel_id.get();
    let actor = identity_of(state, command.user.id.get());
    let preflight = offering::with_live::<HostedProofAssignedRaidOffering, _>(channel, {
        let actor = actor.clone();
        move |live| {
            (
                live.session.roster().len(),
                live.session.roster().first() == Some(&actor.0),
                live.session.assignment().is_some(),
            )
        }
    });
    let Some((seats, is_seat_zero, assigned)) = preflight else {
        let embed = CreateEmbed::new()
            .title("No Ash Gate raid is open in this channel")
            .description(format!(
                "Open one first with `/play offering:{}`.",
                dreggnet_surfaces::private_raid::KEY
            ))
            .color(0xE39B32);
        ack::edit_slash(ctx, command, embed, vec![]).await;
        return;
    };
    if seats != 4 || !is_seat_zero || assigned {
        let (title, description) = if seats != 4 {
            (
                "The public proof roster is not complete",
                format!("{seats}/4 identities have joined; the upload opens after seat 3 lands."),
            )
        } else if !is_seat_zero {
            (
                "Only public proof seat zero may submit",
                "The first identity that joined owns this roster-binding operation.".to_string(),
            )
        } else {
            (
                "This raid already has its verified assignment",
                "Continue with the proof-assigned party capability claims.".to_string(),
            )
        };
        let embed = CreateEmbed::new()
            .title(title)
            .description(description)
            .color(0xE39B32);
        ack::edit_slash(ctx, command, embed, vec![]).await;
        return;
    }
    let attachment = command.data.options.iter().find_map(|option| {
        if option.name != "proof" {
            return None;
        }
        match &option.value {
            CommandDataOptionValue::Attachment(id) => command.data.resolved.attachments.get(id),
            _ => None,
        }
    });
    let Some(attachment) = attachment else {
        let embed = CreateEmbed::new()
            .title("Attach the canonical raid receipt")
            .description(
                "Choose `action:submit raid proof` and attach the postcard HidingFri receipt. The upload is available only after four identities have joined.",
            )
            .color(0xE39B32);
        ack::edit_slash(ctx, command, embed, vec![]).await;
        return;
    };
    let max = dreggnet_surfaces::private_raid::MAX_ASSIGNMENT_BYTES;
    if attachment.size as usize > max {
        let embed = CreateEmbed::new()
            .title("Raid proof is too large")
            .description(format!(
                "The attachment is {} bytes; this verifier accepts at most {max}.",
                attachment.size
            ))
            .color(0xE63946);
        ack::edit_slash(ctx, command, embed, vec![]).await;
        return;
    }
    let downloaded = async {
        let mut response = reqwest::Client::new()
            .get(&attachment.url)
            .send()
            .await
            .map_err(|error| format!("Discord CDN download failed: {error}"))?
            .error_for_status()
            .map_err(|error| format!("Discord CDN refused the download: {error}"))?;
        if response
            .content_length()
            .is_some_and(|length| length > max as u64)
        {
            return Err("Discord CDN response exceeds the raid proof limit".to_string());
        }
        let mut bytes = Vec::with_capacity(attachment.size as usize);
        while let Some(chunk) = response
            .chunk()
            .await
            .map_err(|error| format!("could not read the proof attachment: {error}"))?
        {
            if bytes.len().saturating_add(chunk.len()) > max {
                return Err("downloaded raid proof exceeds its verifier limit".to_string());
            }
            bytes.extend_from_slice(&chunk);
        }
        Ok::<Vec<u8>, String>(bytes)
    }
    .await;
    let payload = match downloaded {
        Ok(payload) => payload,
        Err(reason) => {
            let embed = CreateEmbed::new()
                .title("Raid proof could not be transported")
                .description(reason)
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, vec![]).await;
            return;
        }
    };
    let result = offering::with_live::<HostedProofAssignedRaidOffering, _>(channel, move |live| {
        live.offering
            .invoke_binary_operation(
                &mut live.session,
                dreggnet_surfaces::private_raid::ASSIGN_OPERATION,
                &payload,
                actor.clone(),
            )
            .map(|receipt| {
                let rendered =
                    offering::surface_for::<HostedProofAssignedRaidOffering>(live, &actor);
                (receipt, rendered)
            })
    });
    match result {
        None => {
            let embed = CreateEmbed::new()
                .title("The Ash Gate raid closed during upload")
                .description("No proof was applied. Open or resume the raid, then submit again.")
                .color(0xE39B32);
            ack::edit_slash(ctx, command, embed, vec![]).await;
        }
        Some(Err(error)) => {
            let embed = CreateEmbed::new()
                .title("The raid verifier refused the receipt")
                .description(error.to_string())
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, vec![]).await;
        }
        Some(Ok((_receipt, (embed, rows)))) => {
            ack::edit_slash(ctx, command, embed, rows).await;
        }
    }
}

/// Open the offering `make` builds in the channel and post its shared surface.
/// A hidden-information offering posts only its viewer-blind fog into the
/// channel and sends the opener's private projection as an ephemeral companion.
/// The factory runs on the offering store's own thread
/// ([`offering::open_in`]), so a world-backed non-`Send` offering is born where
/// it lives. Returns the open result so the caller reports a refusal honestly.
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
        crate::commands::open_guard::refuse_with_confirm(
            ctx,
            command,
            O::KEY,
            status,
            Box::new(move || {
                offering::open_in(channel, make, cfg).map_err(|e| e.to_string())?;
                // The confirm card is a shared channel message. Even though
                // the pending closure knows who requested it, it must never
                // publish that user's hidden projection.
                offering::with_live::<O, _>(channel, |live| offering::surface_of::<O>(live))
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
        offering::channel_surfaces::<O>(live, &viewer)
    });
    match rendered {
        Some(((embed, rows), private)) => {
            ack::edit_slash(ctx, command, embed, rows).await;
            if let Some((private_embed, _private_rows)) = private {
                ack::followup_slash_ephemeral_surface(
                    ctx,
                    command,
                    "**Your private view** — only you can read this hand / sealed move. Use the shared board's controls to act.",
                    private_embed,
                    vec![],
                )
                .await;
            }
        }
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
        Driven, channel_surfaces, close_in, drive, fire_id_in, is_open, surface_for, with_live,
    };
    // The tests still drive every generic per-type adapter path (the adapter
    // mechanics); the LIVE `/play` route for the eight identity-owned RPG keys is the per-identity
    // persistent world (`commands::rpg_world`), while party stays on this shared channel path.
    use dreggnet_offerings::{Outcome, Surface};
    use dreggnet_surfaces::SharedWorld;

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// The debug text of a session's rendered surface (the same idiom the game crates' surface tests
    /// use) — a proxy for "the surface is non-empty / not a silent drop".
    fn view_text(surface: &Surface) -> String {
        format!("{:?}", surface.view())
    }

    /// **Every catalog `/play` offering OPENS and renders a NON-EMPTY surface** — the
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
        check!(
            NativeDescentOffering,
            NativeDescentOffering::new(),
            "descent"
        );
        check!(
            DescentCampaignOffering,
            DescentCampaignOffering::new(),
            "descent-campaign"
        );
        check!(SeatedTug, SeatedTug::new(), "tug");
        check!(DarkBazaarOffering, DarkBazaarOffering::new(), "bazaar");
        check!(AutomataflOffering, AutomataflOffering, "automatafl");
        check!(
            HostedProofAssignedRaidOffering,
            HostedProofAssignedRaidOffering::new(),
            "private-raid"
        );
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
            AshenmoorErrandOffering,
            AshenmoorErrandOffering::new(),
            "quest"
        );
        check!(
            TavernOffering,
            TavernOffering::demo("The Salted Tankard"),
            "tavern"
        );
        check!(PartyOffering, PartyOffering::new(), "party");
        let _ = ch; // the macro's channel cursor past the last offering
    }

    #[cfg(feature = "private-bazaar-live")]
    #[test]
    fn private_bazaar_opt_in_drives_the_generic_discord_adapter() {
        use dreggnet_market::private_bazaar_journey::{
            PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy, TURN_ENTER_PRIVATE_BAZAAR,
        };
        use dreggnet_market::private_clearing_guild_allocation::{
            GuildMember, GuildReward, GuildRoster,
        };
        use dungeon_on_dregg::progression::{
            PRIVATE_BAZAAR_XP_METHOD, deploy_hero, private_bazaar_xp_event_topic,
        };

        let hero = deploy_hero(0xA1);
        hero.set_executor_signing_key([0xA2; 32]);
        let raider = DreggIdentity("discord-private-raider".to_owned());
        let roster =
            GuildRoster::new(vec![GuildMember::new(raider.clone(), hero.cell_id())]).unwrap();
        let reward = GuildReward::new("raid-xp/discord/v1", 144).unwrap();
        let pin = PrivateBazaarDeploymentPin::new(
            [0xA3; 32],
            roster.digest(),
            PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
            PRIVATE_BAZAAR_XP_METHOD,
            private_bazaar_xp_event_topic(),
            hero.executor_pubkey().unwrap(),
            hero.federation_id(),
        )
        .unwrap();
        let temp = tempfile::tempdir().unwrap();
        let deployment = dreggnet_catalog::PrivateBazaarLiveDeployment::open(
            PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap(),
            1,
            temp.path(),
        )
        .unwrap();
        let channel = 778_821;
        close_in::<PrivateBazaarRaidOffering>(channel);
        let mounted = deployment.clone();
        offering::open_in::<PrivateBazaarRaidOffering>(
            channel,
            move || mounted.offering(),
            SessionConfig::with_seed(channel),
        )
        .unwrap();
        let control =
            fire_id_in::<PrivateBazaarRaidOffering>(channel, TURN_ENTER_PRIVATE_BAZAAR, 0)
                .expect("the viewer-blind Enter control is mounted");
        assert!(matches!(
            drive::<PrivateBazaarRaidOffering>(channel, &control, raider),
            Driven::Fired(Outcome::Landed { .. })
        ));
        assert!(deployment.registry().contains(channel));
        close_in::<PrivateBazaarRaidOffering>(channel);
    }

    /// **The `/play` choices ARE the ship list** — derived, never hand-listed, so paring or
    /// re-listing an offering in `dreggnet_catalog::SHIPPED_KEYS` moves Discord with everything
    /// else and this test needs no edit.
    ///
    /// Both directions: every shipped offering is a `/play` choice (nothing we ship is
    /// unreachable), and every `/play` choice is shipped (nothing we do not ship is advertised).
    /// Separately: paring the PICKER must not unmount anything, so every catalog key — shipped or
    /// not — is still in the generic component/modal router.
    #[test]
    fn the_play_choices_are_exactly_the_ship_list() {
        let keys = play_keys();

        for k in dreggnet_catalog::SHIPPED_KEYS {
            assert!(
                keys.contains(&k),
                "shipped offering `{k}` must be a /play choice"
            );
            assert!(
                !BESPOKE_COMMAND_KEYS.contains(&k),
                "`{k}` must not be served twice (bespoke AND /play)"
            );
        }
        for k in &keys {
            assert!(
                dreggnet_catalog::is_shipped(k),
                "/play advertises `{k}`, which is not on dreggnet_catalog::SHIPPED_KEYS"
            );
            assert!(
                dreggnet_catalog::CATALOG_KEYS.contains(k)
                    || DISCORD_EXTRA_PLAY_KEYS.contains(k)
                    || DISCORD_OPT_IN_PLAY_KEYS.contains(k),
                "/play key `{k}` is neither a catalog offering nor a declared Discord route"
            );
        }
        assert_eq!(
            keys.len(),
            dreggnet_catalog::SHIPPED_KEYS.len(),
            "the picker is the ship list exactly: {keys:?}"
        );

        // ⚑ UNLISTED IS NOT UNMOUNTED. The Dark Bazaar is off the picker; its per-type
        // component/modal route and its open hint are untouched, so a held press still lands.
        assert!(!keys.contains(&"bazaar"), "the Bazaar is off the shelf");
        assert!(
            offering::generic_offering_keys().contains(&"bazaar"),
            "…and still mounted in the generic component/modal router"
        );
        assert_eq!(DarkBazaarOffering::open_hint(), "/play offering:bazaar");
        for k in dreggnet_catalog::CATALOG_KEYS {
            assert!(
                BESPOKE_COMMAND_KEYS.contains(&k) || offering::generic_offering_keys().contains(&k),
                "catalog offering `{k}` must stay mounted even when it is off the picker"
            );
        }
    }

    /// **The bespoke-command catalog keys are reachable on the 13-command surface** — the
    /// offering SET is the shared catalog's, and the registered surface stays consistent with
    /// it: every catalog key `/play open` does NOT serve rides as its own top-level command or
    /// as a fold under one (`commands::menus`), and `/play` itself is registered with `open`.
    #[test]
    fn the_bespoke_catalog_commands_are_registered() {
        // key → (its top-level home, the subcommand/group name there; None = it IS top-level).
        let homes: &[(&str, Option<(&str, &str)>)] = &[
            ("dungeon", Some(("adventure", "dungeon"))),
            ("council", Some(("govern", "council"))),
            ("market", Some(("play", "market"))),
            ("doc", Some(("hermes", "doc"))),
            ("grain", Some(("hermes", "grain"))),
            ("hermes", None),
        ];
        for key in BESPOKE_COMMAND_KEYS {
            let (_, home) = homes
                .iter()
                .find(|(k, _)| *k == key)
                .unwrap_or_else(|| panic!("bespoke key `{key}` has no declared 13-command home"));
            match home {
                None => assert!(
                    crate::REGISTERED_COMMAND_NAMES.contains(&key),
                    "catalog offering `{key}` is claimed top-level but `/{key}` is not registered"
                ),
                Some((top, sub)) => assert!(
                    crate::commands::menus::subcommand_names(top)
                        .iter()
                        .any(|s| s == sub),
                    "catalog offering `{key}` should be reachable as `/{top} {sub}`"
                ),
            }
        }
        assert!(
            crate::REGISTERED_COMMAND_NAMES.contains(&"play"),
            "`/play` (the derived-catalog reach) must be registered"
        );
        assert!(
            crate::commands::menus::subcommand_names("play")
                .iter()
                .any(|s| s == "open"),
            "`/play open` (the portfolio opener) must be registered"
        );
    }

    /// `/play` registers the `action:verify` choice (backlog Tier-2 #10) — the
    /// portfolio offerings, the flagship games included, expose the chain re-verifier as a
    /// pressable command, not test-only capability.
    #[test]
    fn play_registers_the_verify_action() {
        let cmd = serde_json::to_value(register()).expect("the command serializes");
        let text = cmd.to_string();
        assert!(text.contains("\"action\""), "{text}");
        assert!(text.contains("\"verify\""), "{text}");
    }

    /// The catalog campaign is a real generic Discord offering, not just a slash-command choice:
    /// a presented manual move reaches the native executor and the composed chain re-verifies.
    #[test]
    fn descent_campaign_drives_a_real_turn_on_discord() {
        let channel = 771_073u64;
        close_in::<DescentCampaignOffering>(channel);
        offering::open_in(
            channel,
            DescentCampaignOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("the Descent campaign opens");
        let me = actor("campaign");
        let me_for_actions = me.clone();
        let first = with_live::<DescentCampaignOffering, _>(channel, move |live| {
            live.offering
                .actions_for(&live.session, &me_for_actions)
                .into_iter()
                .find(|action| action.turn == "delve" && action.enabled)
        })
        .flatten()
        .expect("the campaign offers a manual delve");
        match drive::<DescentCampaignOffering>(
            channel,
            &fire_id_in::<DescentCampaignOffering>(channel, &first.turn, first.arg).unwrap(),
            me,
        ) {
            Driven::Fired(Outcome::Landed { .. }) => {}
            other => panic!("the Discord campaign move must land: {other:?}"),
        }
        let report = offering::verify_live::<DescentCampaignOffering>(channel)
            .expect("the campaign remains live");
        assert!(report.verified, "{}", report.detail);
        assert_eq!(report.turns, 2, "genesis plus the submitted delve");
        close_in::<DescentCampaignOffering>(channel);
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
            &fire_id_in::<AutomataflOffering>(channel, &first.turn, first.arg).unwrap(),
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

    /// The JSON text of a rendered embed — every title/description/field value in one string, so an
    /// assertion about what the player can READ does not depend on which slot carried it.
    fn embed_text(embed: &CreateEmbed) -> String {
        serde_json::to_string(embed).expect("an embed serialises")
    }

    /// **THE PRIVATE VIEW SAYS WHERE TO ACT — it is a READING surface, and it now admits it.**
    ///
    /// The concrete defect: for a hidden-information offering `channel_surfaces` returns the public
    /// fogged board plus a PRIVATE ephemeral companion carrying the viewer's own secret — and that
    /// companion shipped with `Vec::new()` for its button rows and NOT ONE WORD about why. The
    /// player could read their sealed move privately and was then left to work out on their own
    /// that they had to scroll up and act on the public board. ember's standard, from the web
    /// surface they rejected: "it looks like a debug view, I can't tell what's happening."
    ///
    /// The controls staying public is a DELIBERATE decision, not an oversight (all presses ride one
    /// board message, so a private press can never leave the public board stale) — so this test
    /// pins the decision AND the honesty it owes:
    ///
    ///   * the companion carries NO controls (no half-built private control surface), and
    ///   * its embed TELLS the player where to act, and
    ///   * that instruction is TRUE — the public board it points at really does carry the presses.
    ///
    /// The third assertion is what keeps this from being a spell-check: a plaque saying "press on
    /// the board" over a board with no buttons would pass the text check and still strand the
    /// player.
    #[test]
    fn the_private_view_tells_the_player_where_to_act() {
        let channel = 771_150u64;
        close_in::<AutomataflOffering>(channel);
        offering::open_in(
            channel,
            || AutomataflOffering,
            SessionConfig::with_seed(channel),
        )
        .expect("automatafl opens");
        let me = actor("pv");

        let ((public_embed, public_rows), private) =
            with_live::<AutomataflOffering, _>(channel, move |live| {
                assert!(
                    live.offering.hidden_information(),
                    "this test is about the hidden-information split; automatafl must be one",
                );
                channel_surfaces::<AutomataflOffering>(live, &me)
            })
            .expect("a live automatafl session renders");

        let (private_embed, private_rows) = private.expect(
            "a hidden-information offering must return a PRIVATE companion — the viewer's own \
             sealed move may never be painted into the shared channel",
        );

        // 1. No half-built private control surface.
        assert!(
            private_rows.is_empty(),
            "the private companion deliberately carries no controls (one board message owns every \
             press); it must not sprout a second control surface that can strand the public board",
        );

        // 2. It says so, and says where to go instead.
        let text = embed_text(&private_embed);
        assert!(
            text.contains(offering::PRIVATE_ACT_FIELD),
            "the private view must carry the where-to-act plaque, or the player is left reading a \
             secret with no idea what to do next: {text}",
        );
        for needle in ["board", "press"] {
            assert!(
                text.to_lowercase().contains(needle),
                "the plaque must name the board and the act of pressing on it (missing \
                 `{needle}`): {text}",
            );
        }

        // 3. And that instruction is TRUE: the public board really does carry the presses.
        let public_buttons: usize = public_rows
            .iter()
            .map(|row| format!("{row:?}").matches("CreateButton").count())
            .sum();
        assert!(
            public_buttons > 0,
            "the plaque sends the player to the public board, so the public board MUST carry \
             controls — otherwise the instruction is a lie and the player is stranded",
        );
        // The public board is the FOGGED one — the private secret never crosses into the channel.
        let public_text = embed_text(&public_embed);
        assert_ne!(
            public_text, text,
            "the public board and the private companion must be different renders (fog vs reveal)",
        );

        // 4. THE NEGATIVE CONTROL — the object that actually shipped.
        //
        // `surface_for` is the bare viewer projection `channel_surfaces` used to hand back
        // untouched, and it is still exactly what a caller gets without the plaque. Asserting that
        // it does NOT carry the guidance is what keeps assertion 2 from being unfalsifiable: if the
        // plaque were ever unwired from `channel_surfaces`, the two halves of this test would
        // agree and 2 would fail. It also pins that the plaque is added by the CHANNEL split and
        // not smuggled into every render (the public board must not carry a "yours alone" note).
        let bare = with_live::<AutomataflOffering, _>(channel, move |live| {
            embed_text(&surface_for::<AutomataflOffering>(live, &actor("pv")).0)
        })
        .expect("the bare viewer projection renders");
        assert!(
            !bare.contains(offering::PRIVATE_ACT_FIELD),
            "the bare viewer projection is the PRE-FIX object — it must not already contain the \
             plaque, or assertion 2 proves nothing about the channel split adding it",
        );
        assert!(
            !public_text.contains(offering::PRIVATE_ACT_FIELD),
            "the PUBLIC board must not carry the private plaque — it is not yours alone, and it \
             is where the controls already are",
        );

        close_in::<AutomataflOffering>(channel);
    }

    /// **THE PLAYED AUTOMATAFL FOLD IS MINTABLE AT THE SIZE DISCORD ACTUALLY PLAYS.**
    ///
    /// The dead path this pins: `/crown` folds a played automatafl match through
    /// [`dreggnet_game_board::AutomataflMatch::played`], whose leaves resolve the PROVEN Lean
    /// descriptors for the played board's size (`Leg R` = resolve, `Leg A` = step). The Discord
    /// surface played 5×5, and no descriptor was ever emitted at n=5 — so **every** automatafl fold
    /// failed, 100% of the time, with `MatchError::NoDescriptor(5, _)`.
    ///
    /// Nothing caught it, and the reason is worth keeping: `dreggnet-game-board`'s own
    /// `n5_has_no_descriptor_blocked_not_faked` pinned the REFUSAL as *correct* (blocked, not
    /// faked) — it asserted the guard works, never that the SHIPPED surface stayed on the right
    /// side of it. The coupling between "the size the bot plays" and "the sizes the fold can mint"
    /// was the untested edge, so that is what this asserts, reading the size off a REAL live
    /// Discord session rather than a constant.
    ///
    /// Deliberately NOT `assert_eq!(n, 11)`: the board may move again (it has once), and what must
    /// hold is not "11" but "a size whose descriptors exist". Written this way it keeps biting.
    #[test]
    fn a_played_automatafl_fold_is_mintable_at_the_live_board_size() {
        use dregg_automatafl::resolve_witness::resolve_descriptor_ident;
        use dregg_automatafl::witness::step_descriptor_name;
        use dregg_circuit::descriptor_by_name::descriptor_by_name;

        let channel = 771_160u64;
        close_in::<AutomataflOffering>(channel);
        offering::open_in(
            channel,
            || AutomataflOffering,
            SessionConfig::with_seed(channel),
        )
        .expect("automatafl opens");

        // The size the bot ACTUALLY deals a board at, read from the live session.
        let n = with_live::<AutomataflOffering, _>(channel, |live| live.session.start_board().n)
            .expect("a live automatafl board");

        assert!(
            descriptor_by_name(&step_descriptor_name(n)).is_some(),
            "the live Discord automatafl board is {n}×{n}, and NO Lean step descriptor is emitted \
             at n={n}: every /crown fold of a played match refuses with NoDescriptor({n}, \
             \"step\"). Either emit the descriptor at this size or do not deal this size.",
        );
        assert!(
            descriptor_by_name(resolve_descriptor_ident(n)).is_some(),
            "the live Discord automatafl board is {n}×{n}, and NO Lean resolve descriptor is \
             emitted at n={n}: the played fold's Leg R cannot be lowered, so /crown refuses every \
             match played on this board.",
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

        // ⚑ The `(turn, arg)` pair is DISCOVERED from the live offering, not hardcoded. It used
        // to be a literal `("comp", 3)`, which assumed the scheduled engine's fixed action order
        // and its fixed card pick — an assumption that stopped holding the moment I-cut-you-choose
        // made the order and the cut a seat's own decision. A test that names a decision index by
        // hand is pinned to one shape of the decision space; this asks for whatever the seat to
        // move may actually do.
        let first_enabled = |c: u64| {
            with_live::<SeatedTug, _>(c, |live| {
                live.offering
                    .actions(&live.session)
                    .into_iter()
                    .find(|action| action.enabled)
            })
            .flatten()
            .expect("the seat to move always has an enabled affordance")
        };

        // Alice claims seat A by landing her first play — a real landed receipt.
        let a_move = first_enabled(channel);
        match drive::<SeatedTug>(
            channel,
            &fire_id_in::<SeatedTug>(channel, &a_move.turn, a_move.arg).unwrap(),
            alice.clone(),
        ) {
            Driven::Fired(o) => assert!(o.landed(), "alice's play lands + claims seat A: {o:?}"),
            other => panic!("alice's play must drive a turn, got {other:?}"),
        }
        // Bob claims seat B only by LANDING his own first play. A refusal must never
        // ghost-reserve a seat.
        let b_move = first_enabled(channel);
        match drive::<SeatedTug>(
            channel,
            &fire_id_in::<SeatedTug>(channel, &b_move.turn, b_move.arg).unwrap(),
            bob.clone(),
        ) {
            Driven::Fired(o) => assert!(o.landed(), "bob's play lands + claims seat B: {o:?}"),
            other => panic!("bob's play must drive a turn, got {other:?}"),
        }

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

        // The ACTUAL async-handler policy is represented by `channel_surfaces`:
        // the first card is what Discord publishes to the whole channel; the
        // second is sent ephemerally to Alice. This is the leak canary that the
        // old handler failed — it edited Alice's `render_for` into the shared
        // message even though the offering declared hidden information.
        let (shared_card, private_card) = with_live::<SeatedTug, _>(channel, {
            let alice = alice.clone();
            move |live| channel_surfaces::<SeatedTug>(live, &alice)
        })
        .expect("live");
        let shared_json = serde_json::to_string(&shared_card.0).expect("shared embed serializes");
        let shared_controls_json =
            serde_json::to_string(&shared_card.1).expect("shared controls serialize");
        let private_json = serde_json::to_string(
            &private_card
                .as_ref()
                .expect("hidden game receives an ephemeral companion")
                .0,
        )
        .expect("private embed serializes");
        assert!(
            private_card
                .as_ref()
                .expect("private companion")
                .1
                .is_empty(),
            "private companions are read-only; actions stay on the shared board"
        );
        assert!(
            shared_json.contains("hidden hand"),
            "the channel still receives useful public fog: {shared_json}"
        );
        assert!(
            !shared_json.contains("card #"),
            "no exact card identity may enter the shared Discord message: {shared_json}"
        );
        assert!(
            !shared_controls_json.contains("card #"),
            "no exact card identity may enter the shared Discord controls: {shared_controls_json}"
        );
        assert!(
            private_json.contains("card #"),
            "the seated player still receives their hand ephemerally: {private_json}"
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
