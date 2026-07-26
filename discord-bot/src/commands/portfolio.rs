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
use crate::embeds;

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

/// The catalog keys served by their own **bespoke slash command** rather than `/play` — the
/// complement of `/play`'s reach within the shared catalog. Each one is asserted to still have
/// a registered home somewhere on `commands::menus::SLASH_SURFACE` by the parity test below.
///
/// ⚑ **THESE ARE THE KEYS THE CHEAT CODE CANNOT OPEN**, because [`all_play_keys`] subtracts
/// them: `open_offering_by_key` has no arm for a bespoke frontend, so `/play cheat code:dungeon`
/// answers [`CheatCode::OwnCommand`] rather than routing to it. This array is therefore also the
/// SET that resolves to that variant — the hand-written `OWN_COMMANDS` table that used to restate
/// these six keys with their invocations beside them is gone, and
/// `commands::menus::offering_door` supplies both the invocation and whether a player can reach
/// it. Five of the six are off the ship list, and their commands are off the advertised surface
/// with them, so what the Cheat Code has to say for those is that the offering is not open here —
/// naming a `DREGG_LAB_GUILD_ID` route would be an instruction they cannot follow.
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
/// ⚠ **This narrows the `/play` PICKER only.** Discord enforces its own choice list, so an
/// unshipped key cannot be typed into `/play open` even though it is still mounted. The typeable
/// door for those is the **Cheat Code** ([`read_cheat_code`], `/play cheat code:<key>`), which
/// dispatches through the exact same [`open_offering_by_key`] this picker does; the per-type
/// component/modal routes (`commands::offering::route_component`, which covers every mounted type)
/// and each bespoke subcommand are untouched.
pub fn play_keys() -> Vec<&'static str> {
    all_play_keys()
        .into_iter()
        .filter(|k| dreggnet_catalog::is_shipped(k))
        .collect()
}

/// **Every key [`open_offering_by_key`] can actually dispatch** — the shared catalog
/// ([`dreggnet_catalog::CATALOG_KEYS`]) minus the [`BESPOKE_COMMAND_KEYS`], plus the
/// [`DISCORD_EXTRA_PLAY_KEYS`] and the [`DISCORD_OPT_IN_PLAY_KEYS`]. NOT narrowed by the ship list.
///
/// This is the REACH of `/play`, as distinct from its advertised [`play_keys`] shelf, and it is what
/// the Cheat Code resolves against. Keeping the two derived from one expression is the point: a key
/// the picker hides is still, provably, a key the opener knows
/// (`the_cheat_code_reaches_every_key_the_picker_hides`).
pub fn all_play_keys() -> Vec<&'static str> {
    dreggnet_catalog::CATALOG_KEYS
        .iter()
        .copied()
        .filter(|k| !BESPOKE_COMMAND_KEYS.contains(k))
        .chain(DISCORD_EXTRA_PLAY_KEYS)
        .chain(DISCORD_OPT_IN_PLAY_KEYS)
        .collect()
}

/// The `offering` picker — the ONE construction of `/play`'s choice enum, so `open` and `status`
/// offer a player exactly the same vocabulary rather than two lists that can drift apart.
fn offering_option(description: &str) -> CreateCommandOption {
    let mut option =
        CreateCommandOption::new(CommandOptionType::String, "offering", description).required(true);
    for key in play_keys() {
        option = option.add_string_choice(key, key);
    }
    option
}

/// Register `/play <offering>` — open any SHIPPED offering (`play_keys`) in this channel.
pub fn register() -> CreateCommand {
    CreateCommand::new("play")
        .description("Open one receipted game, market, or engine offering in this channel")
        .add_option(offering_option(
            "Which portfolio offering to open in this channel",
        ))
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

/// **Register `/play status offering:<key>` — the READ-ONLY re-post of your own private view.**
///
/// ⚑ WHY IT EXISTS. `commands::offering::private_act_plaque` — the one piece of copy that explains
/// the public-board/private-hand split — told a player *"This private copy does not update itself
/// — ask for status again to refresh it"*, and there was no status action: `register`'s `action`
/// option offered exactly `verify` and `submit raid proof`. Both shipped hidden-information games
/// (automatafl, tug) carry that plaque, so a player who dismissed or lost the ephemeral holding
/// their hand had one thing left to try — `/play open offering:<key>` — which finds the live
/// session and renders `commands::open_guard::refuse_with_confirm`: *"Opening a new one would
/// **wipe it**… Press **Replace it**… or **Keep it**."* Neither button shows them their hand, and
/// the live one destroys a two-player match. The bot's own self-help routed into a match-wiping
/// dialog.
///
/// It is a subcommand rather than another `action:` choice because the plaque has to name
/// something that reads like what it does — and because an `action` on `open` would put the
/// read-only path behind the word "open", which is precisely the confusion that produced the
/// hazard. Same picker as `open` ([`offering_option`]); none of `open`'s acting options.
pub fn register_status() -> CreateCommand {
    CreateCommand::new("status")
        // Covers both audiences honestly: a hidden-information offering answers with the invoker's
        // OWN private view as a fresh ephemeral; a public one re-posts its board to the channel.
        .description(
            "Show a live game in this channel: your own private view if it has one. Reads only",
        )
        .add_option(offering_option(
            "Which live offering to show · your own view of it if it is a hidden game",
        ))
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

    open_offering_by_key(ctx, command, state, &key).await;
}

/// **THE ONE OPEN PATH** — open `key` in this channel and post its surface, projected for the
/// invoker. `/play open offering:<key>` (the advertised picker) and `/play cheat code:<key>` (the
/// Cheat Code) both land here, so the second door is a second *spelling* and not a second
/// mechanism: same ACK, same `identity_of` viewer derivation, same channel-seeded
/// [`SessionConfig`], same per-identity routing for the RPG keys, same
/// `commands::open_guard::refuse_with_confirm` protection of a live session, and the same
/// `commands::offering::channel_surfaces` split that keeps a hidden-information offering's private
/// projection in an EPHEMERAL followup instead of the shared channel message.
///
/// ⚑ It therefore grants NOTHING. Every gate that applied to the picker applies here because it is
/// literally the same function body; the only thing the Cheat Code changes is which strings Discord
/// will let you type into the box.
pub async fn open_offering_by_key(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
    key: &str,
) {
    let key = key.to_owned();
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
                    "`{other}` is not in the portfolio. Pick one of the `/play` choices."
                ))
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, vec![]).await;
            return;
        }
    };

    // ⚑ **THE FLAGSHIP'S REFUSAL, TRANSLATED.** This is where `/play open offering:descent` lands
    // when the substrate will not deploy, and it used to read "The executor refused to open the
    // session: {e}" — two defects in one line. "The executor" is machinery a player has never been
    // introduced to (`commands::start::help_embed` defines "receipt", "committed" and "turn", never
    // that), and `{e}` was a bare passthrough of whatever `dungeon_on_dregg` raised: "fail-closed",
    // "Lean-subset", "install_constraint_oracle". `offering::deploy_refusal_embed` renders the
    // player half; the engineer half is already in the operator log, emitted by `offering::open_in`
    // at the instant of refusal.
    if let Err(e) = opened {
        let embed = offering::deploy_refusal_embed("The offering was not opened", &e);
        ack::edit_slash(ctx, command, embed, vec![]).await;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE CHEAT CODE — a free-text door onto the unlisted offerings
// ─────────────────────────────────────────────────────────────────────────────

/// What a typed Cheat Code turned out to name. A pure function of the string, so the whole
/// resolution is testable without a Discord token — and so the reach of the affordance is a thing
/// you can READ rather than infer from an async handler.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheatCode {
    /// A key [`open_offering_by_key`] dispatches. Opened through that exact path.
    Open(&'static str),
    /// A key that EXISTS but is served by its own command. The Cheat Code names that command
    /// instead of building a second route to it — that would be a second mechanism, and the
    /// command was never the thing Discord made untypeable.
    ///
    /// ⚑ **THE INVOCATION IS NOT CARRIED HERE.** It used to be, out of a hand-written
    /// `OWN_COMMANDS` table, and that table could not express the thing that actually mattered:
    /// five of its six commands are un-advertised, so `handle_cheat`'s *"It was never hidden from
    /// you; it just answers to a different command"* was FALSE for `dungeon`, `council`, `doc`,
    /// `grain` and `hermes` — a player guessing "dungeon" (plausible: it was the flagship command
    /// before the pare-down) was confidently told to type something Discord will not offer them.
    /// The path AND whether it is reachable now come from `commands::menus::offering_door`, the
    /// same derivation `open_hint` reads, at render time.
    OwnCommand { key: &'static str },
    /// The one easter egg.
    Konami,
    /// Nothing recognised. Says something and does nothing.
    Unknown,
}

/// Alias spellings a person plausibly types for a real key. Deliberately tiny: the Cheat Code is a
/// door, not a parser.
const CHEAT_ALIASES: [(&str, &str); 6] = [
    ("multiway-tug", "tug"),
    ("dark-bazaar", "bazaar"),
    ("achievements", "cheevos"),
    ("cheevo", "cheevos"),
    ("campaign", DescentCampaignOffering::KEY),
    ("raid", dreggnet_surfaces::private_raid::KEY),
];

/// The shelf, as a sentence — derived from `dreggnet_catalog::SHIPPED_KEYS` so the Cheat Code's
/// answers cannot go on naming three games after the ship list changes.
fn shelf_sentence() -> String {
    let keys: Vec<String> = dreggnet_catalog::SHIPPED_KEYS
        .iter()
        .map(|k| format!("`{k}`"))
        .collect();
    keys.join(" · ")
}

/// The Konami code, in the spellings a person actually types.
const KONAMI: [&str; 5] = [
    "uuddlrlrba",
    "up-up-down-down-left-right-left-right-b-a",
    "↑↑↓↓←→←→ba",
    "⬆⬆⬇⬇⬅➡⬅➡ba",
    "konami",
];

/// **Read a Cheat Code.** Trims, lowercases, drops a leading `/` or `offering:`, and folds spaces
/// and underscores to `-` — the four things that separate "what someone types" from "a catalog
/// key". Then: a real `/play` key, a key with its own command, the easter egg, or nothing.
///
/// ⚑ THE REACH IS EXACTLY [`all_play_keys`]. This function cannot name a key nothing registers, and
/// it cannot construct a route — [`CheatCode::Open`] carries a `&'static str` out of that array, so
/// the value it hands the opener is one the opener already accepted from the picker.
pub fn read_cheat_code(raw: &str) -> CheatCode {
    let mut norm: String = raw
        .trim()
        .to_lowercase()
        .chars()
        .map(|c| {
            if c == '_' || c == ' ' || c == '.' {
                '-'
            } else {
                c
            }
        })
        .collect();
    for prefix in ["/", "play-", "open-", "offering:", "offering-", "key-"] {
        if let Some(rest) = norm.strip_prefix(prefix) {
            norm = rest.to_string();
        }
    }
    let norm = norm.trim_matches('-').to_string();
    if norm.is_empty() {
        return CheatCode::Unknown;
    }
    if KONAMI.contains(&norm.as_str()) {
        return CheatCode::Konami;
    }
    let resolved = CHEAT_ALIASES
        .iter()
        .find(|(alias, _)| *alias == norm)
        .map(|(_, key)| *key)
        .unwrap_or(norm.as_str());
    if let Some(key) = all_play_keys().into_iter().find(|k| *k == resolved) {
        return CheatCode::Open(key);
    }
    // A key served by its own command, read off [`BESPOKE_COMMAND_KEYS`] — the array that already
    // DEFINES that set (it is what `all_play_keys` subtracts), rather than a second hand-written
    // list of the same six keys with their invocations re-typed beside them.
    if let Some(key) = BESPOKE_COMMAND_KEYS.into_iter().find(|k| *k == resolved) {
        return CheatCode::OwnCommand { key };
    }
    CheatCode::Unknown
}

/// `/play cheat code:<anything>` — **the Cheat Code menu.**
///
/// ⚑ WHY IT EXISTS. Paring the public shelf to three games
/// ([`dreggnet_catalog::SHIPPED_KEYS`]) left Discord as the one host where an unlisted key was
/// *untypeable*, because a slash-command choice enum takes no free strings — every other host still
/// opens an unlisted offering by key (web: `/offerings/{key}/session/{id}`; Telegram: `/open
/// <key>`; WeChat: by key). This restores that, and only that.
///
/// ⚑ WHAT IT CAN REACH: exactly [`all_play_keys`], via [`open_offering_by_key`] — the same function
/// the `/play open` picker calls, with the same ACK, viewer derivation, live-session confirm guard,
/// per-identity RPG routing and hidden-information ephemeral split.
///
/// ⚑ WHAT IT CANNOT REACH: anything else. It grants no capability, skips no check, and reads no
/// state — an unlisted offering was ALREADY openable on every other frontend, so "typeable on
/// Discord too" is parity, not escalation. A key with its own command gets the command NAMED, never
/// a second route built to it. And it is a Discord affordance only: Telegram's
/// hidden-information-in-a-group refusal lives in `dreggnet-telegram` and is untouched by anything
/// here, so nothing typed into this box can cause a private projection to be painted into a shared
/// Telegram chat.
pub async fn handle_cheat(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let typed = command
        .data
        .options
        .iter()
        .find(|o| o.name == "code")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    match read_cheat_code(&typed) {
        // The ordinary door, opened by the ordinary path. Public, exactly like `/play open`.
        CheatCode::Open(key) => open_offering_by_key(ctx, command, state, key).await,
        // ⚑ THE TRUTH PER KEY, not one sentence for six keys. `market` really is reachable —
        // `/play market open` rides the advertised arcade — and for that one the old copy was
        // right. The other five ride `/adventure`, `/govern` and `/hermes`, which came off the
        // advertised surface with their offerings, so they are registered ONLY inside
        // `DREGG_LAB_GUILD_ID`: *"it was never hidden from you; it just answers to a different
        // command"* was the opposite of the truth for `dungeon`, `council`, `doc`, `grain` and
        // `hermes`. The distinction is `OfferingDoor::reachable`, derived from the same
        // `SLASH_SURFACE`/ship-list rule that decides what Discord is given — and the invocation
        // comes from the same place, so there is no second list to go stale.
        CheatCode::OwnCommand { key } => {
            let embed = match crate::commands::menus::offering_door(key) {
                Some(door) if door.reachable => {
                    embeds::dregg_embed(&format!("`{key}` has its own door")).description(format!(
                        "That one is not opened through `/play open`. Run `{}`. It was never \
                         hidden from you; it just answers to a different command.",
                        door.open
                    ))
                }
                // Registered nowhere a player can see it, so NAME NO COMMAND: an invocation they
                // cannot type is worse than admitting the offering is closed.
                _ => embeds::dregg_embed(&format!("`{key}` is not open here right now"))
                    .description(format!(
                        "You guessed a real one: `{key}` exists, it is built, and it still \
                         plays. It is just not on this server's command list at the moment, so \
                         there is nothing for you to type and nothing was opened: it came off the \
                         shelf, and un-listing things is how the shelf stays short.\n\nWhat IS \
                         open: {}. Pick one of those, or run `/play menu` to see them properly.",
                        shelf_sentence()
                    )),
            };
            cheat_reply(ctx, command, embed).await;
        }
        // ⚑ THE EASTER EGG, and it is exactly the right joke for this product: the most famous
        // cheat code in the world, granting thirty lives that the executor declines to record.
        // Nothing is committed — which is the promise the whole arcade rests on, said as a gag.
        CheatCode::Konami => {
            cheat_reply(
                ctx,
                command,
                embeds::dregg_embed("⬆ ⬆ ⬇ ⬇ ⬅ ➡ ⬅ ➡ 🅑 🅐").description(
                    "**30 lives granted.**\n\nRefused: no such turn (nothing committed · \
                     anti-ghost).\n\nThe referee re-ran it against the rules and declined. That \
                     is the whole product, and you just made it say so out loud.",
                ),
            )
            .await;
        }
        CheatCode::Unknown => {
            cheat_reply(
                ctx,
                command,
                embeds::dregg_embed("Nothing answers to that").description(format!(
                    "`{}` opens no door here. No harm done: this box only ever opens something \
                     that already exists, so a wrong guess costs you nothing.\n\nOn the shelf: \
                     {}. `/play menu` shows them properly.",
                    typed.chars().take(60).collect::<String>(),
                    shelf_sentence()
                )),
            )
            .await;
        }
    }
}

/// The Cheat Code's non-opening answers — EPHEMERAL, because a miss, a pointer or a joke is between
/// the person who typed it and the bot. An actual open is public: it posts a shared board, which is
/// what every other `/play` open does and what makes the session joinable.
async fn cheat_reply(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .embed(embed)
                    .ephemeral(true),
            ),
        )
        .await;
}

/// **`/play status offering:<key>` — re-post the invoker's OWN private view. READ-ONLY.**
///
/// The destination `commands::offering::private_act_plaque` names. It is the SAME
/// [`offering::handle_status`] every bespoke offering command has always exposed as `/… status`
/// (`/hermes status`, `/govern council status`), reused rather than re-built — the brief's
/// instruction and the right one: that function already threads the requester's derived identity
/// through `surface_for`, already drops the controls and re-attaches the plaque for a
/// hidden-information offering, and already makes THAT answer ephemeral — a hand or a sealed move
/// can never land in the channel — while a public offering's board stays channel-visible, which is
/// the same split `channel_surfaces` makes on open.
///
/// ⚑ **WHY IT CANNOT TOUCH THE LIVE SESSION.** It never reaches [`open_offering_by_key`], so it
/// never reaches `open_and_post`, so it never reaches `commands::open_guard` — there is no path
/// from here to a Replace-it button. What it does reach is:
///
/// * `offering::ensure_live` — which returns immediately if a session is live, and whose
///   `resume_in` explicitly refuses to overwrite one that won the race; it can only bring a
///   channel's persisted log BACK, never replace what is there;
/// * `offering::with_live` — a render closure. `surface_for` calls
///   `Offering::render_for`/`actions_for`, both `&self`/`&Session` reads. No `advance`, no
///   `open_in`, no `close_in`, no `drive`, so no turn is attempted and no receipt is minted.
///
/// The eight identity-owned RPG keys route to the invoker's persistent world
/// (`commands::rpg_world::handle_status`), which is read-only by the same argument: it renders out
/// of the replayed host WITHOUT `ensure_open`, so asking for status cannot mint a world either.
///
/// ⚠ **RESIDUAL, inherited not introduced.** [`offering::handle_status`] answers with
/// `create_response` rather than a defer, because Discord wants the ephemeral flag at DEFER time
/// and this surface only learns whether the offering is hidden-information after it renders. On a
/// channel whose session is merely COLD, `ensure_live` replays the whole log first, and a long
/// enough replay can pass the 3-second window. That is the shape every `/… status` in the bot has
/// always had (`/hermes status`, `/govern council status`, `/play market status`), and it does not
/// touch the case this door exists for — a player who just lost the ephemeral of a LIVE game, where
/// `ensure_live` returns on its first branch. Fixing it means giving `handle_status` an explicit
/// ephemerality argument and a deferred body at all five existing call sites, which is a change to
/// that function and not a second copy of it.
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let key = command
        .data
        .options
        .iter()
        .find(|o| o.name == "offering")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    if crate::commands::rpg_world::is_rpg_key(&key) {
        crate::commands::rpg_world::handle_status(ctx, command, state, &key).await;
        return;
    }
    match key.as_str() {
        DescentCampaignOffering::KEY => {
            offering::handle_status::<DescentCampaignOffering>(ctx, command, state).await
        }
        "descent" => offering::handle_status::<NativeDescentOffering>(ctx, command, state).await,
        "bazaar" => offering::handle_status::<DarkBazaarOffering>(ctx, command, state).await,
        "tug" => offering::handle_status::<SeatedTug>(ctx, command, state).await,
        "automatafl" => offering::handle_status::<AutomataflOffering>(ctx, command, state).await,
        #[cfg(feature = "private-bazaar-live")]
        PrivateBazaarRaidOffering::KEY => {
            offering::handle_status::<PrivateBazaarRaidOffering>(ctx, command, state).await
        }
        dreggnet_surfaces::private_raid::KEY => {
            offering::handle_status::<HostedProofAssignedRaidOffering>(ctx, command, state).await
        }
        "names" => offering::handle_status::<NamesOffering>(ctx, command, state).await,
        "compute" => offering::handle_status::<ComputeOffering>(ctx, command, state).await,
        "party" => offering::handle_status::<PartyOffering>(ctx, command, state).await,
        "gear" => {
            offering::handle_status::<dreggnet_gear::LoadoutOffering>(ctx, command, state).await
        }
        "talents" => {
            offering::handle_status::<dreggnet_gear::TalentTreeOffering>(ctx, command, state).await
        }
        "overworld" => {
            offering::handle_status::<crate::commands::overworld::OverworldPlay>(
                ctx, command, state,
            )
            .await
        }
        other => {
            let _ = command
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(format!(
                                "`{other}` is not an offering served here, so there is no private \
                                 view of it to re-post. Nothing was changed. Pick one from \
                                 `/play menu`."
                            ))
                            .ephemeral(true),
                    ),
                )
                .await;
        }
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
            // Derived, not spelled: this line carried the pre-fold `/play offering:<key>` too.
            .description(format!(
                "Open one first with `{}`.",
                crate::commands::menus::open_invocation(dreggnet_surfaces::private_raid::KEY)
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
                    "**Your private view** · only you can read this hand / sealed move. Use the shared board's controls to act.",
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
mod cheat_code_tests {
    use super::*;

    /// ⚑ **THE CHEAT CODE'S WHOLE JOB, as a property.** Every key the ship list took OUT of the
    /// `/play` picker must be reachable by typing it — otherwise the affordance does not do the one
    /// thing it exists for. Driven off the two derived arrays, so re-listing or un-listing an
    /// offering can never make this stale.
    #[test]
    fn the_cheat_code_reaches_every_key_the_picker_hides() {
        let picker = play_keys();
        let hidden: Vec<&str> = all_play_keys()
            .into_iter()
            .filter(|k| !picker.contains(k))
            .collect();
        assert!(
            !hidden.is_empty(),
            "the ship list hides nothing, so this test is checking nothing — if that is \
             intentional, delete it rather than leaving a green vacuum"
        );
        for key in hidden {
            assert_eq!(
                read_cheat_code(key),
                CheatCode::Open(key),
                "`{key}` is untypeable in the picker AND unreachable by cheat code — the pare-down \
                 would have deleted it in practice"
            );
        }
        // And the three on the shelf still resolve, so the box is not a second, stranger vocabulary.
        for key in dreggnet_catalog::SHIPPED_KEYS {
            assert_eq!(read_cheat_code(key), CheatCode::Open(key));
        }
    }

    /// **It resolves keys, not routes.** The normalizer is allowed to be forgiving about typing;
    /// it is not allowed to invent a target. Anything that is not a registered key comes back
    /// `Unknown` — including the shapes an attacker reaches for.
    #[test]
    fn the_cheat_code_invents_no_target() {
        for junk in [
            "",
            "   ",
            "-",
            "bazaar/../../dungeon",
            "bazaar\0",
            "descent;drop",
            "../secrets",
            "http://example.com/bazaar",
            "select * from offerings",
            "bazaar bazaar",
            "🐉",
        ] {
            assert_eq!(
                read_cheat_code(junk),
                CheatCode::Unknown,
                "`{junk}` must resolve to nothing"
            );
        }
    }

    /// **Forgiving about typing, exactly and only in the four documented ways.**
    #[test]
    fn the_cheat_code_forgives_the_typing_and_not_the_target() {
        for spelling in [
            "bazaar",
            "  Bazaar  ",
            "BAZAAR",
            "/bazaar",
            "offering:bazaar",
            "dark_bazaar",
            "Dark Bazaar",
        ] {
            assert_eq!(
                read_cheat_code(spelling),
                CheatCode::Open("bazaar"),
                "`{spelling}`"
            );
        }
        assert_eq!(read_cheat_code("multiway-tug"), CheatCode::Open("tug"));
        assert_eq!(read_cheat_code("achievements"), CheatCode::Open("cheevos"));
    }

    /// **A key with its own command is POINTED AT, never re-routed.** The Cheat Code builds no
    /// second door onto `/adventure dungeon` — those commands were always typeable, so there is
    /// nothing here to restore and a second mechanism would be pure risk.
    ///
    /// ⚑ And the pointing is HONEST PER KEY. The old shape carried the invocation in the enum out
    /// of a hand-written table and could not express reachability, so one sentence ("it was never
    /// hidden from you") covered six keys and was false for five. The door now comes from
    /// `menus::offering_door`, which answers both questions at once.
    #[test]
    fn a_bespoke_key_gets_its_command_named_and_no_new_route() {
        let mut reachable = 0usize;
        let mut lab_only = 0usize;
        for key in BESPOKE_COMMAND_KEYS {
            match read_cheat_code(key) {
                CheatCode::OwnCommand { key: k } => assert_eq!(k, key),
                other => panic!("`{key}` should name its own command, got {other:?}"),
            }
            assert!(
                !all_play_keys().contains(&key),
                "`{key}` must not ALSO be dispatchable through the /play open path"
            );
            let door = crate::commands::menus::offering_door(key)
                .unwrap_or_else(|| panic!("`{key}` has its own command but no derived door"));
            assert!(door.open.starts_with('/'), "{}", door.open);
            assert!(
                crate::commands::menus::path_is_registered(&door.open),
                "the `{key}` Cheat Code answer would name `{}`, which this build does not register",
                door.open
            );
            if door.reachable {
                reachable += 1;
            } else {
                lab_only += 1;
            }
        }
        // NOT VACUOUS IN EITHER DIRECTION. If every bespoke key were reachable the per-key
        // distinction would be untested and the honest branch dead; if none were, the "run this
        // command" branch would be. Today it is `market` against the other five — and if that
        // ever becomes one-sided, this fails and the reply's two branches get re-examined
        // deliberately instead of one of them rotting unread.
        assert!(
            reachable > 0 && lab_only > 0,
            "the Cheat Code's reachable/not-open split is one-sided ({reachable} reachable, \
             {lab_only} lab-only), so one branch of its reply is untested"
        );
    }

    /// The easter egg is one lookup with a handful of spellings — not an interpreter.
    #[test]
    fn the_easter_egg_is_a_lookup() {
        for spelling in KONAMI {
            assert_eq!(read_cheat_code(spelling), CheatCode::Konami, "{spelling}");
        }
        assert_eq!(read_cheat_code("UUDDLRLRBA"), CheatCode::Konami);
        assert_eq!(
            read_cheat_code("up up down down left right left right b a"),
            CheatCode::Konami
        );
        // Near-misses are not eggs, and eggs are not keys.
        assert_eq!(read_cheat_code("uuddlrlrab"), CheatCode::Unknown);
        assert!(!all_play_keys().contains(&"konami"));
    }
}

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
        // ⚑ **THE HINT IS ASSERTED AGAINST THE REGISTERED TREE, NOT A LITERAL.** This line used
        // to read `assert_eq!(…, "/play offering:bazaar")` — pinning the pre-fold spelling — so
        // the one test touching `open_hint` GUARANTEED the broken string instead of catching it.
        // What must hold is not a spelling but that the hint is typeable.
        assert!(
            crate::commands::menus::path_is_registered(&DarkBazaarOffering::open_hint()),
            "the Bazaar's open hint is not a path this build registers: {}",
            DarkBazaarOffering::open_hint()
        );
        assert_eq!(
            DarkBazaarOffering::open_hint(),
            crate::commands::menus::open_invocation("bazaar"),
            "the hint must come from the ONE derivation, not a second spelling"
        );
        for k in dreggnet_catalog::CATALOG_KEYS {
            assert!(
                BESPOKE_COMMAND_KEYS.contains(&k) || offering::generic_offering_keys().contains(&k),
                "catalog offering `{k}` must stay mounted even when it is off the picker"
            );
        }
    }

    /// **The bespoke-command catalog keys still have a built home** — the offering SET is the
    /// shared catalog's, and the command surface stays consistent with it: every catalog key
    /// `/play open` does NOT serve rides as its own top-level command or as a fold under one
    /// (`commands::menus::SLASH_SURFACE`, advertised rows OR lab rows), and `/play` itself is
    /// registered with `open`.
    ///
    /// ⚑ This asserts the path EXISTS, not that it is advertised. Five of these six keys came
    /// off `dreggnet_catalog::SHIPPED_KEYS`, so their commands are un-advertised and answer
    /// only inside `DREGG_LAB_GUILD_ID` — which is the whole point of keeping this test
    /// separate from `menus::tests::the_lab_surface_is_not_registered_globally`.
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
                .unwrap_or_else(|| panic!("bespoke key `{key}` has no declared home"));
            match home {
                None => assert!(
                    crate::commands::menus::all_surface_names().contains(&key),
                    "catalog offering `{key}` is claimed top-level but `/{key}` is not built"
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
            crate::commands::menus::advertised_names().contains(&"play"),
            "`/play` (the derived-catalog reach) must be ADVERTISED — it is the arcade door"
        );
        assert!(
            crate::commands::menus::subcommand_names("play")
                .iter()
                .any(|s| s == "open"),
            "`/play open` (the portfolio opener) must be registered"
        );
    }

    /// ⚑ **EVERY OFFERING THIS BUILD SERVES HAS A TYPED DOOR, AND IT IS ONE DISCORD ROUTES.**
    ///
    /// The `open_hint` sweep, driven off `commands::offering::for_each_generic_offering` (THE one
    /// mounting table) plus [`BESPOKE_COMMAND_KEYS`] — so an offering added to the bot is checked
    /// the day it is mounted, and nothing here re-types a key.
    ///
    /// This is the tooth `24e47322b` needed. That commit folded `/play` behind subcommands and
    /// eighteen `open_hint` impls kept returning `/play offering:<key>`, a path Discord refuses to
    /// route; the ONE test that touched `open_hint` asserted the broken literal. Every hint (and
    /// the status path the hidden-hand plaque names, and the verify path) now walks the registered
    /// JSON.
    #[test]
    fn every_offering_door_is_a_path_this_build_registers() {
        use crate::commands::menus::{offering_door, path_is_registered};

        let keys: Vec<&str> = offering::generic_offering_keys()
            .into_iter()
            .chain(BESPOKE_COMMAND_KEYS)
            .collect();
        assert!(
            keys.len() > 20,
            "the census collapsed to {} keys — this tooth is checking almost nothing",
            keys.len()
        );
        for key in keys {
            let door = offering_door(key).unwrap_or_else(|| {
                panic!(
                    "`{key}` is mounted on Discord but `menus::offering_door` gives it no typed \
                     door, so its `open_hint` falls back to a spelling nothing verified"
                )
            });
            for (what, path) in [
                ("open", &door.open),
                ("status", &door.status),
                ("verify", &door.verify),
            ] {
                assert!(
                    path_is_registered(path),
                    "the `{key}` {what} path is `{path}`, which this build does not register — a \
                     player told to type it gets nothing from Discord at all"
                );
            }
        }

        // ⚑ THE NEGATIVE CONTROL — the exact string that shipped. Without this the assertions
        // above could be passing because `path_is_registered` says yes to everything.
        assert!(
            !path_is_registered("/play offering:tug"),
            "`/play offering:tug` is the PRE-FIX spelling and is not registered; if this passes, \
             the instrument is blind and the sweep above proves nothing"
        );
        assert!(
            path_is_registered("/play open offering:tug"),
            "…and the post-fold spelling is registered, so the instrument is not simply saying no"
        );
    }

    /// `/play` registers `action:verify` (backlog Tier-2 #10) and the `status` subcommand — the
    /// portfolio offerings, the flagship games included, expose the chain re-verifier AND the
    /// read-only private-view re-post as pressable commands, not test-only capability.
    #[test]
    fn play_registers_the_verify_action_and_the_status_door() {
        let cmd = serde_json::to_value(register()).expect("the command serializes");
        let text = cmd.to_string();
        assert!(text.contains("\"action\""), "{text}");
        assert!(text.contains("\"verify\""), "{text}");

        // ⚑ The plaque's destination has to be REGISTERED, not merely written. The whole headline
        // defect was one sentence of copy naming a `status` refresh that did not exist.
        let subs = crate::commands::menus::subcommand_names("play");
        assert!(
            subs.iter().any(|s| s == "status"),
            "`/play status` (the read-only private-view re-post the hidden-hand plaque names) is \
             not registered — found {subs:?}"
        );
        let status = serde_json::to_value(register_status()).expect("it serializes");
        assert!(
            status.to_string().contains("\"offering\""),
            "`/play status` must carry the offering picker: {status}"
        );
        // And it carries NONE of the acting options: a read-only door that can be handed a
        // `proof` attachment is not read-only in the player's mental model.
        for acting in ["\"action\"", "\"proof\""] {
            assert!(
                !status.to_string().contains(acting),
                "`/play status` must not offer {acting}: {status}"
            );
        }
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

        // ⚑⚑ **2b. AND THE REFRESH IT OFFERS IS A REAL, READ-ONLY DESTINATION.**
        //
        // THE HEADLINE DEFECT. The plaque shipped saying "ask for status again to refresh it" and
        // `/play` had no status action — its `action` option offered `verify` and `submit raid
        // proof` and nothing else. So the one piece of copy explaining the public/private split
        // sent a player who had lost their hand to `/play open offering:automatafl`, which finds
        // the live session and renders `open_guard::refuse_with_confirm` — "Opening a new one
        // would **wipe it**… Press **Replace it**… or **Keep it**" — whose only live button
        // DESTROYS a two-player match, and neither of whose buttons shows them their hand.
        //
        // Three assertions, because the wound had three parts: the plaque must NAME a path, that
        // path must be one Discord ROUTES, and it must not be the open path.
        let status = <AutomataflOffering as DiscordOffering>::status_hint();
        assert!(
            text.contains(&status),
            "the plaque must name the exact refresh path `{status}`, or the player is back to \
             guessing and the only thing left to guess is a re-open: {text}",
        );
        assert!(
            crate::commands::menus::path_is_registered(&status),
            "the plaque names `{status}`, which this build does not register — the pre-fix copy \
             pointed at nothing at all, which is how it ended up pointing at the wipe dialog",
        );
        let open = <AutomataflOffering as DiscordOffering>::open_hint();
        assert_ne!(
            status, open,
            "the refresh must not be the OPEN path — that is the defect verbatim",
        );
        assert!(
            !text.contains(&open),
            "the plaque must not name the open path anywhere: for a live session that path IS \
             the wipe-confirm card ({open})",
        );

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
