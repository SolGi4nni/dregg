//! The curated menu surface — every old flat slash command folded behind a
//! menu-driven top-level command, and then the menu itself PARED to what we ship.
//!
//! [`SLASH_SURFACE`] is the ONE list: one row per top-level command, each row
//! naming the [`Door`] it is. An **offering-shaped** row is advertised *iff* its key
//! is on `dreggnet_catalog::SHIPPED_KEYS`, so paring or re-listing an offering moves
//! Discord's `/` menu with every other host and nothing here needs touching. A row
//! that is not offering-shaped (`/help`, `/verify`) has to say why it earns a slot.
//!
//! ⚑ **UN-ADVERTISED IS NOT DELETED.** A [`Door::Lab`] row keeps its module, its
//! handler, its `menu:`/component/modal routes and its `main.rs` router arm; only the
//! front door comes off the global `/` menu, and `DREGG_LAB_GUILD_ID` puts every one
//! of them back inside one guild ([`lab_commands`]). What that costs is written into
//! each row and re-checked by `the_lab_rows_name_what_they_cost`.
//!
//! Two mechanisms carry the fold:
//!
//! 1. **Registration by serialization** ([`fold`]): an existing module's
//!    `register()` builder is serialized to the Discord JSON it already
//!    produces and demoted to a subcommand (its flat options become
//!    sub-options) or a subcommand group (its subcommands ride along) of the
//!    new top-level command. The old option trees are never re-typed, so they
//!    cannot drift.
//! 2. **Dispatch by re-nesting** ([`as_command`]): when a folded subcommand is
//!    invoked, the interaction is cloned, `data.name` is rewritten to the old
//!    command name and `data.options` un-nested by one level, and the clone is
//!    handed to the EXISTING handler — which sees exactly the shape the old
//!    flat command produced (same options, same resolved map, same
//!    respond-once token).
//!
//! The `menu` subcommand of every folded top-level (and the `/dregg` hub's
//! surface buttons, custom-id prefix `menu:`) renders the button menu; the
//! buttons route to existing component flows (`start:*` actions and modals,
//! `dregg:*` dashboard panels) or to the `execute_*` read helpers the feature
//! modules expose.

use serde_json::{Map, Value};
use serenity::all::{
    ButtonStyle, CommandDataOption, CommandDataOptionValue, CommandInteraction,
    ComponentInteraction, ComponentInteractionDataKind, Context, CreateActionRow, CreateButton,
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage, CreateSelectMenu,
    CreateSelectMenuKind, CreateSelectMenuOption, EditInteractionResponse,
};

use crate::BotState;
use crate::commands;
use crate::embeds;

// ─── menu component custom-ids (the `menu:` namespace) ──────────────────────

/// In-place navigation: swap the current menu message to another surface's menu.
const ID_GO_PREFIX: &str = "menu:go:";
/// Fire a real read through a feature module's `execute_*` helper.
const ID_RUN_PREFIX: &str = "menu:run:";
/// The `/play` arcade select — pick an offering to see how to open it.
const ID_PICK_PLAY: &str = "menu:pick:play";
/// The featured game doors — the ship list, one card each.
const ID_PICK_GAME: &str = "menu:pick:game";

/// One player-facing game door. This is Discord information architecture, not
/// a second game registry: the `key` is checked against the real `/play` and
/// `/adventure` routes below, while the game keeps its own verbs and rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GameDoor {
    key: &'static str,
    title: &'static str,
    rhythm: &'static str,
    open: &'static str,
    verify: &'static str,
    privacy: &'static str,
    special: &'static str,
}

/// ⚑ **THE FEATURED DOORS MUST BE ON THE SHIP LIST.** This is a hand-written advertising shelf —
/// the discord-bot builds no `OfferingHost`, so nothing filters it automatically and a stale entry
/// here would keep promoting an offering we took off every other surface.
/// `the_game_doors_are_exactly_the_ship_list` below is the gate. It previously featured `dungeon`,
/// `bazaar` and `private-raid`, which is exactly the leak `dreggnet_catalog::SHIPPED_KEYS` exists
/// to stop; those offerings all still open by key, they are just no longer advertised.
///
/// ⚑ **Every door here stays LIVE in a guild channel, and unlike Telegram that is honest.** The
/// second, orthogonal filter (`dreggnet_offerings::shelf`) withholds a live control for an offering
/// declaring `Offering::hidden_information` when the surface has more than one reader, because
/// Telegram's group session is ONE message the whole room reads and a hidden-information game
/// simply cannot be hosted there — its `/offerings` shelf dims those rows. Discord has a
/// single-reader surface *inside* a shared channel: `commands::offering::channel_surfaces` posts
/// the VIEWER-BLIND board to the channel and the player's own hidden state as an EPHEMERAL
/// companion (with `private_act_plaque` saying where the controls live). So automatafl and tug play
/// here, in a guild, with two readerships out of one session — which is why the `privacy` field
/// below is a real boundary statement and not an apology. If that split is ever unwired, THIS shelf
/// becomes the dishonest one and the gate belongs here too.
const GAME_DOORS: [GameDoor; 3] = [
    GameDoor {
        key: "descent",
        title: "The Descent",
        rhythm: "a dungeon crawl · one dungeon a day, the same for everyone · one life, no retries",
        open: "/play open offering:descent",
        verify: "/play open offering:descent action:verify",
        privacy: "Your run belongs to you — nobody else can move it — but the board it plays on in this channel is public.",
        special: "go deeper for better loot; you only keep what you carry back out",
    },
    GameDoor {
        key: "automatafl",
        title: "Automatafl",
        rhythm: "a two-player board game · you both choose in secret, then both moves are revealed at once",
        open: "/play open offering:automatafl",
        verify: "/play open offering:automatafl action:verify",
        privacy: "Your sealed move is hidden until the reveal; the board itself is public.",
        special: "a neutral piece reacts to both moves, so you are guessing at your opponent rather than waiting on them",
    },
    GameDoor {
        key: "tug",
        title: "Multiway-Tug",
        rhythm: "a two-player game of hidden influence over seven guilds · cards go down face down",
        open: "/play open offering:tug",
        verify: "/play open offering:tug action:verify",
        privacy: "Your hand is yours alone; a pull becomes public only once both sides have committed.",
        special: "one side cuts, the other chooses",
    },
];

fn game_door(key: &str) -> Option<&'static GameDoor> {
    GAME_DOORS.iter().find(|door| door.key == key)
}

fn game_door_card(door: &GameDoor) -> CreateEmbed {
    embeds::dregg_embed(door.title)
        .description(
            "One Discord contract, game-specific verbs: open one scoped session, act through a \
             typed affordance, receive a landed receipt or an anti-ghost refusal, then replay it.",
        )
        .field("How it moves", door.rhythm, false)
        .field("Open", format!("`{}`", door.open), false)
        .field("Replay / verify", format!("`{}`", door.verify), false)
        .field("Privacy boundary", door.privacy, false)
        .field("Distinctive affordance", door.special, false)
}

// ─── registration: fold existing builders into the curated menu commands ────

/// Serialize an existing `CreateCommand` builder to its Discord JSON body.
fn command_json(cmd: &serenity::all::CreateCommand) -> Value {
    serde_json::to_value(cmd).expect("CreateCommand serializes to the Discord JSON body")
}

/// The `options` array of a serialized command (empty when it had none).
fn options_of(v: &Value) -> Vec<Value> {
    v.get("options")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default()
}

/// Demote an existing command builder to a subcommand (type 1, when its options
/// were flat / absent) or a subcommand group (type 2, when it had subcommands)
/// of a new parent — the old options ride along verbatim. `rename` overrides
/// the old command name (e.g. `federation-status` → `status` under
/// `/federation`).
fn fold(cmd: serenity::all::CreateCommand, rename: Option<&str>) -> Value {
    let v = command_json(&cmd);
    let name = rename
        .map(str::to_owned)
        .or_else(|| v.get("name").and_then(Value::as_str).map(str::to_owned))
        .expect("a registered command has a name");
    let description = v
        .get("description")
        .cloned()
        .unwrap_or_else(|| Value::String(name.clone()));
    let options = options_of(&v);
    // Discord forbids a group inside a group; every folded command is at most
    // one level deep (subcommands of a former top-level), which the parity
    // test below re-checks structurally.
    let is_group = options
        .iter()
        .any(|o| matches!(o.get("type").and_then(Value::as_u64), Some(1) | Some(2)));
    let mut m = Map::new();
    m.insert("type".into(), Value::from(if is_group { 2u64 } else { 1 }));
    m.insert("name".into(), Value::String(name));
    m.insert("description".into(), description);
    if !options.is_empty() {
        m.insert("options".into(), Value::Array(options));
    }
    Value::Object(m)
}

/// A hand-built subcommand (type 1) with no options.
fn sub(name: &str, description: &str) -> Value {
    let mut m = Map::new();
    m.insert("type".into(), Value::from(1u64));
    m.insert("name".into(), Value::String(name.into()));
    m.insert("description".into(), Value::String(description.into()));
    Value::Object(m)
}

/// The standard `menu` subcommand every folded top-level carries.
fn menu_sub() -> Value {
    sub("menu", "Open this surface's button menu")
}

/// ⚑ **The Cheat Code subcommand** — `/play cheat code:<anything>`, the one FREE-TEXT option on the
/// `/play` surface.
///
/// It exists because `open`'s `offering` option is a Discord CHOICE ENUM: paring the public shelf to
/// three games left an unlisted key untypeable here and only here, while every other host still
/// opens one by key. Hand-built rather than folded because it is not a retired flat command — and
/// its option is deliberately a plain string with no `choices`, which is the whole point.
/// `commands::portfolio::handle_cheat` resolves it and dispatches through the SAME
/// `open_offering_by_key` the picker uses.
fn cheat_sub() -> Value {
    let mut m = Map::new();
    m.insert("type".into(), Value::from(1u64));
    m.insert("name".into(), Value::String("cheat".into()));
    m.insert(
        "description".into(),
        Value::String("Cheat Code — type a key to open something that is not on the shelf".into()),
    );
    let mut opt = Map::new();
    opt.insert("type".into(), Value::from(3u64)); // STRING
    opt.insert("name".into(), Value::String("code".into()));
    opt.insert(
        "description".into(),
        Value::String("An offering key, or whatever you feel like trying".into()),
    );
    opt.insert("required".into(), Value::Bool(true));
    m.insert("options".into(), Value::Array(vec![Value::Object(opt)]));
    Value::Object(m)
}

/// A top-level chat-input command from parts.
fn top(name: &str, description: &str, options: Vec<Value>) -> Value {
    let mut m = Map::new();
    m.insert("name".into(), Value::String(name.into()));
    m.insert("description".into(), Value::String(description.into()));
    if !options.is_empty() {
        m.insert("options".into(), Value::Array(options));
    }
    Value::Object(m)
}

// ─── THE CURATED SLASH SURFACE — the ONE list ────────────────────────────────

/// **Why a top-level command has a slot on Discord's `/` menu.** The whole taste
/// judgement, one variant per reason, so that "should this be advertised?" is answered
/// by a rule and not by whoever last edited a `vec![]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Door {
    /// **A door to ONE offering** — advertised *iff* that key is on
    /// `dreggnet_catalog::SHIPPED_KEYS`. This is the DERIVATION: paring or re-listing an
    /// offering moves Discord's `/` menu in step with the web, Telegram and WeChat
    /// shelves, and nothing in this file needs touching
    /// (`the_offering_doors_follow_the_ship_list`).
    Offering(&'static str),
    /// **Not offering-shaped, and a player needs it anyway** — the explicit allow-list.
    /// The string is the reason it earns a slot, and this variant is the ONLY way a
    /// non-offering command reaches an ordinary player's `/` menu.
    Player(&'static str),
    /// **An operator tool.** Registered globally, but stamped with Discord's
    /// `default_member_permissions: "0"`, which the client honours by HIDING the command
    /// from any member who cannot use it — so it is off a player's `/` menu while ember
    /// (Administrator in their own guild) keeps it, and it stays usable in a DM with the
    /// bot where guild permissions do not apply.
    ///
    /// Visibility was never the authority in either direction: every subcommand under an
    /// operator row re-checks `Config::is_admin` (`commands::admin::plan`) or the pinned
    /// `admin_discord_id` (`handle_cleanup`) before it reads its arguments.
    Operator(&'static str),
    /// **Deliberately off the menu.** ⚑ UN-ADVERTISED IS NOT DELETED: the module, the
    /// handler, the `menu:`/component/modal routes and the `main.rs` router arm are all
    /// untouched — only the front door comes off the GLOBAL surface, and setting
    /// `DREGG_LAB_GUILD_ID` re-registers every one of these inside that one guild
    /// ([`lab_commands`]), which is how ember keeps the whole workshop without putting it
    /// in a stranger's autocomplete.
    ///
    /// The string names WHAT A PLAYER LOSES while it is unset. Discord will not route a
    /// command it has not been given, so this is the one variant that genuinely takes a
    /// typed path away, and it has to say so.
    Lab(&'static str),
}

/// One top-level command and the [`Door`] it is.
#[derive(Clone, Copy, Debug)]
pub struct Slash {
    pub name: &'static str,
    pub door: Door,
}

/// ⚑ **THE ONE LIST.** Every top-level command the bot knows how to build, and whether we
/// advertise it. [`global_commands`] and [`lab_commands`] are both derived from this by
/// [`advertises`]; `crate::main`'s boot registration, its unknown-command audit check and
/// the teeth in this file all read it rather than restating it.
///
/// To change the menu, change a row. To ship or pare an OFFERING, edit
/// `dreggnet_catalog::SHIPPED_KEYS` and its [`Door::Offering`] row follows on its own.
pub const SLASH_SURFACE: &[Slash] = &[
    // ── the operator row ────────────────────────────────────────────────────
    Slash {
        name: "dregg",
        door: Door::Operator(
            "the hub dashboard plus `/dregg admin` (narrator, posture, treasury, the \
             $DREGG pool, run-credits) and `/dregg cleanup`",
        ),
    },
    // ── the games ───────────────────────────────────────────────────────────
    // Advertised because `descent` is on the ship list. `/descent` is the DAILY
    // beacon-seeded world with its own reveal cron, board and tournament — a different
    // object from the actor-bound `/play open offering:descent` mount, which is why both
    // exist and why the daily keeps a command of its own.
    Slash {
        name: "descent",
        door: Door::Offering("descent"),
    },
    Slash {
        name: "play",
        door: Door::Player(
            "the arcade: `open` (its choices ARE the ship list), the free-text `cheat` \
             door for a key the picker cannot offer, and the auction `market`",
        ),
    },
    // `dungeon` came off the ship list, so the narrative-worlds command comes off the
    // menu with it. Re-ship `dungeon` and `/adventure` returns with no edit here.
    Slash {
        name: "adventure",
        door: Door::Offering("dungeon"),
    },
    // ── you ─────────────────────────────────────────────────────────────────
    Slash {
        name: "cipherclerk",
        door: Door::Player(
            "you: your cell and keys, DEC balance/send/history/faucet, $DREGG \
             run-credits, and `link-web` — the one ceremony that stops a player being \
             two people on one leaderboard",
        ),
    },
    Slash {
        name: "verify",
        door: Door::Player(
            "the proof surface — the thing that makes a receipted game worth playing: \
             fetch AND verify a turn's STARK, browse committed state, fold a win into \
             one O(1) crown",
        ),
    },
    Slash {
        name: "help",
        door: Door::Player("onboarding, the 2-minute tour, and the map of this menu"),
    },
    // ── the lab: registered only in `DREGG_LAB_GUILD_ID` ────────────────────
    Slash {
        name: "gallery",
        door: Door::Lab(
            "publishing and remixing procgen universes (`list`/`show`/`play`/`publish`) \
             — the whole UGC registry, which no shipped game needs",
        ),
    },
    // `council` is off the ship list, so the DAO surface goes with it.
    Slash {
        name: "govern",
        door: Door::Offering("council"),
    },
    Slash {
        name: "identity",
        door: Door::Lab(
            "CapTP cap-share/accept/delegate/list/revoke/peer, signed handoffs, the \
             external-cell link+unlink ceremonies (and `link-prove`, which only ever \
             answered a challenge `link-cipherclerk` issued), your own LLM key, and \
             roles-as-capabilities. `link-web` is the one piece a player needs, and it \
             is folded into `/cipherclerk` so it survives this row",
        ),
    },
    // `hermes` is off the ship list; `grain` and `doc` ride inside it.
    Slash {
        name: "hermes",
        door: Door::Offering("hermes"),
    },
    Slash {
        name: "federation",
        door: Door::Lab(
            "federation status/peers/setup, presence attestation, the atomic \
             two-agent `coordinate` settle, `channel` (claim your semi-private DreggNet \
             Cloud channel — the Hermes typing surface) and the `deos` cap-gated \
             affordance cards. ⚑ `channel` is the biggest single loss here; the \
             `start:channel` BUTTON on `/help` still claims one",
        ),
    },
    Slash {
        name: "leaderboard",
        door: Door::Lab(
            "the top-DEC-holders board. The GAME boards are elsewhere and stay \
             advertised: `/descent board`, `/descent tournament`, `/verify crown`",
        ),
    },
];

/// Whether a [`Door`] reaches an ordinary player's `/` menu. The offering arm is the
/// derivation from `dreggnet_catalog::SHIPPED_KEYS`; the others are the declared intent.
pub fn advertises(door: &Door) -> bool {
    match *door {
        Door::Offering(key) => dreggnet_catalog::is_shipped(key),
        Door::Player(_) | Door::Operator(_) => true,
        Door::Lab(_) => false,
    }
}

/// The advertised top-level names, in [`SLASH_SURFACE`] order — what a stranger sees when
/// they press `/`. `crate::main` reads this instead of keeping its own copy.
pub fn advertised_names() -> Vec<&'static str> {
    SLASH_SURFACE
        .iter()
        .filter(|s| advertises(&s.door))
        .map(|s| s.name)
        .collect()
}

/// The un-advertised (lab) top-level names, in [`SLASH_SURFACE`] order.
pub fn lab_names() -> Vec<&'static str> {
    SLASH_SURFACE
        .iter()
        .filter(|s| !advertises(&s.door))
        .map(|s| s.name)
        .collect()
}

/// Every name this build can route — advertised plus lab. The router keeps an arm for all
/// of them (a lab command still arrives when `DREGG_LAB_GUILD_ID` is set), so this, not
/// [`advertised_names`], is what "is this a command we know?" must be asked against.
pub fn all_surface_names() -> Vec<&'static str> {
    SLASH_SURFACE.iter().map(|s| s.name).collect()
}

/// **The guild that gets the un-advertised surface**, from `DREGG_LAB_GUILD_ID`.
///
/// Read here rather than in `Config` deliberately: it is a REGISTRATION-TIME fact about
/// which guild receives which command set, consumed once in `Handler::ready`, and it
/// authorizes nothing. Unset = the lab commands are registered nowhere, which
/// `crate::main` reports at boot by NAME rather than leaving as a silent subtraction.
pub fn lab_guild_id() -> Option<u64> {
    let raw = std::env::var("DREGG_LAB_GUILD_ID").ok()?;
    raw.trim().parse().ok().filter(|id| *id != 0)
}

/// Build one top-level command by name. ONE construction site per command, whichever
/// surface it lands on — [`global_commands`] and [`lab_commands`] only decide *where* the
/// same JSON is registered, so a lab command cannot drift from the shape it had when it
/// was advertised.
fn command_for(name: &str) -> Value {
    match name {
        // The hub dashboard (its buttons summon the rest; the retired /dashboard +
        // /status fold in as buttons), plus the operator-only `admin` GROUP.
        "dregg" => dregg_command(),
        // Today's beacon-seeded daily roguelite world, unchanged.
        "descent" => command_json(&commands::descent::register()),
        // The Arcade shelf: open any SHIPPED offering; /market folds in; `cheat` is the
        // FREE-TEXT door (`commands::portfolio::handle_cheat`) that `open`'s choice enum
        // cannot be.
        "play" => top(
            "play",
            &format!(
                "{} — open a receipted game in this channel",
                dreggnet_catalog::SURFACE_NAME
            ),
            vec![
                menu_sub(),
                fold(commands::portfolio::register(), Some("open")),
                cheat_sub(),
                fold(commands::market::register(), None),
            ],
        ),
        // The narrative worlds; /dungeon (the party crawl) folds in.
        "adventure" => top(
            "adventure",
            "Narrative worlds — the shared AI-narrated party dungeon and its kin",
            vec![
                menu_sub(),
                fold(commands::fiction::register(), Some("dungeon")),
            ],
        ),
        // You + your funds: the cipherclerk identity view, the whole economy, and the
        // web-identity link ceremony.
        "cipherclerk" => cipherclerk_command(),
        // The UGC universe registry, unchanged.
        "gallery" => command_json(&commands::gallery::register()),
        // The DAO surface: council, approvals, bounties, intents.
        "govern" => top(
            "govern",
            "The DAO surface — councils, approvals, bounties, and signed intents",
            vec![
                menu_sub(),
                fold(commands::council::register(), None),
                fold(commands::polis::register_council_status(), None),
                fold(commands::polis::register_council_approve(), None),
                fold(commands::bounty::register(), None),
                fold(commands::intent::register(), None),
            ],
        ),
        // The proof surface: fetch + verify artifacts, browse state.
        "verify" => top(
            "verify",
            "The proof surface — fetch, verify, and browse committed state",
            vec![
                menu_sub(),
                fold(commands::status::register_proof(), None),
                fold(commands::explorer::register(), None),
                fold(commands::crown::register(), None),
                fold(commands::export_nft::register(), None),
                fold(commands::card::register(), None),
            ],
        ),
        // Granting authority: caps, handoffs, link ceremonies, keys, roles.
        "identity" => top(
            "identity",
            "Grant authority — capabilities, handoffs, link ceremonies, and your LLM key",
            vec![
                menu_sub(),
                fold(commands::captp::register_share(), None),
                fold(commands::captp::register_accept(), None),
                fold(commands::captp::register_delegate(), None),
                fold(commands::captp::register_list(), None),
                fold(commands::captp::register_revoke(), None),
                fold(commands::captp::register_peer(), None),
                fold(commands::handoff::register(), None),
                fold(commands::handoff::register_redeem(), None),
                fold(commands::handoff::register_status(), None),
                fold(commands::federation::register_link(), None),
                fold(commands::federation::register_unlink(), None),
                fold(commands::link_proof::register(), None),
                // Also folded into `/cipherclerk`, which is the copy a player can reach:
                // the two registrations are the same builder on the same handler, so this
                // is one route spelled in two places, not a second mechanism.
                fold(commands::link_proof::register_link_web(), None),
                fold(commands::key::register(), None),
                // Discord roles as caps — folds as a GROUP (`show`/`unlock`/`grant` ride
                // along) rather than taking a top-level slot of its own.
                fold(crate::roles_caps::register(), None),
            ],
        ),
        // The confined agent, plus the confined grain + shared doc.
        "hermes" => hermes_command(),
        // The network: status, peers, presence, coordination.
        "federation" => top(
            "federation",
            "The network — federation status, peers, presence, and coordination",
            vec![
                menu_sub(),
                fold(commands::federation::register_status(), Some("status")),
                fold(commands::federation::register_peers(), Some("peers")),
                fold(commands::federation::register_setup(), Some("setup")),
                fold(commands::social::register_activity(), None),
                fold(commands::coordinate::register(), None),
                fold(commands::channel::register(), None),
                fold(commands::presence::register(), None),
                fold(commands::deos::register(), None),
            ],
        ),
        // Glory, unchanged.
        "leaderboard" => command_json(&commands::social::register_leaderboard()),
        // Onboarding + the tour (the old /start) + the map.
        "help" => top(
            "help",
            "How the bot works — onboarding, the 2-minute tour, and the command map",
            vec![],
        ),
        other => panic!(
            "`{other}` is on SLASH_SURFACE but has no builder in `command_for` \
             (`every_surface_row_has_a_builder` is the tooth that should have caught this)"
        ),
    }
}

/// Stamp Discord's `default_member_permissions: "0"` onto a command — no guild member may
/// invoke it (so the client hides it) unless a guild overwrite grants it or they hold
/// Administrator. Applied to [`Door::Operator`] rows only.
fn hide_from_players(mut v: Value) -> Value {
    if let Value::Object(m) = &mut v {
        m.insert(
            "default_member_permissions".into(),
            Value::String("0".into()),
        );
    }
    v
}

/// **The GLOBAL slash surface** — the advertised rows of [`SLASH_SURFACE`], in order.
/// Registered with a bulk PUT, so a name that leaves this list disappears from Discord on
/// the next boot.
pub fn global_commands() -> Vec<Value> {
    SLASH_SURFACE
        .iter()
        .filter(|s| advertises(&s.door))
        .map(|s| {
            let v = command_for(s.name);
            if matches!(s.door, Door::Operator(_)) {
                hide_from_players(v)
            } else {
                v
            }
        })
        .collect()
}

/// **The LAB slash surface** — the un-advertised rows, byte-identical to the JSON they
/// registered when they were global (same [`command_for`], same handlers). `crate::main`
/// PUTs these into [`lab_guild_id`] when it is set, and names them in a boot warning when
/// it is not.
pub fn lab_commands() -> Vec<Value> {
    SLASH_SURFACE
        .iter()
        .filter(|s| !advertises(&s.door))
        .map(|s| command_for(s.name))
        .collect()
}

/// `/dregg` — the hub, plus the operator-only `admin` group and the category reaper.
///
/// Discord has no per-SUBCOMMAND permission, so nothing here relies on hiding a
/// subcommand: the whole command carries `default_member_permissions: "0"`
/// ([`Door::Operator`]), and every subcommand under it re-checks the admin gate anyway —
/// `commands::admin::plan` before it reads its arguments, and [`handle_cleanup`] against
/// the pinned `admin_discord_id`.
fn dregg_command() -> Value {
    let base = command_json(&commands::dashboard::register());
    let description = base
        .get("description")
        .and_then(Value::as_str)
        .unwrap_or("Open your Starbridge app dashboard")
        .to_string();
    let mut options = options_of(&base);
    // ⚑ `hub` exists because Discord will NOT let you invoke a command that has
    // subcommands without picking one — the moment the `admin` group folded in, bare
    // `/dregg` stopped being typeable and the hub dashboard `handle_dregg`'s fallback arm
    // renders became unreachable by slash (it survived only behind `menu:go:hub` buttons).
    // This is the `menu` subcommand's job, under the name the hub already answers to.
    options.push(sub(
        "hub",
        "The hub dashboard — the panels and controls behind every surface",
    ));
    options.push(fold(commands::admin::register(), None));
    // De-duplicate the `dreggnet-*` offering categories a restart accreted. It lives on
    // the operator command rather than under `/federation` (where it used to ride)
    // BECAUSE it is a per-guild action: it must be runnable in whichever guild grew the
    // duplicates, and `/federation` is now registered only in the lab guild.
    options.push(sub(
        "cleanup",
        "Admin: de-duplicate dreggnet-* offering categories left by restarts",
    ));
    top("dregg", &description, options)
}

/// `/cipherclerk` — the module's own subcommands ride verbatim; the economy
/// commands fold in beside them.
fn cipherclerk_command() -> Value {
    let mut options = vec![menu_sub()];
    options.extend(options_of(
        &command_json(&commands::cipherclerk::register()),
    ));
    options.push(fold(commands::transfer::register_send(), None));
    options.push(fold(commands::social::register_history(), None));
    options.push(fold(commands::social::register_faucet(), None));
    options.push(fold(commands::pay::register_balance(), None));
    options.push(fold(commands::pay::register_buy(), None));
    options.push(fold(commands::pay::register_treasury(), None));
    // ⚑ `/cipherclerk link-web` — the ISSUER half of the phrase-link ceremony: a
    // single-use code that proves THIS Discord account to the web identity page, so a
    // player whose web identity is 24 words (not a browser-held root key, which is all
    // `/tg/link` and `/da/link` can consume) can stop being two people on one
    // leaderboard. It is the ONE thing off the `/identity` surface that a player of a
    // shipped game actually needs, so it is folded here — onto the same handler — rather
    // than left behind in the lab.
    options.push(fold(commands::link_proof::register_link_web(), None));
    top(
        "cipherclerk",
        "You + your funds — identity, balance, tokens, and the DEC/$DREGG economy",
        options,
    )
}

/// `/hermes` — the confined agent's own subcommands ride verbatim; the grain
/// and doc offerings fold in as groups.
fn hermes_command() -> Value {
    let mut options = vec![menu_sub()];
    options.extend(options_of(&command_json(&commands::hermes::register())));
    options.push(fold(commands::grain::register(), None));
    options.push(fold(commands::doc::register(), None));
    top(
        "hermes",
        "The confined offerings — your Hermes agent, a confined grain, a shared doc",
        options,
    )
}

// ─── the coverage ledger: every retired flat command → its new home ─────────

/// How a retired flat command is reached now. Every entry is asserted structurally
/// against [`global_commands`] **and** [`lab_commands`] by the coverage test below — the
/// question it answers is "did any old command lose its typed path in the code?", not
/// "is it advertised?". Whether the home it names is on the player's `/` menu is the
/// separate question that `the_lab_surface_is_not_registered_globally` answers.
pub enum Reach {
    /// Still a top-level command (same name).
    Top,
    /// A subcommand or group under the named top-level (old options intact).
    Under(&'static str),
    /// A button on the named top-level's menu (no typed path; ≤2 interactions).
    Button(&'static str),
}

/// (old command, how it is reached now). The full retired surface — the
/// coverage test walks this and fails if any old command lost its path.
pub const OLD_COMMAND_REACH: &[(&str, Reach)] = &[
    ("start", Reach::Button("help")),
    ("help", Reach::Top),
    ("explorer", Reach::Under("verify")),
    ("presence", Reach::Under("federation")),
    ("cipherclerk", Reach::Top),
    ("send", Reach::Under("cipherclerk")),
    ("gallery", Reach::Top),
    ("status", Reach::Button("dregg")),
    ("proof", Reach::Under("verify")),
    ("faucet", Reach::Under("cipherclerk")),
    ("leaderboard", Reach::Top),
    ("history", Reach::Under("cipherclerk")),
    ("dregg", Reach::Top),
    ("cap-share", Reach::Under("identity")),
    ("cap-accept", Reach::Under("identity")),
    ("cap-delegate", Reach::Under("identity")),
    ("cap-list", Reach::Under("identity")),
    ("cap-revoke", Reach::Under("identity")),
    ("cap-peer", Reach::Under("identity")),
    ("council-status", Reach::Under("govern")),
    ("council-approve", Reach::Under("govern")),
    ("setup-federation", Reach::Under("federation")), // renamed `setup`
    ("link-cipherclerk", Reach::Under("identity")),
    ("unlink-cipherclerk", Reach::Under("identity")),
    ("handoff", Reach::Under("identity")),
    ("handoff-redeem", Reach::Under("identity")),
    ("handoff-status", Reach::Under("identity")),
    ("intent", Reach::Under("govern")),
    ("bounty", Reach::Under("govern")),
    ("federation-status", Reach::Under("federation")), // renamed `status`
    ("federation-peers", Reach::Under("federation")),  // renamed `peers`
    ("activity", Reach::Under("federation")),
    ("dashboard", Reach::Button("dregg")),
    ("deos", Reach::Under("federation")),
    ("card", Reach::Under("verify")),
    ("coordinate", Reach::Under("federation")),
    ("channel", Reach::Under("federation")),
    ("key", Reach::Under("identity")),
    ("dungeon", Reach::Under("adventure")),
    ("descent", Reach::Top),
    ("council", Reach::Under("govern")),
    ("market", Reach::Under("play")),
    ("hermes", Reach::Top),
    ("grain", Reach::Under("hermes")),
    ("doc", Reach::Under("hermes")),
    ("play", Reach::Under("play")), // its open flow is `/play open`
    ("buy-credits", Reach::Under("cipherclerk")),
    ("credits", Reach::Under("cipherclerk")),
    ("treasury", Reach::Under("cipherclerk")),
    ("crown", Reach::Under("verify")),
    ("export", Reach::Under("verify")),
    ("link-prove", Reach::Under("identity")),
    // Never a flat command — folded straight in as `/identity roles`. Listed here so
    // the coverage test holds the path open the same way it does for the retired ones.
    ("roles", Reach::Under("identity")),
    // Likewise never flat: the operator surface folds straight in as `/dregg admin`, so the
    // global surface stays 13. Listed so the coverage test keeps that path open.
    ("admin", Reach::Under("dregg")),
];

/// The subcommand / group names a top-level exposes (test + boot aid).
///
/// Searches BOTH surfaces — the advertised one and the lab one — because "does this old
/// command still have a typed path?" is a question about the code we register, not about
/// what we currently advertise. Which surface a path landed on is the separate question,
/// answered by [`advertised_names`] / [`lab_names`] and asserted separately.
pub fn subcommand_names(top_name: &str) -> Vec<String> {
    global_commands()
        .into_iter()
        .chain(lab_commands())
        .collect::<Vec<_>>()
        .iter()
        .find(|c| c.get("name").and_then(Value::as_str) == Some(top_name))
        .map(|c| {
            options_of(c)
                .iter()
                .filter(|o| matches!(o.get("type").and_then(Value::as_u64), Some(1) | Some(2)))
                .filter_map(|o| o.get("name").and_then(Value::as_str).map(str::to_owned))
                .collect()
        })
        .unwrap_or_default()
}

// ─── dispatch: re-nest the interaction and call the existing handler ────────

/// The invoked top-level subcommand/group name and its inner options.
fn take_fold(command: &CommandInteraction) -> Option<(&str, Vec<CommandDataOption>)> {
    let first = command.data.options.first()?;
    let inner = match &first.value {
        CommandDataOptionValue::SubCommand(v) | CommandDataOptionValue::SubCommandGroup(v) => {
            v.clone()
        }
        _ => return None,
    };
    Some((first.name.as_str(), inner))
}

/// Clone the interaction as the OLD flat command: `data.name` rewritten,
/// `data.options` un-nested by one level. The existing handler sees exactly
/// the shape it always parsed (the resolved user/channel maps ride along; the
/// respond-once id + token are shared, and only the delegate responds).
fn as_command(
    command: &CommandInteraction,
    name: &str,
    options: Vec<CommandDataOption>,
) -> CommandInteraction {
    let mut c = command.clone();
    c.data.name = name.to_string();
    c.data.options = options;
    c
}

/// `/dregg` — `admin` → the operator surface (gated inside `commands::admin`); `cleanup` →
/// the per-guild category reaper (gated in [`handle_cleanup`]); anything else is the hub
/// dashboard, exactly as before.
pub async fn handle_dregg(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("admin", inner)) => {
            commands::admin::handle(ctx, &as_command(command, "admin", inner), state).await
        }
        Some(("cleanup", _)) => handle_cleanup(ctx, command, state).await,
        // `hub` and anything unrecognised: the hub dashboard, exactly as before.
        // `dashboard::handle` reads no options, so the `hub` wrapper is transparent to it.
        _ => commands::dashboard::handle(ctx, command, state).await,
    }
}

/// `/play` — `open` → the portfolio opener; `cheat` → the free-text Cheat Code door; `market` → the
/// auction offering; otherwise the arcade menu.
pub async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("open", inner)) => {
            commands::portfolio::handle(ctx, &as_command(command, "play", inner), state).await
        }
        // The Cheat Code re-nests exactly like a folded subcommand so the handler reads the same
        // flat option shape everything else does; it then routes through
        // `portfolio::open_offering_by_key`, the very function the `open` arm above reaches.
        Some(("cheat", inner)) => {
            commands::portfolio::handle_cheat(ctx, &as_command(command, "play", inner), state).await
        }
        Some(("market", inner)) => {
            commands::market::handle(ctx, &as_command(command, "market", inner), state).await
        }
        _ => respond_menu(ctx, command, play_view()).await,
    }
}

/// `/adventure` — `dungeon` → the shared AI-narrated party crawl; otherwise the
/// worlds menu.
pub async fn handle_adventure(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("dungeon", inner)) => {
            commands::fiction::handle(ctx, &as_command(command, "dungeon", inner), state).await
        }
        _ => respond_menu(ctx, command, adventure_view()).await,
    }
}

/// `/cipherclerk` — the module's own subcommands pass through untouched (the
/// command name never changed); the folded economy commands re-nest.
pub async fn handle_cipherclerk(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("menu", _)) | None => respond_menu(ctx, command, cipherclerk_view()).await,
        Some(("send", inner)) => {
            commands::transfer::handle(ctx, &as_command(command, "send", inner), state).await
        }
        Some(("history", _)) => commands::social::handle_history(ctx, command, state).await,
        Some(("faucet", _)) => commands::social::handle_faucet(ctx, command, state).await,
        Some(("credits", _)) => commands::pay::handle_balance(ctx, command, state).await,
        Some(("buy-credits", _)) => commands::pay::handle_buy(ctx, command, state).await,
        Some(("treasury", _)) => commands::pay::handle_treasury(ctx, command, state).await,
        // The web-identity link ceremony, on the SAME handler `/identity link-web` calls.
        // No options, so the interaction passes straight through rather than being
        // re-wrapped by `as_command`.
        Some(("link-web", _)) => commands::link_proof::handle_link_web(ctx, command, state).await,
        // create / balance / address / export / mint / attenuate / tokens /
        // authorize — the cipherclerk module's own dispatch, original shape.
        Some(_) => commands::cipherclerk::handle(ctx, command, state).await,
    }
}

/// `/govern` — councils, approvals, bounties, intents; otherwise the DAO menu.
pub async fn handle_govern(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("council", inner)) => {
            commands::council::handle(ctx, &as_command(command, "council", inner), state).await
        }
        Some(("council-status", inner)) => {
            commands::polis::handle_council_status(
                ctx,
                &as_command(command, "council-status", inner),
                state,
            )
            .await
        }
        Some(("council-approve", inner)) => {
            commands::polis::handle_council_approve(
                ctx,
                &as_command(command, "council-approve", inner),
                state,
            )
            .await
        }
        Some(("bounty", inner)) => {
            commands::bounty::handle(ctx, &as_command(command, "bounty", inner), state).await
        }
        Some(("intent", inner)) => {
            commands::intent::handle(ctx, &as_command(command, "intent", inner), state).await
        }
        _ => respond_menu(ctx, command, govern_view()).await,
    }
}

/// `/verify` — proofs, the explorer, the crown, exports, cards; otherwise the
/// proof-surface menu.
pub async fn handle_verify(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("proof", inner)) => {
            commands::status::handle_proof(ctx, &as_command(command, "proof", inner), state).await
        }
        Some(("explorer", inner)) => {
            commands::explorer::handle(ctx, &as_command(command, "explorer", inner), state).await
        }
        Some(("crown", inner)) => {
            commands::crown::handle(ctx, &as_command(command, "crown", inner), state).await
        }
        Some(("export", inner)) => {
            commands::export_nft::handle(ctx, &as_command(command, "export", inner), state).await
        }
        Some(("card", inner)) => {
            commands::card::handle(ctx, &as_command(command, "card", inner), state).await
        }
        _ => respond_menu(ctx, command, verify_view()).await,
    }
}

/// `/identity` — caps, handoffs, link ceremonies, the LLM key; otherwise the
/// delegation menu. (`/identity key set|rotate` open modals, which must be the
/// FIRST response — this dispatch never defers.)
pub async fn handle_identity(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("cap-share", inner)) => {
            commands::captp::handle_share(ctx, &as_command(command, "cap-share", inner), state)
                .await
        }
        Some(("cap-accept", inner)) => {
            commands::captp::handle_accept(ctx, &as_command(command, "cap-accept", inner), state)
                .await
        }
        Some(("cap-delegate", inner)) => {
            commands::captp::handle_delegate(
                ctx,
                &as_command(command, "cap-delegate", inner),
                state,
            )
            .await
        }
        Some(("cap-list", _)) => commands::captp::handle_list(ctx, command, state).await,
        Some(("cap-revoke", inner)) => {
            commands::captp::handle_revoke(ctx, &as_command(command, "cap-revoke", inner), state)
                .await
        }
        Some(("cap-peer", _)) => commands::captp::handle_peer(ctx, command, state).await,
        Some(("handoff", inner)) => {
            commands::handoff::handle(ctx, &as_command(command, "handoff", inner), state).await
        }
        Some(("handoff-redeem", inner)) => {
            commands::handoff::handle_redeem(
                ctx,
                &as_command(command, "handoff-redeem", inner),
                state,
            )
            .await
        }
        Some(("handoff-status", _)) => commands::handoff::handle_status(ctx, command, state).await,
        Some(("link-cipherclerk", inner)) => {
            commands::federation::handle_link(
                ctx,
                &as_command(command, "link-cipherclerk", inner),
                state,
            )
            .await
        }
        Some(("unlink-cipherclerk", _)) => {
            commands::federation::handle_unlink(ctx, command, state).await
        }
        Some(("link-prove", inner)) => {
            commands::link_proof::handle(ctx, &as_command(command, "link-prove", inner), state)
                .await
        }
        // No options, so the interaction is passed straight through (the `cap-list` / `handoff-status`
        // shape) rather than re-wrapped by `as_command`.
        Some(("link-web", _)) => commands::link_proof::handle_link_web(ctx, command, state).await,
        Some(("key", inner)) => {
            commands::key::handle(ctx, &as_command(command, "key", inner), state).await
        }
        Some(("roles", inner)) => {
            crate::roles_caps::handle(ctx, &as_command(command, "roles", inner), state).await
        }
        _ => respond_menu(ctx, command, identity_view()).await,
    }
}

/// `/hermes` — the agent's own subcommands pass through; grain + doc re-nest.
pub async fn handle_hermes(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("menu", _)) | None => respond_menu(ctx, command, hermes_view()).await,
        Some(("grain", inner)) => {
            commands::grain::handle(ctx, &as_command(command, "grain", inner), state).await
        }
        Some(("doc", inner)) => {
            commands::doc::handle(ctx, &as_command(command, "doc", inner), state).await
        }
        // open / status / verify — the hermes module's own dispatch.
        Some(_) => commands::hermes::handle(ctx, command, state).await,
    }
}

/// `/federation` — the network reads + ceremonies; otherwise the network menu.
pub async fn handle_federation(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("status", _)) => commands::federation::handle_status(ctx, command, state).await,
        Some(("peers", _)) => commands::federation::handle_peers(ctx, command, state).await,
        Some(("setup", _)) => commands::federation::handle_setup(ctx, command, state).await,
        Some(("activity", _)) => commands::social::handle_activity(ctx, command, state).await,
        Some(("coordinate", inner)) => {
            commands::coordinate::handle(ctx, &as_command(command, "coordinate", inner), state)
                .await
        }
        Some(("channel", _)) => commands::channel::handle(ctx, command, state).await,
        Some(("presence", inner)) => {
            commands::presence::handle(ctx, &as_command(command, "presence", inner), state).await
        }
        Some(("deos", inner)) => {
            commands::deos::handle(ctx, &as_command(command, "deos", inner), state).await
        }
        // `cleanup` moved to `/dregg cleanup`: it is a per-guild maintenance action and
        // `/federation` is now registered only in the lab guild, so leaving it here would
        // have made the reaper unrunnable in whichever guild grew the duplicates.
        _ => respond_menu(ctx, command, federation_view()).await,
    }
}

/// `/dregg cleanup` — ADMIN-ONLY maintenance: de-duplicate this guild's
/// `dreggnet-<offering>` offering categories (the restart-duplicate reaper) and
/// report the counts.
///
/// Strictly scoped by [`crate::orchestration::SessionOrchestrator::reconcile_guild`]:
/// only categories named exactly `dreggnet-<offering>` are touched, and custodial
/// `dregg-<id>` channels and operator feed channels are never moved or deleted.
///
/// The abandoned-dungeon-THREAD sweep is deliberately NOT wired here: dungeon runs
/// live in per-channel threads and the live-session index is in-memory only, so
/// after a restart every thread looks "orphaned" — a blind archive would kill live
/// runs. A safe thread sweep needs a durable session index (or a per-thread TTL) to
/// tell abandoned from active; until then it stays a TODO rather than a hazard.
async fn handle_cleanup(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // Admin gate: an unset ADMIN_DISCORD_ID DENIES (never "everyone is admin").
    if state.config.admin_discord_id != Some(command.user.id.get()) {
        let msg = CreateInteractionResponseMessage::new()
            .embed(embeds::warning_embed(
                "Admin only",
                "This maintenance action is limited to the pinned bot admin.",
            ))
            .ephemeral(true);
        let _ = command
            .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
            .await;
        return;
    }
    let Some(guild_id) = command.guild_id.map(|g| g.get()) else {
        let msg = CreateInteractionResponseMessage::new()
            .embed(embeds::warning_embed(
                "Run in a server",
                "Category cleanup only applies inside a guild.",
            ))
            .ephemeral(true);
        let _ = command
            .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
            .await;
        return;
    };

    // Defer (the reaper fetches channels and may issue edits/deletes).
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;

    let registered_by = state.config.admin_discord_id.unwrap_or(0);
    let embed = match state
        .orchestrator
        .reconcile_guild(
            guild_id,
            "dungeon",
            None, // fetch the live channel list ourselves
            &state.discord_caps,
            &ctx.http,
            registered_by,
        )
        .await
    {
        Ok(r) => embeds::success_embed("Category cleanup complete").description(format!(
            "Reconciled the `dreggnet-dungeon` categories in this server.\n\n\
                 \u{2022} Canonical category: {}\n\
                 \u{2022} Duplicates found: {}\n\
                 \u{2022} Duplicates deleted: {}\n\
                 \u{2022} Session channels re-filed: {}\n\n\
                 Custodial `dregg-<id>` and feed channels were never touched. \
                 (Abandoned dungeon *threads* are not swept — see the handler note.)",
            r.canonical_id
                .map(|c| format!("<#{c}>"))
                .unwrap_or_else(|| "none".into()),
            r.duplicates_found,
            r.duplicates_deleted,
            r.children_moved,
        )),
        Err(e) => embeds::error_embed(
            "Cleanup failed",
            &format!("Could not reconcile categories: {e}. The bot needs MANAGE_CHANNELS."),
        ),
    };
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// `/help` — the map of the 13 surfaces + the onboarding menu (the old
/// `/start`, tour included, rides along as the second embed's buttons).
pub async fn handle_help(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let (welcome, components) = commands::start::home_view(state, command.user.id.get()).await;
    let msg = CreateInteractionResponseMessage::new()
        .embed(commands::start::help_embed())
        .add_embed(welcome)
        .components(components)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

// ─── the menus themselves ────────────────────────────────────────────────────

fn button(id: &str, label: &str, style: ButtonStyle) -> CreateButton {
    CreateButton::new(id).label(label).style(style)
}

fn back_row() -> CreateActionRow {
    CreateActionRow::Buttons(vec![button(
        "menu:go:hub",
        "\u{2302} Hub",
        ButtonStyle::Secondary,
    )])
}

/// The `/play` arcade: the shipped game doors (`GAME_DOORS`, which IS
/// `dreggnet_catalog::SHIPPED_KEYS`), then the same set as a selector. They share a
/// session/receipt/replay contract without pretending their mechanics are interchangeable.
fn play_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed(&format!("🎮 {}", dreggnet_catalog::SURFACE_NAME))
        .description(format!(
            "{shelf}\n\nThe rhythm is the same in all of them: **take a turn → the game \
             re-runs it against the rules → it lands, or it is refused and nothing is \
             recorded → anyone can replay the whole thing afterwards.**",
            shelf = dreggnet_catalog::shelf_intro(),
        ))
        .field(
            "Three games",
            "**The Descent** — a solo dungeon crawl, one a day · **Automatafl** — a \
             two-player board where both moves reveal at once · **Multiway-Tug** — a \
             two-player game of hidden influence",
            false,
        )
        .field(
            "One replay gesture",
            "`/play open offering:<key> action:verify` re-checks the live session's \
             receipt chain.",
            false,
        )
        .field(
            "Crown a win",
            "`/verify crown` folds a finished match into ONE proof — prove you won \
             without revealing how.",
            false,
        )
        // ⚑ The Cheat Code is ANNOUNCED but nothing unlisted is NAMED — the affordance is
        // discoverable, the shelf stays three games long. Discord's `/play open` picker is a choice
        // enum, so this is the only way to type a key it does not offer; every other host has
        // always had one (a URL, `/open <key>`, a key entry).
        .field(
            "Cheat Code",
            "`/play cheat code:<anything>` takes free text. If you know the key of something \
             that is not on the shelf, type it and it opens — same rules, same receipts, no \
             shortcuts. Wrong guesses are free.",
            false,
        );
    let game_options: Vec<CreateSelectMenuOption> = GAME_DOORS
        .iter()
        .map(|door| CreateSelectMenuOption::new(door.title, door.key))
        .collect();
    let game_select = CreateActionRow::SelectMenu(
        CreateSelectMenu::new(
            ID_PICK_GAME,
            CreateSelectMenuKind::String {
                options: game_options,
            },
        )
        .placeholder("Choose a game door…"),
    );
    // Discord rejects a string select with MORE than 25 options, which would fail the whole
    // `/play` render. The ship list is far under that, but clamp so a growing one can never
    // silently break the menu.
    let offering_options: Vec<CreateSelectMenuOption> = commands::portfolio::play_keys()
        .into_iter()
        .take(25)
        .map(|k| CreateSelectMenuOption::new(k, k))
        .collect();
    let offering_select = CreateActionRow::SelectMenu(
        CreateSelectMenu::new(
            ID_PICK_PLAY,
            CreateSelectMenuKind::String {
                options: offering_options,
            },
        )
        .placeholder("Browse the games…"),
    );
    (embed, vec![game_select, offering_select, back_row()])
}

fn adventure_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Narrative Worlds")
        .description(
            "The shared, AI-narrated party dungeon: buttons are write-once ballots, and the \
             plurality choice lands as one real executor turn, receipted and hash-linked to \
             the turn before it. Narration can describe that turn; it cannot invent one.",
        )
        .field(
            "The Warden's Keep",
            "`/adventure dungeon start` — open it in this channel · \
             `/adventure dungeon close` — apply the party's choice · \
             `/adventure dungeon verify` — re-verify the playthrough by replay · \
             `/adventure dungeon operation` — attach a private producer receipt · \
             `/adventure dungeon list` — the world + its executor-enforced rules",
            false,
        )
        .field(
            "A narrated turn, deliberately narrow",
            "`/adventure dungeon chutes-turn confirm:true` lets Chutes choose exactly one \
             currently legal command. It sees only the current public room; free prose and \
             extra effect fields are refused, and the native executor alone changes state.",
            false,
        )
        .field(
            "Private operations",
            "Preference aggregation, fair shuffle, and quest reduction arrive as canonical \
             opaque receipts through `operation` — never as narrator prose. The card discloses \
             the exact live operation name and what becomes public.",
            false,
        )
        .field(
            "Its neighboring worlds",
            "The actor-bound native crawl is `/play open offering:descent`; today's \
             beacon-seeded season remains `/descent play`; the sealed market is \
             `/play open offering:bazaar`.",
            false,
        );
    let rows = vec![CreateActionRow::Buttons(vec![
        button("menu:run:credits", "Run-credits", ButtonStyle::Primary),
        button("menu:run:buy", "Buy credits", ButtonStyle::Success),
        button("menu:go:hub", "\u{2302} Hub", ButtonStyle::Secondary),
    ])];
    (embed, rows)
}

fn cipherclerk_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Your Cipherclerk")
        .description(
            "Your cipherclerk is *you* on the network: a real cell + keys, your DEC balance, \
             your macaroon tokens, and the economy around them. The buttons fire the same \
             real, receipted turns the subcommands do.",
        )
        .field(
            "Identity",
            "`/cipherclerk create` · `address` · `export` (your key, ephemeral)",
            false,
        )
        .field(
            "Tokens",
            "`/cipherclerk mint` · `attenuate` · `tokens` · `authorize` — real macaroon \
             attenuation",
            false,
        )
        .field(
            "The three monies",
            "**DEC** — the on-network currency (faucet, send, fees). **$DREGG** — buys \
             run-credits for real-AI runs. **computrons** — what a turn meters.",
            false,
        )
        .field(
            "One player, one board",
            "`/cipherclerk link-web` — get a single-use code that proves this Discord \
             account to your web identity, so a leaderboard sees one of you instead of two.",
            false,
        );
    let rows = vec![
        CreateActionRow::Buttons(vec![
            button("start:faucet", "Get test DEC", ButtonStyle::Success),
            button("start:balance", "Balance (DEC)", ButtonStyle::Primary),
            button("start:send", "Send", ButtonStyle::Primary),
            button("menu:run:history", "History", ButtonStyle::Primary),
        ]),
        CreateActionRow::Buttons(vec![
            button("menu:run:credits", "Run-credits", ButtonStyle::Primary),
            button("menu:run:buy", "Buy credits", ButtonStyle::Success),
            button("menu:run:treasury", "Treasury", ButtonStyle::Secondary),
            button("start:create", "Create cipherclerk", ButtonStyle::Secondary),
        ]),
        back_row(),
    ];
    (embed, rows)
}

fn govern_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Govern")
        .description(
            "Real governance on real turns: propose, vote (optionally standing-weighted on \
             the verified engine), enact — and every decision chain re-verifiable.",
        )
        .field(
            "Council (this channel)",
            "`/govern council open` (add `weighted:true` for standing-weighted ballots) · \
             `status` · `verify` · `close`",
            false,
        )
        .field(
            "Approvals",
            "`/govern council-status cell:<id>` · `/govern council-approve`",
            false,
        )
        .field(
            "Bounties",
            "`/govern bounty post|claim|submit|payout|status`",
            false,
        )
        .field(
            "Intents",
            "`/govern intent post spec:<what you want>`",
            false,
        );
    let rows = vec![
        CreateActionRow::Buttons(vec![
            button(
                "dregg:app:governance",
                "Governance panel",
                ButtonStyle::Primary,
            ),
            button(
                "dregg:modal:gov_propose",
                "New proposal",
                ButtonStyle::Success,
            ),
            button("dregg:modal:gov_vote", "Vote", ButtonStyle::Primary),
            button(
                commands::governance_card::ID_LIST,
                "Proposals",
                ButtonStyle::Primary,
            ),
        ]),
        back_row(),
    ];
    (embed, rows)
}

fn verify_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Verify It Yourself")
        .description(
            "Everything the bot narrates is re-checkable against the live node — these are \
             the surfaces that do the checking in front of you.",
        )
        .field(
            "Proofs",
            "`/verify proof turn hash:<64-hex>` — fetch AND verify the committed turn's \
             STARK against its VK",
            false,
        )
        .field(
            "Explorer",
            "`/verify explorer cell|turn|block|blocklace|checkpoint|witnesses|note|proof|\
             factory|search|stats|recent|watch|…` — browse devnet state",
            false,
        )
        .field(
            "The Crown",
            "`/verify crown` — fold a finished match into ONE O(1)-verifiable proof",
            false,
        )
        .field(
            "Export + cards",
            "`/verify export` — mint a VERIFIED Descent win as a 1-of-1 NFT · \
             `/verify card` — an interactive ViewNode card whose buttons fire real turns",
            false,
        );
    let rows = vec![
        CreateActionRow::Buttons(vec![
            button("start:status", "Node status", ButtonStyle::Primary),
            button("menu:run:ops", "Ops dashboard", ButtonStyle::Primary),
            button("menu:run:activity", "Live activity", ButtonStyle::Primary),
        ]),
        back_row(),
    ];
    (embed, rows)
}

fn identity_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Granting Authority")
        .description(
            "Share, attenuate, and hand off your authority — capabilities, signed handoff \
             certificates, and the ceremonies that link an external cell to you.",
        )
        .field(
            "Capabilities (CapTP)",
            "`/identity cap-share` · `cap-accept` · `cap-delegate` · `cap-list` · \
             `cap-revoke` · `cap-peer`",
            false,
        )
        .field(
            "Handoffs (signed certificates)",
            "`/identity handoff` · `handoff-redeem` · `handoff-status`",
            false,
        )
        .field(
            "Link ceremonies",
            "`/identity link-cipherclerk` · `link-prove` (sign the challenge) · \
             `unlink-cipherclerk`",
            false,
        )
        .field(
            "Your LLM key",
            "`/identity key set|rotate|revoke|status` — sealed at rest, never echoed",
            false,
        )
        .field(
            "Roles as capabilities",
            "`/identity roles show|unlock|grant` — a server role can GATE a surface, but it \
             is an attestation by this server, never the cryptographic authority",
            false,
        );
    let rows = vec![
        CreateActionRow::Buttons(vec![
            button(
                "dregg:app:identity",
                "Credentials panel",
                ButtonStyle::Primary,
            ),
            button("start:key", "Set my LLM key", ButtonStyle::Primary),
            button(
                "menu:run:caplist",
                "Held capabilities",
                ButtonStyle::Primary,
            ),
        ]),
        back_row(),
    ];
    (embed, rows)
}

fn hermes_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("The Confined Offerings")
        .description(
            "Cap-bounded, metered, receipted compute you can converse with — every action one \
             real dregg turn under your own cell.",
        )
        .field(
            "Hermes (a confined agent)",
            "`/hermes open` · `status` · `verify` — or claim your channel and just type",
            false,
        )
        .field(
            "Grain (a confined worker cell)",
            "`/hermes grain open|status|verify`",
            false,
        )
        .field(
            "Doc (a shared document)",
            "`/hermes doc open|status|verify` — each edit one finalized executor turn",
            false,
        );
    let rows = vec![
        CreateActionRow::Buttons(vec![
            button("start:channel", "Claim my channel", ButtonStyle::Success),
            button("start:key", "Set my LLM key", ButtonStyle::Primary),
        ]),
        back_row(),
    ];
    (embed, rows)
}

fn federation_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("The Network")
        .description("Federation health, committee membership, presence, and coordination.")
        .field(
            "Reads",
            "`/federation status` · `peers` · `activity` — or press the buttons",
            false,
        )
        .field(
            "Presence attestation",
            "`/federation presence status|attest|verify|history`",
            false,
        )
        .field(
            "Coordination",
            "`/federation coordinate` — two agents settle atomically over the \
             promise-pipeline · `/federation channel` — claim your semi-private channel",
            false,
        )
        .field(
            "Setup + deos",
            "`/federation setup` · `/federation deos council` — cap-gated affordance \
             buttons + live transclusion",
            false,
        );
    let rows = vec![
        CreateActionRow::Buttons(vec![
            button(
                "menu:run:fedstatus",
                "Federation status",
                ButtonStyle::Primary,
            ),
            button("menu:run:fedpeers", "Peers", ButtonStyle::Primary),
            button("menu:run:activity", "Live activity", ButtonStyle::Primary),
        ]),
        back_row(),
    ];
    (embed, rows)
}

fn gallery_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("The Gallery")
        .description(
            "Publish + remix procgen universes (signed by your cipherclerk key); only a \
             verified win is ranked.",
        )
        .field(
            "Browse + play",
            "`/gallery list` · `/gallery show universe:<id>` · `/gallery play`",
            false,
        )
        .field("Publish", "`/gallery publish` — optionally a remix", false);
    (embed, vec![back_row()])
}

fn descent_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("The Descent")
        .description(
            "Today's beacon-seeded permadeath roguelite — a real permadeath run on the dregg \
             executor; a hardcore character carries level/class/scars across days.",
        )
        .field(
            "Play",
            "`/descent play` · `room` · `verify` · `board` · `today` · `tournament`",
            false,
        );
    (embed, vec![back_row()])
}

fn leaderboard_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Glory")
        .description("Boards + tournaments — every ranked entry re-checkable against the chain.")
        .field("Boards", "`/leaderboard` — top DEC holders", false)
        .field(
            "Game boards",
            "`/descent board` — the no-cheat daily board · `/descent tournament` — the \
             weekly verify-gated bracket · `/verify crown` — the proof-carrying game board",
            false,
        );
    (embed, vec![back_row()])
}

fn help_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    (commands::start::help_embed(), vec![back_row()])
}

/// Render a surface's menu view by its `menu:go:` key. The hub is the live
/// `/dregg` dashboard home (a db read); the rest are pure.
async fn view_for(
    surface: &str,
    state: &BotState,
    user_id: u64,
) -> (CreateEmbed, Vec<CreateActionRow>) {
    match surface {
        "hub" => (
            commands::dashboard::home_embed(user_id, state).await,
            commands::dashboard::home_components(),
        ),
        "play" => play_view(),
        "adventure" => adventure_view(),
        "cipherclerk" => cipherclerk_view(),
        "govern" => govern_view(),
        "verify" => verify_view(),
        "identity" => identity_view(),
        "hermes" => hermes_view(),
        "federation" => federation_view(),
        "gallery" => gallery_view(),
        "descent" => descent_view(),
        "leaderboard" => leaderboard_view(),
        "help" => help_view(),
        _ => (
            embeds::warning_embed(
                "Unknown Surface",
                "This menu destination isn't recognised by this bot build.",
            ),
            vec![back_row()],
        ),
    }
}

// ─── component routing (`menu:` prefix, dispatched from main.rs) ────────────

/// Route a `menu:` component press: `menu:go:<surface>` swaps the menu message
/// in place; `menu:run:<read>` defers an ephemeral follow-up and fires the
/// EXISTING module's `execute_*` read; the `/play` select answers ephemerally.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let custom_id = component.data.custom_id.clone();

    if let Some(surface) = custom_id.strip_prefix(ID_GO_PREFIX) {
        let (embed, rows) = view_for(surface, state, component.user.id.get()).await;
        let msg = CreateInteractionResponseMessage::new()
            .embed(embed)
            .components(rows);
        let _ = component
            .create_response(&ctx.http, CreateInteractionResponse::UpdateMessage(msg))
            .await;
        return;
    }

    if custom_id == ID_PICK_GAME {
        if let ComponentInteractionDataKind::StringSelect { values } = &component.data.kind {
            if let Some(door) = values.first().and_then(|key| game_door(key)) {
                let _ = component
                    .create_response(
                        &ctx.http,
                        CreateInteractionResponse::Message(
                            CreateInteractionResponseMessage::new()
                                .embed(game_door_card(door))
                                .ephemeral(true),
                        ),
                    )
                    .await;
                return;
            }
        }
        let _ = component
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(embeds::warning_embed(
                            "Unknown game door",
                            "That selector value is not one of this build's exact game routes.",
                        ))
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }

    if custom_id == ID_PICK_PLAY {
        if let ComponentInteractionDataKind::StringSelect { values } = &component.data.kind {
            if let Some(key) = values.first() {
                let _ = component
                    .create_response(
                        &ctx.http,
                        CreateInteractionResponse::Message(
                            CreateInteractionResponseMessage::new()
                                .content(format!(
                                    "**{key}** — open it in a channel with \
                                     `/play open offering:{key}` \u{2022} re-check its live \
                                     session anytime with `/play open offering:{key} \
                                     action:verify`."
                                ))
                                .ephemeral(true),
                        ),
                    )
                    .await;
                return;
            }
        }
    }

    if let Some(action) = custom_id.strip_prefix(ID_RUN_PREFIX) {
        // Defer an ephemeral follow-up, then land the module's real read.
        let _ = component
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Defer(
                    CreateInteractionResponseMessage::new().ephemeral(true),
                ),
            )
            .await;
        let user_id = component.user.id.get();
        let (embed, rows): (CreateEmbed, Vec<CreateActionRow>) = match action {
            "history" => commands::social::execute_history(state, user_id).await,
            "credits" => (commands::pay::execute_balance(state, user_id).await, vec![]),
            "buy" => (commands::pay::execute_buy(state, user_id).await, vec![]),
            "treasury" => (commands::pay::execute_treasury(state).await, vec![]),
            "activity" => (commands::social::execute_activity(state).await, vec![]),
            "fedstatus" => (commands::federation::execute_status(state).await, vec![]),
            "fedpeers" => (commands::federation::execute_peers(state).await, vec![]),
            "caplist" => (commands::captp::execute_list(state).await, vec![]),
            "ops" => (
                commands::dashboard::ops_dashboard_embed(state).await,
                vec![],
            ),
            _ => (
                embeds::warning_embed(
                    "Unknown Control",
                    "This menu action isn't recognised by this bot build.",
                ),
                vec![],
            ),
        };
        let _ = component
            .edit_response(
                &ctx.http,
                EditInteractionResponse::new().embed(embed).components(rows),
            )
            .await;
        return;
    }

    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .embed(embeds::warning_embed(
                        "Unknown Control",
                        "This menu control isn't recognised by this bot build.",
                    ))
                    .ephemeral(true),
            ),
        )
        .await;
}

/// Answer a top-level menu invocation (the `menu` subcommand / a bare call).
async fn respond_menu(
    ctx: &Context,
    command: &CommandInteraction,
    (embed, rows): (CreateEmbed, Vec<CreateActionRow>),
) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(rows)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

// ─── tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn names(commands: &[Value]) -> Vec<String> {
        commands
            .iter()
            .map(|c| c["name"].as_str().expect("command name").to_owned())
            .collect()
    }

    /// ⚑ **THE REGISTERED SURFACE IS THE CURATED TABLE.** Reads [`SLASH_SURFACE`] through
    /// [`advertised_names`], never a second list, so changing ember's mind is one row and
    /// this test needs no edit — which is the only reason it will still be true next month.
    #[test]
    fn the_registered_surface_is_exactly_the_advertised_rows() {
        assert_eq!(
            names(&global_commands()),
            advertised_names()
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>(),
            "the registered JSON IS the advertised rows of SLASH_SURFACE, in order"
        );
        assert_eq!(
            names(&lab_commands()),
            lab_names()
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>(),
            "the lab JSON IS the un-advertised rows of SLASH_SURFACE, in order"
        );
        // The two surfaces partition the table: nothing is registered twice, nothing is
        // built and then registered nowhere.
        let advertised: BTreeSet<&str> = advertised_names().into_iter().collect();
        let lab: BTreeSet<&str> = lab_names().into_iter().collect();
        assert!(
            advertised.is_disjoint(&lab),
            "a command cannot be both advertised and lab"
        );
        assert_eq!(
            advertised.len() + lab.len(),
            SLASH_SURFACE.len(),
            "SLASH_SURFACE has a duplicate name"
        );
    }

    /// ⚑ **A PLAYER'S `/` MENU IS SMALL, AND THIS IS THE NUMBER.** Not a derived
    /// tautology: the count is written down so that quietly re-advertising a surface has
    /// to come past ember. Ordinary members see the `Player` + `Offering` rows; the
    /// `Operator` row is registered but hidden from them by Discord.
    #[test]
    fn a_stranger_sees_only_the_small_menu() {
        let visible_to_players: Vec<&str> = SLASH_SURFACE
            .iter()
            .filter(|s| advertises(&s.door) && !matches!(s.door, Door::Operator(_)))
            .map(|s| s.name)
            .collect();
        assert_eq!(
            visible_to_players,
            vec!["descent", "play", "cipherclerk", "verify", "help"],
            "the player-visible `/` menu changed — if that is the intent, change this line \
             too, deliberately"
        );
        assert_eq!(
            advertised_names(),
            vec!["dregg", "descent", "play", "cipherclerk", "verify", "help"],
            "the registered set changed — same rule"
        );
    }

    /// ⚑ **THE OFFERING-SHAPED DOORS FOLLOW THE SHIP LIST**, both directions. This is the
    /// derivation the whole design rests on: pare `dreggnet_catalog::SHIPPED_KEYS` and the
    /// command comes off Discord's menu; re-list it and the command comes back. Nothing
    /// here re-types a key.
    #[test]
    fn the_offering_doors_follow_the_ship_list() {
        let advertised: BTreeSet<&str> = advertised_names().into_iter().collect();
        let mut checked = 0usize;
        for row in SLASH_SURFACE {
            if let Door::Offering(key) = row.door {
                checked += 1;
                assert_eq!(
                    advertised.contains(row.name),
                    dreggnet_catalog::is_shipped(key),
                    "`/{}` is a door to `{key}`, so it must be advertised exactly when \
                     `{key}` is on dreggnet_catalog::SHIPPED_KEYS",
                    row.name
                );
            }
        }
        assert!(
            checked >= 3,
            "the offering arm must actually be exercised — {checked} offering-shaped rows"
        );
        // And the ones we DO ship are all reachable: as their own advertised command, or
        // as a `/play open` choice (which is itself derived from the ship list).
        let play_choices = commands::portfolio::play_keys();
        for key in dreggnet_catalog::SHIPPED_KEYS {
            let own_command = SLASH_SURFACE
                .iter()
                .any(|s| s.door == Door::Offering(key) && advertised.contains(s.name));
            assert!(
                own_command || play_choices.contains(&key),
                "`{key}` is shipped but has neither an advertised command nor a `/play \
                 open` choice"
            );
        }
    }

    /// ⚑ **THE LAB IS REGISTERED NOWHERE GLOBAL.** The point of the pare-down: a lab
    /// command must not be in the bulk-PUT global set, or it is back in every stranger's
    /// autocomplete. It stays in [`lab_commands`] (and so in `DREGG_LAB_GUILD_ID`), and it
    /// keeps its router arm — which `crate::main`'s router-surface test asserts.
    #[test]
    fn the_lab_surface_is_not_registered_globally() {
        let global: BTreeSet<String> = names(&global_commands()).into_iter().collect();
        for name in lab_names() {
            assert!(
                !global.contains(name),
                "`/{name}` is a lab row but is in the global set"
            );
        }
        assert!(
            !lab_names().is_empty(),
            "this test is vacuous with an empty lab — if the lab is genuinely empty, delete \
             it and the DREGG_LAB_GUILD_ID path rather than leaving a gate that cannot fire"
        );
    }

    /// ⚑ **EVERY LAB ROW SAYS WHAT IT COSTS.** `Door::Lab` is the one variant that takes a
    /// typed path away from a player, so a bare marker is not allowed: the row has to name
    /// the capability that goes with it, in enough words to be read as a loss.
    #[test]
    fn the_lab_rows_name_what_they_cost() {
        for row in SLASH_SURFACE {
            let (kind, why) = match row.door {
                Door::Offering(_) => continue,
                Door::Player(why) => ("Player", why),
                Door::Operator(why) => ("Operator", why),
                Door::Lab(why) => ("Lab", why),
            };
            assert!(
                why.len() > 40,
                "the {kind} row `/{}` must state its reason, not gesture at one: {why:?}",
                row.name
            );
        }
    }

    /// ⚑ **NO ADVERTISED SURFACE ADVERTISES A LAB COMMAND.** The registration JSON is not
    /// the only shelf: a menu embed or the `/help` map naming `/gallery` is just as loud,
    /// and a pointer at a command Discord will refuse to route is worse than no pointer.
    /// Driven over [`lab_names`], so re-listing something fixes this test too.
    #[test]
    fn no_advertised_surface_names_a_lab_command() {
        let mut shelves: Vec<(String, String)> = vec![(
            "the registered JSON".to_string(),
            serde_json::to_value(global_commands()).unwrap().to_string(),
        )];
        for (label, view) in [
            ("/play menu", play_view()),
            ("/cipherclerk menu", cipherclerk_view()),
            ("/verify menu", verify_view()),
            ("/descent menu", descent_view()),
            ("/help map", help_view()),
        ] {
            let (embed, rows) = view;
            let mut text = serde_json::to_value(embed).unwrap().to_string();
            text.push_str(&serde_json::to_value(rows).unwrap().to_string());
            shelves.push((label.to_string(), text));
        }
        for name in lab_names() {
            for (label, text) in &shelves {
                assert!(
                    !mentions_command(text, name),
                    "{label} advertises `/{name}`, which this build does not register \
                     globally — either re-list it on SLASH_SURFACE or stop pointing at it"
                );
            }
        }
        // Not vacuous: the same scan DOES fire on an advertised command's own name.
        assert!(
            mentions_command(
                &serde_json::to_value(play_view().0).unwrap().to_string(),
                "play"
            ),
            "the scanner must be able to see a command mention at all"
        );
    }

    /// Whether `text` names the slash command `/{name}` — a whole path segment, so
    /// `/api/federations` is not a mention of `/federation` and `/identity` inside
    /// `/api/identity/credentials` is not a mention of `/identity`.
    fn mentions_command(text: &str, name: &str) -> bool {
        let token = format!("/{name}");
        let bytes = text.as_bytes();
        text.match_indices(&token).any(|(at, _)| {
            let before_ok = at == 0 || !bytes[at - 1].is_ascii_alphanumeric();
            let after = at + token.len();
            let after_ok = after >= bytes.len()
                || !(bytes[after].is_ascii_alphanumeric()
                    || bytes[after] == b'-'
                    || bytes[after] == b'_'
                    || bytes[after] == b'/');
            before_ok && after_ok
        })
    }

    /// ⚑ **THE HUB GRID IS A SHELF TOO, AND IT WAS THE ONE I NEARLY MISSED.** Every player
    /// reaches the hub from the "⌂ Hub" button on every other menu, and a
    /// `menu:go:<lab surface>` button there walks them into a view whose prose names commands
    /// Discord will refuse to route. `commands::dashboard::home_components` derives its grid
    /// from [`advertised_names`]; this checks BOTH directions, so a pared surface loses its
    /// hub button and a re-listed one gains it back without either being hand-edited.
    #[test]
    fn the_hub_grid_summons_only_advertised_surfaces() {
        let wire = serde_json::to_value(commands::dashboard::home_components())
            .expect("the hub components serialize")
            .to_string();
        for name in lab_names() {
            assert!(
                !wire.contains(&format!("{ID_GO_PREFIX}{name}")),
                "the hub grid has a `{ID_GO_PREFIX}{name}` button, but `/{name}` is not on \
                 the advertised surface — pressing it lands a player in a menu full of \
                 commands they cannot type"
            );
        }
        for name in advertised_names() {
            // The hub does not link to itself.
            if name == "dregg" {
                continue;
            }
            assert!(
                wire.contains(&format!("{ID_GO_PREFIX}{name}")),
                "`/{name}` is advertised but the hub grid has no button to it"
            );
        }
    }

    /// ⚑ **THE OPERATOR ROW IS HIDDEN AND THE PLAYER ROWS ARE NOT.** The mechanism, not
    /// the intention: `default_member_permissions: "0"` is what actually keeps `/dregg`
    /// out of a member's autocomplete, and stamping it on a player command would hide the
    /// games from everyone.
    #[test]
    fn only_the_operator_rows_are_hidden_from_players() {
        let cmds = global_commands();
        for row in SLASH_SURFACE.iter().filter(|s| advertises(&s.door)) {
            let json = cmds
                .iter()
                .find(|c| c["name"].as_str() == Some(row.name))
                .expect("an advertised row is registered");
            let perms = json
                .get("default_member_permissions")
                .and_then(Value::as_str);
            if matches!(row.door, Door::Operator(_)) {
                assert_eq!(
                    perms,
                    Some("0"),
                    "`/{}` is an operator row and must carry default_member_permissions=0",
                    row.name
                );
            } else {
                assert_eq!(
                    perms, None,
                    "`/{}` is a player-facing row and must NOT be permission-gated",
                    row.name
                );
            }
        }
        // ⚑ Ember does not lose the operator surface: it is REGISTERED (globally, so it is
        // present in every guild and in a DM with the bot), merely hidden from members who
        // cannot use it. An operator row that stopped being registered would be a genuine
        // loss of access, so assert the registration and not just the flag.
        assert!(
            SLASH_SURFACE
                .iter()
                .any(|s| matches!(s.door, Door::Operator(_)) && advertises(&s.door)),
            "at least one operator row must stay registered, or ember loses ops access"
        );
    }

    /// ⚑ **THE TWO PATHS THAT HAD TO BE CARRIED OUT OF THE LAB.** Paring `/identity` and
    /// `/federation` would otherwise have taken a load-bearing player ceremony and a
    /// per-guild operator action with them, so both were re-homed rather than dropped, and
    /// both must land on a surface that is actually registered globally.
    ///
    /// * `link-web` — the ISSUER half of the phrase-link ceremony. Without it a player
    ///   whose web identity is 24 words is permanently two people on one leaderboard, and
    ///   nothing else on Discord issues that code.
    /// * `cleanup` — the `dreggnet-*` category reaper. It must run IN the guild that grew
    ///   the duplicates, so leaving it on the lab-only `/federation` would have made it
    ///   unrunnable exactly where it is needed.
    #[test]
    fn the_rehomed_paths_land_on_advertised_commands() {
        let advertised = advertised_names();
        let home_of = |sub: &str| -> Option<&'static str> {
            advertised
                .iter()
                .copied()
                .find(|top| subcommand_names(top).iter().any(|s| s == sub))
        };
        assert_eq!(
            home_of("link-web"),
            Some("cipherclerk"),
            "`link-web` must be reachable on an ADVERTISED command (it is the one piece of \
             `/identity` a player of a shipped game needs)"
        );
        assert_eq!(
            home_of("cleanup"),
            Some("dregg"),
            "the category reaper must sit on the globally-registered operator command, or \
             ember cannot run it in the guild that needs it"
        );
        // And it is the same handler in both places — `/identity link-web` still exists on
        // the lab surface, which is what makes the `/cipherclerk` copy a second spelling
        // rather than a second mechanism.
        assert!(
            subcommand_names("identity").iter().any(|s| s == "link-web"),
            "the `/identity` fold of `link-web` should still be built for the lab surface"
        );
    }

    /// Every row builds, and `command_for` has no orphan arm claiming a name the table
    /// does not carry. (`command_for` panics on an unknown name; this is the other
    /// direction, and it is what makes that panic unreachable in production.)
    #[test]
    fn every_surface_row_has_a_builder() {
        for row in SLASH_SURFACE {
            let v = command_for(row.name);
            assert_eq!(
                v["name"].as_str(),
                Some(row.name),
                "`command_for({:?})` built a command named {:?}",
                row.name,
                v["name"]
            );
        }
    }

    /// Discord structural limits: ≤25 options per command, groups contain only
    /// subcommands, names ≤32 chars, descriptions 1..=100 chars.
    #[test]
    fn registration_json_respects_discord_limits() {
        fn check_option(opt: &Value, depth: usize) {
            let ty = opt["type"].as_u64().expect("option type");
            let name = opt["name"].as_str().expect("option name");
            let desc = opt["description"].as_str().expect("option description");
            assert!(name.len() <= 32, "option name too long: {name}");
            assert!(
                !desc.is_empty() && desc.len() <= 100,
                "bad description length for {name}: {}",
                desc.len()
            );
            let children = opt
                .get("options")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default();
            match ty {
                2 => {
                    assert!(depth == 0, "a group must sit at the top level ({name})");
                    assert!(!children.is_empty(), "group {name} has no subcommands");
                    for c in &children {
                        assert_eq!(
                            c["type"].as_u64(),
                            Some(1),
                            "group {name} may contain only subcommands"
                        );
                        check_option(c, depth + 1);
                    }
                }
                1 => {
                    for c in &children {
                        let cty = c["type"].as_u64().unwrap_or(0);
                        assert!(
                            (3..=11).contains(&cty),
                            "subcommand {name} child has non-basic type {cty}"
                        );
                        check_option(c, depth + 1);
                    }
                }
                3..=11 => {}
                other => panic!("unexpected option type {other} for {name}"),
            }
        }
        // BOTH surfaces: the lab set is PUT to a guild the same way the global set is PUT
        // to the application, so malformed lab JSON is a 400 that takes the whole guild
        // registration with it — exactly as invisible as an unregistered command, and
        // exactly the kind of silent subtraction this file is trying to stop.
        for cmd in global_commands().into_iter().chain(lab_commands()) {
            let name = cmd["name"].as_str().expect("command name");
            assert!(name.len() <= 32);
            let desc = cmd["description"].as_str().expect("command description");
            assert!(
                !desc.is_empty() && desc.len() <= 100,
                "{name}: {}",
                desc.len()
            );
            let opts = cmd
                .get("options")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default();
            assert!(opts.len() <= 25, "{name} has {} options (>25)", opts.len());
            let mut seen = BTreeSet::new();
            for o in &opts {
                assert!(
                    seen.insert(o["name"].as_str().unwrap().to_owned()),
                    "{name} has a duplicate option: {:?}",
                    o["name"]
                );
                check_option(o, 0);
            }
        }
    }

    /// EVERY retired flat command keeps a path IN THE CODE: still a top-level, a folded
    /// subcommand/group under its new home, or a button on a menu that exists — on the
    /// advertised surface or the lab one. Paring the menu is allowed to move a path; it is
    /// not allowed to silently delete one.
    #[test]
    fn every_old_command_is_still_reachable() {
        let cmds: Vec<Value> = global_commands()
            .into_iter()
            .chain(lab_commands())
            .collect();
        let tops: BTreeSet<String> = names(&cmds).into_iter().collect();
        for (old, reach) in OLD_COMMAND_REACH {
            match reach {
                Reach::Top => {
                    assert!(tops.contains(*old), "`/{old}` should still be a top-level");
                }
                Reach::Under(home) => {
                    // Renamed folds: the ledger key is the OLD name; the sub
                    // name under the home is asserted via the rename table.
                    let sub_name = match *old {
                        "setup-federation" => "setup",
                        "federation-status" => "status",
                        "federation-peers" => "peers",
                        "proof" => "proof",
                        "play" => "open",
                        _ => old,
                    };
                    let subs = subcommand_names(home);
                    assert!(
                        subs.iter().any(|s| s == sub_name),
                        "`/{old}` should be reachable as `/{home} {sub_name}` — found {subs:?}"
                    );
                }
                Reach::Button(home) => {
                    assert!(
                        tops.contains(*home),
                        "`/{old}` folds behind a `/{home}` button, but `/{home}` is unregistered"
                    );
                }
            }
        }
    }

    /// The dispatch shim un-nests one level and rewrites the name, so an
    /// existing handler sees the exact old shape.
    #[test]
    fn fold_json_shapes_are_what_dispatch_expects() {
        // A former flat-option command folds to a type-1 subcommand whose
        // children are its old flat options.
        let send = fold(crate::commands::transfer::register_send(), None);
        assert_eq!(send["type"], 1);
        assert_eq!(send["name"], "send");
        let send_children = send["options"].as_array().unwrap();
        assert!(
            send_children
                .iter()
                .all(|o| o["type"] != 1 && o["type"] != 2)
        );

        // A former subcommand-bearing command folds to a type-2 group whose
        // children are its old subcommands.
        let council = fold(crate::commands::council::register(), None);
        assert_eq!(council["type"], 2);
        assert_eq!(council["name"], "council");
        let council_children = council["options"].as_array().unwrap();
        assert!(council_children.iter().all(|o| o["type"] == 1));
        assert!(council_children.iter().any(|o| o["name"] == "open"));

        // A rename keeps everything but the name.
        let status = fold(
            crate::commands::federation::register_status(),
            Some("status"),
        );
        assert_eq!(status["name"], "status");
        assert_eq!(status["type"], 1);
    }

    /// The 13 all summon a menu or a world: every folded top-level carries the
    /// `menu` subcommand; the four kept surfaces are bare/world commands.
    #[test]
    fn every_folded_top_level_carries_the_menu_subcommand() {
        for name in [
            "play",
            "adventure",
            "cipherclerk",
            "govern",
            "verify",
            "identity",
            "hermes",
            "federation",
        ] {
            assert!(
                subcommand_names(name).iter().any(|s| s == "menu"),
                "/{name} should carry the `menu` subcommand"
            );
        }
    }

    /// The different games share one *interaction* contract without being flattened into
    /// one mechanics layer. Every card names an exact open route and an exact replay route
    /// that the real registry serves; selector values are a closed vocabulary.
    #[test]
    fn game_doors_are_exact_replayable_routes() {
        // ⚑ THE FEATURED DOORS ARE THE SHIP LIST, both directions — nothing unshipped is
        // promoted here, and nothing shipped is missing a door.
        for door in GAME_DOORS {
            assert!(
                dreggnet_catalog::is_shipped(door.key),
                "the `{}` door advertises an offering that is not on \
                 dreggnet_catalog::SHIPPED_KEYS",
                door.key
            );
        }
        for key in dreggnet_catalog::SHIPPED_KEYS {
            assert!(
                game_door(key).is_some(),
                "`{key}` is shipped but has no featured door"
            );
        }

        let mut seen = BTreeSet::new();
        for door in GAME_DOORS {
            assert!(seen.insert(door.key), "duplicate game door `{}`", door.key);
            assert!(door.open.starts_with('/'));
            assert!(door.verify.starts_with('/'));
            assert_ne!(door.open, door.verify);
            assert!(door.verify.contains("verify"));
            if door.key == "dungeon" {
                assert!(
                    subcommand_names("adventure")
                        .iter()
                        .any(|name| name == "dungeon"),
                    "the Dungeon card must route to the registered folded command"
                );
            } else {
                assert!(
                    commands::portfolio::play_keys().contains(&door.key),
                    "`{}` must be a real /play offering choice",
                    door.key
                );
            }
            let wire = serde_json::to_value(game_door_card(&door)).expect("game card serializes");
            let text = wire.to_string();
            assert!(text.contains(door.open), "{text}");
            assert!(text.contains(door.verify), "{text}");
        }
        for substituted in [
            "Bazaar",
            "bazaar:verify",
            "bazaar\0",
            "please open the dungeon",
            "private-raid/../../dungeon",
        ] {
            assert_eq!(
                game_door(substituted),
                None,
                "game navigation accepts only an exact structured selector value"
            );
        }
    }

    /// Player-facing privacy text is part of the command UX. It must state what becomes public
    /// and must not let hidden inputs leak into a shared card.
    ///
    /// ⚑ Driven over `GAME_DOORS` (which IS `dreggnet_catalog::SHIPPED_KEYS`), never over three
    /// named keys: it used to assert exact sentences from the Dungeon, Bazaar and Ash Gate cards,
    /// so paring the shelf blew it up instead of moving it. The PROPERTY is what matters — every
    /// door a player can see must draw the public/hidden line for itself.
    #[test]
    fn game_door_cards_state_the_real_privacy_boundary() {
        for door in GAME_DOORS {
            let text = serde_json::to_value(game_door_card(&door))
                .unwrap()
                .to_string();
            assert!(
                door.privacy.len() > 40,
                "the `{}` card must actually explain its boundary, not gesture at one: {}",
                door.key,
                door.privacy
            );
            assert!(
                door.privacy.contains("public"),
                "the `{}` card must say what becomes PUBLIC: {}",
                door.key,
                door.privacy
            );
            assert!(
                door.privacy.contains("hidden")
                    || door.privacy.contains("secret")
                    || door.privacy.contains("yours")
                    || door.privacy.contains("belongs to you"),
                "the `{}` card must say what stays private: {}",
                door.key,
                door.privacy
            );
            assert!(
                text.contains("public"),
                "and the boundary must reach the rendered card: {text}"
            );
        }

        for secret in [
            "sealed-card=ace",
            "bid=987654321",
            "private-score-matrix",
            "player-credit-balance",
        ] {
            for door in GAME_DOORS {
                let text = serde_json::to_value(game_door_card(&door))
                    .unwrap()
                    .to_string();
                assert!(!text.contains(secret), "shared game card leaked `{secret}`");
            }
        }
    }

    /// Menus stay within Discord component limits (≤5 rows, ≤5 buttons/row).
    #[test]
    fn menu_views_fit_discord_component_limits() {
        for (_, rows) in [
            play_view(),
            adventure_view(),
            cipherclerk_view(),
            govern_view(),
            verify_view(),
            identity_view(),
            hermes_view(),
            federation_view(),
            gallery_view(),
            descent_view(),
            leaderboard_view(),
            help_view(),
        ] {
            assert!(rows.len() <= 5, "at most 5 action rows");
            for row in &rows {
                if let CreateActionRow::Buttons(b) = row {
                    assert!(b.len() <= 5, "at most 5 buttons per row");
                }
                // Discord rejects a string select with >25 options — such a menu fails to render
                // entirely (the `/play` offering selector is the one that can grow past the cap).
                let json = serde_json::to_value(row).expect("action row serializes");
                assert!(
                    max_select_options(&json) <= 25,
                    "a string select carries {} options (>25) — Discord would reject the menu",
                    max_select_options(&json),
                );
            }
        }
    }

    /// The largest `options` array anywhere in a serialized component tree (a select menu's
    /// options live nested under the action row's `components`), or 0 if there is no select.
    fn max_select_options(v: &serde_json::Value) -> usize {
        match v {
            serde_json::Value::Object(map) => {
                let here = map
                    .get("options")
                    .and_then(|o| o.as_array())
                    .map(|a| a.len())
                    .unwrap_or(0);
                map.values()
                    .map(max_select_options)
                    .fold(here, |a, b| a.max(b))
            }
            serde_json::Value::Array(arr) => {
                arr.iter().map(max_select_options).fold(0, |a, b| a.max(b))
            }
            _ => 0,
        }
    }
}
