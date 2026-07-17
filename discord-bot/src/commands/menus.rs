//! The 13-command menu surface — every old flat slash command folded behind
//! a menu-driven top-level command.
//!
//! The bot's global slash surface is EXACTLY thirteen commands (`/dregg` + 12);
//! each one either summons a world (`/descent`) or opens a menu (an embed +
//! action-row buttons / a select), and every one of the ~53 retired flat
//! commands is folded in as a subcommand (its options preserved verbatim) or a
//! menu button — the handlers themselves are UNCHANGED; only the front door
//! moved.
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
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseFollowup,
    CreateInteractionResponseMessage, CreateSelectMenu, CreateSelectMenuKind,
    CreateSelectMenuOption, EditInteractionResponse,
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

// ─── registration: fold existing builders into 13 menu commands ─────────────

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

/// The EXACT 13 global slash commands, in registration order. Kept in sync
/// with `crate::REGISTERED_COMMAND_NAMES` (asserted at boot and by test).
pub fn global_commands() -> Vec<Value> {
    vec![
        // 1. /dregg — the hub dashboard (bare; its buttons summon every other
        //    surface; folds the retired /dashboard + /status behind buttons).
        command_json(&commands::dashboard::register()),
        // 2. /descent — today's beacon-seeded daily roguelite world, unchanged.
        command_json(&commands::descent::register()),
        // 3. /play — the arcade: open any portfolio offering; /market folds in.
        top(
            "play",
            "The DreggNet arcade — open a game or offering world in this channel",
            vec![
                menu_sub(),
                fold(commands::portfolio::register(), Some("open")),
                fold(commands::market::register(), None),
            ],
        ),
        // 4. /adventure — the narrative worlds; /dungeon (the party crawl) folds in.
        top(
            "adventure",
            "Narrative worlds — the shared AI-narrated party dungeon and its kin",
            vec![
                menu_sub(),
                fold(commands::fiction::register(), Some("dungeon")),
            ],
        ),
        // 5. /cipherclerk — you + your funds: the cipherclerk identity view and
        //    the whole economy (send/history/faucet/credits/treasury) fold in.
        cipherclerk_command(),
        // 6. /gallery — the UGC universe registry, unchanged.
        command_json(&commands::gallery::register()),
        // 7. /govern — the DAO surface: council, approvals, bounties, intents.
        top(
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
        // 8. /verify — the proof surface: fetch + verify artifacts, browse state.
        top(
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
        // 9. /identity — granting authority: caps, handoffs, link ceremonies, keys.
        top(
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
                fold(commands::key::register(), None),
            ],
        ),
        // 10. /hermes — the confined agent, plus the confined grain + shared doc.
        hermes_command(),
        // 11. /federation — the network: status, peers, presence, coordination.
        top(
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
        // 12. /leaderboard — glory, unchanged.
        command_json(&commands::social::register_leaderboard()),
        // 13. /help — onboarding + the tour (the old /start) + the map.
        top(
            "help",
            "How the bot works — onboarding, the 2-minute tour, and the command map",
            vec![],
        ),
    ]
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

/// How a retired flat command is reached now. Every entry is asserted
/// structurally against [`global_commands`] by the coverage test below.
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
];

/// The subcommand / group names a registered top-level exposes (test + boot aid).
pub fn subcommand_names(top_name: &str) -> Vec<String> {
    global_commands()
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

/// `/play` — `open` → the portfolio opener; `market` → the auction offering;
/// otherwise the arcade menu.
pub async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match take_fold(command) {
        Some(("open", inner)) => {
            commands::portfolio::handle(ctx, &as_command(command, "play", inner), state).await
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
        Some(("key", inner)) => {
            commands::key::handle(ctx, &as_command(command, "key", inner), state).await
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
        _ => respond_menu(ctx, command, federation_view()).await,
    }
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

/// The `/play` arcade: a select of every portfolio offering + the market.
fn play_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("The Arcade")
        .description(
            "Every move in every game is a real, receipted dregg turn. Open a world in this \
             channel with **/play open** — or pick an offering below to see what it is.",
        )
        .field(
            "Games",
            "`/play open offering:tug` — the hidden-hand tug-of-war · \
             `/play open offering:automatafl` — the board of automata",
            false,
        )
        .field(
            "Market",
            "`/play market open` — sealed-bid auctions (list, bid, verify, close)",
            false,
        )
        .field(
            "Verify-don't-trust",
            "`/play open offering:<key> action:verify` re-checks the live session's \
             receipt chain in front of you.",
            false,
        )
        .field(
            "Crown a win",
            "`/verify crown` folds a finished match into ONE proof — prove you won \
             without revealing how.",
            false,
        );
    let options: Vec<CreateSelectMenuOption> = commands::portfolio::play_keys()
        .into_iter()
        .map(|k| CreateSelectMenuOption::new(k, k))
        .collect();
    let select = CreateActionRow::SelectMenu(
        CreateSelectMenu::new(ID_PICK_PLAY, CreateSelectMenuKind::String { options })
            .placeholder("Browse the offerings…"),
    );
    (embed, vec![select, back_row()])
}

fn adventure_view() -> (CreateEmbed, Vec<CreateActionRow>) {
    let embed = embeds::dregg_embed("Narrative Worlds")
        .description(
            "The shared, AI-narrated, on-chain party dungeon: buttons are write-once ballots, \
             the plurality choice lands as one real verified turn.",
        )
        .field(
            "The Warden's Keep",
            "`/adventure dungeon start` — open it in this channel · \
             `/adventure dungeon close` — apply the party's choice · \
             `/adventure dungeon verify` — re-verify the playthrough by replay · \
             `/adventure dungeon list` — the world + its executor-enforced rules",
            false,
        )
        .field(
            "The daily descent",
            "`/descent play` — today's beacon-seeded permadeath roguelite (a separate world).",
            false,
        )
        .field(
            "Paid narration",
            "A run-credit buys a real-AI narrated room; without one you get the free narrator.",
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

    /// EXACTLY 13 global commands, and they are the names main.rs routes —
    /// registration, router, and the const stay one surface.
    #[test]
    fn exactly_thirteen_commands_matching_the_router() {
        let cmds = global_commands();
        assert_eq!(
            cmds.len(),
            13,
            "ember directive: exactly 13 global commands"
        );
        assert_eq!(
            names(&cmds),
            crate::REGISTERED_COMMAND_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>(),
            "the registered JSON and REGISTERED_COMMAND_NAMES must agree, in order"
        );
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
        for cmd in global_commands() {
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

    /// EVERY retired flat command keeps a path: still a top-level, a folded
    /// subcommand/group under its new home, or a button on a menu that exists.
    #[test]
    fn every_old_command_is_still_reachable() {
        let cmds = global_commands();
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
            }
        }
    }
}
