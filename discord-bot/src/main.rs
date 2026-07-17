//! dregg Discord Bot — custodial-cclerk front-end to the dregg devnet.
//!
//! Lives at the workspace toplevel `/discord-bot` (peer of `node`, `sdk`,
//! `app-framework`) rather than under `apps/`. Per-user cipherclerks are
//! handles to `dregg_app_framework::AppCipherclerk` — the canonical narrow
//! SDK surface — derived deterministically from the bot's secret and
//! Discord user id.
//!
//! The global slash surface is EXACTLY 13 menu-driven commands (`/dregg` +
//! 12 — see `REGISTERED_COMMAND_NAMES` and `commands::menus`); every former
//! flat command (cclerk management, transfers, gallery, credentials,
//! block-explorer browsing, presence attestation, CapTP, governance, name
//! service, federation linking, the games…) folds behind one of them as a
//! subcommand with its old options intact or as a menu button, on its
//! unchanged handler.

mod activity_feed;
// DreggNet Cloud — semi-private per-user channels (the visibility plan + name).
pub mod channels;
// DreggNet Cloud — drive-your-Hermes-from-your-channel: a channel message becomes
// a cap-gated, metered, receipted dregg turn through the proven `ToolGateway`,
// bounded by the user's own cell. The confined per-user agent loop.
pub mod hermes_channel;
// BYO-LLM-keys: a user ports in their OWN provider key (Anthropic / OpenAI /
// OpenRouter / Kimi / DeepSeek). `key_vault` seals it at rest (AEAD, per-user
// derived key, redacted, zeroized); `llm_provider` is the multi-provider
// abstraction + policy; `hermes_channel` drives the metered, permissioned brain.
pub mod key_vault;
pub mod llm_provider;
// The bot's surfaces authored ONCE as `deos-view` `ViewNode` cards and rendered through
// the Discord backend (`deos_view::discord`) — the card-authored-once-renders-everywhere
// thesis extended to Discord (the FOURTH `ViewNode` backend, alongside native gpui / web
// HTML / seL4 framebuffer). The activity feed routes through it live.
pub mod captp_client;
pub mod cards;
mod cipherclerk;
mod commands;
// Two channel-agents cooperate over the promise-pipeline and settle ATOMICALLY:
// a producer hands a promise (`EventualRef`), the consumer pipelines its payment
// against it, the round settles all-or-nothing through the verified executor
// (`dregg_app_framework::agent_coordination`). Discord-independent + proven.
pub mod coordinate_flow;
// §4.7 canonical, Discord-independent capability-handoff flow: produces and
// validates *real* `dregg_captp::handoff::HandoffCertificate` artifacts.
pub mod handoff_flow;
// §4.7 canonical, Discord-independent signed-intent flow: produces and verifies
// *real* signed `dregg_turn::action::Action` intents (Authorization::Signature).
mod config;
mod credential_issue;
mod db;
// The deos surface inside Discord: a cell's cap-gated affordances projected
// per-viewer as Discord buttons (the REAL `is_attenuation`), transclusion into
// embeds (the REAL `TranscludedField` live quote), and `dregg://` what-links-here
// (the REAL `Backlinks`/`Membrane`). Built on `starbridge-web-surface`.
pub mod deos_surface;
// The deos-desktop ↔ bot drive seam: a desktop surface POSTs a `BotOp` to the bot's
// HTTP surface (`POST /api/op`); the bot builds + signs + submits the SAME real dregg
// turn the Discord command would, records the SAME activity, and can reflect it to
// Discord — desktop + Discord as two faces of one dregg-driven bot.
pub mod deos_drive;
// The bot as a CHAIN-REACTOR: the desktop submits a command turn to the on-chain
// command cell; the bot's `app_framework::Reactor` WATCHES that cell + reacts with
// its custodial turn. The on-chain replacement for the `/api/op` HTTP command
// path — the chain is the message bus, the bot is the reactor.
pub mod bot_reactor;
// THE DAILY-REVEAL CRON — the Descent rolls automatically at the UTC-day boundary. A tokio
// interval task that, when the UTC day strictly advances, FETCHES today's live drand `quicknet`
// round (BLS-verified), caches it into every `/descent` surface, OPENS today's beacon-seeded world
// (fail-closed), and announces the day. Replaces the manual `/descent play`-to-open the daily. The
// reveal core is driven by tests over an in-memory store (a new day rolls a new dungeon).
mod devnet;
pub mod discord_caps;
mod embeds;
// The shared DREGG_EXPLORER_BASE link helper — every former fg-goose.online URL site
// now renders a link only when the operator configured a base, and the full id
// (copyable) otherwise. One pattern, all surfaces (`explorer_link`).
pub mod explorer_link;
pub mod orchestration;
pub mod reveal_cron;
// The sqlite-backed `commands::gallery::GalleryStore` — the durable backing of the
// `/gallery` universe registry over the bot's async `Database` (the sync↔async bridge
// mirrors `pay::SqliteCreditStore`). Installed once at boot; the gallery module then
// loads + re-verifies the live registry from it. See [`gallery_store`].
pub mod gallery_store;
// The sqlite-backed `dreggnet_offerings::character::CharacterStore` — the durable backing of a
// player's LEVELING character over the bot's async `Database` (the sync↔async bridge mirrors
// `pay::SqliteCreditStore`). A leveling character now survives a process restart: a returning
// player resumes their carried level / XP / class. See [`character_store`].
pub mod character_store;
// The sqlite-backed `commands::descent::DescentBoardStore` — the durable backing of the `/descent`
// no-cheat leaderboard board over the bot's async `Database`. Installed once at boot; the descent
// module then loads + re-verifies the live board from it (regenerating each day-world from its
// committed seed and replaying every winning run through the no-cheat gate). See [`descent_board_store`].
pub mod descent_board_store;
// The durable sqlite SessionResumeStore behind the per-identity `/play` RPG worlds
// (`commands::rpg_world`): session opens + landed advances persist as reproducible
// public input and reopen by replay (never a trusted state blob).
pub mod rpg_store;
// $DREGG-paid, real-AI dungeon runs: the sqlite-backed `dregg_pay::CreditStore`, the per-user
// deposit-address provider, the credit ledger, the payment poll, and the `/dungeon` gate that
// debits one earned credit and routes to real Bedrock (`dregg_narrator`) under a PER-RUN budget.
// Free tier stays ollama/scripted. Devnet/mock by default; mainnet is an operator env flip.
pub mod pay;
// Real selective-disclosure proofs: parses a predicate (`age>=18`), reads the
// subject's attribute, and wires the SDK's `prove_predicate_unlinkable` so
// `/credential verify` emits a GENUINE unlinkable STARK proof (not a null one).
pub mod identity_proof;
pub mod intent_flow;
pub mod presence;
/// The bot's command surface published as a typed, cap-gated service-cell
/// `InterfaceDescriptor`, driven through the `invoke()` front door (the modern
/// service-cell face, mirroring the `starbridge-nameservice` citizen).
pub mod service;

// Production HTTP read surface (§4.7) — axum + tower middlewares, graceful shutdown,
// SSE, CellStateView-compatible responses, reuses devnet/captp/db/NullifierSet.
mod http_server;

// The interactive ViewNode loop inside Discord: a `deosturn:<turn>:<arg>` button press →
// a REAL cap-gated verified dregg turn → the card embed re-renders from the new committed
// state (the interactive half of the `deos_view` Discord backend, `69e15322`).
pub mod viewnode_applet;

use std::sync::Arc;

use serenity::Client;
use serenity::all::{
    Context, EventHandler, GatewayIntents, Guild, Interaction, Message, Presence, Ready,
};
use serenity::async_trait;
use tokio::sync::Mutex;
use tracing::{error, info, warn};

use captp_client::CapTPClient;
use config::Config;
use db::Database;
use devnet::DevnetClient;
use discord_caps::{DiscordCapRegistry, EventBridge};
use presence::{PresenceStatus, PresenceTracker};

// The slash-command surface after the 13-command consolidation: EXACTLY
// thirteen global commands (`/dregg` + 12), each of which opens a menu or
// summons a world. Every retired flat command (~53 of them) is folded behind
// its new home as a subcommand with its old options intact, or as a menu
// button — the handlers are unchanged; only the front door moved. The fold
// (registration by serialization + dispatch by re-nesting) lives in
// `commands::menus`, whose tests assert this list, the registered JSON, and
// the router agree, and that every old command kept a path.
const REGISTERED_COMMAND_NAMES: &[&str] = &[
    // 1. the HUB — panels + buttons that summon every other surface
    //    (folds: dashboard → the Ops button, status → the Node-status button)
    "dregg",
    // 2. today's beacon-seeded permadeath roguelite WORLD (unchanged)
    "descent",
    // 3. the games ARCADE (folds: play → `open`, market; tug/automatafl are
    //    `open` choices)
    "play",
    // 4. narrative WORLDS (folds: dungeon — the shared AI-narrated crawl)
    "adventure",
    // 5. you + your funds (folds: the cipherclerk's own subcommands, plus
    //    send, history, faucet, credits, buy-credits, treasury)
    "cipherclerk",
    // 6. the UGC universe registry (unchanged)
    "gallery",
    // 7. the DAO (folds: council, council-status, council-approve, bounty, intent)
    "govern",
    // 8. the proof surface (folds: proof, explorer, crown, export, card)
    "verify",
    // 9. granting authority (folds: cap-*, handoff*, link-*, key)
    "identity",
    // 10. the confined offerings (folds: hermes's own subcommands, grain, doc)
    "hermes",
    // 11. the network (folds: federation-status/peers, setup-federation,
    //     activity, coordinate, channel, presence, deos)
    "federation",
    // 12. glory (unchanged)
    "leaderboard",
    // 13. onboarding + the tour + the map (folds: start, help)
    "help",
];

#[cfg(test)]
const ROUTED_COMMAND_NAMES: &[&str] = REGISTERED_COMMAND_NAMES;

/// Shared bot state accessible from all command handlers.
pub struct BotState {
    pub config: Config,
    pub db: Database,
    pub devnet: DevnetClient,
    pub presence: Mutex<PresenceTracker>,
    /// The bot's CapTP client — its identity and capability management.
    pub captp: CapTPClient,
    /// Registry of Discord capabilities exercisable via CapTP.
    pub discord_caps: DiscordCapRegistry,
    /// Event bridge: Discord events → dregg turns.
    pub event_bridge: EventBridge,
    /// The offering session→surface lifecycle (the "Midjourney layer"): spins a
    /// per-session channel/thread by EXERCISING `discord_caps`, links it to a dregg
    /// queue, and revokes every cap cell at teardown. A `guild_create` handler drives
    /// its per-offering bootstrap (mint-if-absent the offering category) the moment the
    /// bot joins/restarts against a guild. See [`orchestration`].
    pub orchestrator: orchestration::SessionOrchestrator,
    /// The federation id this bot binds cipherclerk signatures to. Threaded
    /// through every per-user `UserCipherclerk::derive(...)` call so the
    /// AppCipherclerk's action signatures are bound to the correct group.
    pub federation_id_bytes: [u8; 32],
    /// §4.7 soft-federation for the friend clique: small NullifierSet used to
    /// order note-spends among trusted peers. Single Ed25519 root; defers to
    /// real federation when present. (Populated from captp_client state.)
    pub nullifier_set: Mutex<Vec<[u8; 32]>>, // minimal in-memory set for demo
    /// §4.7 canonical capability-handoff broker — the bot as the tiny
    /// federation that mints and validates *real* signed
    /// `dregg_captp::handoff::HandoffCertificate` artifacts (target swiss
    /// table + trusted introducer set). See `handoff_flow.rs`.
    pub handoff_broker: Mutex<handoff_flow::HandoffBroker>,
    /// The per-(user, card) registry of live embedded card applets — the in-process
    /// substance the interactive ViewNode loop drives. A `deosturn:` button press fires
    /// a real cap-gated verified turn on the pressing user's card and re-renders it
    /// (`viewnode_applet`).
    pub card_applets: viewnode_applet::CardApplets,
    /// DreggNet Cloud — the per-user confined Hermes sessions, keyed by Discord
    /// user id. Held here so a user's rate budgets accumulate across the messages
    /// they post in their channel. Each session is bounded by the user's own cell
    /// (derived from their custodial seed). See [`hermes_channel`].
    pub channel_hermes:
        std::sync::Mutex<std::collections::HashMap<u64, hermes_channel::ChannelHermes>>,
    /// $DREGG earning state: the sqlite-backed per-user run-credit ledger, the deterministic
    /// deposit-address provider, the payment watcher, and the paid real-AI narrator. Powers
    /// `/buy-credits`, `/credits`, the payment poll, and the `/dungeon` credit gate. Devnet/mock by
    /// default; mainnet is an operator env flip (`PayConfig::from_env`). See [`crate::pay`].
    pub pay: pay::PayState,
    /// Persistent, LEVELING characters — the durable [`character_store::SqliteCharacterStore`]
    /// keyed by a player's stable dregg identity. A player's `/dungeon` character (xp / level /
    /// class) survives a process restart: on their first move in a run their carried sheet is
    /// resumed, XP earned by the party's real outcomes is saved back through the gated character
    /// turn, and a tampered/absent row fails safe to a fresh level-1 character.
    pub characters: character_store::SqliteCharacterStore,
}

/// The main event handler for Discord gateway events.
struct Handler {
    state: Arc<BotState>,
}

#[async_trait]
impl EventHandler for Handler {
    async fn ready(&self, ctx: Context, ready: Ready) {
        info!("Bot connected as {}", ready.user.name);

        // Register the EXACTLY-13 global slash commands (`commands::menus`):
        // each opens a menu or summons a world, and every retired flat
        // command rides inside one of them as a subcommand/group with its old
        // options intact (registration by serialization — the old builders
        // are folded, never re-typed). Names retired from this set (the ~40
        // old flat commands) disappear from Discord on re-registration.
        let commands = commands::menus::global_commands();
        debug_assert_eq!(
            commands
                .iter()
                .map(|c| c["name"].as_str().unwrap_or_default().to_owned())
                .collect::<Vec<_>>(),
            REGISTERED_COMMAND_NAMES
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>(),
            "registered commands and REGISTERED_COMMAND_NAMES must agree"
        );

        match ctx.http.create_global_commands(&commands).await {
            Ok(cmds) => info!("Registered {} global slash commands", cmds.len()),
            Err(e) => error!("Failed to register commands: {e}"),
        }

        // Start the activity feed background task.
        activity_feed::start(self.state.clone(), ctx.http.clone());

        // Start the on-chain command reactor: watch the command cell + react to
        // desktop-submitted command turns (the on-chain replacement for the
        // `/api/op` HTTP command path). The bot is a chain-reactor, not an
        // endpoint the desktop pokes.
        bot_reactor::start(self.state.clone(), ctx.http.clone());

        // Start the daily-reveal cron: at the UTC-day boundary it fetches + verifies today's live
        // drand round, caches it into every `/descent` surface, opens today's beacon-seeded world,
        // and announces the day — the Descent rolls automatically (no manual `/descent play`).
        reveal_cron::start(self.state.clone(), ctx.http.clone());
    }

    /// The moment the bot joins (or restarts against) a guild: bootstrap every
    /// offering the guild hosts BEFORE its first session opens. For the dungeon this
    /// mints-if-absent the `dreggnet-dungeon` category (by EXERCISING a `CreateCategory`
    /// capability) and caches it, so a later `orchestrator.open(...)` files its session
    /// channel under a category that already exists rather than paying the mint on the
    /// user's critical path. An `Err` here means the bot lacks `MANAGE_CHANNELS` in this
    /// guild — logged as a warning, not fatal (the bot serves everything else fine).
    async fn guild_create(&self, ctx: Context, guild: Guild, _is_new: Option<bool>) {
        let guild_id = guild.id.get();
        // Attribute the bootstrap's guild-writes to the pinned admin in the audit log
        // (the bot/admin acting on guild_create, not any end user); `0` when unpinned.
        let registered_by = self.state.config.admin_discord_id.unwrap_or(0);
        let bootstraps = [orchestration::OfferingBootstrap::new(
            "dungeon",
            guild_id,
            registered_by,
        )];
        match self
            .state
            .orchestrator
            .bootstrap_guild(&bootstraps, &self.state.discord_caps, &ctx.http)
            .await
        {
            Ok(reports) => {
                for report in reports {
                    info!(
                        offering = %report.offering,
                        guild_id = report.guild_id,
                        category_id = ?report.category_id,
                        "Bootstrapped offering on guild_create"
                    );
                }
            }
            Err(e) => {
                warn!(
                    guild_id,
                    error = %e,
                    "Failed to bootstrap offerings on guild_create (the bot likely lacks \
                     MANAGE_CHANNELS in this guild); sessions can still open once granted"
                );
            }
        }
    }

    async fn interaction_create(&self, ctx: Context, interaction: Interaction) {
        if let Interaction::Command(command) = interaction {
            let name = command.data.name.as_str();

            match name {
                // The 13-command surface: each arm opens a menu or summons a
                // world; the folded old commands re-nest through
                // `commands::menus` onto their UNCHANGED handlers.
                "dregg" => commands::dashboard::handle(&ctx, &command, &self.state).await,
                "descent" => commands::descent::handle(&ctx, &command, &self.state).await,
                "play" => commands::menus::handle_play(&ctx, &command, &self.state).await,
                "adventure" => commands::menus::handle_adventure(&ctx, &command, &self.state).await,
                "cipherclerk" => {
                    commands::menus::handle_cipherclerk(&ctx, &command, &self.state).await
                }
                "gallery" => commands::gallery::handle(&ctx, &command, &self.state).await,
                "govern" => commands::menus::handle_govern(&ctx, &command, &self.state).await,
                "verify" => commands::menus::handle_verify(&ctx, &command, &self.state).await,
                "identity" => commands::menus::handle_identity(&ctx, &command, &self.state).await,
                "hermes" => commands::menus::handle_hermes(&ctx, &command, &self.state).await,
                "federation" => {
                    commands::menus::handle_federation(&ctx, &command, &self.state).await
                }
                "leaderboard" => {
                    commands::social::handle_leaderboard(&ctx, &command, &self.state).await
                }
                "help" => commands::menus::handle_help(&ctx, &command, &self.state).await,
                _ => {
                    tracing::warn!("Unknown command: {name}");
                }
            }
        } else if let Interaction::Component(component) = interaction {
            // Route component presses by custom-id prefix:
            //   `start:<action>` — a `/start` button (onboarding/menu): fire the
            //     real cap-gated turn or open the relevant modal;
            //   `deosturn:<turn>:<arg>` — a ViewNode card affordance: fire it as a REAL
            //     cap-gated verified turn and re-render the card (the interactive loop);
            //   `deos:<hex8>:<affordance>` — a cap-gated deos-surface button: RE-RUN the
            //     cap gate in the deos handler;
            //   everything else is the dashboard's (`dregg:*`).
            let custom_id = &component.data.custom_id;
            if custom_id.starts_with("menu:") {
                // A 13-command menu press: `menu:go:*` swaps the menu message in
                // place; `menu:run:*` fires the module's real `execute_*` read;
                // `menu:pick:*` answers the arcade select (`commands::menus`).
                commands::menus::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("start:") {
                commands::start::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("deosturn:") {
                viewnode_applet::handle_deosturn_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("deos:") {
                commands::deos::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("fiction:") {
                // A `/dungeon` ballot button — a write-once vote attributed to the presser's
                // derived dregg identity (`commands::fiction`).
                commands::fiction::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("descent:") {
                // A `/descent` move button — advances the presser's OWN permadeath run by one real
                // executor turn (`commands::descent`).
                commands::descent::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("offering:") {
                // A DreggNet-offering affordance (`offering:fire:<key>:<turn>:<arg>` /
                // `offering:ask:<key>:<turn>`): the generic adapter fires it as ONE real
                // `Offering::advance` attributed to the presser's derived dregg identity —
                // a landed `TurnReceipt` or a real executor `Refused` — and re-renders the
                // offering's own deos surface. `<key>` selects `/council` vs `/market`.
                commands::offering::route_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("crown:") {
                // 👑 A crown button — fold a finished match to ONE proof, poll the background
                // fold, or stranger-re-verify the proof-carrying board entry (`commands::crown`).
                commands::crown::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("verifychain:") {
                // The standing "⛓ re-verify chain" press on every offering surface
                // (`commands::verify_chain`, backlog Tier-2 #10/#12).
                commands::verify_chain::handle_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("txcheck:") {
                // A `/history`/`/leaderboard` ledger row's re-check-against-the-chain press
                // (`commands::tx_recheck`, backlog Tier-2 #13).
                commands::tx_recheck::handle_component(&ctx, &component, &self.state).await;
            } else {
                commands::dashboard::handle_component(&ctx, &component, &self.state).await;
            }
        } else if let Interaction::Modal(modal) = interaction {
            // `start:modal:*` forms (Send / Set key) belong to the `/start` flow;
            // `offering:submit:<key>:<turn>` is a DreggNet-offering affordance whose arg the
            // user typed (a market reserve / a sealed bid) — the generic adapter fires it as
            // ONE real turn; everything else is the dashboard's.
            if modal.data.custom_id.starts_with("start:") {
                commands::start::handle_modal(&ctx, &modal, &self.state).await;
            } else if modal.data.custom_id.starts_with("offering:") {
                commands::offering::route_modal(&ctx, &modal, &self.state).await;
            } else {
                commands::dashboard::handle_modal(&ctx, &modal, &self.state).await;
            }
        }
    }

    async fn message(&self, ctx: Context, msg: Message) {
        // Bridge messages to dregg queues if the channel is linked.
        self.state.event_bridge.on_message(&msg).await;
        // DreggNet Cloud: if this is a per-user channel, the message drives the
        // owner's confined Hermes (a cap-gated, metered, receipted dregg turn).
        hermes_channel::on_message(&ctx, &msg, &self.state).await;
    }

    async fn presence_update(&self, _ctx: Context, data: Presence) {
        let user_id = data.user.id.get();

        // Map serenity's OnlineStatus to our PresenceStatus.
        let status = match data.status {
            serenity::all::OnlineStatus::Online => PresenceStatus::Online,
            serenity::all::OnlineStatus::Idle => PresenceStatus::Idle,
            serenity::all::OnlineStatus::DoNotDisturb => PresenceStatus::Dnd,
            serenity::all::OnlineStatus::Offline | serenity::all::OnlineStatus::Invisible => {
                PresenceStatus::Offline
            }
            _ => PresenceStatus::Offline,
        };

        let mut tracker = self.state.presence.lock().await;
        let (old, new) = tracker.update(user_id, status);

        // Log significant transitions.
        if let Some(old_status) = old {
            if old_status != new {
                tracing::debug!(
                    user_id,
                    old = %old_status,
                    new = %new,
                    "Presence update"
                );
            }
        }
    }
}

/// The boot preflight's federation-id check against a reachable **SOLO** node: the node's
/// executor signs under `blake3(node_pubkey)`, so a bot whose `FEDERATION_ID` differs (including
/// the all-zero dev default) would have EVERY transfer rejected at runtime with
/// "Ed25519 signature verification failed". `Ok(())` when they match; `Err` carries the clear
/// operator message (naming the env var and the exact expected value). `main` fails FAST on
/// `Err` unless `FEDERATION_ID_ALLOW_MISMATCH=1` (a deliberate dev escape hatch).
fn check_solo_federation_id(node_pubkey: &[u8], federation_id: [u8; 32]) -> Result<(), String> {
    let expected = *blake3::hash(node_pubkey).as_bytes();
    if expected == federation_id {
        return Ok(());
    }
    Err(format!(
        "FEDERATION_ID mismatch: this is a SOLO node whose executor signs under \
         blake3(node_pubkey)={expected}, but the bot's FEDERATION_ID is {actual}. Every transfer \
         would fail at runtime with 'Ed25519 signature verification failed'. Set \
         FEDERATION_ID={expected} to match (or FEDERATION_ID_ALLOW_MISMATCH=1 to boot anyway, \
         for a deliberate dev setup).",
        expected = hex::encode(expected),
        actual = hex::encode(federation_id),
    ))
}

#[tokio::main]
async fn main() {
    // Initialize tracing.
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    info!("Starting dregg Discord bot...");

    // Load configuration. Graceful error (no panic) for operator UX.
    let config = match Config::from_env() {
        Ok(c) => c,
        Err(msg) => {
            eprintln!("error: {msg}");
            eprintln!();
            eprintln!("Set the required environment variables and try again. Example:");
            eprintln!("  export DISCORD_TOKEN=...");
            eprintln!("  export DISCORD_APP_ID=...");
            eprintln!("  export BOT_SECRET=...  # 64 hex chars");
            eprintln!("  export FEDERATION_ID=...  # 64 hex chars (soft-federation root)");
            eprintln!("  export HTTP_PORT=8080");
            std::process::exit(1);
        }
    };

    // Use the configured (non-zero in real deployments) federation root for the
    // soft-federation friend clique. No more hard-coded [0u8;32].
    let federation_id_bytes = config.federation_id_bytes;
    if federation_id_bytes.iter().all(|&b| b == 0) {
        info!(
            "using all-zero federation id (dev default); set FEDERATION_ID for production cliques"
        );
    }

    // Connect to database.
    let db = Database::connect(&config.database_url)
        .await
        .expect("failed to connect to database");
    info!("Database connected");

    // Install the durable UGC-gallery store and load + re-verify the live registry from
    // it (every persisted completion re-executed on a fresh identically-seeded world).
    // First install wins; done BEFORE any `/gallery` command is served. Built on a
    // blocking thread because `install_store` drives the sync GalleryStore (which uses
    // `block_in_place`) and forces the registry to initialize from the store now.
    {
        let store =
            gallery_store::SqliteGalleryStore::new(db.clone(), tokio::runtime::Handle::current());
        tokio::task::spawn_blocking(move || {
            commands::gallery::install_store(Box::new(store));
        })
        .await
        .expect("install gallery store");
    }
    info!("UGC gallery store installed (registry loaded + re-verified from sqlite)");

    // Install the durable /descent board store and load + re-verify the live no-cheat board from it
    // (each day-world regenerated from its committed seed, every winning run replayed through the
    // no-cheat gate). First install wins; done BEFORE any `/descent` command is served. Built on a
    // blocking thread because `install_store` drives the sync DescentBoardStore and forces the
    // dedicated board thread to spawn + load now.
    {
        let store = descent_board_store::SqliteDescentBoardStore::new(
            db.clone(),
            tokio::runtime::Handle::current(),
        );
        tokio::task::spawn_blocking(move || {
            commands::descent::install_store(Box::new(store));
        })
        .await
        .expect("install descent board store");
    }
    info!("Descent board store installed (board loaded + re-verified from sqlite)");

    // Create devnet client.
    let devnet = DevnetClient::new(&config.devnet_url);
    info!("Devnet client configured for {}", config.devnet_url);

    // Startup preflight: probe the node and catch the two most common
    // misconfigurations BEFORE users hit them as cryptic command failures.
    //   1. node unreachable   -> warn (bot still boots; recovers when node up)
    //   2. FEDERATION_ID wrong -> on a SOLO node the executor signs under
    //      blake3(node_pubkey); if the bot's FEDERATION_ID doesn't match,
    //      EVERY transfer is rejected with "Ed25519 signature verification
    //      failed". We compute the expected value and warn on mismatch.
    {
        let pf = devnet.preflight().await;
        if pf.reachable {
            info!(
                "node OK: mode={} consensus_live={} dag_height={} height={}",
                pf.federation_mode, pf.consensus_live, pf.dag_height, pf.latest_height
            );
            if pf.federation_mode == "solo" && !pf.public_key.is_empty() {
                if let Ok(pk) = hex::decode(&pf.public_key) {
                    match check_solo_federation_id(&pk, federation_id_bytes) {
                        Ok(()) => {
                            info!("FEDERATION_ID matches the solo node's executor signing domain")
                        }
                        Err(msg) => {
                            // A mismatch here is not a degraded mode — EVERY transfer fails at
                            // runtime. Fail FAST at boot so the operator fixes the env var now,
                            // unless they deliberately opted out (a dev bot pointed at a node it
                            // never transfers through).
                            let allow = std::env::var("FEDERATION_ID_ALLOW_MISMATCH")
                                .is_ok_and(|v| v == "1");
                            if allow {
                                warn!("{msg} (booting anyway: FEDERATION_ID_ALLOW_MISMATCH=1)");
                            } else {
                                error!("{msg}");
                                eprintln!("error: {msg}");
                                std::process::exit(1);
                            }
                        }
                    }
                }
            }
        } else {
            warn!(
                "node at {} is unreachable at startup ({}). The bot will boot and \
                 retry per-command; check the node and DEVNET_URL.",
                config.devnet_url,
                pf.error.as_deref().unwrap_or("unknown error"),
            );
        }
    }

    // Build presence tracker.
    let presence = Mutex::new(PresenceTracker::new(config.bot_secret));
    info!("Presence tracker initialized");

    // Build CapTP client (the bot's own dregg identity).
    //
    // The bot's own cclerk is the user_id == 0 derivation. We use the
    // canonical AppCipherclerk so the bot's identity (cell id, public key)
    // is computed the same way as any other dregg agent.
    let (bot_cell_id, bot_public_key) = {
        let cclerk =
            cipherclerk::UserCipherclerk::derive(&config.bot_secret, 0, federation_id_bytes);
        (
            cclerk.cell_id_hex().to_string(),
            cclerk.public_key_hex().to_string(),
        )
    };
    match devnet.register_cell(&bot_cell_id, &bot_public_key).await {
        Ok(()) => info!("Bot dregg cell materialized on devnet"),
        Err(err) => warn!("Failed to materialize bot dregg cell: {err}"),
    }
    let federation_id = dregg_captp::FederationId(federation_id_bytes);
    let captp = CapTPClient::new(
        federation_id,
        bot_cell_id.clone(),
        config.devnet_url.clone(),
    );
    info!(
        "CapTP client initialized, bot cell: {}...",
        &bot_cell_id[..16]
    );

    // Build Discord capability registry and event bridge.
    let discord_caps = DiscordCapRegistry::new();
    let event_bridge = EventBridge::new(config.devnet_url.clone());

    // Build the $DREGG earning state (devnet/mock by default; mainnet is an operator env flip via
    // DREGG_PAY_*). The sqlite CreditStore drives on this multi-thread runtime. Built on a blocking
    // thread because the hosted Bedrock client (when configured) constructs its OWN Tokio runtime,
    // which must not happen on an async worker.
    let pay = {
        let db_for_pay = db.clone();
        let bot_secret = config.bot_secret;
        let handle = tokio::runtime::Handle::current();
        tokio::task::spawn_blocking(move || {
            pay::PayState::from_env_or_devnet(db_for_pay, &bot_secret, handle)
        })
        .await
        .expect("build pay state")
    };
    // The durable character store: persistent leveling characters keyed by a player's stable
    // dregg identity, so a `/dungeon` character survives a process restart. A plain durable handle
    // (no boot-time registry to re-verify — a character is loaded lazily on a player's first move);
    // the sync↔async bridge drives the async db from the sync `CharacterStore` trait.
    let characters =
        character_store::SqliteCharacterStore::new(db.clone(), tokio::runtime::Handle::current());
    info!("Character store ready (persistent leveling characters over sqlite; survive restart)");

    info!(
        "Pay backend ready: network={:?} price_per_run={} paid_narrator={}",
        pay.network(),
        pay.price_per_run(),
        if pay.paid.is_some() {
            "bedrock"
        } else {
            "free-tier-only"
        },
    );

    // Build shared state (now carries the real federation + HTTP config).
    let state = Arc::new(BotState {
        config,
        db,
        devnet,
        presence,
        captp,
        discord_caps,
        event_bridge,
        orchestrator: orchestration::SessionOrchestrator::new(),
        federation_id_bytes,
        nullifier_set: Mutex::new(Vec::new()), // §4.7 friend-clique soft-federation
        handoff_broker: Mutex::new(handoff_flow::HandoffBroker::new(dregg_captp::FederationId(
            federation_id_bytes,
        ))),
        card_applets: viewnode_applet::CardApplets::new(),
        channel_hermes: std::sync::Mutex::new(std::collections::HashMap::new()),
        pay,
        characters,
    });

    // §4.7 Production HTTP read surface (Starbridge RemoteRuntime + humans).
    // Spawn the axum server (with body limits, tracing, graceful shutdown, SSE,
    // CellStateView-compatible responses for inspectors). Runs concurrently
    // with the Discord client. The CapTP + activity_feed + devnet + NullifierSet
    // foundation is now fully surfaced as a reliable third-party dregg peer.
    tokio::spawn(http_server::start(state.clone()));
    info!(
        "HTTP read surface scheduled on {}:{} (see /api/cells, /api/cell/<id>, /observability/stream etc.)",
        state.config.http_host, state.config.http_port
    );

    // Build Discord client. GUILD_PRESENCES + GUILD_MESSAGES for message bridging;
    // GUILDS delivers `guild_create` (the offering-bootstrap trigger) + guild/channel
    // metadata; GUILD_MEMBERS is needed to resolve members for per-session role grants
    // (`orchestration`'s AssignRole path).
    let intents = GatewayIntents::GUILDS
        | GatewayIntents::GUILD_MEMBERS
        | GatewayIntents::GUILD_PRESENCES
        | GatewayIntents::GUILD_MESSAGES
        | GatewayIntents::MESSAGE_CONTENT
        | GatewayIntents::GUILD_MESSAGE_REACTIONS;
    let mut client = Client::builder(&state.config.discord_token, intents)
        .event_handler(Handler {
            state: state.clone(),
        })
        .await
        .expect("failed to create Discord client");

    // Start the bot.
    info!("Connecting to Discord...");
    if let Err(e) = client.start().await {
        error!("Bot error: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::{REGISTERED_COMMAND_NAMES, ROUTED_COMMAND_NAMES, check_solo_federation_id};
    use std::collections::BTreeSet;

    /// A FEDERATION_ID matching the solo node's signing domain (blake3 of its pubkey) boots.
    #[test]
    fn a_matching_solo_federation_id_passes_the_boot_preflight() {
        let pk = [7u8; 32];
        let fed = *blake3::hash(&pk).as_bytes();
        assert!(check_solo_federation_id(&pk, fed).is_ok());
    }

    /// A mismatched FEDERATION_ID (the all-zero dev-default footgun included) is fatal at boot,
    /// and the message names the env var, the exact expected value, and the escape hatch.
    #[test]
    fn a_mismatched_solo_federation_id_is_fatal_with_the_fix_in_the_message() {
        let pk = [7u8; 32];
        let expected = hex::encode(blake3::hash(&pk).as_bytes());
        let err = check_solo_federation_id(&pk, [0u8; 32])
            .expect_err("an all-zero FEDERATION_ID against a solo node must be refused at boot");
        assert!(err.contains("FEDERATION_ID"), "{err}");
        assert!(
            err.contains(&expected),
            "the message names the exact expected value: {err}"
        );
        assert!(err.contains("FEDERATION_ID_ALLOW_MISMATCH"), "{err}");
    }

    #[test]
    fn registered_commands_have_no_duplicates() {
        let unique: BTreeSet<_> = REGISTERED_COMMAND_NAMES.iter().copied().collect();
        assert_eq!(
            unique.len(),
            REGISTERED_COMMAND_NAMES.len(),
            "registered slash command names must be unique"
        );
    }

    #[test]
    fn registered_commands_match_router_surface() {
        let registered: BTreeSet<_> = REGISTERED_COMMAND_NAMES.iter().copied().collect();
        let routed: BTreeSet<_> = ROUTED_COMMAND_NAMES.iter().copied().collect();
        assert_eq!(
            registered, routed,
            "every registered command must have a router arm and every router arm must be registered"
        );
    }
}
