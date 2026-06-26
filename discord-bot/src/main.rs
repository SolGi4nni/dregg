//! dregg Discord Bot — custodial-cclerk front-end to the dregg devnet.
//!
//! Lives at the workspace toplevel `/discord-bot` (peer of `node`, `sdk`,
//! `app-framework`) rather than under `apps/`. Per-user cipherclerks are
//! handles to `dregg_app_framework::AppCipherclerk` — the canonical narrow
//! SDK surface — derived deterministically from the bot's secret and
//! Discord user id.
//!
//! Slash commands cover: cclerk management, transfers, gallery
//! (apps/gallery), credentials (apps/identity), block-explorer browsing,
//! presence attestation (proof-of-online dischargeable caveats), CapTP
//! (bot as a capability peer), programmable queues, governance
//! (apps/governed-namespace), name service (apps/nameservice), and
//! Discord<->dregg federation linking.

mod activity_feed;
// The bot's surfaces authored ONCE as `deos-view` `ViewNode` cards and rendered through
// the Discord backend (`deos_view::discord`) — the card-authored-once-renders-everywhere
// thesis extended to Discord (the FOURTH `ViewNode` backend, alongside native gpui / web
// HTML / seL4 framebuffer). The activity feed routes through it live.
pub mod captp_client;
pub mod cards;
mod cipherclerk;
mod commands;
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
mod devnet;
pub mod discord_caps;
mod embeds;
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
    Command, Context, EventHandler, GatewayIntents, Interaction, Message, Presence, Ready,
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

const REGISTERED_COMMAND_NAMES: &[&str] = &[
    "explorer",
    "presence",
    "cipherclerk",
    "send",
    "tip",
    "gallery",
    "credential",
    "status",
    "proof",
    "metrics",
    "faucet",
    "leaderboard",
    "history",
    "dregg",
    "cap-share",
    "cap-accept",
    "cap-delegate",
    "cap-list",
    "cap-revoke",
    "queue-create",
    "queue-publish",
    "queue-subscribe",
    "queue-status",
    "queue-mount",
    "gov-propose",
    "gov-vote",
    "gov-status",
    "gov-routes",
    "council-status",
    "name-register",
    "name-resolve",
    "name-whois",
    "setup-federation",
    "link-cipherclerk",
    "unlink-cipherclerk",
    "handoff",
    "handoff-redeem",
    "intent",
    "bounty",
    // ─── new reads + organ actions (wired this integration) ─────────────
    "federation-status",
    "federation-peers",
    "council-approve",
    "activity",
    "dashboard",
    "cap-peer",
    "handoff-status",
    // ─── deos surface inside Discord (cap-gated affordance buttons + transclusion) ─
    "deos",
    // ─── interactive ViewNode card (buttons fire real verified turns) ───────────
    "card",
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
}

/// The main event handler for Discord gateway events.
struct Handler {
    state: Arc<BotState>,
}

#[async_trait]
impl EventHandler for Handler {
    async fn ready(&self, ctx: Context, ready: Ready) {
        info!("Bot connected as {}", ready.user.name);

        // Register global slash commands.
        //
        // Commands tied to apps deleted from the workspace (AMM `swap`/
        // `pool`/`lend`, orderbook `order`/`book`/`trades`) were retired
        // in the post-relocation cleanup; their slash-command names will
        // disappear from Discord once this set is re-registered.
        let commands = vec![
            // ─── Bot core ───────────────────────────────────────────────────
            commands::explorer::register(),
            commands::presence::register(),
            commands::cipherclerk::register(),
            commands::transfer::register_send(),
            commands::transfer::register_tip(),
            commands::gallery::register(),
            commands::identity::register(),
            commands::status::register_status(),
            commands::status::register_proof(),
            commands::status::register_metrics(),
            commands::social::register_faucet(),
            commands::social::register_leaderboard(),
            commands::social::register_history(),
            commands::dashboard::register(),
            // ─── CapTP commands ─────────────────────────────────────────────
            commands::captp::register_share(),
            commands::captp::register_accept(),
            commands::captp::register_delegate(),
            commands::captp::register_list(),
            commands::captp::register_revoke(),
            // ─── Programmable queue commands ─────────────────────────────────
            commands::queue::register_create(),
            commands::queue::register_publish(),
            commands::queue::register_subscribe(),
            commands::queue::register_status(),
            commands::queue::register_mount(),
            // ─── Governance commands ────────────────────────────────────────
            commands::governance::register_propose(),
            commands::governance::register_vote(),
            commands::governance::register_status(),
            commands::governance::register_routes(),
            commands::polis::register_council_status(),
            // ─── Name service commands ──────────────────────────────────────
            commands::names::register_register(),
            commands::names::register_resolve(),
            commands::names::register_whois(),
            // ─── Federation setup commands ──────────────────────────────────
            commands::federation::register_setup(),
            commands::federation::register_link(),
            commands::federation::register_unlink(),
            // ─── Canonical CapTP handoff (§4.7) ─────────────────────────────
            commands::handoff::register(),
            commands::handoff::register_redeem(),
            commands::intent::register(),
            // ─── Bounty board (starbridge-bounty-board) ─────────────────────
            commands::bounty::register(),
            // ─── New reads + organ actions (wired this integration) ─────────
            commands::federation::register_status(),
            commands::federation::register_peers(),
            commands::polis::register_council_approve(),
            commands::social::register_activity(),
            commands::dashboard::register_dashboard(),
            commands::captp::register_peer(),
            commands::handoff::register_status(),
            // ─── deos surface inside Discord ────────────────────────────────
            commands::deos::register(),
            // ─── interactive ViewNode card ──────────────────────────────────
            commands::card::register(),
        ];
        debug_assert_eq!(commands.len(), REGISTERED_COMMAND_NAMES.len());

        match Command::set_global_commands(&ctx.http, commands).await {
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
    }

    async fn interaction_create(&self, ctx: Context, interaction: Interaction) {
        if let Interaction::Command(command) = interaction {
            let name = command.data.name.as_str();

            match name {
                // ─── Bot core ───────────────────────────────────────────────
                "explorer" => commands::explorer::handle(&ctx, &command, &self.state).await,
                "presence" => commands::presence::handle(&ctx, &command, &self.state).await,
                "cipherclerk" => commands::cipherclerk::handle(&ctx, &command, &self.state).await,
                "send" | "tip" => commands::transfer::handle(&ctx, &command, &self.state).await,
                "gallery" => commands::gallery::handle(&ctx, &command, &self.state).await,
                "credential" => commands::identity::handle(&ctx, &command, &self.state).await,
                "status" => commands::status::handle_status(&ctx, &command, &self.state).await,
                "proof" => commands::status::handle_proof(&ctx, &command, &self.state).await,
                "metrics" => commands::status::handle_metrics(&ctx, &command, &self.state).await,
                "faucet" => commands::social::handle_faucet(&ctx, &command, &self.state).await,
                "leaderboard" => {
                    commands::social::handle_leaderboard(&ctx, &command, &self.state).await
                }
                "history" => commands::social::handle_history(&ctx, &command, &self.state).await,
                "dregg" => commands::dashboard::handle(&ctx, &command, &self.state).await,
                // ─── CapTP commands ─────────────────────────────────────────
                "cap-share" => commands::captp::handle_share(&ctx, &command, &self.state).await,
                "cap-accept" => commands::captp::handle_accept(&ctx, &command, &self.state).await,
                "cap-delegate" => {
                    commands::captp::handle_delegate(&ctx, &command, &self.state).await
                }
                "cap-list" => commands::captp::handle_list(&ctx, &command, &self.state).await,
                "cap-revoke" => commands::captp::handle_revoke(&ctx, &command, &self.state).await,
                // ─── Programmable queue commands ─────────────────────────────
                "queue-create" => commands::queue::handle_create(&ctx, &command, &self.state).await,
                "queue-publish" => {
                    commands::queue::handle_publish(&ctx, &command, &self.state).await
                }
                "queue-subscribe" => {
                    commands::queue::handle_subscribe(&ctx, &command, &self.state).await
                }
                "queue-status" => commands::queue::handle_status(&ctx, &command, &self.state).await,
                "queue-mount" => commands::queue::handle_mount(&ctx, &command, &self.state).await,
                // ─── Governance commands ────────────────────────────────────
                "gov-propose" => {
                    commands::governance::handle_propose(&ctx, &command, &self.state).await
                }
                "gov-vote" => commands::governance::handle_vote(&ctx, &command, &self.state).await,
                "gov-status" => {
                    commands::governance::handle_status(&ctx, &command, &self.state).await
                }
                "gov-routes" => {
                    commands::governance::handle_routes(&ctx, &command, &self.state).await
                }
                // ─── Polis governance (starbridge-polis) ─────────────────────
                "council-status" => {
                    commands::polis::handle_council_status(&ctx, &command, &self.state).await
                }
                // ─── Name service commands ──────────────────────────────────
                "name-register" => {
                    commands::names::handle_register(&ctx, &command, &self.state).await
                }
                "name-resolve" => {
                    commands::names::handle_resolve(&ctx, &command, &self.state).await
                }
                "name-whois" => commands::names::handle_whois(&ctx, &command, &self.state).await,
                // ─── Federation setup commands ──────────────────────────────
                "setup-federation" => {
                    commands::federation::handle_setup(&ctx, &command, &self.state).await
                }
                "link-cipherclerk" => {
                    commands::federation::handle_link(&ctx, &command, &self.state).await
                }
                "unlink-cipherclerk" => {
                    commands::federation::handle_unlink(&ctx, &command, &self.state).await
                }
                // ─── New reads + organ actions (wired this integration) ──────
                "federation-status" => {
                    commands::federation::handle_status(&ctx, &command, &self.state).await
                }
                "federation-peers" => {
                    commands::federation::handle_peers(&ctx, &command, &self.state).await
                }
                "council-approve" => {
                    commands::polis::handle_council_approve(&ctx, &command, &self.state).await
                }
                "activity" => commands::social::handle_activity(&ctx, &command, &self.state).await,
                "dashboard" => {
                    commands::dashboard::handle_dashboard(&ctx, &command, &self.state).await
                }
                "cap-peer" => commands::captp::handle_peer(&ctx, &command, &self.state).await,
                "handoff-status" => {
                    commands::handoff::handle_status(&ctx, &command, &self.state).await
                }
                // ─── Canonical CapTP handoff (§4.7) ─────────────────────────
                "handoff" => commands::handoff::handle(&ctx, &command, &self.state).await,
                "handoff-redeem" => {
                    commands::handoff::handle_redeem(&ctx, &command, &self.state).await
                }
                "intent" => commands::intent::handle(&ctx, &command, &self.state).await,
                "bounty" => commands::bounty::handle(&ctx, &command, &self.state).await,
                "deos" => commands::deos::handle(&ctx, &command, &self.state).await,
                "card" => commands::card::handle(&ctx, &command, &self.state).await,
                _ => {
                    tracing::warn!("Unknown command: {name}");
                }
            }
        } else if let Interaction::Component(component) = interaction {
            // Route component presses by custom-id prefix:
            //   `deosturn:<turn>:<arg>` — a ViewNode card affordance: fire it as a REAL
            //     cap-gated verified turn and re-render the card (the interactive loop);
            //   `deos:<hex8>:<affordance>` — a cap-gated deos-surface button: RE-RUN the
            //     cap gate in the deos handler;
            //   everything else is the dashboard's.
            let custom_id = &component.data.custom_id;
            if custom_id.starts_with("deosturn:") {
                viewnode_applet::handle_deosturn_component(&ctx, &component, &self.state).await;
            } else if custom_id.starts_with("deos:") {
                commands::deos::handle_component(&ctx, &component, &self.state).await;
            } else {
                commands::dashboard::handle_component(&ctx, &component, &self.state).await;
            }
        } else if let Interaction::Modal(modal) = interaction {
            commands::dashboard::handle_modal(&ctx, &modal, &self.state).await;
        }
    }

    async fn message(&self, _ctx: Context, msg: Message) {
        // Bridge messages to dregg queues if the channel is linked.
        self.state.event_bridge.on_message(&msg).await;
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
                    let expected = *blake3::hash(&pk).as_bytes();
                    if expected != federation_id_bytes {
                        warn!(
                            "FEDERATION_ID mismatch: this is a SOLO node whose executor signs \
                             under blake3(node_pubkey)={}, but the bot's FEDERATION_ID is {}. \
                             Transfers WILL fail with 'Ed25519 signature verification failed'. \
                             Set FEDERATION_ID={} to match.",
                            hex::encode(expected),
                            hex::encode(federation_id_bytes),
                            hex::encode(expected),
                        );
                    } else {
                        info!("FEDERATION_ID matches the solo node's executor signing domain");
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

    // Build shared state (now carries the real federation + HTTP config).
    let state = Arc::new(BotState {
        config,
        db,
        devnet,
        presence,
        captp,
        discord_caps,
        event_bridge,
        federation_id_bytes,
        nullifier_set: Mutex::new(Vec::new()), // §4.7 friend-clique soft-federation
        handoff_broker: Mutex::new(handoff_flow::HandoffBroker::new(dregg_captp::FederationId(
            federation_id_bytes,
        ))),
        card_applets: viewnode_applet::CardApplets::new(),
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

    // Build Discord client (GUILD_PRESENCES + GUILD_MESSAGES for message bridging).
    let intents = GatewayIntents::GUILD_PRESENCES
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
    use super::{REGISTERED_COMMAND_NAMES, ROUTED_COMMAND_NAMES};
    use std::collections::BTreeSet;

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
