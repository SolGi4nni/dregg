//! Programmable queue commands: `/queue-create`, `/queue-publish`,
//! `/queue-subscribe`, `/queue-status`, `/queue-mount`.
//!
//! Discord channels become programmable queues mounted in the dregg namespace at
//! `/discord/<guild-id>/<name>`. The mount/subscribe/ACL state is bot-local
//! (the bot's own SQLite), but a **publish** is a real, canonical Ed25519-signed
//! `dregg_turn` from the publisher's hosted cipherclerk: it emits an on-chain
//! `EmitEvent` carrying the message hash on a `queue.publish` topic, so every
//! published message produces a real receipt/turn hash visible in `/explorer`
//! and the node's `/api/events` feed.
//!
//! NOTE: there is no dedicated node-side queue *organ* API (`/api/queues/...`)
//! yet — the canonical home for queue depth/ordering would be a programmable
//! queue cell. Until that organ lands, "occupancy" is the count of on-chain
//! publish events the node has retained for this queue's namespace, and the
//! local mount registry carries ACL/rate-limit/subscriber metadata. The dedicated
//! queue-cell organ is a reported follow-up (see the swarm report / HORIZONLOG).

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dregg_app_framework::{Effect, Event, field_from_bytes, symbol};
// `CellId` is obtained via `cclerk.app.cell_id()`; no direct constructor needed.

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/queue-create <name> [acl role] [rate-limit N] [deposit min]`.
pub fn register_create() -> CreateCommand {
    CreateCommand::new("queue-create")
        .description("Create a programmable queue mounted in the guild namespace")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::Role,
            "acl",
            "Required role to publish (optional)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::Integer,
            "rate-limit",
            "Max messages per minute (optional)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::Integer,
            "deposit",
            "Minimum deposit per message in computrons (optional)",
        ))
}

/// Register `/queue-publish <name> <message>`.
pub fn register_publish() -> CreateCommand {
    CreateCommand::new("queue-publish")
        .description("Publish a message to a programmable queue (a real signed on-chain event)")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "message", "Message to publish")
                .required(true),
        )
}

/// Register `/queue-subscribe <name>`.
pub fn register_subscribe() -> CreateCommand {
    CreateCommand::new("queue-subscribe")
        .description("Subscribe to a queue (receive DMs on new messages)")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
}

/// Register `/queue-status <name>`.
pub fn register_status() -> CreateCommand {
    CreateCommand::new("queue-status")
        .description("Show queue stats: published events, subscribers, ACL, deposits")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Queue name")
                .required(true),
        )
}

/// Register `/queue-mount <name> <dregg-uri>`.
pub fn register_mount() -> CreateCommand {
    CreateCommand::new("queue-mount")
        .description("Mount an external dregg queue in this guild")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Local mount name")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "uri",
                "dregg:// URI of the external queue",
            )
            .required(true),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/queue-create` — register a bot-local queue mount in the guild
/// namespace. Mutating, so it requires a hosted cipherclerk (cap-gating).
pub async fn handle_create(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let acl_role = command
        .data
        .options
        .iter()
        .find(|o| o.name == "acl")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Role(r) => Some(r.get()),
            _ => None,
        });
    let rate_limit = get_integer_option(&command.data.options, "rate-limit");
    let deposit = get_integer_option(&command.data.options, "deposit");

    let Some(guild_id) = require_guild(ctx, command).await else {
        return;
    };
    if name.trim().is_empty() {
        respond_warning(
            ctx,
            command,
            "Missing Name",
            "A queue needs a non-empty name.",
        )
        .await;
        return;
    }

    defer_ephemeral(ctx, command).await;

    // Cap-gate: only a hosted identity (one the bot can sign for) may own a queue.
    if require_hosted(ctx, command, state).await.is_none() {
        return;
    }

    let namespace_path = format!("/discord/{guild_id}/{name}");
    if let Ok(Some(_)) = state.db.get_starbridge_queue(&namespace_path).await {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "Queue Exists",
                &format!("A queue is already mounted at `{namespace_path}`."),
            ),
        )
        .await;
        return;
    }

    // Deterministic queue id from the namespace path (no phantom node call).
    let queue_id = namespace_queue_id(&namespace_path);
    let acl_role_str = acl_role.map(|role| role.to_string());
    let actor = command.user.id.get().to_string();

    if let Err(e) = state
        .db
        .upsert_starbridge_queue(
            &namespace_path,
            &guild_id.to_string(),
            &name,
            &queue_id,
            &actor,
            acl_role_str.as_deref(),
            rate_limit,
            deposit,
        )
        .await
    {
        edit_embed(
            ctx,
            command,
            embeds::error_embed("Queue State Error", &e.to_string()),
        )
        .await;
        return;
    }
    let _ = state
        .db
        .record_starbridge_activity(
            "subscription",
            "queue.create",
            &actor,
            Some(&guild_id.to_string()),
            Some(&namespace_path),
            "accepted",
            serde_json::json!({ "queue_id": queue_id }),
        )
        .await;

    let embed = embeds::success_embed("Queue Created")
        .field("Name", &name, true)
        .field("Path", format!("`{namespace_path}`"), true)
        .field("Queue ID", short_queue(&queue_id), true)
        .field(
            "ACL Role",
            acl_role.map_or("anyone".to_string(), |r| format!("<@&{r}>")),
            true,
        )
        .field(
            "Rate Limit",
            rate_limit.map_or("none".to_string(), |r| format!("{r}/min")),
            true,
        )
        .field(
            "Min Deposit",
            deposit.map_or("none".to_string(), |d| format!("{d} computrons")),
            true,
        )
        .field(
            "Publish",
            "Each `/queue-publish` emits a real signed on-chain event from your hosted cipherclerk.",
            false,
        );
    edit_embed(ctx, command, embed).await;
}

/// Handle `/queue-publish` — emit a real, signed on-chain `EmitEvent` carrying
/// the message hash on the `queue.publish` topic.
pub async fn handle_publish(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let message = get_string_option(&command.data.options, "message").unwrap_or_default();

    let Some(guild_id) = require_guild(ctx, command).await else {
        return;
    };

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let queue = match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(queue)) => queue,
        Ok(None) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed(
                    "Queue Not Found",
                    &format!(
                        "No queue is mounted at `{namespace_path}`. Run `/queue-create` first."
                    ),
                ),
            )
            .await;
            return;
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Queue State Error", &e.to_string()),
            )
            .await;
            return;
        }
    };

    // ACL gate: if the queue has a required role, the publisher must hold it.
    if let Some(role_str) = queue.acl_role.as_deref() {
        if let Ok(role_id) = role_str.parse::<u64>() {
            if !publisher_has_role(ctx, command, role_id).await {
                edit_embed(
                    ctx,
                    command,
                    embeds::warning_embed(
                        "ACL Denied",
                        &format!("Publishing to **{name}** requires the <@&{role_id}> role."),
                    ),
                )
                .await;
                return;
            }
        }
    }

    // Cap-gate: a publish is a signed turn, so it needs a hosted cipherclerk.
    let Some(cclerk) = require_hosted(ctx, command, state).await else {
        return;
    };

    // Build a real canonical action: EmitEvent on the publisher's own cell,
    // topic "queue.publish", carrying the queue-id hash + message hash as fields.
    let publisher_cell = cclerk.app.cell_id();
    let queue_field = field_from_bytes(namespace_path.as_bytes());
    let message_field = field_from_bytes(message.as_bytes());
    let event = Event::new(symbol("queue.publish"), vec![queue_field, message_field]);
    let action = cclerk.app.make_action(
        publisher_cell,
        "queue_publish",
        vec![Effect::EmitEvent {
            cell: publisher_cell,
            event,
        }],
    );

    let embed = match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:queue:publish:{namespace_path}")),
        )
        .await
    {
        Ok(r) if r.accepted => {
            let actor = command.user.id.get().to_string();
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.publish",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({
                        "queue_id": queue.queue_id,
                        "message_hash": message_hash_hex(&message),
                        "turn_hash": r.turn_hash.clone(),
                    }),
                )
                .await;
            embeds::success_embed("Published")
                .field("Queue", &name, true)
                .field("Publisher", short_queue(cclerk.cell_id_hex()), true)
                .field("Turn", turn_field(r.turn_hash), false)
                .field("Message", format!("`{}`", truncate(&message, 100)), false)
        }
        Ok(r) => embeds::error_embed(
            "Publish Rejected",
            r.error
                .as_deref()
                .unwrap_or("the node rejected the signed publish"),
        ),
        Err(e) => embeds::error_embed("Publish Failed", &e.user_message("publish to the queue")),
    };
    edit_embed(ctx, command, embed).await;
}

/// Handle `/queue-subscribe` — bot-local subscription (DM fan-out).
pub async fn handle_subscribe(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

    let Some(guild_id) = require_guild(ctx, command).await else {
        return;
    };

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(_)) => {}
        Ok(None) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed(
                    "Queue Not Found",
                    &format!(
                        "No queue is mounted at `{namespace_path}`. Run `/queue-create` first."
                    ),
                ),
            )
            .await;
            return;
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Queue State Error", &e.to_string()),
            )
            .await;
            return;
        }
    }

    let discord_id = command.user.id.get().to_string();
    match state
        .db
        .subscribe_starbridge_queue(&namespace_path, &discord_id)
        .await
    {
        Ok(inserted) => {
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.subscribe",
                    &discord_id,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    if inserted { "accepted" } else { "unchanged" },
                    serde_json::json!({}),
                )
                .await;
            let embed = embeds::success_embed(if inserted {
                "Subscribed"
            } else {
                "Already Subscribed"
            })
            .description(format!(
                "You will receive DMs when new messages arrive in **{name}**."
            ))
            .field("Queue", &name, true)
            .field("Path", format!("`{namespace_path}`"), true);
            edit_embed(ctx, command, embed).await;
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Subscribe Failed", &e.to_string()),
            )
            .await;
        }
    }
}

/// Handle `/queue-status` — DB-backed mount metadata + real on-chain publish
/// events the node has retained for this namespace.
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

    let Some(guild_id) = require_guild(ctx, command).await else {
        return;
    };

    defer_ephemeral(ctx, command).await;

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let queue = match state.db.get_starbridge_queue(&namespace_path).await {
        Ok(Some(queue)) => queue,
        Ok(None) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed(
                    "Queue Not Found",
                    &format!("No queue is mounted at `{namespace_path}`."),
                ),
            )
            .await;
            return;
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Queue State Error", &e.to_string()),
            )
            .await;
            return;
        }
    };

    let subscribers = state
        .db
        .count_starbridge_queue_subscribers(&namespace_path)
        .await
        .unwrap_or(0);

    // Bot-local activity ledger is the authoritative publish count (each publish
    // is recorded with its real turn hash); on-chain events corroborate it.
    let activities = state
        .db
        .get_recent_starbridge_activity_for_app("subscription", 200)
        .await
        .unwrap_or_default();
    let published = activities
        .iter()
        .filter(|a| {
            a.action == "queue.publish" && a.subject.as_deref() == Some(namespace_path.as_str())
        })
        .count();
    let recent_turns = activities
        .iter()
        .filter(|a| {
            a.action == "queue.publish" && a.subject.as_deref() == Some(namespace_path.as_str())
        })
        .filter_map(|a| {
            serde_json::from_str::<serde_json::Value>(&a.details_json)
                .ok()
                .and_then(|v| v.get("turn_hash").and_then(|h| h.as_str()).map(short_queue))
        })
        .take(5)
        .collect::<Vec<_>>();

    let mut embed = embeds::dregg_embed("Queue Status")
        .field("Name", &name, true)
        .field("Published", published.to_string(), true)
        .field("Subscribers", subscribers.to_string(), true)
        .field(
            "ACL Role",
            queue
                .acl_role
                .as_deref()
                .and_then(|r| r.parse::<u64>().ok())
                .map_or("anyone".to_string(), |r| format!("<@&{r}>")),
            true,
        )
        .field(
            "Rate Limit",
            queue
                .rate_limit
                .map_or("none".to_string(), |r| format!("{r}/min")),
            true,
        )
        .field("Queue ID", short_queue(&queue.queue_id), true)
        .field("Path", format!("`{namespace_path}`"), false);
    if !recent_turns.is_empty() {
        embed = embed.field("Recent Publish Turns", recent_turns.join("\n"), false);
    }
    edit_embed(ctx, command, embed).await;
}

/// Handle `/queue-mount` — register an external dregg queue locally.
pub async fn handle_mount(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let uri = get_string_option(&command.data.options, "uri").unwrap_or_default();

    let Some(guild_id) = require_guild(ctx, command).await else {
        return;
    };

    defer_ephemeral(ctx, command).await;

    // Cap-gate the mount: only a hosted identity may bind external state locally.
    if require_hosted(ctx, command, state).await.is_none() {
        return;
    }

    let namespace_path = format!("/discord/{guild_id}/{name}");
    let Some(queue_id) = queue_id_from_uri(&uri) else {
        edit_embed(
            ctx,
            command,
            embeds::error_embed(
                "Invalid Queue URI",
                "Mount expects a URI ending in a 64-character hex queue id.",
            ),
        )
        .await;
        return;
    };
    let actor = command.user.id.get().to_string();

    match state
        .db
        .upsert_starbridge_queue(
            &namespace_path,
            &guild_id.to_string(),
            &name,
            &queue_id,
            &actor,
            None,
            None,
            None,
        )
        .await
    {
        Ok(()) => {
            let _ = state
                .db
                .record_starbridge_activity(
                    "subscription",
                    "queue.mount",
                    &actor,
                    Some(&guild_id.to_string()),
                    Some(&namespace_path),
                    "accepted",
                    serde_json::json!({ "queue_id": queue_id, "uri": uri }),
                )
                .await;
            let embed = embeds::success_embed("Queue Mounted")
                .description("External dregg queue is now accessible in this guild.")
                .field("Local Name", &name, true)
                .field("Path", format!("`{namespace_path}`"), true)
                .field("Queue ID", short_queue(&queue_id), true)
                .field("External URI", format!("`{}`", truncate(&uri, 60)), false);
            edit_embed(ctx, command, embed).await;
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Mount Failed", &e.to_string()),
            )
            .await;
        }
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn get_string_option(options: &[serenity::all::CommandDataOption], name: &str) -> Option<String> {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn get_integer_option(options: &[serenity::all::CommandDataOption], name: &str) -> Option<i64> {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n),
            _ => None,
        })
}

fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() > max {
        format!("{}...", s.chars().take(max).collect::<String>())
    } else {
        s.to_string()
    }
}

fn message_hash_hex(message: &str) -> String {
    hex::encode(blake3::hash(message.as_bytes()).as_bytes())
}

/// Deterministic, content-addressed queue id for a namespace path.
fn namespace_queue_id(namespace_path: &str) -> String {
    hex::encode(blake3::hash(namespace_path.as_bytes()).as_bytes())
}

fn short_queue(queue_id: &str) -> String {
    format!("`{}...`", &queue_id[..16.min(queue_id.len())])
}

fn turn_field(turn_hash: Option<String>) -> String {
    turn_hash
        .map(|h| format!("`{h}`"))
        .unwrap_or_else(|| "`unknown`".to_string())
}

fn queue_id_from_uri(uri: &str) -> Option<String> {
    let candidate = uri
        .trim_end_matches('/')
        .rsplit(['/', ':'])
        .next()
        .unwrap_or_default();
    if candidate.len() == 64 && candidate.chars().all(|ch| ch.is_ascii_hexdigit()) {
        Some(candidate.to_ascii_lowercase())
    } else {
        None
    }
}

/// Require a guild context, responding with an error if missing. Returns the
/// guild id on success.
async fn require_guild(ctx: &Context, command: &CommandInteraction) -> Option<u64> {
    match command.guild_id {
        Some(id) => Some(id.get()),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "This command must be run in a server.",
            )
            .await;
            None
        }
    }
}

/// Require the invoking user to have a hosted cipherclerk (mutating queue
/// actions must be signed by a `/cipherclerk create` identity).
async fn require_hosted(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
) -> Option<UserCipherclerk> {
    match state
        .db
        .get_user_identity(&command.user.id.get().to_string())
        .await
    {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => {
            Some(UserCipherclerk::derive(
                &state.config.bot_secret,
                command.user.id.get(),
                state.federation_id_bytes,
            ))
        }
        Ok(Some(_)) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed(
                    "Hosted Identity Required",
                    "Queue actions must be signed by a hosted `/cipherclerk create` identity.",
                ),
            )
            .await;
            None
        }
        Ok(None) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed(
                    "No Cipherclerk",
                    "Create a hosted cipherclerk with `/cipherclerk create` before using queues.",
                ),
            )
            .await;
            None
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Database Error", &e.to_string()),
            )
            .await;
            None
        }
    }
}

/// Does the invoking member hold the given role? Used for queue ACL gating.
async fn publisher_has_role(ctx: &Context, command: &CommandInteraction, role_id: u64) -> bool {
    // Member roles from the interaction; fall back to a live fetch if absent.
    if let Some(member) = &command.member {
        if member.roles.iter().any(|r| r.get() == role_id) {
            return true;
        }
    }
    if let (Some(guild_id), user_id) = (command.guild_id, command.user.id) {
        if let Ok(member) = guild_id.member(&ctx.http, user_id).await {
            return member.roles.iter().any(|r| r.get() == role_id);
        }
    }
    false
}

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}

async fn respond_error(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let embed = embeds::error_embed(title, desc);
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn respond_warning(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let embed = embeds::warning_embed(title, desc);
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn edit_embed(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}
