//! Federation commands: `/setup-federation`, `/link-cipherclerk`,
//! `/unlink-cipherclerk`, `/federation-status`, `/federation-peers`.
//!
//! Links a Discord guild to a dregg reference group, binds user identities, and
//! reads the live federation surface (`/api/federations`) so Discord can see the
//! real reference-group committee/epoch/threshold and finalized roots — Discord
//! as a first-class peer of node/sdk.

use serde::Deserialize;
use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Live federation surface (`/api/federations`) ────────────────────────────

/// Mirror of the node's `FederationInfo` (`node/src/api.rs`). `default` on the
/// optional/newer fields keeps older node responses valid.
#[derive(Debug, Clone, Deserialize)]
struct FederationInfo {
    #[serde(default)]
    id: String,
    #[serde(default)]
    federation_id: String,
    #[serde(default)]
    committee_epoch: u64,
    #[serde(default)]
    threshold: u32,
    #[serde(default)]
    member_count: usize,
    #[serde(default)]
    members: Vec<String>,
    #[serde(default)]
    is_local: bool,
    #[serde(default)]
    latest_height: u64,
    #[serde(default)]
    latest_root: Option<String>,
    #[serde(default)]
    num_finalized_roots: usize,
}

/// Fetch the live federation list from the node's real `/api/federations` route.
async fn fetch_federations(state: &BotState) -> Result<Vec<FederationInfo>, String> {
    let url = format!(
        "{}/api/federations",
        state.config.devnet_url.trim_end_matches('/')
    );
    let resp = state.devnet.client().get(&url).send().await.map_err(|e| {
        if e.is_connect() || e.is_timeout() {
            "Couldn't reach the node. The devnet may be offline — check `/status`.".to_string()
        } else {
            format!("Network error reading the federation surface: {e}")
        }
    })?;
    if !resp.status().is_success() {
        return Err(format!(
            "Node returned HTTP {} reading `/api/federations`.",
            resp.status().as_u16()
        ));
    }
    resp.json::<Vec<FederationInfo>>()
        .await
        .map_err(|e| format!("Couldn't parse the federation response: {e}"))
}

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/setup-federation`.
pub fn register_setup() -> CreateCommand {
    CreateCommand::new("setup-federation")
        .description("Register this guild as a dregg reference group (federation)")
}

/// Register `/link-cipherclerk <dregg-address>`.
pub fn register_link() -> CreateCommand {
    CreateCommand::new("link-cipherclerk")
        .description("Link your Discord account to your dregg identity")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "address",
                "Your dregg cell address (hex)",
            )
            .required(true),
        )
}

/// Register `/unlink-cipherclerk`.
pub fn register_unlink() -> CreateCommand {
    CreateCommand::new("unlink-cipherclerk")
        .description("Unlink your Discord account from your dregg identity")
}

/// Register `/federation-status` — the live committee/epoch/threshold + roots.
pub fn register_status() -> CreateCommand {
    CreateCommand::new("federation-status")
        .description("Show the live federation: committee, epoch, threshold, finalized roots")
}

/// Register `/federation-peers` — the reference-group members (committee keys).
pub fn register_peers() -> CreateCommand {
    CreateCommand::new("federation-peers")
        .description("List the federation committee members (reference-group keys)")
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/setup-federation`.
pub async fn handle_setup(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "This command must be run in a server.",
            )
            .await;
            return;
        }
    };

    // Check that the user has admin permissions.
    let member = match &command.member {
        Some(m) => m,
        None => {
            respond_error(
                ctx,
                command,
                "Permission Denied",
                "Cannot determine your server permissions.",
            )
            .await;
            return;
        }
    };

    let has_admin = member
        .permissions
        .map(|p| p.administrator())
        .unwrap_or(false);

    if !has_admin {
        respond_error(
            ctx,
            command,
            "Permission Denied",
            "Only server administrators can set up federation.",
        )
        .await;
        return;
    }

    defer_ephemeral(ctx, command).await;

    let actor = command.user.id.get().to_string();
    let _ = state
        .db
        .record_starbridge_activity(
            "federation",
            "guild.configure",
            &actor,
            Some(&guild_id.to_string()),
            Some(&format!("/discord/{guild_id}/")),
            "accepted",
            serde_json::json!({
                "bot_cell": state.captp.bot_cell_id,
                "mode": "discord-local",
            }),
        )
        .await;

    let embed = embeds::success_embed("Federation Configured")
        .description(
            "This guild is configured as a Discord-local Starbridge namespace. The old `/federation/register-guild` node endpoint has been retired; route and app state now move through canonical Starbridge app actions.",
        )
        .field("Namespace", format!("`/discord/{guild_id}/`"), true)
        .field(
            "Bot Cell",
            format!(
                "`{}...`",
                &state.captp.bot_cell_id[..16.min(state.captp.bot_cell_id.len())]
            ),
            true,
        );
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Handle `/link-cipherclerk`.
pub async fn handle_link(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let address = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    let discord_id = command.user.id.get().to_string();

    // Validate the address format (should be hex, 64 chars = 32 bytes).
    if address.len() != 64 || hex::decode(&address).is_err() {
        let embed = embeds::error_embed(
            "Invalid Address",
            "Dregg cell address must be 64 hex characters (32 bytes).",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    // Check if already linked.
    match state.db.get_cell_id(&discord_id).await {
        Ok(Some(existing)) => {
            let embed = embeds::warning_embed(
                "Already Linked",
                &format!(
                    "Your account is already linked to `{}...`.\nUse `/unlink-cipherclerk` first to change it.",
                    &existing[..16.min(existing.len())]
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        _ => {}
    }

    let challenge = ownership_challenge(&discord_id, &address);

    // Store as pending only. A later verifier can promote this record after a
    // signature proof over the challenge; until then the bot will not sign for it.
    match state
        .db
        .create_pending_external_link(&discord_id, &address, &challenge)
        .await
    {
        Ok(()) => {
            let embed = embeds::success_embed("External Link Pending")
                .description(
                    "Your Discord account recorded this external identity. It activates when \
                     you prove ownership with `/link-prove` — until then the bot will not sign \
                     for it (and commands needing a signable identity treat it as pending; \
                     `/unlink-cipherclerk` backs out any time).",
                )
                .field("Cell ID", format!("`{}...`", &address[..16]), true)
                .field(
                    "Challenge (sign EXACTLY these bytes)",
                    format!("```\n{challenge}\n```"),
                    false,
                )
                .field(
                    "Next step",
                    crate::commands::link_proof::how_to_prove(),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Link Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/unlink-cipherclerk`.
pub async fn handle_unlink(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let discord_id = command.user.id.get().to_string();

    match state.db.get_cell_id(&discord_id).await {
        Ok(Some(_)) => match state.db.unlink_user(&discord_id).await {
            Ok(()) => {
                let embed = embeds::success_embed("Cipherclerk Unlinked").description(
                    "Your Discord account has been unlinked from your dregg identity.",
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
            }
            Err(e) => {
                let embed = embeds::error_embed("Unlink Failed", &e.to_string());
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
            }
        },
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Not Linked",
                "Your Discord account is not linked to any dregg identity.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/federation-status` — read the real `/api/federations` route.
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let feds = match fetch_federations(state).await {
        Ok(feds) => feds,
        Err(msg) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Federation Unavailable", &msg),
            )
            .await;
            return;
        }
    };

    if feds.is_empty() {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "No Federations",
                "The node reports no known reference groups yet.",
            ),
        )
        .await;
        return;
    }

    // Lead with the local federation (the one this guild's turns settle on),
    // falling back to the first if none is flagged local.
    let local = feds.iter().find(|f| f.is_local).unwrap_or(&feds[0]);
    let mut embed = embeds::dregg_embed("Federation Status")
        .field("Federation", short_hex(fed_id(local)), true)
        .field(
            "Scope",
            if local.is_local { "local" } else { "remote" },
            true,
        )
        .field("Epoch", local.committee_epoch.to_string(), true)
        .field(
            "Threshold",
            format!("{}-of-{}", local.threshold, local.member_count.max(1)),
            true,
        )
        .field("Members", local.member_count.to_string(), true)
        .field("Latest Height", local.latest_height.to_string(), true)
        .field(
            "Finalized Roots",
            local.num_finalized_roots.to_string(),
            true,
        )
        .field(
            "Latest Root",
            local
                .latest_root
                .as_deref()
                .map(short_hex)
                .unwrap_or_else(|| "—".to_string()),
            true,
        );

    if feds.len() > 1 {
        let others = feds
            .iter()
            .filter(|f| fed_id(f) != fed_id(local))
            .take(8)
            .map(|f| {
                format!(
                    "{} — epoch {}, {}-of-{}{}",
                    short_hex(fed_id(f)),
                    f.committee_epoch,
                    f.threshold,
                    f.member_count.max(1),
                    if f.is_local { " (local)" } else { "" }
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        embed = embed.field(format!("Known Federations ({})", feds.len()), others, false);
    }

    edit_embed(ctx, command, embed).await;
}

/// Handle `/federation-peers` — the live committee membership.
pub async fn handle_peers(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let feds = match fetch_federations(state).await {
        Ok(feds) => feds,
        Err(msg) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Federation Unavailable", &msg),
            )
            .await;
            return;
        }
    };

    let Some(local) = feds.iter().find(|f| f.is_local).or_else(|| feds.first()) else {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "No Federations",
                "The node reports no known reference groups.",
            ),
        )
        .await;
        return;
    };

    let members = if local.members.is_empty() {
        "_(node did not expose member keys)_".to_string()
    } else {
        local
            .members
            .iter()
            .enumerate()
            .take(20)
            .map(|(i, key)| format!("{}. `{}`", i + 1, short_hex(key)))
            .collect::<Vec<_>>()
            .join("\n")
    };

    let embed = embeds::dregg_embed("Federation Peers")
        .field("Federation", short_hex(fed_id(local)), true)
        .field("Epoch", local.committee_epoch.to_string(), true)
        .field(
            "Threshold",
            format!("{}-of-{}", local.threshold, local.member_count.max(1)),
            true,
        )
        .field("Committee", members, false);
    edit_embed(ctx, command, embed).await;
}

/// Prefer `federation_id`, fall back to `id` (the node sets both equal).
fn fed_id(info: &FederationInfo) -> &str {
    if info.federation_id.is_empty() {
        &info.id
    } else {
        &info.federation_id
    }
}

fn short_hex(hex: &str) -> String {
    let trimmed = hex.trim();
    if trimmed.len() <= 16 {
        format!("`{trimmed}`")
    } else {
        format!("`{}...`", &trimmed[..16])
    }
}

async fn edit_embed(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

fn ownership_challenge(discord_id: &str, address: &str) -> String {
    let input = format!("dregg-discord-link-v1:{discord_id}:{address}");
    format!(
        "dregg-discord-link-v1:{}",
        blake3::hash(input.as_bytes()).to_hex()
    )
}

// ─── Helpers ────────────────────────────────────────────────────────────────

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
