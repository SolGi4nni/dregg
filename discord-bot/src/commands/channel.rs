//! `/channel` — claim your own semi-private DreggNet Cloud channel.
//!
//! The user gets a Discord channel gated to them + the admin
//! ([`crate::channels`]), bound to their custodial dregg cell, recorded in the
//! bot DB. Messages in that channel drive THEIR confined Hermes
//! ([`crate::hermes_channel`]). Idempotent: re-running returns the existing one.
//!
//! The permission-plan + DB record are unit-tested without Discord
//! ([`crate::channels`], [`crate::db`]); only the live `create_channel` call here
//! needs a token.

use serenity::all::{
    ChannelType, CommandInteraction, Context, CreateChannel, CreateCommand,
    CreateInteractionResponse, CreateInteractionResponseMessage, EditInteractionResponse, RoleId,
    UserId,
};

use crate::BotState;
use crate::channels;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;

/// Register `/channel`.
pub fn register() -> CreateCommand {
    CreateCommand::new("channel")
        .description("Claim your own semi-private channel to drive your Hermes (admin can monitor)")
}

/// Handle `/channel` — claim (or recover) the invoker's semi-private channel.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let Some(guild_id) = command.guild_id else {
        return reply_err(
            ctx,
            command,
            "Run In A Server",
            "`/channel` claims a server channel — run it in a DreggNet Cloud server, not a DM.",
        )
        .await;
    };

    let embed = execute_claim(ctx, guild_id, &command.user, state).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Claim (or recover) a user's semi-private channel — the real flow behind both
/// `/channel` and the `/start` "Claim my channel" button. Ensures the user has a
/// custodial cell, is idempotent (returns the existing channel), creates the
/// gated channel (the one live-Discord step), and records the binding so
/// messages there drive the owner's confined Hermes. Returns the embed to show.
pub(crate) async fn execute_claim(
    ctx: &Context,
    guild_id: serenity::all::GuildId,
    user: &serenity::all::User,
    state: &BotState,
) -> serenity::all::CreateEmbed {
    let discord_id = user.id.get();
    let discord_id_str = discord_id.to_string();
    let guild_str = guild_id.get().to_string();

    // Ensure the user has a custodial cell (derive + register on first claim).
    let cell_id = match ensure_cell(state, &discord_id_str, discord_id).await {
        Ok(cell_id) => cell_id,
        Err(msg) => return embeds::error_embed("Identity Error", &msg),
    };

    // Idempotent: if the user already owns an active channel here, return it.
    match state
        .db
        .get_user_channel_for_user(&discord_id_str, &guild_str)
        .await
    {
        Ok(Some(existing)) => {
            return embeds::dregg_embed("Your Channel")
                .description(format!(
                    "You already have a semi-private channel: <#{}>.\nJust type in it to drive your Hermes.",
                    existing.channel_id
                ))
                .field("Cell", format!("`{}`", short(&existing.cell_id)), true);
        }
        Ok(None) => {}
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    }

    // Build the semi-private permission plan (pure; tested offline).
    let everyone = RoleId::new(guild_id.get()); // @everyone role id == guild id
    let admin = state.config.admin_discord_id.map(UserId::new);
    let overwrites = channels::plan_private_overwrites(everyone, user.id, admin);

    // The only live-Discord step: create the gated channel.
    let name = channels::channel_name_for(discord_id);
    let builder = CreateChannel::new(name)
        .kind(ChannelType::Text)
        .topic(format!(
            "DreggNet Cloud — {}'s semi-private channel. Messages drive their confined Hermes (cap-gated, receipted). Admin-monitored.",
            user.name
        ))
        .permissions(overwrites);

    let channel = match guild_id.create_channel(&ctx.http, builder).await {
        Ok(channel) => channel,
        Err(e) => {
            return embeds::error_embed(
                "Channel Creation Failed",
                &format!(
                    "Could not create the channel ({e}). The bot needs MANAGE_CHANNELS in this server.",
                ),
            );
        }
    };

    // Record the binding (user → channel → cell).
    if let Err(e) = state
        .db
        .upsert_user_channel(
            &channel.id.get().to_string(),
            &discord_id_str,
            &guild_str,
            &cell_id,
            now_secs(),
        )
        .await
    {
        return embeds::error_embed("Database Error", &e.to_string());
    }

    embeds::success_embed("Channel Claimed")
        .description(format!(
            "Your semi-private channel is ready: <#{}>.\n\nJust type in it to drive your Hermes. Each message becomes a cap-gated, metered, receipted dregg turn under YOUR cell. Try `read <path>`, `search <query>`, `fetch <url>`, `run <cmd>`, `write <path>`, or just chat.",
            channel.id.get()
        ))
        .field("Cell", format!("`{}`", short(&cell_id)), true)
        .field("Visibility", "You + admin (semi-private)", true)
}

/// Ensure the invoker has a custodial cell, deriving + registering one on first
/// claim. Returns the cell-id hex.
async fn ensure_cell(state: &BotState, discord_id: &str, user_id: u64) -> Result<String, String> {
    if let Ok(Some(id)) = state.db.get_cell_id(discord_id).await {
        return Ok(id);
    }
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let cell_id = cclerk.cell_id_hex().to_string();
    // Best-effort devnet registration (the cell is valid locally regardless).
    let _ = state
        .devnet
        .register_cell(&cell_id, cclerk.public_key_hex())
        .await;
    state
        .db
        .register_user_with_mode(discord_id, &cell_id, IdentityMode::Hosted, None)
        .await
        .map_err(|e| e.to_string())?;
    Ok(cell_id)
}

fn short(s: &str) -> &str {
    &s[..s.len().min(16)]
}

fn now_secs() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
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

async fn reply_err(ctx: &Context, command: &CommandInteraction, title: &str, msg: &str) {
    let embed = embeds::error_embed(title, msg);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}
