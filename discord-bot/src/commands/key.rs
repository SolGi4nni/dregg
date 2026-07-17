//! `/key` — port in / rotate / revoke YOUR OWN LLM provider key.
//!
//! A user brings their own provider key (Anthropic / OpenAI / OpenRouter / Kimi
//! / DeepSeek). The key is sealed at rest under a per-user derived key
//! ([`crate::key_vault`]) and bounded by a metering policy (token budget + rate)
//! enforced through the dregg gateway ([`crate::hermes_channel`]). Every response
//! is EPHEMERAL — only the invoking user sees it — and NEVER echoes the key
//! (only a redacted fingerprint).
//!
//! Subcommands:
//! * `set` — open a private modal to store a key (provider / model / budget /
//!   rate) — the key NEVER travels as a visible slash option;
//! * `rotate` — open the same modal to replace the stored key (blank fields
//!   keep the existing provider + policy);
//! * `revoke` — delete the stored key (nothing recoverable afterward);
//! * `status` — show the configured provider / model / budget + a redacted
//!   fingerprint of the stored key.

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateInteractionResponse, CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::key_vault::{self, PlaintextKey};
use crate::llm_provider::Provider;

/// Register `/key`.
///
/// Neither `set` nor `rotate` takes the key as a slash option — a slash option
/// sits VISIBLE in the composer (and the client's command history). Both open
/// the same private modal the `/start` Key button uses
/// ([`crate::commands::start::key_modal`]).
pub fn register() -> CreateCommand {
    CreateCommand::new("key")
        .description("Port in your OWN LLM provider key (encrypted, metered, revocable)")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "set",
            "Open a private form to store an API key",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "rotate",
            "Open a private form to replace your stored key",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "revoke",
            "Delete your stored key",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show your configured provider / model / budget",
        ))
}

/// Route `/key <sub>`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sub = command
        .data
        .options
        .first()
        .map(|o| o.name.clone())
        .unwrap_or_default();
    match sub.as_str() {
        "set" => handle_set(ctx, command, state).await,
        "rotate" => handle_rotate(ctx, command, state).await,
        "revoke" => handle_revoke(ctx, command, state).await,
        "status" => handle_status(ctx, command, state).await,
        other => {
            reply_warn(
                ctx,
                command,
                "Unknown subcommand",
                &format!("`/key {other}` is not known."),
            )
            .await
        }
    }
}

/// `/key set` — open the shared private modal
/// ([`crate::commands::start::key_modal`]). The modal MUST be the interaction's
/// FIRST response, so no defer; the submission routes through
/// `start::handle_modal` (custom-id `start:modal:key`), the same sealing path.
async fn handle_set(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Modal(crate::commands::start::key_modal()),
        )
        .await;
}

/// `/key rotate` — open the SAME modal, after confirming there is a key to
/// rotate. Blank modal fields keep the stored provider / model / policy, so a
/// rotate is "paste the new key, submit".
async fn handle_rotate(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match state
        .db
        .get_llm_key(&command.user.id.get().to_string())
        .await
    {
        Ok(Some(_)) => {
            let _ = command
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Modal(crate::commands::start::key_modal()),
                )
                .await;
        }
        Ok(None) => {
            reply_warn(
                ctx,
                command,
                "No Key Set",
                "Use `/key set` first — there is nothing to rotate.",
            )
            .await
        }
        Err(e) => reply_warn(ctx, command, "Database Error", &e.to_string()).await,
    }
}

async fn handle_revoke(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let owner = command.user.id.get();
    match state.db.revoke_llm_key(&owner.to_string()).await {
        Ok(true) => {
            reset_session(state, owner);
            let embed = embeds::dregg_embed("Key Revoked").description(
                "Your stored key was deleted — the sealed ciphertext is gone and nothing is recoverable. Chat falls back to the built-in classifier until you `/key set` again.",
            );
            edit(ctx, command, embed).await;
        }
        Ok(false) => edit_warn(ctx, command, "No Key Set", "There was nothing to revoke.").await,
        Err(e) => edit_warn(ctx, command, "Database Error", &e.to_string()).await,
    }
}

async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let owner = command.user.id.get();
    match state.db.get_llm_key(&owner.to_string()).await {
        Ok(Some(rec)) => {
            let provider = Provider::parse(&rec.provider).unwrap_or(Provider::Anthropic);
            // Decrypt only to show the REDACTED fingerprint (never the key).
            let fingerprint =
                key_vault::EncryptedKey::from_b64(&rec.nonce_b64, &rec.ciphertext_b64)
                    .ok()
                    .and_then(|sealed| {
                        key_vault::open(&state.config.bot_secret, owner, provider.as_str(), &sealed)
                            .ok()
                    })
                    .map(|k| k.fingerprint())
                    .unwrap_or_else(|| "(stored — could not verify; re-set?)".to_string());
            let embed = embeds::dregg_embed("Your Key")
                .field("Provider", format!("`{}`", rec.provider), true)
                .field("Model", format!("`{}`", rec.model), true)
                .field("Key", format!("`{fingerprint}`"), true)
                .field("Token budget", rec.token_budget.to_string(), true)
                .field("Rate / window", rec.rate_limit.to_string(), true);
            edit(ctx, command, embed).await;
        }
        Ok(None) => {
            let embed = embeds::dregg_embed("No Key Set").description(
                "You haven't ported in a key. Use `/key set` to bring your own provider key — it's encrypted at rest and metered by dregg.",
            );
            edit(ctx, command, embed).await;
        }
        Err(e) => edit_warn(ctx, command, "Database Error", &e.to_string()).await,
    }
}

/// Seal the key and persist it. Returns the redacted fingerprint on success.
pub(crate) async fn store_key(
    state: &BotState,
    owner: u64,
    provider: Provider,
    model: &str,
    key: &PlaintextKey,
    budget: i64,
    rate: i64,
) -> Result<String, String> {
    let sealed = key_vault::seal(&state.config.bot_secret, owner, provider.as_str(), key)
        .map_err(|e| e.to_string())?;
    let now = now_secs();
    state
        .db
        .set_llm_key(
            &owner.to_string(),
            provider.as_str(),
            model,
            &sealed.nonce_b64(),
            &sealed.ciphertext_b64(),
            budget,
            rate,
            now,
        )
        .await
        .map_err(|e| e.to_string())?;
    Ok(key.fingerprint())
}

/// Drop the in-memory session so the new policy (or its absence) is applied on
/// the next message.
pub(crate) fn reset_session(state: &BotState, owner: u64) {
    let mut sessions = state
        .channel_hermes
        .lock()
        .unwrap_or_else(|p| p.into_inner());
    sessions.remove(&owner);
}

fn now_secs() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// ─── response helpers (ephemeral) ────────────────────────────────────────────

async fn defer(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}

async fn edit(ctx: &Context, command: &CommandInteraction, embed: serenity::all::CreateEmbed) {
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn edit_warn(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    edit(ctx, command, embeds::warning_embed(title, desc)).await;
}

async fn reply_warn(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embeds::warning_embed(title, desc))
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}
