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
//! * `set` — store a key for a provider (with optional model / budget / rate);
//! * `rotate` — replace the stored key (keeps the existing provider + policy);
//! * `revoke` — delete the stored key (nothing recoverable afterward);
//! * `status` — show the configured provider / model / budget + a redacted
//!   fingerprint of the stored key.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::key_vault::{self, PlaintextKey};
use crate::llm_provider::Provider;

const DEFAULT_TOKEN_BUDGET: i64 = 200_000;
const DEFAULT_RATE_LIMIT: i64 = 100;

/// Register `/key`.
pub fn register() -> CreateCommand {
    let provider_opt = || {
        let mut opt = CreateCommandOption::new(
            CommandOptionType::String,
            "provider",
            "Which provider this key is for",
        )
        .required(true);
        for p in Provider::ALL {
            opt = opt.add_string_choice(p.display_name(), p.as_str());
        }
        opt
    };

    CreateCommand::new("key")
        .description("Port in your OWN LLM provider key (encrypted, metered, revocable)")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "set",
                "Store an API key for a provider",
            )
            .add_sub_option(provider_opt())
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::String, "key", "Your provider API key")
                    .required(true),
            )
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::String,
                "model",
                "Model to use (optional; provider default otherwise)",
            ))
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Integer,
                    "budget",
                    "Token budget for the session window (optional)",
                )
                .min_int_value(1),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Integer,
                    "rate",
                    "Max LLM calls per window (optional)",
                )
                .min_int_value(1),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "rotate",
                "Replace your stored key (keeps provider + policy)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "key",
                    "Your NEW provider API key",
                )
                .required(true),
            ),
        )
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

async fn handle_set(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let owner = command.user.id.get();

    let provider = match sub_string(command, "provider")
        .as_deref()
        .and_then(Provider::parse)
    {
        Some(p) => p,
        None => {
            return edit_warn(
                ctx,
                command,
                "Unknown Provider",
                "Pick one of the listed providers.",
            )
            .await;
        }
    };
    let key = PlaintextKey::new(sub_string(command, "key").unwrap_or_default());
    if key.is_empty() {
        return edit_warn(ctx, command, "Empty Key", "The key must not be empty.").await;
    }
    let model = sub_string(command, "model")
        .filter(|m| !m.trim().is_empty())
        .unwrap_or_else(|| provider.default_model().to_string());
    let budget = sub_integer(command, "budget")
        .unwrap_or(DEFAULT_TOKEN_BUDGET)
        .max(1);
    let rate = sub_integer(command, "rate")
        .unwrap_or(DEFAULT_RATE_LIMIT)
        .max(1);

    match store_key(state, owner, provider, &model, &key, budget, rate).await {
        Ok(fingerprint) => {
            reset_session(state, owner);
            let embed = embeds::dregg_embed("Key Stored")
                .description(format!(
                    "Your **{}** key is sealed (encrypted at rest, never logged).",
                    provider.display_name()
                ))
                .field("Provider", format!("`{}`", provider.as_str()), true)
                .field("Model", format!("`{model}`"), true)
                .field("Key", format!("`{fingerprint}`"), true)
                .field("Token budget", budget.to_string(), true)
                .field("Rate / window", rate.to_string(), true)
                .field(
                    "Use it",
                    "Just chat in this channel — conversational messages are routed through your keyed LLM, metered + receipted.",
                    false,
                );
            edit(ctx, command, embed).await;
        }
        Err(msg) => edit_warn(ctx, command, "Could Not Store Key", &msg).await,
    }
}

async fn handle_rotate(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let owner = command.user.id.get();

    let existing = match state.db.get_llm_key(&owner.to_string()).await {
        Ok(Some(r)) => r,
        Ok(None) => {
            return edit_warn(
                ctx,
                command,
                "No Key Set",
                "Use `/key set` first — there is nothing to rotate.",
            )
            .await;
        }
        Err(e) => return edit_warn(ctx, command, "Database Error", &e.to_string()).await,
    };
    let provider = Provider::parse(&existing.provider).unwrap_or(Provider::Anthropic);
    let key = PlaintextKey::new(sub_string(command, "key").unwrap_or_default());
    if key.is_empty() {
        return edit_warn(ctx, command, "Empty Key", "The new key must not be empty.").await;
    }

    match store_key(
        state,
        owner,
        provider,
        &existing.model,
        &key,
        existing.token_budget,
        existing.rate_limit,
    )
    .await
    {
        Ok(fingerprint) => {
            reset_session(state, owner);
            let embed = embeds::dregg_embed("Key Rotated")
                .description(format!(
                    "Your **{}** key was replaced. The old ciphertext is gone.",
                    provider.display_name()
                ))
                .field("Key", format!("`{fingerprint}`"), true);
            edit(ctx, command, embed).await;
        }
        Err(msg) => edit_warn(ctx, command, "Could Not Rotate Key", &msg).await,
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
async fn store_key(
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
fn reset_session(state: &BotState, owner: u64) {
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

// ─── option + response helpers (ephemeral) ──────────────────────────────────

fn sub_string(command: &CommandInteraction, name: &str) -> Option<String> {
    let sub = command.data.options.first()?;
    let CommandDataOptionValue::SubCommand(opts) = &sub.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn sub_integer(command: &CommandInteraction, name: &str) -> Option<i64> {
    let sub = command.data.options.first()?;
    let CommandDataOptionValue::SubCommand(opts) = &sub.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(i) => Some(*i),
            _ => None,
        })
}

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
