//! `/cipherclerk` command — create, balance, address, export, and the real
//! macaroon **token** keychain (mint / attenuate / tokens / authorize).
//!
//! The token subcommands drive the canonical `dregg_sdk::AgentCipherclerk`
//! macaroon machinery (`mint_token`, `attenuate`, `verify_token`, `tokens`)
//! on the user's REAL per-user cipherclerk — an owned `AgentCipherclerk`
//! re-derived from the same seed `UserCipherclerk::derive` uses
//! (`AgentCipherclerk::from_key_bytes`), so its keys / cell-id are exactly the
//! identity apps and the node derive. There is no parallel token
//! implementation: the same code path apps and the node use.
//!
//! Because the custodial bot re-derives each user's cipherclerk
//! deterministically per command (no per-user token persistence table is
//! available in the shared `db.rs`), tokens are minted with a
//! **deterministic** root key derived from the user seed plus the service
//! name. That makes `tokens` reconstructable statelessly: `mint` and `list`
//! re-materialize the exact same `HeldToken`s every time, while `attenuate`
//! and `authorize` exercise the live macaroon HMAC chain.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dregg_sdk::{AgentCipherclerk, Attenuation, AuthRequest, HeldToken};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;

/// The fixed set of macaroon services a custodial user may mint a root token
/// for. Keeping the list closed makes the deterministic root-key derivation
/// (and thus the stateless re-materialization of `tokens`) total and
/// auditable.
const MINTABLE_SERVICES: &[&str] = &["dns", "storage", "compute", "http", "secrets"];

/// Register the /cipherclerk command with all subcommands.
pub fn register() -> CreateCommand {
    CreateCommand::new("cipherclerk")
        .description(
            "Manage your dregg wallet: identity, keys, and tokens (a.k.a. the cipherclerk)",
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "create",
            "Create your dregg wallet (a real cell + keys)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "balance",
            "Check your wallet's on-network DEC balance",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "address",
            "Show your cell ID",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "export",
            "Show your private key (ephemeral)",
        ))
        // ─── macaroon token keychain (real AgentCipherclerk) ────────────────
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "mint",
                "Mint a root macaroon token for a service",
            )
            .add_sub_option({
                let mut opt = CreateCommandOption::new(
                    CommandOptionType::String,
                    "service",
                    "Service the token authorizes",
                )
                .required(true);
                for service in MINTABLE_SERVICES {
                    opt = opt.add_string_choice(*service, *service);
                }
                opt
            }),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "attenuate",
                "Narrow a held token (real macaroon attenuation)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "token-id",
                    "ID of the held token to attenuate (see /cipherclerk tokens)",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "action",
                    "Action mask to confine the service to (e.g. r, rw, read)",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Integer,
                    "ttl-seconds",
                    "Optional expiry: token invalid after now + ttl seconds",
                )
                .required(false)
                .min_int_value(1),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "tokens",
            "List the macaroon tokens held by your cipherclerk",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "authorize",
                "Check whether a held token authorizes a service+action",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "token-id",
                    "ID of the held token to test",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "service",
                    "Service being requested",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "action",
                    "Action being requested (e.g. read, write)",
                )
                .required(true),
            ),
        )
}

/// Handle /cipherclerk interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "create" => handle_create(ctx, command, state).await,
        "balance" => handle_balance(ctx, command, state).await,
        "address" => handle_address(ctx, command, state).await,
        "export" => handle_export(ctx, command, state).await,
        "mint" => handle_mint(ctx, command, state).await,
        "attenuate" => handle_attenuate(ctx, command, state).await,
        "tokens" => handle_tokens(ctx, command, state).await,
        "authorize" => handle_authorize(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_create(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let embed = execute_create(state, command.user.id.get()).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Create the invoker's custodial cell (the real turn behind both the
/// `/cipherclerk create` slash command and the `/start` "Create my wallet"
/// button): derive the per-user cipherclerk, register the cell on the devnet,
/// and record the hosted identity. Returns the embed to show.
pub(crate) async fn execute_create(state: &BotState, user_id: u64) -> serenity::all::CreateEmbed {
    let discord_id = user_id.to_string();

    match state.db.user_exists(&discord_id).await {
        Ok(true) => {
            return embeds::warning_embed(
                "Wallet Exists",
                "You already have a dregg wallet. Use `/start` → **Balance** to see it.",
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
        _ => {}
    }

    // Derive keys.
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let cell_id = cclerk.cell_id_hex().to_string();

    // Register on devnet.
    if let Err(e) = state
        .devnet
        .register_cell(&cell_id, cclerk.public_key_hex())
        .await
    {
        return embeds::error_embed(
            "Devnet Error",
            &format!("Failed to register cell on devnet: {e}"),
        );
    }

    // Store in database.
    if let Err(e) = state
        .db
        .register_user_with_mode(&discord_id, &cell_id, IdentityMode::Hosted, None)
        .await
    {
        return embeds::error_embed("Database Error", &e.to_string());
    }

    embeds::success_embed("Wallet Created")
        .description("Your dregg wallet is ready! Grab some test DEC, then just chat.")
        .field("Cell ID", format!("`{}`", cclerk.cell_id_short()), true)
        .field("Mode", "Hosted (custodial)", true)
}

async fn handle_balance(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let embed = execute_balance(state, command.user.id.get()).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Read the invoker's on-chain balance (the read behind `/cipherclerk balance`
/// and the `/start` "Balance" button). Returns the embed to show.
pub(crate) async fn execute_balance(state: &BotState, user_id: u64) -> serenity::all::CreateEmbed {
    let discord_id = user_id.to_string();
    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            return embeds::warning_embed(
                "No Wallet",
                "You don't have a wallet yet. Use `/start` → **Create my wallet** first.",
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    };

    match state.devnet.get_balance(&cell_id).await {
        Ok(balance) => embeds::dregg_embed("Your Wallet Balance (DEC)")
            .description(
                "**DEC** is the on-network devnet currency your wallet holds (top up with \
                 `/faucet`, spend with `/send`). Real-AI dungeon run-credits bought with \
                 **$DREGG** are a different balance — see `/credits`.",
            )
            .field("Balance", format!("{balance} DEC"), true)
            .field("Cell ID", format!("`{}...`", &cell_id[..16]), true),
        Err(e) => {
            // A 404 here means the cell hasn't been materialized on-chain yet
            // (no faucet/transfer has touched it); user_message surfaces the
            // "/faucet first" hint. Other codes get their own guidance.
            let title = match &e {
                crate::devnet::DevnetError::Status { code: 404, .. } => "No On-Chain Balance Yet",
                _ => "Balance Unavailable",
            };
            embeds::error_embed(title, &e.user_message("query your balance"))
        }
    }
}

async fn handle_address(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You don't have a wallet yet. Use `/start` → **Just create my wallet** (or `/cipherclerk create`).",
            );
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
    };

    let mut embed = embeds::dregg_embed("Your Cell Address").field(
        "Cell ID",
        format!("```\n{cell_id}\n```"),
        false,
    );
    // Explorer link only when DREGG_EXPLORER_BASE is configured — the full,
    // copyable Cell ID above is the always-works reference; never a dead link.
    if let Some(url) = crate::explorer_link::explorer_url("cell", &cell_id) {
        embed = embed.field("Explorer", format!("[View]({url})"), false);
    }

    respond_ephemeral(ctx, command, embed).await;
}

async fn handle_export(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let discord_id = user_id.to_string();

    match state.db.user_exists(&discord_id).await {
        Ok(true) => {}
        Ok(false) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You don't have a wallet yet. Use `/start` → **Just create my wallet** (or `/cipherclerk create`).",
            );
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            respond_ephemeral(ctx, command, embed).await;
            return;
        }
    }

    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);

    let embed = embeds::dregg_embed("Private Key Export")
        .description("**Keep this secret!** Anyone with this key controls your cell.")
        .field(
            "Private Key",
            format!("```\n{}\n```", cclerk.private_key_hex()),
            false,
        )
        .field("Cell ID", format!("`{}`", cclerk.cell_id_short()), true);

    respond_ephemeral(ctx, command, embed).await;
}

// ─── Macaroon token keychain (real AgentCipherclerk) ────────────────────────

/// Re-materialize the user's macaroon keychain into a fresh
/// [`AgentCipherclerk`] by re-minting every service the user "owns".
///
/// The bot has no per-user token persistence in the shared `db.rs`, so the
/// keychain is reconstructed deterministically: each service's root key is
/// `blake3(seed ‖ "macaroon-root" ‖ service)`. Minting is idempotent — the
/// same encoded `HeldToken` (same id `service:N`) re-appears every call — so
/// `tokens` / `attenuate` / `authorize` all see a stable keychain without any
/// stored state. Returns the live cipherclerk (with the root tokens present).
fn rematerialize_keychain(cclerk: &UserCipherclerk) -> AgentCipherclerk {
    // Build a fresh owned AgentCipherclerk from the user's seed — the SAME
    // canonical construction `UserCipherclerk::derive` uses
    // (`AgentCipherclerk::from_key_bytes`), so keys / cell-id match the
    // identity apps and the node derive. (AgentCipherclerk is intentionally
    // not Clone, so we re-derive rather than copy the shared handle.)
    let mut agent = fresh_agent(cclerk);
    for service in MINTABLE_SERVICES {
        let root_key = derive_root_key(cclerk, service);
        // mint_token pushes the HeldToken into the agent's keychain. The kid
        // counter starts at 0 for a fresh clone, so ids are stable as
        // `service:N` in MINTABLE_SERVICES order.
        let _ = agent.mint_token(&root_key, service);
    }
    agent
}

/// Build a fresh owned [`AgentCipherclerk`] for this user from the same seed
/// `UserCipherclerk::derive` uses. `AgentCipherclerk` is not `Clone`, so the
/// token handlers re-derive an owned, mutable agent to mint into.
fn fresh_agent(cclerk: &UserCipherclerk) -> AgentCipherclerk {
    use zeroize::Zeroizing;
    AgentCipherclerk::from_key_bytes(Zeroizing::new(*cclerk.legacy_secret()))
}

/// Deterministic per-(user, service) macaroon root key.
fn derive_root_key(cclerk: &UserCipherclerk, service: &str) -> [u8; 32] {
    let mut input = Vec::with_capacity(32 + 16 + service.len());
    input.extend_from_slice(cclerk.legacy_secret());
    input.extend_from_slice(b"macaroon-root");
    input.extend_from_slice(service.as_bytes());
    blake3::derive_key("dregg-discord-bot-macaroon-v1", &input)
}

/// Format a [`HeldToken`]'s capability flags for an embed line.
fn token_flags(token: &HeldToken) -> String {
    let mut flags = Vec::new();
    flags.push(if token.can_mint() {
        "root (can mint)".to_string()
    } else {
        "attenuated".to_string()
    });
    flags.push(if token.can_prove() {
        "can-prove".to_string()
    } else {
        "no-proof".to_string()
    });
    flags.push(if token.is_verified() {
        "verified".to_string()
    } else {
        "unverified".to_string()
    });
    flags.join(" · ")
}

async fn require_cclerk(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
) -> Option<UserCipherclerk> {
    let discord_id = command.user.id.get().to_string();
    match state.db.user_exists(&discord_id).await {
        Ok(true) => Some(UserCipherclerk::derive(
            &state.config.bot_secret,
            command.user.id.get(),
            state.federation_id_bytes,
        )),
        Ok(false) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cipherclerk to manage macaroon tokens. Use `/cipherclerk create` first.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            None
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            None
        }
    }
}

async fn handle_mint(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let Some(cclerk) = require_cclerk(ctx, command, state).await else {
        return;
    };

    let service = sub_string_opt(command, "service").unwrap_or_default();
    if !MINTABLE_SERVICES.contains(&service.as_str()) {
        let embed = embeds::error_embed(
            "Unknown Service",
            &format!(
                "`{service}` is not a mintable service. Choose one of: {}.",
                MINTABLE_SERVICES.join(", ")
            ),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    // Mint against the REAL AgentCipherclerk macaroon machinery.
    let root_key = derive_root_key(&cclerk, &service);
    let mut agent = fresh_agent(&cclerk);
    let held = agent.mint_token(&root_key, &service);

    let embed = embeds::success_embed("Macaroon Token Minted")
        .description(
            "Minted on your **real** cipherclerk via `AgentCipherclerk::mint_token`. The token id is deterministic, so `/cipherclerk tokens` always lists it.",
        )
        .field("Token ID", format!("`{}`", held.id()), true)
        .field("Service", held.service(), true)
        .field("Label", format!("`{}`", held.label()), true)
        .field("Capabilities", token_flags(&held), false);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_tokens(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let Some(cclerk) = require_cclerk(ctx, command, state).await else {
        return;
    };

    let agent = rematerialize_keychain(&cclerk);
    let tokens = agent.tokens();
    if tokens.is_empty() {
        let embed = embeds::dregg_embed("Macaroon Keychain")
            .description("No tokens held. Use `/cipherclerk mint service:<svc>` to mint one.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let mut description = String::new();
    for token in tokens {
        description.push_str(&format!(
            "`{}` — service **{}** — {}\n",
            token.id(),
            token.service(),
            token_flags(token),
        ));
    }
    let embed = embeds::dregg_embed("Macaroon Keychain")
        .description(description)
        .field("Held", tokens.len().to_string(), true)
        .field(
            "Source",
            "Real `AgentCipherclerk::tokens()` (deterministic root tokens)",
            true,
        );
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_attenuate(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let Some(cclerk) = require_cclerk(ctx, command, state).await else {
        return;
    };

    let token_id = sub_string_opt(command, "token-id").unwrap_or_default();
    let action = sub_string_opt(command, "action").unwrap_or_default();
    let ttl = sub_integer_opt(command, "ttl-seconds");

    let mut agent = rematerialize_keychain(&cclerk);
    let Some(parent) = agent.find_token_by_id(&token_id).cloned() else {
        let embed = embeds::error_embed(
            "Token Not Found",
            &format!("No held token `{token_id}`. Run `/cipherclerk tokens` to list ids."),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };

    // Real macaroon narrowing: confine the token to its own service with the
    // requested action mask, plus an optional expiry caveat.
    let not_after = ttl.map(|secs| now_unix() + secs.max(1));
    let restrictions = Attenuation {
        services: vec![(parent.service().to_string(), action.clone())],
        not_after,
        ..Default::default()
    };

    match agent.attenuate(&parent, &restrictions) {
        Ok(child) => {
            let mut embed = embeds::success_embed("Macaroon Token Attenuated")
                .description(
                    "Real `AgentCipherclerk::attenuate` — strictly narrows authority; the attenuated token drops the root forging key.",
                )
                .field("Parent", format!("`{}`", parent.id()), true)
                .field("New Token", format!("`{}`", child.id()), true)
                .field("Service", child.service(), true)
                .field("Confined Action", format!("`{action}`"), true)
                .field("Capabilities", token_flags(&child), false);
            if let Some(expiry) = not_after {
                embed = embed.field("Expires", format!("<t:{expiry}:R>"), true);
            }
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Attenuation Failed",
                &format!("Could not attenuate `{token_id}`: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_authorize(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let Some(cclerk) = require_cclerk(ctx, command, state).await else {
        return;
    };

    let token_id = sub_string_opt(command, "token-id").unwrap_or_default();
    let service = sub_string_opt(command, "service").unwrap_or_default();
    let action = sub_string_opt(command, "action").unwrap_or_default();

    let agent = rematerialize_keychain(&cclerk);
    let Some(token) = agent.find_token_by_id(&token_id) else {
        let embed = embeds::error_embed(
            "Token Not Found",
            &format!("No held token `{token_id}`. Run `/cipherclerk tokens` to list ids."),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };

    let auth_req = AuthRequest {
        service: Some(service.clone()),
        action: Some(action.clone()),
        ..Default::default()
    };
    // Real macaroon HMAC-chain verification.
    let authorized = agent.verify_token(token, &auth_req);

    let embed = if authorized {
        embeds::success_embed("Authorized")
            .description("`AgentCipherclerk::verify_token` accepted the request against the token's caveat chain.")
    } else {
        embeds::warning_embed(
            "Not Authorized",
            "The token's caveat chain does not satisfy this service+action request.",
        )
    }
    .field("Token", format!("`{token_id}`"), true)
    .field("Service", format!("`{service}`"), true)
    .field("Action", format!("`{action}`"), true)
    .field("Capabilities", token_flags(token), false);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

fn now_unix() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

/// Pull a String sub-option from the first (sub-command) option.
fn sub_string_opt(command: &CommandInteraction, name: &str) -> Option<String> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options[0].value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

/// Pull an Integer sub-option from the first (sub-command) option.
fn sub_integer_opt(command: &CommandInteraction, name: &str) -> Option<i64> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options[0].value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n),
            _ => None,
        })
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

async fn respond_ephemeral(
    ctx: &Context,
    command: &CommandInteraction,
    embed: serenity::all::CreateEmbed,
) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}
