//! Bounty board commands: `/bounty post | claim | submit | payout | status`.
//!
//! Drives the `starbridge-bounty-board` app (`starbridge-apps/bounty-board`)
//! against the live node. Each write is a canonical Ed25519-signed `Action`
//! built by the app's own turn-builders (`build_post_action`,
//! `build_claim_action`, `build_submit_action`, `build_payout_action`) and
//! submitted through `DevnetClient::submit_app_actions` — the same signed-turn
//! path the nameservice and governance commands use. The bot signs as the
//! invoking user's hosted cipherclerk.
//!
//! The bounty *cell* is supplied by the caller (a factory-born sovereign cell;
//! the Starbridge seed / `/dregg` dashboard births these). Lifecycle state is
//! enforced on-chain by the bounty cell's `CellProgram` — `STATE` is strictly
//! monotone OPEN→CLAIMED→SUBMITTED→PAID, so a double-claim or double-payout is
//! rejected by the executor, not by the bot.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dregg_app_framework::CellId;
use starbridge_bounty_board::{
    build_claim_action, build_payout_action, build_post_action, build_submit_action,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::devnet::DevnetError;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register the `/bounty` command with its five subcommands.
pub fn register() -> CreateCommand {
    let bounty_cell = |required: bool| {
        CreateCommandOption::new(
            CommandOptionType::String,
            "bounty-cell",
            "Bounty cell ID (64 hex chars)",
        )
        .required(required)
    };

    CreateCommand::new("bounty")
        .description("Post, claim, submit, and pay out bounties on the live node")
        .add_option(
            CreateCommandOption::new(CommandOptionType::SubCommand, "post", "Post a new bounty")
                .add_sub_option(bounty_cell(true))
                .add_sub_option(
                    CreateCommandOption::new(
                        CommandOptionType::String,
                        "title",
                        "Bounty title (hashed into the cell)",
                    )
                    .required(true),
                )
                .add_sub_option(
                    CreateCommandOption::new(
                        CommandOptionType::Integer,
                        "reward",
                        "Reward amount (computrons)",
                    )
                    .required(true),
                ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "claim",
                "Claim an open bounty (first-claimer-wins)",
            )
            .add_sub_option(bounty_cell(true)),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "submit",
                "Submit work for a claimed bounty",
            )
            .add_sub_option(bounty_cell(true))
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "artifact-uri",
                    "URI of the submitted work (hashed into the cell)",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "payout",
                "Pay out a submitted bounty (terminal)",
            )
            .add_sub_option(bounty_cell(true)),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "status",
                "Show a bounty cell's on-chain status",
            )
            .add_sub_option(bounty_cell(true)),
        )
}

// ─── Dispatch ─────────────────────────────────────────────────────────────--

/// Route `/bounty <sub>` to its handler.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sub = command
        .data
        .options
        .first()
        .map(|o| o.name.clone())
        .unwrap_or_default();
    match sub.as_str() {
        "post" => handle_post(ctx, command, state).await,
        "claim" => handle_claim(ctx, command, state).await,
        "submit" => handle_submit(ctx, command, state).await,
        "payout" => handle_payout(ctx, command, state).await,
        "status" => handle_status(ctx, command, state).await,
        other => {
            respond_warning(
                ctx,
                command,
                "Unknown subcommand",
                &format!("`/bounty {other}` is not a known subcommand."),
            )
            .await
        }
    }
}

// ─── Handlers ─────────────────────────────────────────────────────────────--

async fn handle_post(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let cell = match resolve_cell(ctx, command).await {
        Some(c) => c,
        None => return,
    };
    let title = sub_string(command, "title").unwrap_or_default();
    let reward = match sub_integer(command, "reward") {
        Some(v) if v >= 0 => v as u64,
        _ => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed("Invalid Reward", "Reward must be a non-negative integer."),
            )
            .await;
            return;
        }
    };
    if title.trim().is_empty() {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed("Missing Title", "A bounty needs a non-empty title."),
        )
        .await;
        return;
    }

    let Some(cclerk) = require_hosted(ctx, command, state).await else {
        return;
    };
    let action = build_post_action(&cclerk.app, cell.cell, &title, reward);
    let embed = match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:bounty:post:{}", cell.hex)),
        )
        .await
    {
        Ok(r) if r.accepted => {
            record(state, command, "post", &cell.hex, "accepted").await;
            with_receipt(
                embeds::success_embed("Bounty Posted")
                    .field("Title", title.clone(), true)
                    .field("Reward", format!("{reward} DEC"), true)
                    .field("Bounty", short_cell(&cell.hex), true)
                    .field("Turn", turn_field(r.turn_hash.clone()), false),
                state,
                r.turn_hash,
            )
        }
        Ok(r) => rejected("Post Rejected", r.error),
        Err(e) => embeds::error_embed("Post Failed", &e.user_message("post the bounty")),
    };
    edit_embed(ctx, command, embed).await;
}

async fn handle_claim(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let cell = match resolve_cell(ctx, command).await {
        Some(c) => c,
        None => return,
    };
    let Some(cclerk) = require_hosted(ctx, command, state).await else {
        return;
    };
    // The claimant identity is the invoking user's cell — bound write-once on
    // chain (first-claimer-wins).
    let claimant = cclerk.cell_id_hex().to_string();
    let action = build_claim_action(&cclerk.app, cell.cell, &claimant);
    let embed = match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:bounty:claim:{}", cell.hex)),
        )
        .await
    {
        Ok(r) if r.accepted => {
            record(state, command, "claim", &cell.hex, "accepted").await;
            with_receipt(
                embeds::success_embed("Bounty Claimed")
                    .field("Bounty", short_cell(&cell.hex), true)
                    .field("Claimant", short_cell(&claimant), true)
                    .field("Turn", turn_field(r.turn_hash.clone()), false),
                state,
                r.turn_hash,
            )
        }
        Ok(r) => rejected("Claim Rejected", r.error),
        Err(e) => embeds::error_embed("Claim Failed", &e.user_message("claim the bounty")),
    };
    edit_embed(ctx, command, embed).await;
}

async fn handle_submit(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let cell = match resolve_cell(ctx, command).await {
        Some(c) => c,
        None => return,
    };
    let artifact = sub_string(command, "artifact-uri").unwrap_or_default();
    if artifact.trim().is_empty() {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "Missing Artifact",
                "Provide the URI of your submitted work.",
            ),
        )
        .await;
        return;
    }
    let Some(cclerk) = require_hosted(ctx, command, state).await else {
        return;
    };
    let action = build_submit_action(&cclerk.app, cell.cell, &artifact);
    let embed = match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:bounty:submit:{}", cell.hex)),
        )
        .await
    {
        Ok(r) if r.accepted => {
            record(state, command, "submit", &cell.hex, "accepted").await;
            with_receipt(
                embeds::success_embed("Work Submitted")
                    .field("Bounty", short_cell(&cell.hex), true)
                    .field("Artifact", truncate(&artifact, 60), false)
                    .field("Turn", turn_field(r.turn_hash.clone()), false),
                state,
                r.turn_hash,
            )
        }
        Ok(r) => rejected("Submission Rejected", r.error),
        Err(e) => embeds::error_embed("Submission Failed", &e.user_message("submit the work")),
    };
    edit_embed(ctx, command, embed).await;
}

async fn handle_payout(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let cell = match resolve_cell(ctx, command).await {
        Some(c) => c,
        None => return,
    };
    let Some(cclerk) = require_hosted(ctx, command, state).await else {
        return;
    };
    let action = build_payout_action(&cclerk.app, cell.cell);
    let embed = match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:bounty:payout:{}", cell.hex)),
        )
        .await
    {
        Ok(r) if r.accepted => {
            record(state, command, "payout", &cell.hex, "accepted").await;
            with_receipt(
                embeds::success_embed("Bounty Paid")
                    .field("Bounty", short_cell(&cell.hex), true)
                    .field("Turn", turn_field(r.turn_hash.clone()), false),
                state,
                r.turn_hash,
            )
        }
        Ok(r) => rejected("Payout Rejected", r.error),
        Err(e) => embeds::error_embed("Payout Failed", &e.user_message("pay out the bounty")),
    };
    edit_embed(ctx, command, embed).await;
}

async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer(ctx, command).await;
    let cell = match resolve_cell(ctx, command).await {
        Some(c) => c,
        None => return,
    };
    // The public read API exposes the cell's existence + balance + nonce +
    // provenance, but NOT individual state slots, so we report what is really
    // available rather than fabricate a lifecycle state value.
    let embed = match state.devnet.get_cell_details(&cell.hex).await {
        Ok(details) => embeds::dregg_embed("Bounty Status")
            .field("Bounty", short_cell(&cell.hex), true)
            .field("Mode", details.mode.clone(), true)
            .field("Escrowed", format!("{} DEC", details.balance), true)
            .field("Turns", details.nonce.to_string(), true)
            .field(
                "Provenance",
                details
                    .created_by_factory
                    .as_deref()
                    .map(short_cell)
                    .unwrap_or_else(|| "—".to_string()),
                true,
            )
            .field(
                "Note",
                "Lifecycle state (OPEN/CLAIMED/SUBMITTED/PAID) is enforced on-chain by the cell's program; \
                 the public read API does not expose individual state slots. Watch `/explorer feed` for bounty-* events.",
                false,
            ),
        Err(DevnetError::Status { code: 404, .. }) => embeds::warning_embed(
            "No Such Bounty",
            "No cell with that ID exists on-chain yet. Bounty cells are factory-born — create one via the Starbridge seed or the `/dregg` dashboard first.",
        ),
        Err(e) => embeds::error_embed("Status Unavailable", &e.user_message("read the bounty cell")),
    };
    edit_embed(ctx, command, embed).await;
}

// ─── Helpers ──────────────────────────────────────────────────────────────--

/// A parsed bounty cell: the typed id + its canonical hex form.
struct BountyCell {
    cell: CellId,
    hex: String,
}

/// Parse the `bounty-cell` option, responding with a warning on bad input.
async fn resolve_cell(ctx: &Context, command: &CommandInteraction) -> Option<BountyCell> {
    let raw = sub_string(command, "bounty-cell").unwrap_or_default();
    match parse_cell_bytes(&raw) {
        Ok(bytes) => Some(BountyCell {
            cell: CellId(bytes),
            hex: hex::encode(bytes),
        }),
        Err(msg) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed("Invalid Bounty Cell", &msg),
            )
            .await;
            None
        }
    }
}

/// Require the invoking user to have a hosted cipherclerk (writes must be
/// signed by a `/cipherclerk create` identity).
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
                    "Bounty actions must be signed by a hosted `/cipherclerk create` identity.",
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
                    "Create a hosted cipherclerk with `/cipherclerk create` before using bounties.",
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

async fn record(
    state: &BotState,
    command: &CommandInteraction,
    action: &str,
    cell_hex: &str,
    status: &str,
) {
    let actor = command.user.id.get().to_string();
    let guild = command.guild_id.map(|g| g.get().to_string());
    let _ = state
        .db
        .record_starbridge_activity(
            "bounty-board",
            action,
            &actor,
            guild.as_deref(),
            Some(cell_hex),
            status,
            serde_json::json!({ "bounty_cell": cell_hex }),
        )
        .await;
}

fn rejected(title: &str, error: Option<String>) -> CreateEmbed {
    embeds::error_embed(
        title,
        error
            .as_deref()
            .unwrap_or("the node rejected the signed bounty action"),
    )
}

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

fn parse_cell_bytes(input: &str) -> Result<[u8; 32], String> {
    let trimmed = input
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| input.trim());
    let bytes = hex::decode(trimmed).map_err(|e| format!("cell id must be hex: {e}"))?;
    bytes
        .try_into()
        .map_err(|_| "cell id must decode to exactly 32 bytes / 64 hex chars".to_string())
}

fn short_cell(cell_id: &str) -> String {
    let trimmed = cell_id
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| cell_id.trim());
    format!("`{}...`", &trimmed[..16.min(trimmed.len())])
}

fn turn_field(turn_hash: Option<String>) -> String {
    turn_hash
        .map(|h| format!("`{h}`"))
        .unwrap_or_else(|| "`unknown`".to_string())
}

/// Append an explorer receipt (link when `DREGG_EXPLORER_BASE` is configured, plus
/// the full copyable turn hash — never a dead link) when a turn hash is available.
fn with_receipt(embed: CreateEmbed, _state: &BotState, turn_hash: Option<String>) -> CreateEmbed {
    match turn_hash {
        Some(hash) => embed.field(
            "Receipt (turn hash)",
            crate::explorer_link::receipt_field("turn", &hash, "view on explorer"),
            false,
        ),
        None => embed,
    }
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(n).collect::<String>())
    }
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
