//! Bounty board commands: `/bounty post | claim | submit | payout | status`.
//!
//! Drives the `starbridge-bounty-board` app (`starbridge-apps/bounty-board`)
//! against the live node. Each write is a canonical Ed25519-signed `Action`
//! built by the app's own turn-builders (`build_post_action`,
//! `build_claim_action`, `build_submit_action`, `build_payout_actions`) and
//! submitted through `DevnetClient::submit_app_actions` — the same signed-turn
//! path the nameservice and governance commands use. The bot signs as the
//! invoking user's hosted cipherclerk.
//!
//! The bounty *cell* is supplied by the caller (a factory-born sovereign cell;
//! the Starbridge seed / `/dregg` dashboard births these). Lifecycle state is
//! enforced on-chain by the bounty cell's `CellProgram` — `STATE` is strictly
//! monotone OPEN→CLAIMED→SUBMITTED→PAID, so a double-claim or double-payout is
//! rejected by the executor, not by the bot.
//!
//! ## `/bounty payout` moves value, or it says it did not
//!
//! Until 2026-07-28 this file rendered a green "Bounty Paid" embed for a turn
//! that wrote a state code and moved nothing: `build_payout_action` carried a
//! `SetField` and an `EmitEvent` and no `Transfer`. A claimant got a receipt for
//! a payment that did not happen, which is worse than an error. The `status`
//! embed compounded it by labelling the bounty cell's balance "Escrowed" when
//! nothing had ever funded it.
//!
//! Now `/bounty payout` submits the conserving `Effect::Transfer` and the
//! `STATE=PAID` advance as roots of ONE turn, so they commit or roll back
//! together. Every reason the payout cannot conserve is a REFUSAL with its own
//! embed and no turn submitted: the bounty is not at SUBMITTED, the named payee
//! is not the bound claimant, no reward is recorded, or the payer cannot cover
//! it. The last word is the executor's `InsufficientBalance`, which takes the
//! PAID stamp down with the payment.
//!
//! ⚠ Two honest limits, both named on the surface rather than papered over:
//!
//!   * **The reward is a promise, not an escrow.** The bounty cell cannot hold
//!     it (see the crate docs: `StrictMonotonic(STATE)` refuses any action that
//!     credits the cell without advancing its state, and a `Transfer` from an
//!     outside cell needs that cell's `send` permission to be `None`). So
//!     `status` says "Promised", and settling is what tests whether the money is
//!     there.
//!   * **The payee/claimant match is checked HERE**, against the committed
//!     `CLAIMANT_HASH` slot the node serves. That is a real check on a real
//!     committed value, and it is NOT executor-enforced: no `StateConstraint`
//!     binds a `Transfer` destination to a state slot. Adding one is
//!     Lean-authored work on the constraint language, not something this file
//!     may fake.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dregg_app_framework::CellId;
use starbridge_bounty_board::{
    CLAIMANT_HASH_SLOT, REWARD_SLOT, STATE_CLAIMED, STATE_OPEN, STATE_PAID, STATE_SLOT,
    STATE_SUBMITTED, build_claim_action, build_payout_actions, build_post_action,
    build_submit_action, claimant_hash,
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
                        "Reward you promise the claimant (computrons)",
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
                "Pay the claimant and close the bounty (terminal)",
            )
            .add_sub_option(bounty_cell(true))
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "claimant-cell",
                    "Cell ID to pay (must match the claimant bound on chain)",
                )
                .required(true),
            ),
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
        Some(v) if v > 0 => v as u64,
        _ => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed(
                    "Invalid Reward",
                    "A reward must be a positive whole number. You pay it out of your own \
                     balance when you settle, so a bounty worth nothing cannot be posted.",
                ),
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
    let action = match build_post_action(&cclerk.app, cell.cell, &title, reward) {
        Ok(a) => a,
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed("Bounty Not Posted", &e.to_string()),
            )
            .await;
            return;
        }
    };
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
                    .field("Promised", format!("{reward} DEC"), true)
                    .field("Bounty", short_cell(&cell.hex), true)
                    .field(
                        "What this is",
                        format!(
                            "A promise of {reward} DEC, not money set aside. You pay it \
                             from your own balance when you settle, and the settlement \
                             fails if you cannot."
                        ),
                        false,
                    )
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
    let payee =
        match resolve_named_cell(ctx, command, "claimant-cell", "Invalid Claimant Cell").await {
            Some(c) => c,
            None => return,
        };
    let Some(cclerk) = require_hosted(ctx, command, state).await else {
        return;
    };

    // Read the bounty BEFORE building anything. Every reason this payout could
    // not move value is a refusal with its own name, not a green embed.
    let details = match state.devnet.get_cell_details(&cell.hex).await {
        Ok(d) => d,
        Err(DevnetError::Status { code: 404, .. }) => {
            edit_embed(ctx, command, no_such_bounty_embed()).await;
            return;
        }
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::error_embed("Payout Failed", &e.user_message("read the bounty cell")),
            )
            .await;
            return;
        }
    };

    let lifecycle = slot_u64(&details.fields, STATE_SLOT);
    if lifecycle != STATE_SUBMITTED {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "Payout Refused",
                &format!(
                    "This bounty is {}. Only work that has been submitted can be paid out, \
                     and a bounty can be paid once.",
                    state_word(lifecycle)
                ),
            ),
        )
        .await;
        return;
    }

    // The claimant was bound on chain when the bounty was claimed. The cell named
    // here must be that claimant, checked against the committed value.
    let bound = details
        .fields
        .get(CLAIMANT_HASH_SLOT)
        .cloned()
        .unwrap_or_default();
    if !claimant_matches(&bound, &payee.hex) {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "Wrong Payee",
                "That cell is not the claimant this bounty is bound to. Pay the cell that \
                 claimed the bounty, or nobody is paid.",
            ),
        )
        .await;
        return;
    }

    let reward = slot_u64(&details.fields, REWARD_SLOT);
    if reward == 0 {
        edit_embed(
            ctx,
            command,
            embeds::warning_embed(
                "Nothing To Pay",
                "This bounty records no reward, so there is nothing to hand over.",
            ),
        )
        .await;
        return;
    }

    // The payment and the `STATE=PAID` advance go up as roots of ONE turn. If the
    // payment is refused the whole turn rolls back, so there is no way to reach
    // the success embed below over a bounty nobody was paid for.
    let actions = match build_payout_actions(&cclerk.app, cell.cell, payee.cell, reward) {
        Ok(a) => a,
        Err(e) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed("Payout Refused", &e.to_string()),
            )
            .await;
            return;
        }
    };
    let embed = match state
        .devnet
        .submit_app_actions(
            &cclerk,
            actions,
            Some(format!("discord:bounty:payout:{}", cell.hex)),
        )
        .await
    {
        Ok(r) if r.accepted => {
            record(state, command, "payout", &cell.hex, "accepted").await;
            with_receipt(
                embeds::success_embed("Bounty Paid")
                    .field("Bounty", short_cell(&cell.hex), true)
                    .field("Paid", format!("{reward} DEC"), true)
                    .field("To", short_cell(&payee.hex), true)
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
    // `GET /api/cell/{id}` serves the cell's per-slot field values, so the stage
    // and the promised reward are read off the chain rather than guessed at. This
    // embed used to say the cell's balance was "Escrowed" and that the read API
    // could not show the stage; both were untrue. The reward is a PROMISE the
    // poster settles from its own balance, so that is what it is called.
    let embed = match state.devnet.get_cell_details(&cell.hex).await {
        Ok(details) => embeds::dregg_embed("Bounty Status")
            .field("Bounty", short_cell(&cell.hex), true)
            .field(
                "Stage",
                state_word(slot_u64(&details.fields, STATE_SLOT)),
                true,
            )
            .field("Mode", details.mode.clone(), true)
            .field(
                "Promised",
                format!("{} DEC", slot_u64(&details.fields, REWARD_SLOT)),
                true,
            )
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
                "The reward is a promise, not money set aside: whoever settles pays it \
                 from their own balance, and the settlement fails if they cannot. The \
                 stage can only move forward, and it is the chain that enforces that, \
                 not this bot. Watch `/explorer feed` for bounty-* events.",
                false,
            ),
        Err(DevnetError::Status { code: 404, .. }) => no_such_bounty_embed(),
        Err(e) => embeds::error_embed(
            "Status Unavailable",
            &e.user_message("read the bounty cell"),
        ),
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
    resolve_named_cell(ctx, command, "bounty-cell", "Invalid Bounty Cell").await
}

/// Parse any cell-id option, responding with `title` and the parse error on bad
/// input. A bad payee must never fall through to a turn.
async fn resolve_named_cell(
    ctx: &Context,
    command: &CommandInteraction,
    option: &str,
    title: &str,
) -> Option<BountyCell> {
    let raw = sub_string(command, option).unwrap_or_default();
    match parse_cell_bytes(&raw) {
        Ok(bytes) => Some(BountyCell {
            cell: CellId(bytes),
            hex: hex::encode(bytes),
        }),
        Err(msg) => {
            edit_embed(ctx, command, embeds::warning_embed(title, &msg)).await;
            None
        }
    }
}

/// The one "this bounty does not exist" embed, shared by `payout` and `status`.
fn no_such_bounty_embed() -> CreateEmbed {
    embeds::warning_embed(
        "No Such Bounty",
        "No cell with that ID exists on-chain yet. Bounty cells are factory-born. \
         Create one via the Starbridge seed or the `/dregg` dashboard first.",
    )
}

/// Read slot `index` of a cell's committed fields as the canonical u64 (the
/// big-endian trailing 8 bytes of the 32-byte field element, the lane
/// `dregg_cell::field_from_u64` writes and `field_to_u64` reads). An absent or
/// malformed slot reads 0, which every caller treats as "no value", never as
/// permission to proceed.
fn slot_u64(fields: &[String], index: usize) -> u64 {
    let Some(hex_field) = fields.get(index) else {
        return 0;
    };
    let Ok(bytes) = hex::decode(hex_field.trim()) else {
        return 0;
    };
    if bytes.len() != 32 {
        return 0;
    }
    let mut tail = [0u8; 8];
    tail.copy_from_slice(&bytes[24..32]);
    u64::from_be_bytes(tail)
}

/// Does the committed `CLAIMANT_HASH` slot name this cell? The claim bound
/// `blake3` of the claimant's cell-id hex, so the check is to recompute that
/// hash from the supplied cell and compare it to what the chain holds.
fn claimant_matches(bound_slot_hex: &str, payee_hex: &str) -> bool {
    let Ok(bound) = hex::decode(bound_slot_hex.trim()) else {
        return false;
    };
    if bound.len() != 32 || bound == [0u8; 32] {
        // An unclaimed bounty binds nothing; there is nobody to pay.
        return false;
    }
    bound == claimant_hash(payee_hex)
}

/// The lifecycle stage as a word a reader can say out loud.
fn state_word(code: u64) -> String {
    match code {
        STATE_OPEN => "open for claims".to_string(),
        STATE_CLAIMED => "claimed, waiting on the work".to_string(),
        STATE_SUBMITTED => "submitted, waiting on payment".to_string(),
        STATE_PAID => "paid and closed".to_string(),
        _ => "not posted yet".to_string(),
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
            edit_embed(ctx, command, embeds::store_unavailable_embed(&e)).await;
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
