//! Polis command: `/council-status` — read-only inspection of a
//! `starbridge-polis` council proposal cell.
//!
//! Decodes the council machine straight from the node's public cell read
//! (`/api/cell/{id}` per-slot fields): lifecycle state, staged proposal
//! hash, per-member approval bits, the certified-threshold flag, and the
//! published membership commitment. The THRESHOLD itself is content-
//! addressed into the factory descriptor (committed with the member list
//! under the membership commitment shown), so what the cell shows is the
//! approval COUNT and the certified flag the executor enforced.
//!
//! Slot schema mirrors `starbridge-apps/polis/src/lib.rs` (`council`).

use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::{BotState, embeds};
use dregg_app_framework::{CellId, Effect, field_from_u64};
use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

// Council proposal-cell slot schema — mirrors starbridge_polis::council.
const STATE_SLOT: usize = 0;
const PROPOSAL_HASH_SLOT: usize = 1;
const APPROVED_FLAG_SLOT: usize = 2;
const FIRST_APPROVAL_SLOT: usize = 3;
const MAX_MEMBERS: usize = 3;
const MEMBERS_COMMIT_SLOT: usize = 6;

/// Register `/council-status <proposal-cell>`.
pub fn register_council_status() -> CreateCommand {
    CreateCommand::new("council-status")
        .description("Show a polis council proposal cell: state, approvals, certification")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "proposal-cell",
                "Council proposal cell ID (64 hex chars)",
            )
            .required(true),
        )
}

/// Register `/council-approve <proposal-cell> <member-index>`.
pub fn register_council_approve() -> CreateCommand {
    CreateCommand::new("council-approve")
        .description("Cast your actor-bound approval on a polis council proposal cell")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "proposal-cell",
                "Council proposal cell ID (64 hex chars)",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Integer,
                "member-index",
                "Your member slot index in the council (0-based)",
            )
            .required(true)
            .min_int_value(0)
            .max_int_value((MAX_MEMBERS as u64) - 1),
        )
}

fn state_name(code: u64) -> &'static str {
    match code {
        0 => "DRAFT",
        1 => "PROPOSED",
        2 => "REJECTED (terminal)",
        3 => "APPROVED",
        4 => "EXECUTED (terminal)",
        _ => "UNKNOWN",
    }
}

/// Big-endian u64 in the low 8 bytes of a 64-hex field (the
/// `field_from_u64` encoding).
fn u64_from_field_hex(hexstr: &str) -> u64 {
    if hexstr.len() != 64 {
        return 0;
    }
    u64::from_str_radix(&hexstr[48..], 16).unwrap_or(0)
}

fn short_hex(value: &str) -> String {
    if value.len() <= 16 {
        value.to_string()
    } else {
        format!("{}…{}", &value[..8], &value[value.len() - 4..])
    }
}

/// Handle `/council-status`.
pub async fn handle_council_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let cell_hex = command
        .data
        .options
        .iter()
        .find(|o| o.name == "proposal-cell")
        .and_then(|o| o.value.as_str())
        .unwrap_or("")
        .to_string();
    if cell_hex.len() != 64 || !cell_hex.chars().all(|c| c.is_ascii_hexdigit()) {
        let embed = embeds::error_embed(
            "Invalid Proposal Cell",
            "Expected a 64-character hex cell id.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    match state.devnet.get_cell_details(&cell_hex).await {
        Ok(cell) => {
            let slot = |i: usize| cell.fields.get(i).cloned().unwrap_or_default();
            let u64_at = |i: usize| u64_from_field_hex(&slot(i));
            let desc = if cell.fields.is_empty() {
                format!(
                    "**Cell:** `{}`\n\nThis node's `/api/cell` response did not include per-slot fields, so the council machine cannot be decoded here.",
                    short_hex(&cell_hex),
                )
            } else {
                let state_code = u64_at(STATE_SLOT);
                let approvals: Vec<bool> = (0..MAX_MEMBERS)
                    .map(|i| u64_at(FIRST_APPROVAL_SLOT + i) == 1)
                    .collect();
                let count = approvals.iter().filter(|a| **a).count();
                let board = approvals
                    .iter()
                    .enumerate()
                    .map(|(i, a)| format!("member {i}: {}", if *a { "✅" } else { "—" }))
                    .collect::<Vec<_>>()
                    .join(" · ");
                format!(
                    "**Cell:** `{}`\n**State:** {}\n**Proposal:** `{}`\n**Approvals:** {count} ({board})\n**Certified:** {}\n**Members commit:** `{}`\n\nThe threshold and member list are content-addressed into the factory descriptor (committed under the members commit); the certified flag is the executor-enforced `Σ approvals ≥ M` gate.",
                    short_hex(&cell_hex),
                    state_name(state_code),
                    short_hex(&slot(PROPOSAL_HASH_SLOT)),
                    if u64_at(APPROVED_FLAG_SLOT) == 1 {
                        "YES (threshold met)"
                    } else {
                        "no"
                    },
                    short_hex(&slot(MEMBERS_COMMIT_SLOT)),
                )
            };
            let embed = embeds::dregg_embed("Council Proposal").description(desc);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Council Status Unavailable", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/council-approve` — submit the actor-bound approval turn.
///
/// The council cell program (`starbridge_polis::council`) binds approval slot
/// `i` to member `i`'s key: the slot may flip 0→1 only in a turn whose sender
/// is that member. We submit a single `SetField` effect writing `1` into
/// `FIRST_APPROVAL_SLOT + member_index`, signed by the caller's hosted
/// cipherclerk, and let the on-cell predicate enforce the binding — a
/// non-member's turn is rejected by the executor, not by the bot.
pub async fn handle_council_approve(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let cell_hex = string_opt(command, "proposal-cell").unwrap_or_default();
    let member_index = integer_opt(command, "member-index").unwrap_or(-1);

    if cell_hex.len() != 64 || !cell_hex.chars().all(|c| c.is_ascii_hexdigit()) {
        edit_err(
            ctx,
            command,
            "Invalid Proposal Cell",
            "Expected a 64-character hex cell id.",
        )
        .await;
        return;
    }
    if !(0..MAX_MEMBERS as i64).contains(&member_index) {
        edit_err(
            ctx,
            command,
            "Invalid Member Index",
            &format!("`member-index` must be between 0 and {}.", MAX_MEMBERS - 1),
        )
        .await;
        return;
    }
    let member_index = member_index as usize;

    let cclerk = match hosted_cclerk(command.user.id.get(), state).await {
        Ok(cclerk) => cclerk,
        Err(embed) => {
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    // Read the live cell so we can give a useful pre-flight error instead of a
    // bare executor rejection.
    match state.devnet.get_cell_details(&cell_hex).await {
        Ok(cell) if !cell.fields.is_empty() => {
            let slot = |i: usize| cell.fields.get(i).cloned().unwrap_or_default();
            let state_code = u64_from_field_hex(&slot(STATE_SLOT));
            if state_code != 1 {
                edit_err(
                    ctx,
                    command,
                    "Proposal Not Open",
                    &format!(
                        "Council cell is **{}**; approvals are only accepted in PROPOSED state.",
                        state_name(state_code),
                    ),
                )
                .await;
                return;
            }
            if u64_from_field_hex(&slot(FIRST_APPROVAL_SLOT + member_index)) == 1 {
                edit_err(
                    ctx,
                    command,
                    "Already Approved",
                    &format!("Member slot {member_index} has already approved this proposal."),
                )
                .await;
                return;
            }
        }
        Ok(_) => {
            // No per-slot fields exposed — proceed and let the executor decide.
        }
        Err(e) => {
            edit_err(ctx, command, "Council Read Failed", &e.to_string()).await;
            return;
        }
    }

    let proposal_cell = CellId::from_bytes(parse_cell_bytes(&cell_hex));
    let slot = FIRST_APPROVAL_SLOT + member_index;
    let action = cclerk.app.make_action(
        proposal_cell,
        "council-approve",
        vec![Effect::SetField {
            cell: proposal_cell,
            index: slot,
            value: field_from_u64(1),
        }],
    );

    match state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:polis:approve:slot:{member_index}")),
        )
        .await
    {
        Ok(result) if result.accepted => {
            let embed = embeds::success_embed("Approval Cast")
                .field("Proposal", format!("`{}`", short_hex(&cell_hex)), true)
                .field("Member Slot", member_index.to_string(), true)
                .field(
                    "Turn",
                    result
                        .turn_hash
                        .map(|h| format!("`{h}`"))
                        .unwrap_or_else(|| "`unknown`".to_string()),
                    false,
                )
                .field(
                    "Note",
                    "The on-cell predicate enforced actor-binding: only your member key could flip this slot. Re-run `/council-status` to see the new approval count and certified flag.",
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(result) => {
            let embed = embeds::error_embed(
                "Approval Rejected",
                result.error.as_deref().unwrap_or(
                    "the executor rejected the approval — your cipherclerk is likely not the bound key for this member slot, or the proposal is not open",
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            edit_err(
                ctx,
                command,
                "Approval Failed",
                &e.user_message("cast your approval"),
            )
            .await;
        }
    }
}

fn string_opt(command: &CommandInteraction, name: &str) -> Option<String> {
    command
        .data
        .options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn integer_opt(command: &CommandInteraction, name: &str) -> Option<i64> {
    command
        .data
        .options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n),
            _ => None,
        })
}

fn parse_cell_bytes(hexstr: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    if let Ok(bytes) = hex::decode(hexstr) {
        if bytes.len() == 32 {
            out.copy_from_slice(&bytes);
        }
    }
    out
}

async fn hosted_cclerk(
    user_id: u64,
    state: &BotState,
) -> Result<UserCipherclerk, serenity::builder::CreateEmbed> {
    match state.db.get_user_identity(&user_id.to_string()).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => Ok(UserCipherclerk::derive(
            &state.config.bot_secret,
            user_id,
            state.federation_id_bytes,
        )),
        Ok(Some(_)) => Err(embeds::warning_embed(
            "Hosted Identity Required",
            "Council approvals are signed canonical turns, so they require a hosted `/cipherclerk create` identity.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` before approving proposals.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}

async fn edit_err(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let embed = embeds::error_embed(title, desc);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
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
