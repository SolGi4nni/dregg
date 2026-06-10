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

use crate::{BotState, embeds};
use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateInteractionResponse, CreateInteractionResponseMessage, EditInteractionResponse,
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
