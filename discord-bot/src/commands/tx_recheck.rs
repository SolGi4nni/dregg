//! **The "re-check against the chain" press for ledger rows** (bot-excellence backlog
//! Tier-2 #13).
//!
//! `/history` and `/leaderboard` render from the bot's private sqlite — pure trust-me, even
//! though the transfer path records the committed turn's `tx_hash` into that same table
//! (`commands::transfer`). This module makes each row checkable: a `txcheck:<turn_hash>`
//! button press asks the LIVE node whether that hash is a committed turn on its receipt chain
//! ([`crate::devnet::DevnetClient::get_turn_details`], which scans the node's served
//! `/api/receipts`) and reports what the chain — not the bot's DB — says: finality, signer,
//! and the receipt/proof posture, checked just now.
//!
//! Honest boundaries, stated on the surface:
//! * a faucet row (`tx_hash == "faucet"`) has no chain receipt — the button is never minted;
//! * the node serves a finite receipt window — an old receipt scrolling past it (or a devnet
//!   ledger reset) is reported as "not found in the served window", not as forgery.

use serenity::all::{
    ButtonStyle, ComponentInteraction, Context, CreateActionRow, CreateButton,
    CreateInteractionResponse, CreateInteractionResponseMessage,
};

use crate::BotState;
use crate::devnet::TurnDetails;
use crate::embeds;

/// The custom-id prefix the `main.rs` component router dispatches here.
pub const PREFIX: &str = "txcheck";

/// Whether a recorded `tx_hash` is a chain-checkable committed-turn hash (64 hex chars) —
/// faucet rows and legacy sentinels are not.
pub fn checkable(tx_hash: &str) -> bool {
    tx_hash.len() == 64 && hex::decode(tx_hash).is_ok()
}

/// A row's receipt reference: the explorer link (when configured) with the short hash, else
/// the full copyable hash — never a dead link.
pub fn receipt_ref(tx_hash: &str) -> String {
    if checkable(tx_hash) {
        crate::explorer_link::short_ref("turn", tx_hash, 12)
    } else {
        format!("`{tx_hash}`")
    }
}

/// Up to `max` re-check buttons for the checkable hashes among `hashes` (insertion order,
/// deduplicated), chunked five per action row. Labels carry the row number they re-check.
pub fn recheck_rows(hashes: &[&str], max: usize) -> Vec<CreateActionRow> {
    let mut seen: Vec<&str> = Vec::new();
    for &h in hashes {
        if checkable(h) && !seen.contains(&h) {
            seen.push(h);
            if seen.len() == max {
                break;
            }
        }
    }
    let mut rows = Vec::new();
    for (chunk_idx, chunk) in seen.chunks(5).enumerate() {
        let buttons: Vec<CreateButton> = chunk
            .iter()
            .enumerate()
            .map(|(i, h)| {
                CreateButton::new(format!("{PREFIX}:{h}"))
                    .label(format!(
                        "⛓ re-check #{} ({}…)",
                        chunk_idx * 5 + i + 1,
                        &h[..6]
                    ))
                    .style(ButtonStyle::Secondary)
            })
            .collect();
        rows.push(CreateActionRow::Buttons(buttons));
    }
    rows
}

/// Route a `txcheck:<turn_hash>` press: ask the live node whether the hash is a committed
/// turn on its receipt chain, and post what the CHAIN said — publicly, checked just now.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let Some(hash) = component.data.custom_id.strip_prefix(&format!("{PREFIX}:")) else {
        return;
    };
    if !checkable(hash) {
        let _ = component
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content("This row carries no committed-turn hash to re-check (a faucet grant has no chain receipt).")
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }

    let embed = match state.devnet.get_turn_details(hash).await {
        Ok(details) => found_embed(hash, &details, &state.config.devnet_url),
        Err(e) => embeds::warning_embed(
            "✗ Not found in the node's served receipt window",
            &not_found_text(hash, &e.to_string()),
        ),
    };
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new().embed(embed),
            ),
        )
        .await;
}

/// The found-on-chain embed: what the node's receipt chain says about this hash, just now.
fn found_embed(hash: &str, details: &TurnDetails, node_url: &str) -> serenity::all::CreateEmbed {
    embeds::success_embed("✓ Found on the chain's receipt chain — checked just now")
        .description(format!(
            "The node at `{node}` serves a committed turn for this hash — the bot's ledger row \
             has a live chain counterpart. Below is what the CHAIN (not the bot's database) \
             reports; fetch it yourself: `GET {node}/api/receipts`.",
            node = node_url.trim_end_matches('/'),
        ))
        .field(
            "Turn",
            crate::explorer_link::receipt_field("turn", hash, "view on explorer"),
            false,
        )
        .field("Finality", details.result.clone(), true)
        .field(
            "Signer",
            format!("`{}…`", &details.signer[..16.min(details.signer.len())]),
            true,
        )
        .field("Receipt posture", details.proof_type.clone(), true)
}

/// The honest not-found report — a finite window / reset ledger is named, not dramatized.
fn not_found_text(hash: &str, err: &str) -> String {
    format!(
        "`{short}…` has no committed turn in the receipt window the node currently serves \
         ({err}). The node's window is finite: an old receipt may have scrolled past it, or \
         the devnet ledger was reset since this row was recorded. The bot's local row still \
         says what it said — it just cannot be independently confirmed against the live chain \
         right now.",
        short = &hash[..12.min(hash.len())],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checkable_admits_only_full_turn_hashes() {
        assert!(checkable(&"ab".repeat(32)));
        assert!(!checkable("faucet"));
        assert!(!checkable(&"ab".repeat(31)));
        assert!(!checkable(&"zz".repeat(32)));
    }

    /// The buttons ride the documented wire (`txcheck:<hash>`), deduplicate, skip
    /// non-checkable rows, and respect the cap.
    #[test]
    fn recheck_rows_mint_the_documented_ids_and_skip_faucet_rows() {
        let h1 = "11".repeat(32);
        let h2 = "22".repeat(32);
        let rows = recheck_rows(&[h1.as_str(), "faucet", h1.as_str(), h2.as_str()], 5);
        let json = serde_json::to_value(&rows).expect("rows serialize");
        let text = json.to_string();
        assert!(text.contains(&format!("txcheck:{h1}")), "{text}");
        assert!(text.contains(&format!("txcheck:{h2}")), "{text}");
        assert!(!text.contains("txcheck:faucet"), "{text}");
        assert_eq!(text.matches("txcheck:").count(), 2, "deduplicated: {text}");
    }

    /// The not-found register names the finite window — honest, not alarmist and not soothing.
    #[test]
    fn the_not_found_text_names_the_finite_window() {
        let text = not_found_text(&"ab".repeat(32), "turn not found");
        assert!(text.contains("finite"), "{text}");
        assert!(text.contains("cannot be independently confirmed"), "{text}");
    }
}
