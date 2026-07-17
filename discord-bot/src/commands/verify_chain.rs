//! **The standing "⛓ re-verify chain" press** — verify-don't-trust as a BUTTON on every
//! offering surface (bot-excellence backlog Tier-2 #10, and the pressable half of #12).
//!
//! Every offering already carries a real verifier ([`dreggnet_offerings::Offering::verify`]
//! re-derives the session's receipt hash-chain from its committed move history), but on most
//! surfaces nobody could PRESS it: `/council /market /grain /doc /dungeon` register a `verify`
//! subcommand while the twelve `/play` offerings — including both flagship games — registered
//! only the offering choice. This module mints one uniform affordance:
//!
//! * [`row`] — a `verifychain:<key>` button appended to every offering surface (the generic
//!   adapter's `action_rows` adds it), so ANY viewer of ANY offering can demand the re-check;
//! * [`handle_component`] — the press: dispatch on the offering key, run the REAL
//!   [`crate::commands::offering::verify_live`] against the channel's live session, and post
//!   the honest report publicly — what was recomputed, from what, just now, in how long.
//!
//! This is also what makes the surfaced `turn_hash` MEANINGFUL (#12): each landed move's hash
//! is a link in the session's hash-linked receipt chain, and this press recomputes that chain
//! from the move history in front of the presser — mutate any past move and every later hash
//! (and this check) changes. The bot never asks to be believed; it hands over the button.

use serenity::all::{
    ButtonStyle, ComponentInteraction, Context, CreateActionRow, CreateButton, CreateEmbed,
    CreateInteractionResponse, CreateInteractionResponseMessage,
};

use crate::BotState;
use crate::commands::offering::{self, DiscordOffering};

/// The custom-id prefix the `main.rs` component router dispatches here.
pub const PREFIX: &str = "verifychain";

/// The standing re-verify affordance for an offering surface: one Secondary-styled button whose
/// press re-derives the channel's committed chain. Appended by the generic adapter's
/// `action_rows`, so it rides every render (open / status / post-press re-render) uniformly.
pub fn row(key: &str) -> CreateActionRow {
    CreateActionRow::Buttons(vec![
        CreateButton::new(format!("{PREFIX}:{key}"))
            .label("⛓ re-verify chain")
            .style(ButtonStyle::Secondary),
    ])
}

/// Route a `verifychain:<key>` press: re-verify the pressed channel's live session for the
/// offering that owns the key, and post the honest recomputation report (publicly — the point
/// is verification anyone can watch, not a private reassurance).
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, _state: &BotState) {
    let Some(key) = component.data.custom_id.strip_prefix(&format!("{PREFIX}:")) else {
        return;
    };

    macro_rules! dispatch {
        ($($ty:ty),+ $(,)?) => {
            match key {
                $(k if k == <$ty as DiscordOffering>::KEY => {
                    respond::<$ty>(ctx, component).await;
                })+
                _ => {}
            }
        };
    }

    dispatch!(
        dreggnet_council::CouncilOffering,
        dreggnet_market::MarketOffering,
        dreggnet_hermes::HermesOffering,
        dreggnet_grain::GrainOffering,
        dreggnet_doc::DocOffering,
        dreggnet_offerings::dungeon::DungeonOffering,
        crate::commands::portfolio::SeatedTug,
        dregg_automatafl::AutomataflOffering,
        dreggnet_names::NamesOffering,
        dreggnet_compute::ComputeOffering,
        dreggnet_surfaces::TradeOffering,
        dreggnet_surfaces::InventoryOffering,
        dreggnet_surfaces::CheevoShowcase,
        dreggnet_surfaces::GuildPage,
        dreggnet_surfaces::CraftOffering,
        dreggnet_surfaces::CompanionOffering,
        dreggnet_surfaces::TavernOffering,
        dreggnet_surfaces::PartyOffering,
    );
}

/// The press resolved for one concrete offering: run the REAL verifier against the channel's
/// live session and post what was recomputed. Pure Discord I/O around
/// [`offering::verify_live`]; the report text core is [`recheck_note`] (test-readable).
async fn respond<O: DiscordOffering>(ctx: &Context, component: &ComponentInteraction) {
    let channel = component.channel_id.get();
    let started = std::time::Instant::now();
    let report = offering::verify_live::<O>(channel);
    let elapsed_ms = started.elapsed().as_millis();

    let msg = match report {
        Some(report) => {
            let embed = CreateEmbed::new()
                .title(format!("{} — chain re-verified in front of you", O::TITLE))
                .description(recheck_note(&offering::verify_note(&report), elapsed_ms))
                .color(if report.verified { O::COLOR } else { 0xE63946 });
            CreateInteractionResponseMessage::new().embed(embed)
        }
        None => CreateInteractionResponseMessage::new()
            .content(format!(
                "No live {} session in this channel to re-verify — the chain lives with the \
                 session. Open one and every landed move extends a hash-linked receipt chain \
                 this button re-derives.",
                O::KEY
            ))
            .ephemeral(true),
    };
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

/// The honest recomputation report: the verifier's own note plus what the press actually did —
/// and why the `turn_hash` each landed move printed matters (it chains). Pure, so tests read
/// exactly what a presser sees.
pub fn recheck_note(verify_note: &str, elapsed_ms: u128) -> String {
    format!(
        "{verify_note}\n\nRecomputed just now ({elapsed_ms} ms): the bot re-derived the \
         session's hash-linked receipt chain from its committed move history. The `turn_hash` \
         each landed move printed is a link in this chain — mutate ANY past move and every \
         later hash (and this check) changes. Nothing above is taken on trust."
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The button rides the documented wire (`verifychain:<key>`) so the `main.rs` router's
    /// prefix dispatch reaches [`handle_component`], and the label names the action.
    #[test]
    fn the_row_mints_the_documented_custom_id() {
        let row = row("council");
        let json = serde_json::to_value(&row).expect("the action row serializes");
        let text = json.to_string();
        assert!(text.contains("verifychain:council"), "{text}");
        assert!(text.contains("re-verify chain"), "{text}");
    }

    /// The press report says WHAT was recomputed and WHY the surfaced turn_hash matters — the
    /// dead-end hash (#12) becomes a explained, chained, re-checkable value.
    #[test]
    fn the_recheck_note_explains_the_chain_and_the_recomputation() {
        let note = recheck_note("✓ **3 verified turns re-verify.** ok", 12);
        assert!(note.contains("3 verified turns"), "{note}");
        assert!(note.contains("Recomputed just now (12 ms)"), "{note}");
        assert!(note.contains("turn_hash"), "{note}");
        assert!(note.contains("mutate ANY past move"), "{note}");
    }
}
