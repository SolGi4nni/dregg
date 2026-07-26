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

/// Whether this build routes a `verifychain:<key>` press to a real verifier. Derived from the
/// SAME table [`handle_component`] dispatches on, so it cannot claim a route that does not exist.
pub fn routes(key: &str) -> bool {
    let mut routed = false;
    macro_rules! probe {
        ($ty:ty) => {
            routed |= key == <$ty as DiscordOffering>::KEY;
        };
    }
    crate::commands::offering::for_each_generic_offering!(probe);
    probe!(dreggnet_offerings::dungeon::DungeonOffering);
    routed
}

/// Route a `verifychain:<key>` press: re-verify the pressed channel's live session for the
/// offering that owns the key, and post the honest recomputation report (publicly — the point
/// is verification anyone can watch, not a private reassurance).
///
/// **The arms come from the generic adapter's ONE mounting table**
/// (`offering::for_each_generic_offering`), plus the bespoke `/dungeon` crowd surface which is
/// not in it. They used to be a second, hand-typed list — and it had drifted eight entries
/// behind the table, so the Dark Bazaar, the Descent CAMPAIGN, the Ash Gate raid, the quest
/// board, the loadout, the talent tree, and the overworld each shipped a `⛓ re-verify chain`
/// button whose press fell into `_ => {}`, returned without ever answering the interaction, and
/// showed the player **"This interaction failed"** on a surface that was working perfectly.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, _state: &BotState) {
    let Some(key) = component.data.custom_id.strip_prefix(&format!("{PREFIX}:")) else {
        return;
    };

    macro_rules! arm {
        ($ty:ty) => {
            if key == <$ty as DiscordOffering>::KEY {
                respond::<$ty>(ctx, component).await;
                return;
            }
        };
    }
    crate::commands::offering::for_each_generic_offering!(arm);
    // `/dungeon` keeps its bespoke crowd surface, so it is not in the generic table.
    arm!(dreggnet_offerings::dungeon::DungeonOffering);

    // NEVER a silent drop. An unrecognised key is a button from a surface this build no longer
    // serves; say so rather than leaving the press to time out as "This interaction failed".
    crate::commands::offering::component_ephemeral(
        ctx,
        component,
        // The shared stale-control stem with THIS press's own (better, more specific) next step.
        &dreggnet_offerings::refusal::stale_control(
            "Re-open the offering and press the re-verify button on the fresh board.",
        ),
    )
    .await;
}

/// The press resolved for one concrete offering: run the REAL verifier against the channel's
/// live session and post what was recomputed. Pure Discord I/O around
/// [`offering::verify_live`]; the report text core is [`recheck_note`] (test-readable).
async fn respond<O: DiscordOffering>(ctx: &Context, component: &ComponentInteraction) {
    // ACK inside the 3s window (a deferred update that leaves the pressed offering surface
    // intact) BEFORE the re-derivation: a long receipt chain replay runs on the offering's store
    // thread and would otherwise park the async worker past the window, showing "interaction
    // failed" on a check that is running fine.
    crate::commands::ack::ack_component(ctx, component).await;

    let channel = component.channel_id.get();
    let started = std::time::Instant::now();
    // The verifier re-derives the whole chain on the store thread; move the blocking wait OFF the
    // async worker.
    let report = tokio::task::spawn_blocking(move || offering::verify_live::<O>(channel))
        .await
        .ok()
        .flatten();
    let elapsed_ms = started.elapsed().as_millis();

    match report {
        Some(report) => {
            let embed = CreateEmbed::new()
                .title(format!("{} — chain re-verified in front of you", O::TITLE))
                .description(recheck_note(&offering::verify_note(&report), elapsed_ms))
                .color(if report.verified { O::COLOR } else { 0xE63946 });
            // PUBLIC, as before — the point is a re-verification anyone can watch.
            crate::commands::ack::followup_embed(ctx, component, embed).await;
        }
        None => {
            crate::commands::ack::followup_ephemeral(
                ctx,
                component,
                &format!(
                    "No live {} session in this channel to re-verify — the chain lives with the \
                     session. Open one and every landed move extends a hash-linked receipt chain \
                     this button re-derives.",
                    O::KEY
                ),
            )
            .await;
        }
    }
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

    /// **EVERY key that can MINT this button must ROUTE it.** `offering::action_rows_at` appends
    /// `row(O::KEY)` to every offering surface unconditionally, so any key the generic adapter
    /// serves ships a pressable `⛓ re-verify chain`. If the router does not know that key the
    /// press falls through, the interaction is never answered, and the player is shown "This
    /// interaction failed" on a live, healthy board.
    #[test]
    fn every_mintable_key_is_routed() {
        let unrouted: Vec<&str> = crate::commands::offering::generic_offering_keys()
            .into_iter()
            .filter(|key| !routes(key))
            .collect();
        assert!(
            unrouted.is_empty(),
            "these offerings mint a re-verify button that answers no press: {unrouted:?}"
        );
        assert!(routes("dungeon"), "the bespoke crowd surface routes too");
    }

    /// The eight keys that WERE dead — named, so a future hand-edit of the dispatch cannot
    /// quietly re-strand them. (`gear`/`talents` are the loadout and talent-tree surfaces.)
    #[test]
    fn the_previously_stranded_buttons_route() {
        for key in [
            "bazaar",
            "descent-campaign",
            "private-raid",
            "quest",
            "gear",
            "talents",
            "overworld",
            "descent",
        ] {
            assert!(
                routes(key),
                "`{key}` ships a re-verify button that must fire"
            );
        }
    }

    /// A key from no surface at all is REFUSED, not dropped: the router falls through to an
    /// honest ephemeral rather than returning without answering the interaction.
    #[test]
    fn an_unknown_key_is_not_claimed_as_routed() {
        assert!(!routes("not-an-offering"));
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
