//! **Public governance proposal cards** — the surface that makes voting possible for anyone
//! but the proposer (backlog 2026-07-17 #5).
//!
//! Before this module, the ONLY route to a vote was the `/dregg` Governance panel's Vote modal,
//! which demands the 64-hex "Prior proposal root" — a value shown once, in the proposer's own
//! EPHEMERAL embed. Collective governance presented as a single-player loop.
//!
//! Now a successful proposal (a) is recorded as durable `starbridge_activity` (app
//! `governance`, action `propose`, with the namespace cell + proposed root in the details), and
//! (b) posts a PUBLIC card to the channel carrying **Vote yes / Vote no buttons** whose
//! custom-id is just the activity row id — a presser never types a root. The Governance panel
//! also gains a **Proposals** button listing the recent proposals (with their full roots, so
//! the modal path still works for anyone) plus per-proposal vote buttons.
//!
//! A vote press is the SAME real signed governance action the modal submits
//! (`build_vote_on_proposal_action` through the presser's derived hosted cipherclerk) — the
//! node stays the referee; this module only closes the discovery gap.
//!
//! Custom-id wire (routed here by `commands::dashboard::handle_component`, which receives every
//! unprefixed component press from `main.rs`):
//!
//! | id                          | meaning                                   |
//! |-----------------------------|-------------------------------------------|
//! | `govprop:list`              | list recent proposals (+ vote buttons)    |
//! | `govprop:vote:yes:<id>`     | cast APPROVE on proposal (activity) `<id>` |
//! | `govprop:vote:no:<id>`      | cast REJECT on proposal (activity) `<id>`  |

use serenity::all::{
    ButtonStyle, ComponentInteraction, Context, CreateActionRow, CreateButton, CreateEmbed,
    CreateInteractionResponse, CreateInteractionResponseMessage, CreateMessage,
};

use starbridge_governed_namespace::{VoteKind, build_vote_on_proposal_action};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::{IdentityMode, StarbridgeActivity};
use crate::embeds;

/// The custom-id namespace of every proposal-card press (dashboard forwards on it).
pub const PREFIX: &str = "govprop:";
/// The Governance panel's proposals-list button id.
pub const ID_LIST: &str = "govprop:list";

/// The durable facts of one submitted proposal — what the public card renders and what a vote
/// press needs back. Built by the dashboard's propose submit; persisted as the activity row.
pub struct ProposalCard {
    /// The `starbridge_activity` row id (the vote buttons' handle).
    pub activity_id: i64,
    /// The governed namespace cell (64 hex).
    pub namespace_cell_hex: String,
    /// The proposed route-table root (64 hex) — the exact "prior proposal root" a vote names.
    pub proposed_root_hex: String,
    /// The human description.
    pub description: String,
    /// The dispute window (heights).
    pub dispute_window: u64,
    /// The proposer's Discord user id.
    pub proposer: u64,
    /// The committed turn hash, when the node reported one.
    pub turn_hash: Option<String>,
}

// ─── Rendering ───────────────────────────────────────────────────────────────

/// The public proposal embed — full root + namespace in copyable blocks, so the card is ALSO
/// enough for the manual `/dregg` Vote-modal path.
pub fn proposal_embed(card: &ProposalCard) -> CreateEmbed {
    embeds::dregg_embed(&format!("Governance Proposal #{}", card.activity_id))
        .description(format!(
            "<@{}> proposed a route-table update. **Anyone with a hosted cipherclerk can vote \
             with the buttons below** — each press casts a real signed governance action; the \
             node is the referee.",
            card.proposer
        ))
        .field(
            "Namespace cell",
            format!("```\n{}\n```", card.namespace_cell_hex),
            false,
        )
        .field(
            "Proposal root (the value a vote names)",
            format!("```\n{}\n```", card.proposed_root_hex),
            false,
        )
        .field("Description", truncate(&card.description, 900), false)
        .field("Dispute window", card.dispute_window.to_string(), true)
        .field(
            "Turn",
            card.turn_hash
                .as_deref()
                .map(|h| format!("`{h}`"))
                .unwrap_or_else(|| "`unknown`".to_string()),
            true,
        )
}

/// The Vote yes / Vote no button row for proposal (activity) `id`.
pub fn vote_rows(activity_id: i64) -> Vec<CreateActionRow> {
    vec![CreateActionRow::Buttons(vec![
        CreateButton::new(format!("govprop:vote:yes:{activity_id}"))
            .label("Vote yes")
            .style(ButtonStyle::Success),
        CreateButton::new(format!("govprop:vote:no:{activity_id}"))
            .label("Vote no")
            .style(ButtonStyle::Danger),
    ])]
}

/// Post the PUBLIC proposal card (embed + vote buttons) to the channel.
pub async fn post_public_card(
    ctx: &Context,
    channel_id: serenity::all::ChannelId,
    card: &ProposalCard,
) {
    let msg = CreateMessage::new()
        .embed(proposal_embed(card))
        .components(vote_rows(card.activity_id));
    let _ = channel_id.send_message(&ctx.http, msg).await;
}

// ─── Component handling ──────────────────────────────────────────────────────

/// Route a `govprop:` press: the proposals list, or a vote cast by activity id.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.as_str();
    if id == ID_LIST {
        handle_list(ctx, component, state).await;
        return;
    }
    if let Some(rest) = id.strip_prefix("govprop:vote:") {
        let (vote, activity_id) = match rest.split_once(':') {
            Some((v @ ("yes" | "no"), n)) => match n.parse::<i64>() {
                Ok(n) => (v, n),
                Err(_) => return ack(ctx, component, "Malformed vote button.").await,
            },
            _ => return ack(ctx, component, "Malformed vote button.").await,
        };
        handle_vote(ctx, component, state, vote, activity_id).await;
        return;
    }
    // Never a silent drop (backlog #31): an unrecognized govprop press says so.
    ack(
        ctx,
        component,
        "This governance control is not recognized by this bot build.",
    )
    .await;
}

/// The Governance panel's **Proposals** press: list recent proposals in this guild, each with
/// its full root (the modal path stays possible) and its own vote buttons (≤4 shown — the
/// Discord component budget).
async fn handle_list(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let guild = component.guild_id.map(|g| g.get().to_string());
    let proposals: Vec<StarbridgeActivity> = state
        .db
        .get_recent_starbridge_activity_for_app("governance", 50)
        .await
        .unwrap_or_default()
        .into_iter()
        .filter(|a| a.action == "propose")
        .filter(|a| match (&guild, &a.guild_id) {
            (Some(g), Some(ag)) => g == ag,
            (None, _) => true,
            (Some(_), None) => false,
        })
        .take(4)
        .collect();

    if proposals.is_empty() {
        let embed = embeds::dregg_embed("Proposals").description(
            "No proposals are on record for this guild yet. Open one with the **New Proposal** \
             button — it posts a public card anyone can vote on.",
        );
        let msg = CreateInteractionResponseMessage::new()
            .embed(embed)
            .ephemeral(true);
        let _ = component
            .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
            .await;
        return;
    }

    let mut desc = String::from(
        "The most recent proposals on record (bot-local record of node-committed actions). \
         Vote with the buttons, or paste a root into the Vote modal.\n",
    );
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for p in &proposals {
        let root = detail(p, "proposed_root").unwrap_or_else(|| "unknown".into());
        let ns = detail(p, "namespace_cell").unwrap_or_else(|| "unknown".into());
        desc.push_str(&format!(
            "\n**#{}** by <@{}> · ns `{}…`\nroot: `{}`\n",
            p.id,
            p.actor_discord_id,
            &ns[..16.min(ns.len())],
            root,
        ));
        rows.push(CreateActionRow::Buttons(vec![
            CreateButton::new(format!("govprop:vote:yes:{}", p.id))
                .label(format!("Yes #{}", p.id))
                .style(ButtonStyle::Success),
            CreateButton::new(format!("govprop:vote:no:{}", p.id))
                .label(format!("No #{}", p.id))
                .style(ButtonStyle::Danger),
        ]));
    }
    let embed = embeds::dregg_embed("Proposals").description(truncate(&desc, 3900));
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(rows)
        .ephemeral(true);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

/// A vote press: load the proposal's durable facts by activity id, build the SAME signed
/// governance action the modal path builds, submit, and report the node's own verdict.
async fn handle_vote(
    ctx: &Context,
    component: &ComponentInteraction,
    state: &BotState,
    vote: &str,
    activity_id: i64,
) {
    let user_id = component.user.id.get();

    // A hosted cipherclerk signs the vote (the same requirement the modal path enforces).
    match state.db.get_user_identity(&user_id.to_string()).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => {}
        Ok(_) => {
            return ack(
                ctx,
                component,
                "Voting signs a real governance action, which needs a hosted identity — \
                 `/cipherclerk create` first.",
            )
            .await;
        }
        Err(e) => return ack(ctx, component, &format!("Database error: {e}")).await,
    }

    let Ok(Some(activity)) = state.db.get_starbridge_activity(activity_id).await else {
        return ack(
            ctx,
            component,
            "That proposal is no longer on record — list current ones with the Proposals button.",
        )
        .await;
    };
    let (Some(ns_hex), Some(root_hex)) = (
        detail(&activity, "namespace_cell"),
        detail(&activity, "proposed_root"),
    ) else {
        return ack(
            ctx,
            component,
            "The proposal record is missing its namespace/root.",
        )
        .await;
    };
    let Some(namespace_cell) = decode32(&ns_hex) else {
        return ack(
            ctx,
            component,
            "The recorded namespace cell does not parse.",
        )
        .await;
    };
    let Some(prior_proposal_root) = decode32(&root_hex) else {
        return ack(ctx, component, "The recorded proposal root does not parse.").await;
    };

    let vote_kind = if vote == "yes" {
        VoteKind::Approve
    } else {
        VoteKind::Reject
    };
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let action = build_vote_on_proposal_action(
        &cclerk.app,
        dregg_app_framework::CellId(namespace_cell),
        prior_proposal_root,
        vote_kind,
        1,
    );

    let guild = component.guild_id.map(|g| g.get().to_string());
    let result = state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!(
                "discord:governance:vote:{vote}:guild:{}",
                guild.as_deref().unwrap_or("dm")
            )),
        )
        .await;

    let embed = match result {
        Ok(result) if result.accepted => {
            let _ = state
                .db
                .record_starbridge_activity(
                    "governance",
                    "vote",
                    &user_id.to_string(),
                    guild.as_deref(),
                    Some(&root_hex),
                    "accepted",
                    serde_json::json!({
                        "proposal_activity_id": activity_id,
                        "vote": vote,
                        "namespace_cell": ns_hex,
                        "turn_hash": result.turn_hash,
                    }),
                )
                .await;
            embeds::success_embed("Vote Submitted")
                .description(format!(
                    "Your **{vote}** vote on proposal #{activity_id} committed."
                ))
                .field(
                    "Turn",
                    result
                        .turn_hash
                        .map(|h| format!("`{h}`"))
                        .unwrap_or_else(|| "`unknown`".to_string()),
                    false,
                )
        }
        Ok(result) => embeds::error_embed(
            "Vote Rejected",
            result
                .error
                .as_deref()
                .unwrap_or("the node rejected the signed governance action"),
        ),
        Err(e) => embeds::error_embed("Node Unreachable", &e.to_string()),
    };
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

// ─── Helpers ────────────────────────────────────────────────────────────────

async fn ack(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let msg = CreateInteractionResponseMessage::new()
        .content(text.to_string())
        .ephemeral(true);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

fn detail(activity: &StarbridgeActivity, key: &str) -> Option<String> {
    serde_json::from_str::<serde_json::Value>(&activity.details_json)
        .ok()?
        .get(key)?
        .as_str()
        .map(str::to_string)
}

fn decode32(hex_str: &str) -> Option<[u8; 32]> {
    hex::decode(hex_str.trim()).ok()?.try_into().ok()
}

fn truncate(value: &str, max: usize) -> String {
    if value.chars().count() <= max {
        value.to_string()
    } else {
        let mut out: String = value.chars().take(max.saturating_sub(1)).collect();
        out.push('…');
        out
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the custom-id wire + the record round-trip. No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// The vote-button ids round-trip through the same parse the component handler uses, and
    /// stay comfortably inside Discord's 100-char custom-id budget.
    #[test]
    fn vote_button_ids_parse_and_fit() {
        for (vote, id) in [("yes", i64::MAX), ("no", 1)] {
            let custom = format!("govprop:vote:{vote}:{id}");
            assert!(custom.len() <= 100, "{custom}");
            let rest = custom.strip_prefix("govprop:vote:").unwrap();
            let (v, n) = rest.split_once(':').unwrap();
            assert_eq!(v, vote);
            assert_eq!(n.parse::<i64>().unwrap(), id);
        }
    }

    /// The details a propose records are exactly what a vote press reads back.
    #[test]
    fn proposal_details_round_trip() {
        let details = serde_json::json!({
            "namespace_cell": "ab".repeat(32),
            "proposed_root": "cd".repeat(32),
            "dispute_window": 1000,
        })
        .to_string();
        let activity = StarbridgeActivity {
            id: 7,
            app: "governance".into(),
            action: "propose".into(),
            actor_discord_id: "1".into(),
            guild_id: Some("2".into()),
            subject: Some("cd".repeat(32)),
            status: "accepted".into(),
            details_json: details,
            timestamp: 0,
        };
        assert_eq!(
            detail(&activity, "namespace_cell").unwrap(),
            "ab".repeat(32)
        );
        assert!(decode32(&detail(&activity, "proposed_root").unwrap()).is_some());
    }
}
