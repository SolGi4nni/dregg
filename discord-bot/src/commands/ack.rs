//! Deferred-ACK helpers for the GAME interaction paths — the fix for the most dangerous
//! bot bug (BOT-EXCELLENCE-BACKLOG-2026-07-17 Tier-1 #1): a game press used to commit a
//! permadeath turn on-chain, THEN await the narrator (up to ~20s) before the FIRST Discord
//! ACK. Discord's 3-second interaction window blew, and the player saw "This interaction
//! failed" — on a move that permanently landed.
//!
//! The discipline these helpers carry (every path that commits a turn adopts it):
//! 1. **ACK first** ([`defer_slash`] / [`ack_component`]) — inside the 3s window, BEFORE the
//!    commit and BEFORE any network narration;
//! 2. **commit the turn** (the store-thread advance);
//! 3. **EDIT the deferred response** ([`edit_slash`] / [`edit_component`]) with the narrated
//!    re-render — a slow narrator now only delays prose; it can never falsify the outcome.
//!
//! A press ACKed with [`ack_component`] (a deferred UPDATE of the pressed message) can still
//! answer ephemerally afterwards via [`followup_ephemeral`] (the no-run / expired cases).
//!
//! One Discord constraint to respect: a modal ([`serenity::all::CreateInteractionResponse::Modal`])
//! must be the FIRST response — a path that may open a modal decides that BEFORE deferring.

use serenity::all::{
    CommandInteraction, ComponentInteraction, Context, CreateActionRow, CreateEmbed,
    CreateInteractionResponse, CreateInteractionResponseFollowup, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

/// ACK a slash command with a deferred ("thinking…") response — call BEFORE committing a turn
/// or narrating. `ephemeral` fixes the final message's visibility once and for all (Discord
/// decides it at defer time; the later edit cannot change it).
pub async fn defer_slash(ctx: &Context, command: &CommandInteraction, ephemeral: bool) {
    let mut msg = CreateInteractionResponseMessage::new();
    if ephemeral {
        msg = msg.ephemeral(true);
    }
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Defer(msg))
        .await;
}

/// Resolve a [`defer_slash`] — EDIT the deferred response into the real embed (+ button rows).
pub async fn edit_slash(
    ctx: &Context,
    command: &CommandInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
) {
    let _ = command
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new().embed(embed).components(rows),
        )
        .await;
}

/// ACK a component press with a deferred UPDATE of the pressed message — call BEFORE
/// committing the turn. The press stops spinning immediately; [`edit_component`] lands the
/// post-turn re-render whenever the narrator finishes.
pub async fn ack_component(ctx: &Context, component: &ComponentInteraction) {
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Acknowledge)
        .await;
}

/// Resolve an [`ack_component`] — EDIT the pressed message into the post-turn render.
pub async fn edit_component(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
) {
    let _ = component
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new().embed(embed).components(rows),
        )
        .await;
}

/// An ephemeral note to the presser AFTER [`ack_component`] (a followup — the deferred update
/// already consumed the interaction response; the pressed message itself is left untouched).
pub async fn followup_ephemeral(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let _ = component
        .create_followup(
            &ctx.http,
            CreateInteractionResponseFollowup::new()
                .content(text)
                .ephemeral(true),
        )
        .await;
}
