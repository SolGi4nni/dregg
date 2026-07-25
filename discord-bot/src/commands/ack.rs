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
//!
//! # THE BOARD IS ONE MESSAGE. THE CHANNEL IS WHAT HAPPENED.
//!
//! A turn-based game read like a program printing at you because every surface here can either
//! MUTATE the message a player is looking at or APPEND a new one, and the choice was being made
//! per call site. It is not a per-call-site choice. It is one rule, and it is about where a thing
//! BELONGS, not about how much output there is:
//!
//! **1. An ordinary turn EDITS the board. Always.**
//! A move, a bid, a vote landing, a tally ticking up, a refusal repainting the same room, the
//! in-flight "your turn is being taken" state — these are not events, they are the board being a
//! different shape than it was a second ago. A board is a LIVE OBJECT the party stares at
//! together; it is not a transcript entry. Ten moves is ONE message that changed ten times.
//! ([`ack_component`] then [`edit_component`]; a modal opened from a press answers with
//! `UpdateMessage` so a typed move edits the board it was typed on.)
//!
//! Editing is also the only way the affordances stay HONEST. Every board carries buttons stamped
//! with the state that minted them, and a stale press is refused. Append a new board and the old
//! one does not go away — it sits there looking playable, with live-styled buttons, and the only
//! way to learn it is dead is to press it and be told so. A board that lies about being
//! actionable is worse than a board that is merely out of date.
//!
//! **2. A NEW message is minted for something that HAPPENED TO SOMEONE.**
//! Not for state — for events with a subject and a past tense, the things a player would scroll
//! back to find tomorrow, or screenshot. A run ending (banked, or dead). A crown: the fold that
//! ranked, with its proof attached. Someone joining the party. A round resolving, with who voted
//! for what. A day's dungeon opening. These EARN their permanence, and they are the reason the
//! channel is worth reading at all — a channel of "the board is now like this" ten times is a
//! log; a channel of "Sen went down four floors and came back with the crown" is a game.
//!
//! **3. A message about ONE PERSON'S PRESS is EPHEMERAL.**
//! "That isn't your run." "You already voted." "That button expired — nothing was committed."
//! "There's no session here." These are answers to one player, and they are the ones that
//! multiply fastest under load: five people fumbling one board is five refusals, and none of
//! them are anybody else's business. They belong to the presser, not to the channel's memory.
//! ([`followup_ephemeral`] after a defer; a direct ephemeral response when nothing was ACKed.)
//!
//! The one deliberate exception is a re-verification report ([`crate::commands::verify_chain`]):
//! it posts PUBLICLY even though one person asked for it, because the entire point is a check
//! anyone can watch happen. Evidence is a channel event. Reassurance is not.
//!
//! **4. Hidden information NEVER rides an edit.**
//! An edit lands on the shared channel surface, so a viewer-projected render must never be what
//! it carries. A hidden-information game edits the viewer-BLIND fog into the board and hands the
//! presser their own projection as an ephemeral followup with NO controls — so every actionable
//! affordance stays on the one shared board and a private view can never leave it stale.
//! ([`followup_ephemeral_surface`]; the decision itself is
//! [`crate::commands::offering::channel_surfaces`], kept pure so tests can inspect exactly what
//! reaches the channel.)

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
    let result = command
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new().embed(embed).components(rows),
        )
        .await;
    warn_dropped_edit(&result, "slash", &command.data.name);
}

/// **A refused board edit must not be invisible.** These edits are the ONLY thing that lands a
/// turn's outcome on screen, and they were all `let _ = …`: when Discord refused one — an embed
/// description over 4096, a 15-minute-expired interaction token, a components payload over the
/// 25-per-message cap — the player was left staring at a board frozen mid-turn, holding buttons
/// that no longer matched the state, and the bot's log said NOTHING. A frozen surface that is
/// also unlogged is the hardest possible bug to report, so the failure gets a line.
pub(crate) fn warn_dropped_edit<T>(result: &serenity::Result<T>, surface: &str, route: &str) {
    if let Err(error) = result {
        tracing::warn!(
            %error,
            surface,
            route,
            "Discord REFUSED the surface edit — the board a player is looking at is now stale \
             and its controls no longer match the committed state"
        );
    }
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
    let result = component
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new().embed(embed).components(rows),
        )
        .await;
    warn_dropped_edit(&result, "component", &component.data.custom_id);
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

/// A PUBLIC followup embed after [`ack_component`] — a new in-channel message (never ephemeral),
/// leaving the pressed message untouched. The public counterpart of [`followup_ephemeral`], for a
/// press whose slow deferred work posts a fresh public result into the channel (a re-verification
/// report, a chain re-check) rather than editing the pressed surface.
pub async fn followup_embed(ctx: &Context, component: &ComponentInteraction, embed: CreateEmbed) {
    let _ = component
        .create_followup(
            &ctx.http,
            CreateInteractionResponseFollowup::new().embed(embed),
        )
        .await;
}

/// Send a single-reader companion surface after a shared message was updated.
///
/// Hidden-information games keep the channel message viewer-blind, then hand
/// the presser their own cards/sealed move here. Discord fixes followup
/// visibility on creation, so this helper always sets `ephemeral(true)` and is
/// the only generic path that accepts a viewer-projected embed.
pub async fn followup_ephemeral_surface(
    ctx: &Context,
    component: &ComponentInteraction,
    text: &str,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
) {
    let _ = component
        .create_followup(
            &ctx.http,
            CreateInteractionResponseFollowup::new()
                .content(text)
                .embed(embed)
                .components(rows)
                .ephemeral(true),
        )
        .await;
}

/// The slash-command form of [`followup_ephemeral_surface`]. The command's
/// original response remains the shared, viewer-blind board; this is the
/// opener's private companion hand/sealed-move view.
pub async fn followup_slash_ephemeral_surface(
    ctx: &Context,
    command: &CommandInteraction,
    text: &str,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
) {
    let _ = command
        .create_followup(
            &ctx.http,
            CreateInteractionResponseFollowup::new()
                .content(text)
                .embed(embed)
                .components(rows)
                .ephemeral(true),
        )
        .await;
}
