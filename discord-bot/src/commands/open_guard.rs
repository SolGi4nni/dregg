//! **The live-session wipe guard** — refuse-with-confirm for every offering `open` (backlog
//! 2026-07-17 #32).
//!
//! `offering::open_in` replaces any session already open in the channel; before this module a
//! bare `/market open` mid-auction (or any `/play <offering>` re-open) silently nuked another
//! user's live chain — sealed bids, seats, receipts gone, with only an after-the-fact "Note".
//!
//! Now every open path first checks for a live session. If one exists, the open is **refused**
//! and the would-be replacement is stashed as a pending closure behind a Confirm/Cancel card;
//! only the requester's explicit **Confirm** press runs it (and re-renders the fresh surface),
//! **Cancel** keeps the live session. Sessions are per-channel and process-local, so the
//! pending table is a plain in-memory map keyed by channel (a restart clears both — honestly).
//!
//! Custom-id wire (routed here by `commands::dashboard::handle_component`, which receives
//! every unprefixed component press from `main.rs`):
//!
//! | id                  | meaning                                    |
//! |---------------------|--------------------------------------------|
//! | `openguard:confirm` | run this channel's pending replacement open |
//! | `openguard:cancel`  | drop it — keep the live session             |

use std::collections::HashMap;
use std::sync::Mutex;

use serenity::all::{
    ButtonStyle, CommandInteraction, ComponentInteraction, Context, CreateActionRow, CreateButton,
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use crate::embeds;

/// The Confirm button id.
pub const ID_CONFIRM: &str = "openguard:confirm";
/// The Cancel button id.
pub const ID_CANCEL: &str = "openguard:cancel";
/// The custom-id namespace (dashboard forwards on it).
pub const PREFIX: &str = "openguard:";

/// A stashed replacement open: runs the real `offering::open_in` + re-render, all type-erased
/// so ONE pending table serves every offering type. Returns the fresh surface or the
/// executor's own refusal.
pub type PendingOpenFn =
    Box<dyn FnOnce() -> Result<(CreateEmbed, Vec<CreateActionRow>), String> + Send>;

struct Pending {
    key: String,
    requested_by: u64,
    open: PendingOpenFn,
}

fn pending() -> &'static Mutex<HashMap<u64, Pending>> {
    static PENDING: std::sync::OnceLock<Mutex<HashMap<u64, Pending>>> = std::sync::OnceLock::new();
    PENDING.get_or_init(|| Mutex::new(HashMap::new()))
}

/// **Refuse a live-session replacement and stash the pending open.** The caller has already
/// established a live session of `key` exists in the command's channel; this responds with the
/// refuse-with-confirm card and parks `open` for the Confirm press.
pub async fn refuse_with_confirm(
    ctx: &Context,
    command: &CommandInteraction,
    key: &str,
    status_line: Option<String>,
    open: PendingOpenFn,
) {
    let channel = command.channel_id.get();
    let requested_by = command.user.id.get();
    pending().lock().expect("open-guard pending table").insert(
        channel,
        Pending {
            key: key.to_string(),
            requested_by,
            open,
        },
    );

    let mut embed = embeds::warning_embed(
        &format!("A live {key} session is already open here"),
        &format!(
            "Opening a new one would **wipe it** — its moves and receipts are process-local and \
             unrecoverable. Press **Replace it** to confirm (only <@{requested_by}> can), or \
             **Keep it** to leave the live session untouched."
        ),
    );
    if let Some(status) = status_line {
        embed = embed.field("Live session", status, false);
    }
    let rows = vec![CreateActionRow::Buttons(vec![
        CreateButton::new(ID_CONFIRM)
            .label("Replace it")
            .style(ButtonStyle::Danger),
        CreateButton::new(ID_CANCEL)
            .label("Keep it")
            .style(ButtonStyle::Secondary),
    ])];
    // Defer-aware: some callers (`/play`) ACK inside the 3s window BEFORE reaching the guard,
    // in which case create_response errors ("already acknowledged") and the card must land as
    // an EDIT of the deferred response instead.
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed.clone())
        .components(rows.clone());
    if command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await
        .is_err()
    {
        let _ = command
            .edit_response(
                &ctx.http,
                serenity::all::EditInteractionResponse::new()
                    .embed(embed)
                    .components(rows),
            )
            .await;
    }
}

/// The outcome of trying to claim a channel's pending replacement.
enum Claim {
    /// The presser owns the ask — here is the pending open, removed from the table.
    Taken(Pending),
    /// Someone else's ask is pending; the presser may not decide it.
    NotYours,
    /// Nothing is pending in this channel.
    Nothing,
}

/// Atomically claim (and remove) the channel's pending open if `presser` made the ask.
fn claim(channel: u64, presser: u64) -> Claim {
    let mut table = pending().lock().expect("open-guard pending table");
    match table.get(&channel).map(|p| p.requested_by == presser) {
        Some(true) => Claim::Taken(table.remove(&channel).expect("present under the same lock")),
        Some(false) => Claim::NotYours,
        None => Claim::Nothing,
    }
}

/// Route an `openguard:` press (Confirm/Cancel), always ACKing (backlog #31).
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction) {
    let channel = component.channel_id.get();
    let presser = component.user.id.get();
    let id = component.data.custom_id.as_str();

    match id {
        ID_CANCEL => {
            let text = match claim(channel, presser) {
                Claim::Taken(p) => format!(
                    "Kept the live {} session — the replacement was discarded.",
                    p.key
                ),
                Claim::NotYours => {
                    return ephemeral(
                        ctx,
                        component,
                        "Only the user who asked to replace the session can cancel that ask.",
                    )
                    .await;
                }
                Claim::Nothing => {
                    "Nothing pending here (a restart clears pending replacements).".to_string()
                }
            };
            update_plain(ctx, component, &text).await;
        }
        ID_CONFIRM => {
            let p = match claim(channel, presser) {
                Claim::Taken(p) => p,
                Claim::NotYours => {
                    return ephemeral(
                        ctx,
                        component,
                        "Only the user who asked to replace the session can confirm the wipe.",
                    )
                    .await;
                }
                Claim::Nothing => {
                    return update_plain(
                        ctx,
                        component,
                        "Nothing pending here (a restart clears pending replacements) — \
                         re-run the open command.",
                    )
                    .await;
                }
            };
            // Run the real open (one short store-thread job) and post the fresh surface.
            match (p.open)() {
                Ok((embed, rows)) => {
                    let msg = CreateInteractionResponseMessage::new()
                        .content(format!(
                            "**Replaced.** The previous {} session's chain is gone; this is a \
                             fresh one.",
                            p.key
                        ))
                        .embed(embed)
                        .components(rows);
                    let _ = component
                        .create_response(&ctx.http, CreateInteractionResponse::UpdateMessage(msg))
                        .await;
                }
                Err(e) => {
                    update_plain(
                        ctx,
                        component,
                        &format!(
                            "The replacement refused to open ({e}) — the previous session, if \
                             still live, was not touched."
                        ),
                    )
                    .await;
                }
            }
        }
        _ => {
            ephemeral(ctx, component, "This open-guard control is not recognized.").await;
        }
    }
}

async fn update_plain(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let msg = CreateInteractionResponseMessage::new()
        .content(text.to_string())
        .embeds(vec![])
        .components(vec![]);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::UpdateMessage(msg))
        .await;
}

async fn ephemeral(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let msg = CreateInteractionResponseMessage::new()
        .content(text.to_string())
        .ephemeral(true);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}
