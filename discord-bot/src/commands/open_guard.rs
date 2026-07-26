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

use crate::commands::ack;
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

/// ⚑ **RESTART: PROCEED, deliberately** (`docs/reference/RESTART-SEMANTICS.md`). A parked
/// replacement-open holds a `PendingOpenFn` — a live closure over this process's offering store
/// — so it is not merely un-persisted, it is UNPERSISTABLE. Empty at boot means a Confirm button
/// left over from before the restart finds nothing and is refused; the requester re-runs the
/// command. Absence here refuses, and the thing it refuses is the destructive half (replacing a
/// live session), so a forced restart can only cost a click.
fn pending() -> &'static Mutex<HashMap<u64, Pending>> {
    static PENDING: std::sync::OnceLock<Mutex<HashMap<u64, Pending>>> = std::sync::OnceLock::new();
    PENDING.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Park a channel's pending replacement open under the requester's id (the table write behind
/// [`refuse_with_confirm`], split out so the tests can drive the real Confirm job).
fn stash(channel: u64, requested_by: u64, key: &str, open: PendingOpenFn) {
    pending().lock().expect("open-guard pending table").insert(
        channel,
        Pending {
            key: key.to_string(),
            requested_by,
            open,
        },
    );
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
    stash(channel, requested_by, key, open);

    let mut embed = embeds::warning_embed(
        &format!("A live {key} session is already open here"),
        &format!(
            "Opening a new one would **wipe it**: its moves and receipts are process-local and \
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
///
/// # Confirm is a WIPE, so it answers FIRST
///
/// The Confirm arm used to `claim()` the pending open and RUN it — replacing a live session,
/// destroying its moves and receipts — and only then send its first Discord response. Every one of
/// those steps is inside the 3-second interaction window, and `(p.open)()` is a real offering
/// deploy on a store thread other players' moves also queue on. Losing that race is the worst
/// shape in this file: the chain is **gone**, the pending entry is **gone** (claimed), and the
/// presser is shown "This interaction failed" — a phrase that means *nothing happened* — with a
/// re-press answering "Nothing pending here". Somebody's game is deleted and the bot's last word
/// about it is a lie.
///
/// The confirm itself was never the missing piece: **this press IS the confirmation**
/// ([`refuse_with_confirm`] already refused the bare open and parked it behind this button; every
/// production open path in the bot routes through it, so there is no unconfirmed wipe), and a
/// second Are-you-sure would be ceremony, not safety. What was missing is that the answer must be
/// guaranteed BEFORE the wipe, and the wipe must not run on the async worker — so the Confirm arm
/// goes through [`ack::ack_component_then`], and a job the blocking pool drops is reported as
/// exactly that instead of being rendered as a success. **Cancel** keeps its direct response: it
/// touches only the in-memory pending table (one mutex lookup) and runs nothing.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction) {
    let channel = component.channel_id.get();
    let presser = component.user.id.get();
    let id = component.data.custom_id.as_str();

    match id {
        ID_CONFIRM => {
            // ACK, THEN WIPE — and the wipe runs on the blocking pool, never on the async
            // worker (`(p.open)()` bottoms out in a `sync_channel` `recv()` against the
            // offering's store thread).
            let done =
                ack::ack_component_then(ctx, component, move || confirm_job(channel, presser))
                    .await;

            match done {
                Some(Confirmed::Replaced { key, embed, rows }) => {
                    ack::edit_component_full(
                        ctx,
                        component,
                        &format!(
                            "**Replaced.** The previous {key} session's chain is gone; this is a \
                             fresh one."
                        ),
                        Some(*embed),
                        rows,
                    )
                    .await;
                }
                Some(Confirmed::Refused { key, why }) => {
                    edit_plain(
                        ctx,
                        component,
                        &format!(
                            "The replacement {key} session refused to open ({why}); the previous \
                             session, if still live, was not touched."
                        ),
                    )
                    .await;
                }
                Some(Confirmed::NotYours) => {
                    ack::followup_ephemeral(
                        ctx,
                        component,
                        "Only the user who asked to replace the session can confirm the wipe.",
                    )
                    .await;
                }
                Some(Confirmed::Nothing) => {
                    edit_plain(
                        ctx,
                        component,
                        "Nothing pending here (a restart clears pending replacements). \
                         Re-run the open command.",
                    )
                    .await;
                }
                // NEVER render a dropped job as a wipe that worked. The pending entry was
                // claimed inside the job, so it is gone either way; say so rather than
                // implying a fresh session is live.
                None => {
                    edit_plain(
                        ctx,
                        component,
                        "The replacement could not be run (the offering service dropped the \
                         job). Nothing here is trustworthy to report as replaced. Re-run the \
                         open command and check `status` before playing on.",
                    )
                    .await;
                }
            }
        }
        ID_CANCEL => {
            let text = match claim(channel, presser) {
                Claim::Taken(p) => format!(
                    "Kept the live {} session; the replacement was discarded.",
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
        _ => {
            ephemeral(ctx, component, "This open-guard control is not recognized.").await;
        }
    }
}

/// What the Confirm job did — the whole outcome, computed on the blocking pool and carried back
/// as plain data so the async side does nothing but paint it.
enum Confirmed {
    /// The wipe ran and the fresh surface rendered.
    Replaced {
        key: String,
        /// Boxed: a `CreateEmbed` is large, and this enum is returned by value.
        embed: Box<CreateEmbed>,
        rows: Vec<CreateActionRow>,
    },
    /// The replacement itself refused to open — the previous session, if live, was untouched.
    Refused { key: String, why: String },
    /// Someone else's ask is pending here.
    NotYours,
    /// Nothing was pending (a restart clears the table).
    Nothing,
}

/// **The whole Confirm press, as one blocking job.** Claim the channel's pending replacement
/// (atomically, so two simultaneous presses cannot both wipe), run it, and hand back plain data.
///
/// Sync and `Send`, which is exactly what lets it run through [`ack::ack_component_then`]: the
/// interaction is answered first and this never touches the async worker. Named (not an inline
/// closure) so the tests can drive the real job — including a deliberately slow one — rather than
/// a re-typed imitation of it.
fn confirm_job(channel: u64, presser: u64) -> Confirmed {
    let p = match claim(channel, presser) {
        Claim::Taken(p) => p,
        Claim::NotYours => return Confirmed::NotYours,
        Claim::Nothing => return Confirmed::Nothing,
    };
    match (p.open)() {
        Ok((embed, rows)) => Confirmed::Replaced {
            key: p.key,
            embed: Box::new(embed),
            rows,
        },
        Err(why) => Confirmed::Refused { key: p.key, why },
    }
}

/// Land a one-line answer as an EDIT of an already-ACKed press (the deferred-update counterpart
/// of [`update_plain`]): the card collapses to the sentence, embeds and buttons cleared.
async fn edit_plain(ctx: &Context, component: &ComponentInteraction, text: &str) {
    ack::edit_component_full(ctx, component, text, None, Vec::new()).await;
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    fn a_card() -> Result<(CreateEmbed, Vec<CreateActionRow>), String> {
        Ok((CreateEmbed::new().title("fresh session"), Vec::new()))
    }

    /// **THE WIPE ANSWERS FIRST, EVEN WHEN IT IS SLOW.**
    ///
    /// This drives the REAL Confirm job ([`confirm_job`]) through the REAL ordering helper the
    /// handler uses, with an open that takes 3.5s — past Discord's 3-second interaction window,
    /// which is what a contended offering store thread actually looks like. Under the old
    /// ordering (`claim()`, `(p.open)()`, *then* the first response) the wipe had destroyed a live
    /// session's receipt chain and consumed the pending entry before Discord ever heard from us:
    /// the player saw "This interaction failed" over a game that no longer existed, and a second
    /// press answered "Nothing pending here".
    ///
    /// The assertion is the ordering itself: the ACK is recorded BEFORE the open runs, and the
    /// open still completes. Revert the handler to work-first and the recorded trace inverts.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_slow_wipe_is_answered_before_it_destroys_anything() {
        let channel = 0xA4_0001;
        let presser = 777;
        let trace: Arc<std::sync::Mutex<Vec<&'static str>>> =
            Arc::new(std::sync::Mutex::new(Vec::new()));

        let open_trace = Arc::clone(&trace);
        stash(
            channel,
            presser,
            "market",
            Box::new(move || {
                // The wipe: on the real path this is `offering::open_in`, a store-thread job
                // every other player's move also queues on.
                std::thread::sleep(std::time::Duration::from_millis(3_500));
                open_trace.lock().unwrap().push("wiped");
                a_card()
            }),
        );

        let ack_trace = Arc::clone(&trace);
        let done = super::ack::testing::ack_then_blocking_for_test(
            async move {
                tokio::task::yield_now().await;
                ack_trace.lock().unwrap().push("acked");
            },
            move || confirm_job(channel, presser),
        )
        .await;

        assert!(
            matches!(done, Some(Confirmed::Replaced { .. })),
            "the confirmed replacement must still run to completion"
        );
        assert_eq!(
            trace.lock().unwrap().as_slice(),
            ["acked", "wiped"],
            "the receipt chain was destroyed before Discord was told anything — lose that race \
             and the player's game is gone with no message explaining why"
        );
    }

    /// The press IS the confirmation, and it is single-use: the claim and the wipe are ONE
    /// atomic job, so a second Confirm (a double-click, a second player on the same card) finds
    /// nothing pending and cannot wipe the freshly-opened session too.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_confirmed_wipe_cannot_be_replayed() {
        let channel = 0xA4_0002;
        let presser = 778;
        let opened_twice = Arc::new(AtomicBool::new(false));
        let ran_once = Arc::new(AtomicBool::new(false));

        let (a, b) = (Arc::clone(&ran_once), Arc::clone(&opened_twice));
        stash(
            channel,
            presser,
            "council",
            Box::new(move || {
                if a.swap(true, Ordering::SeqCst) {
                    b.store(true, Ordering::SeqCst);
                }
                a_card()
            }),
        );

        assert!(matches!(
            confirm_job(channel, presser),
            Confirmed::Replaced { .. }
        ));
        assert!(matches!(confirm_job(channel, presser), Confirmed::Nothing));
        assert!(
            !opened_twice.load(Ordering::SeqCst),
            "one confirmation must wipe at most once"
        );
    }

    /// Only the user who ASKED may confirm the wipe — and a refused press must not consume the
    /// pending entry, or a bystander's click would silently cancel the real requester's ask.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_bystander_can_neither_wipe_nor_consume_the_ask() {
        let channel = 0xA4_0003;
        let (requester, bystander) = (779, 780);
        let opened = Arc::new(AtomicBool::new(false));

        let flag = Arc::clone(&opened);
        stash(
            channel,
            requester,
            "doc",
            Box::new(move || {
                flag.store(true, Ordering::SeqCst);
                a_card()
            }),
        );

        assert!(matches!(
            confirm_job(channel, bystander),
            Confirmed::NotYours
        ));
        assert!(
            !opened.load(Ordering::SeqCst),
            "a bystander's press ran the wipe"
        );
        assert!(
            matches!(confirm_job(channel, requester), Confirmed::Replaced { .. }),
            "the requester's own ask must survive a bystander's press"
        );
    }

    /// A replacement that REFUSES to open is reported as a refusal — the previous session, if
    /// still live, was never touched, and the surface must not claim a fresh one exists.
    #[test]
    fn a_refused_replacement_says_so() {
        let channel = 0xA4_0004;
        let presser = 781;
        stash(
            channel,
            presser,
            "grain",
            Box::new(|| Err("the cell exceeded its computron budget".to_string())),
        );
        match confirm_job(channel, presser) {
            Confirmed::Refused { key, why } => {
                assert_eq!(key, "grain");
                assert!(why.contains("computron"), "{why}");
            }
            _ => panic!("a refusing open must come back as Refused, never as Replaced"),
        }
    }
}
