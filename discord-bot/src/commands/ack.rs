//! Deferred-ACK helpers for the GAME interaction paths — the fix for the most dangerous
//! bot bug (BOT-EXCELLENCE-BACKLOG-2026-07-17 Tier-1 #1): a game press used to commit a
//! permadeath turn on-chain, THEN await the narrator (up to ~20s) before the FIRST Discord
//! ACK. Discord's 3-second interaction window blew, and the player saw "This interaction
//! failed" — on a move that permanently landed.
//!
//! The discipline these helpers carry (every path that commits a turn adopts it):
//! 1. **ACK first** ([`defer_slash`] / [`ack_component`] / [`defer_component_ephemeral`] /
//!    [`defer_modal`]) — inside the 3s window, BEFORE the commit and BEFORE any network work;
//! 2. **commit the turn** ([`work_after`] on a blocking thread, [`async_work_after`] for an RPC);
//! 3. **EDIT the deferred response** ([`edit_slash`] / [`edit_component`] / [`edit_modal`]) with
//!    the re-render — a slow narrator now only delays prose; it can never falsify the outcome.
//!
//! **It is a TYPE now, not a discipline.** A discipline is something six handlers forgot: a real
//! on-chain governance vote, a match fold on the proving pool, a modal-typed turn, a live
//! session's receipt chain WIPED, a council cell deployed, and an RPC that credits money all ran
//! BEFORE their first response. So the work handles take an [`Acked`] — a witness only an ACK can
//! mint — and the `*_then` helpers ([`ack_component_then`], [`defer_slash_then`],
//! [`defer_modal_then`], [`defer_slash_then_async`]) take the job as an ARGUMENT, so a call site
//! cannot put it first. Losing the race never *delays* work; it ORPHANS it — the work landed, and
//! the user is shown "This interaction failed", the one message that means nothing happened.
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

use std::future::Future;

use serenity::all::{
    CommandInteraction, ComponentInteraction, Context, CreateActionRow, CreateEmbed,
    CreateInteractionResponse, CreateInteractionResponseFollowup, CreateInteractionResponseMessage,
    EditInteractionResponse, ModalInteraction,
};

// ─────────────────────────────────────────────────────────────────────────────
// ACK-THEN-WORK, as a TYPE rather than a discipline.
// ─────────────────────────────────────────────────────────────────────────────

/// **A witness that this interaction has already been ANSWERED** inside Discord's 3-second window.
///
/// It has a private field, so the only way to obtain one is to await [`defer_slash`],
/// [`ack_component`], [`defer_component_ephemeral`] or [`defer_modal`] — and [`work_after`] /
/// [`async_work_after`], the handles the repaired sites run their irreversible job through, take
/// one by reference. So "commit the turn, THEN ack" is not a rule a call site has to remember:
/// it does not typecheck.
///
/// Why that matters concretely, and it is not hypothetical — a survey of the live bot found six
/// handlers doing the work first, and losing the race there does not delay the work, it ORPHANS
/// it: a real on-chain governance vote, a match fold enqueued on the proving pool, a modal-typed
/// turn, a live session's receipt chain WIPED, a council cell deployed, and an RPC that credits
/// money. Each of them landed, and each of them then showed the user **"This interaction
/// failed"** — the one message that means "nothing happened".
pub struct Acked(());

/// Run a **blocking, irreversible** job after the interaction was answered — on a blocking thread,
/// never on the async worker.
///
/// The `&Acked` is the whole point (see [`Acked`]). The `spawn_blocking` is the other half: every
/// one of these jobs ends in a `sync_channel` `rx.recv()` against a store thread that owns
/// `!Send` sessions (`offering::Store::run`, `crown::run`), so calling it inline parks a Tokio
/// worker for the length of a real executor turn — and *that* latency lands on every other
/// in-flight interaction's 3-second clock at once.
///
/// `None` means the blocking pool dropped the job (a panic inside it, or runtime shutdown); the
/// caller reports that honestly rather than pretending the work succeeded.
pub async fn work_after<T: Send + 'static>(
    _acked: &Acked,
    job: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    tokio::task::spawn_blocking(job).await.ok()
}

/// The already-async counterpart of [`work_after`] — an RPC or a database write needs no blocking
/// thread, but it still must not run before the interaction is answered.
pub async fn async_work_after<F: Future>(_acked: &Acked, job: F) -> F::Output {
    job.await
}

/// The ordering itself, factored out of the concrete Discord types so a test can drive it: ACK
/// (await it to completion), and only then hand the job to the blocking pool. Every `*_then`
/// helper below is a one-line wrapper over this, so there is exactly ONE place the order lives.
async fn ack_then_blocking<A, T: Send + 'static>(
    ack: impl Future<Output = A>,
    job: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    let _acked: A = ack.await;
    tokio::task::spawn_blocking(job).await.ok()
}

/// The already-async twin of [`ack_then_blocking`], for work that is a future rather than a
/// blocking job (an RPC, a database write): ACK to completion, and only then poll the job. Futures
/// are lazy, so constructing `job` at the call site does not start it — the `await` here does.
async fn ack_then_async<A, F: Future>(ack: impl Future<Output = A>, job: F) -> F::Output {
    let _acked: A = ack.await;
    job.await
}

/// [`defer_slash`] then the async job, as one call.
pub async fn defer_slash_then_async<F: Future>(
    ctx: &Context,
    command: &CommandInteraction,
    ephemeral: bool,
    job: F,
) -> F::Output {
    ack_then_async(defer_slash(ctx, command, ephemeral), job).await
}

/// The ordering helpers, reachable from the OTHER modules' tests so a repaired site can be driven
/// through the very function its handler runs — never a re-typed imitation of it. Test-only on
/// purpose: a real call site must not be able to hand these a fake ACK.
///
/// These are thin wrappers, not `use` re-exports: a private item cannot be re-exported at wider
/// visibility (E0364), but a CHILD module may call it — so the ordering functions stay private to
/// production code while the tests still drive the real ones.
#[cfg(test)]
pub(crate) mod testing {
    use std::future::Future;

    pub(crate) async fn ack_then_blocking_for_test<A, T: Send + 'static>(
        ack: impl Future<Output = A>,
        job: impl FnOnce() -> T + Send + 'static,
    ) -> Option<T> {
        super::ack_then_blocking(ack, job).await
    }

    pub(crate) async fn ack_then_async_for_test<A, F: Future>(
        ack: impl Future<Output = A>,
        job: F,
    ) -> F::Output {
        super::ack_then_async(ack, job).await
    }
}

/// ACK a slash command with a deferred ("thinking…") response — call BEFORE committing a turn
/// or narrating. `ephemeral` fixes the final message's visibility once and for all (Discord
/// decides it at defer time; the later edit cannot change it).
pub async fn defer_slash(ctx: &Context, command: &CommandInteraction, ephemeral: bool) -> Acked {
    let mut msg = CreateInteractionResponseMessage::new();
    if ephemeral {
        msg = msg.ephemeral(true);
    }
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Defer(msg))
        .await;
    Acked(())
}

/// [`defer_slash`] then [`work_after`], as one call — the shape a slash command whose work is a
/// blocking store-thread job takes, with no way to invert the two.
pub async fn defer_slash_then<T: Send + 'static>(
    ctx: &Context,
    command: &CommandInteraction,
    ephemeral: bool,
    job: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    ack_then_blocking(defer_slash(ctx, command, ephemeral), job).await
}

/// [`ack_component`] then [`work_after`], as one call.
pub async fn ack_component_then<T: Send + 'static>(
    ctx: &Context,
    component: &ComponentInteraction,
    job: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    ack_then_blocking(ack_component(ctx, component), job).await
}

/// [`defer_modal`] then [`work_after`], as one call.
pub async fn defer_modal_then<T: Send + 'static>(
    ctx: &Context,
    modal: &ModalInteraction,
    job: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    ack_then_blocking(defer_modal(ctx, modal), job).await
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
pub async fn ack_component(ctx: &Context, component: &ComponentInteraction) -> Acked {
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Acknowledge)
        .await;
    Acked(())
}

/// ACK a component press with a deferred **ephemeral** answer to the PRESSER, leaving the pressed
/// message untouched. The counterpart of [`ack_component`] for rule 3 (a message about one
/// person's press): a press whose whole answer is private — a vote receipt, a balance — defers
/// like this and lands the real embed through [`edit_component`], which is what the presser sees.
pub async fn defer_component_ephemeral(ctx: &Context, component: &ComponentInteraction) -> Acked {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
    Acked(())
}

/// ACK a **modal submit** — the interaction with the same 3-second clock as a press, and the one
/// most likely to blow it, because a typed move (a bid, a reserve price, a paragraph) resolves a
/// real turn on the store thread before anything is painted.
///
/// A modal opened from a component press carries its origin message, so the deferred UPDATE is
/// legal and a later [`edit_modal`] MUTATES the board the move was typed on (rule 1). A modal
/// reached without one has no board to mutate, so it defers a fresh message instead.
pub async fn defer_modal(ctx: &Context, modal: &ModalInteraction) -> Acked {
    let response = if modal.message.is_some() {
        CreateInteractionResponse::Acknowledge
    } else {
        CreateInteractionResponse::Defer(CreateInteractionResponseMessage::new())
    };
    let _ = modal.create_response(&ctx.http, response).await;
    Acked(())
}

/// Resolve a [`defer_modal`] — EDIT the deferred response (the origin board, or the fresh
/// message) into the typed move's outcome.
pub async fn edit_modal(
    ctx: &Context,
    modal: &ModalInteraction,
    content: &str,
    embed: Option<CreateEmbed>,
    rows: Vec<CreateActionRow>,
) {
    let mut edit = EditInteractionResponse::new()
        .content(content.to_string())
        .components(rows);
    edit = match embed {
        Some(embed) => edit.embed(embed),
        None => edit.embeds(Vec::new()),
    };
    let result = modal.edit_response(&ctx.http, edit).await;
    warn_dropped_edit(&result, "modal", &modal.data.custom_id);
}

/// A one-line private answer after [`defer_modal`], landed the way that submit's deferral
/// requires.
///
/// The two cases are NOT interchangeable, and getting it wrong is visible: a submit that carried
/// an origin board deferred as an UPDATE, so the note must be a followup — editing would blow the
/// board's embed and buttons away. A submit with no board deferred a fresh message, so the note
/// must be that EDIT — a followup would leave the deferred "thinking" message hanging empty
/// forever.
pub async fn note_modal(ctx: &Context, modal: &ModalInteraction, text: &str) {
    if modal.message.is_some() {
        let _ = modal
            .create_followup(
                &ctx.http,
                CreateInteractionResponseFollowup::new()
                    .content(text)
                    .ephemeral(true),
            )
            .await;
    } else {
        edit_modal(ctx, modal, text, None, Vec::new()).await;
    }
}

/// Resolve an [`ack_component`] / [`defer_component_ephemeral`] with a message that carries a
/// leading CONTENT line as well as the re-rendered board — the shape a turn whose outcome is a
/// sentence ("**Replaced.** …", a landed receipt) takes. `embed: None` clears the embeds, which
/// is how a card collapses to a one-line answer.
pub async fn edit_component_full(
    ctx: &Context,
    component: &ComponentInteraction,
    content: &str,
    embed: Option<CreateEmbed>,
    rows: Vec<CreateActionRow>,
) {
    let mut edit = EditInteractionResponse::new()
        .content(content.to_string())
        .components(rows);
    edit = match embed {
        Some(embed) => edit.embed(embed),
        None => edit.embeds(Vec::new()),
    };
    let result = component.edit_response(&ctx.http, edit).await;
    warn_dropped_edit(&result, "component", &component.data.custom_id);
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

/// A PUBLIC followup **message body** after [`ack_component`] — a new in-channel message whose
/// text is plain content, never an embed. This is rule 2 above: the thing that HAPPENED, minted as
/// its own message.
///
/// It exists as a distinct helper from [`followup_embed`] because of one hard Discord behaviour:
/// **a link inside a bot embed is never unfurled.** Discord builds a link preview (the OpenGraph
/// card) only from a URL in a message's `content`. A share link posted as an embed FIELD therefore
/// renders as bare blue text — the run-card's `og:title` / `og:description` are fetched by nobody —
/// which is the same as having no card at all. Anything whose whole job is to be previewed goes
/// here.
pub async fn followup_public(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let _ = component
        .create_followup(
            &ctx.http,
            CreateInteractionResponseFollowup::new().content(text),
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

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Mutex};

    /// **The ordering, driven.** [`super::ack_then_blocking`] is the ONE place the ack-then-work
    /// order lives — every `*_then` helper is a one-line wrapper over it — so this is the test
    /// that goes red the moment somebody reverts a repaired site to "commit the turn, then
    /// answer". Swap the two statements in `ack_then_blocking` and the recorded trace reads
    /// `["work", "ack"]`.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn the_ack_completes_before_the_work_starts() {
        let trace: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));

        let ack_trace = Arc::clone(&trace);
        let ack = async move {
            // A real ACK is an HTTP round-trip to Discord; yield so a work-first ordering has
            // every chance to interleave ahead of it rather than being hidden by an eager future.
            tokio::task::yield_now().await;
            ack_trace.lock().unwrap().push("ack");
        };

        let work_trace = Arc::clone(&trace);
        let done = super::ack_then_blocking(ack, move || {
            work_trace.lock().unwrap().push("work");
            "landed"
        })
        .await;

        assert_eq!(done, Some("landed"));
        assert_eq!(
            trace.lock().unwrap().as_slice(),
            ["ack", "work"],
            "the irreversible job ran before the interaction was answered — losing Discord's 3s \
             race there ORPHANS the work: it happened, and the user is told it failed"
        );
    }

    /// **The amplifier.** The job must not run on the async worker: every one of these jobs ends
    /// in a blocking `rx.recv()` against a store thread, and blocking a worker puts that latency
    /// on every other in-flight interaction's 3-second clock at once. Fails on the old
    /// `let x = drive::<O>(…);` inline shape, which runs on the caller's thread.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn the_work_leaves_the_async_worker() {
        let caller = std::thread::current().id();
        let ran_on = super::ack_then_blocking(async {}, move || std::thread::current().id())
            .await
            .expect("the blocking pool ran the job");
        assert_ne!(
            ran_on, caller,
            "the blocking store-thread job ran ON the async worker — a real executor turn now \
             parks a Tokio worker, and every other interaction's clock pays for it"
        );
    }

    /// A job that PANICS is contained: the helper reports `None` rather than unwinding into the
    /// handler (which would drop the interaction entirely — the failure mode this module exists
    /// to abolish).
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_panicking_job_is_reported_not_propagated() {
        let out: Option<()> =
            super::ack_then_blocking(async {}, || panic!("the store fell over")).await;
        assert!(
            out.is_none(),
            "a panicking job must come back as an honest None"
        );
    }
}
