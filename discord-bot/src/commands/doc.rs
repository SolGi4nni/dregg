//! `/doc` — a Discord channel opens a **shared collaborative document**: each edit is one real
//! executor-refereed turn on the `dregg-doc` substrate.
//!
//! The offering is [`dreggnet_doc::DocOffering`], consumed (never re-implemented) through the
//! generic [`crate::commands::offering`] adapter:
//!
//! * **INSERT / SET TITLE / RESOLVE** — the presser types text into a modal; the edit is
//!   desugared into a real `dregg_doc::Patch` and driven through the substrate's SOLE executor
//!   entry ([`ExecutorDrivenDoc::edit`]). An authorized edit lands a genuine finalized
//!   `TurnReceipt` ([`Outcome::Landed`]); an edit by an actor **without the region's edit cap** is
//!   a real **executor** refusal (`TurnError::CapabilityNotHeld`), and an edit that would leave an
//!   **unresolved conflict** is refused by dregg-doc's own conflict semantics — nothing commits
//!   either way (the anti-ghost tooth).
//! * **DELETE / ORDER** — fixed-arg affordances (a live cell / a conflict region).
//! * **`/doc verify`** re-drives the whole edit chain from genesis through the real executor and
//!   checks the document reproduces byte-for-byte at every step (a forged edit fails).
//!
//! The opener is invited as an **editor** (their derived dregg identity holds the region's edit
//! cap); anyone else who presses without the cap is refused **by the executor**, not the bot.

use std::sync::OnceLock;

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dreggnet_doc::{
    DocOffering, DocSession, Role, TURN_INSERT, TURN_RESOLVE_TITLE, TURN_SET_TITLE,
};
use dreggnet_offerings::SessionConfig;

use crate::BotState;
use crate::commands::offering::{
    self, DiscordOffering, Store, TextPrompt, ValuePrompt, identity_of,
};

/// The document brand colour (a paper indigo).
const DOC_COLOR: u32 = 0x4361EE;

impl DiscordOffering for DocOffering {
    const KEY: &'static str = "doc";
    const TITLE: &'static str = "A shared document";
    const COLOR: u32 = DOC_COLOR;
    const TAGLINE: &'static str = "every edit one cap-gated finalized executor turn · a conflict/unauthorized edit refused · replay-verified";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<DocOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    /// The text-carrying edits (insert / set-title / resolve) collect a **free-text string** the
    /// presser types (the affordance wire carries no string payload — it rides the label). Delete
    /// and order-conflict are fixed-arg buttons.
    fn text_prompt(turn: &str) -> Option<TextPrompt> {
        match turn {
            TURN_INSERT => Some(TextPrompt {
                title: "Add to the document",
                label: "The text to insert",
                placeholder: "In the beginning…",
                paragraph: true,
            }),
            TURN_SET_TITLE => Some(TextPrompt {
                title: "Set the document title",
                label: "The title",
                placeholder: "Untitled",
                paragraph: false,
            }),
            TURN_RESOLVE_TITLE => Some(TextPrompt {
                title: "Settle the title clash",
                label: "The settled title (supersedes the clashing values)",
                placeholder: "The agreed title",
                paragraph: false,
            }),
            _ => None,
        }
    }

    fn status_line(&self, session: &DocSession) -> String {
        format!("{} verified edits", session.turns())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register `/doc` (open / status / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("doc")
        .description("Open a shared collaborative document in this channel — each edit one real executor turn")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "open",
            "Open a shared document here (you are its first editor)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show this channel's document: its text, cells, collaborators, and edit affordances",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify the document's whole edit chain by re-driving it from genesis",
        ))
}

/// Route `/doc` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "open" => handle_open(ctx, command, state).await,
        "status" => offering::handle_status::<DocOffering>(ctx, command).await,
        "verify" => offering::handle_verify::<DocOffering>(ctx, command).await,
        _ => {}
    }
}

/// `/doc open` — open a fresh shared document, invite the opener as its first **editor** (their
/// derived dregg identity holds the region's edit cap), and post the surface.
async fn handle_open(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let channel = command.channel_id.get();
    let replaced = offering::is_open::<DocOffering>(channel);
    if let Err(e) = offering::open_in(
        channel,
        DocOffering::new(),
        SessionConfig::with_seed(channel),
    ) {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content(format!("The document did not open: {e}"))
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }
    // Invite the opener as the first editor — their derived identity holds the region edit cap.
    let opener = identity_of(state, command.user.id.get());
    offering::with_live::<DocOffering, _>(channel, move |live| {
        live.session.invite(opener, Role::Editor);
    });

    let rendered = offering::with_live::<DocOffering, _>(channel, |live| {
        offering::surface_of::<DocOffering>(live)
    });
    let Some((mut embed, rows)) = rendered else {
        return;
    };
    if replaced {
        embed = embed.field(
            "Note",
            "This channel's previous document was replaced — a fresh document, an empty chain.",
            false,
        );
    }
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .embed(embed)
                    .components(rows),
            ),
        )
        .await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the `/doc` surface DRIVEN at the logic level (the SAME `offering`
// free-text path a live edit-modal takes), against the REAL dregg-doc substrate.
// No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::{DreggIdentity, Outcome};

    use crate::commands::offering::{Driven, close_in, with_live};

    fn ident(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// Open a document in `channel`, inviting `editor` (holds the edit cap) and `commenter` (does
    /// not) — the SAME roster the executor's cap gate reads.
    fn open(channel: u64, editor: &DreggIdentity, commenter: &DreggIdentity) {
        close_in::<DocOffering>(channel);
        offering::open_in(
            channel,
            DocOffering::new(),
            SessionConfig::with_seed(channel),
        )
        .expect("the document opens");
        let editor = editor.clone();
        let commenter = commenter.clone();
        with_live::<DocOffering, _>(channel, move |live| {
            live.session.invite(editor, Role::Editor);
            live.session.invite(commenter, Role::Commenter);
        });
    }

    /// Drive an insert at anchor `at` through the adapter's free-text path (the modal-submit a
    /// live press takes). `at` is the insert's anchor arg: `0` = the start, `n` = after the n-th
    /// live cell (the tip is `cells.len()` — the always-clean append position).
    fn insert(channel: u64, at: i64, text: &str, who: &DreggIdentity) -> Outcome {
        match offering::drive_text::<DocOffering>(channel, TURN_INSERT, at, text, who.clone()) {
            Driven::Fired(o) => o,
            other => panic!("a doc insert must fire a real turn, got {other:?}"),
        }
    }

    /// The document's current tip (the clean append anchor) — the live cell count.
    fn tip(channel: u64) -> i64 {
        with_live::<DocOffering, _>(channel, |l| l.session.cells().len() as i64).unwrap()
    }

    /// An authorized editor's insert lands a REAL finalized turn; an unauthorized actor's insert
    /// is a real EXECUTOR refusal (`CapabilityNotHeld`); the edit chain re-verifies by re-drive.
    #[test]
    fn an_authorized_edit_lands_and_an_unauthorized_one_is_refused() {
        let channel = 92_301;
        let editor = ident("ed");
        let commenter = ident("c0");
        open(channel, &editor, &commenter);
        assert_eq!(
            with_live::<DocOffering, _>(channel, |l| l.session.turns()).unwrap(),
            0,
            "a fresh document has committed nothing"
        );

        // The editor's insert at the tip (arg 0 on an empty doc) lands a real finalized turn.
        match insert(channel, tip(channel), "In the beginning", &editor) {
            Outcome::Landed { receipt, ended } => {
                assert!(!ended, "a document is never ended");
                assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine finalized turn");
            }
            other => panic!("the editor's insert must land, got {other:?}"),
        }
        assert_eq!(
            with_live::<DocOffering, _>(channel, |l| l.session.turns()).unwrap(),
            1
        );

        // The commenter (no edit cap) tries to insert AT THE CLEAN TIP — so no conflict gate
        // fires first; the EXECUTOR refuses it in-band on the missing edit capability.
        let before = with_live::<DocOffering, _>(channel, |l| l.session.turns()).unwrap();
        match insert(channel, tip(channel), "sneak this in", &commenter) {
            Outcome::Refused(why) => assert!(
                why.contains("capability") || why.to_lowercase().contains("cap"),
                "the executor's own refusal: {why}"
            ),
            other => panic!("a commenter's edit must be a real executor refusal, got {other:?}"),
        }
        assert_eq!(
            with_live::<DocOffering, _>(channel, |l| l.session.turns()).unwrap(),
            before,
            "a refused edit commits nothing (anti-ghost)"
        );

        // The document's whole edit chain re-verifies by re-driving from genesis.
        let report = offering::verify_live::<DocOffering>(channel).expect("a live document");
        assert!(report.verified, "{}", report.detail);
        close_in::<DocOffering>(channel);
    }

    /// An outsider (never invited) is refused too — an outsider gets a real editor cell with NO
    /// region cap, so the edit reaches the executor and is refused there.
    #[test]
    fn an_outsider_edit_is_refused() {
        let channel = 92_302;
        let editor = ident("ed");
        let commenter = ident("c0");
        open(channel, &editor, &commenter);
        insert(channel, tip(channel), "the opening line", &editor);
        let before = with_live::<DocOffering, _>(channel, |l| l.session.turns()).unwrap();
        match insert(channel, tip(channel), "outsider text", &ident("ff")) {
            Outcome::Refused(_) => {}
            other => panic!("an outsider's edit must be refused, got {other:?}"),
        }
        assert_eq!(
            with_live::<DocOffering, _>(channel, |l| l.session.turns()).unwrap(),
            before
        );
        close_in::<DocOffering>(channel);
    }
}
