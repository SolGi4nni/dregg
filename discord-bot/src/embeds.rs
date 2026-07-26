//! Rich embed builders for Discord messages — **and this surface's two shared refusal sentences.**
//!
//! The copy lives beside the builders because the audit's finding was that copy re-typed at a call
//! site drifts: one condition wore twelve wordings in `commands/` alone. The *stem* of each sentence
//! is [`dreggnet_offerings::refusal`]'s, shared with the web, Telegram and the game engines; what this
//! module adds is the clause naming the control a DISCORD reader actually has.

use serenity::all::CreateEmbed;

/// Brand color for dregg embeds (a nice teal).
const DREGG_COLOR: u32 = 0x00B4D8;
/// Error color (red).
const ERROR_COLOR: u32 = 0xE63946;
/// Success color (green).
const SUCCESS_COLOR: u32 = 0x2A9D8F;
/// Warning color (amber).
const WARNING_COLOR: u32 = 0xE9C46A;

/// Create a standard dregg-branded embed.
pub fn dregg_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .color(DREGG_COLOR)
        .footer(serenity::all::CreateEmbedFooter::new("dregg devnet"))
}

/// Create a success embed.
pub fn success_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .color(SUCCESS_COLOR)
        .footer(serenity::all::CreateEmbedFooter::new("dregg devnet"))
}

/// Create an error embed.
pub fn error_embed(title: &str, description: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(description)
        .color(ERROR_COLOR)
}

/// Create a warning embed.
#[allow(dead_code)]
pub fn warning_embed(title: &str, description: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(description)
        .color(WARNING_COLOR)
}

/// **This surface's `next_step` clause** for [`dreggnet_offerings::refusal::stale_control`]. A Discord
/// message cannot be reloaded, so the working controls are the newest message for this thing and the
/// command that mints one.
const DISCORD_NEXT_STEP: &str =
    "Use the buttons on the newest message for this, or run the command again to get a fresh one.";

/// ⚑ **THE STALE-CONTROL SENTENCE for this surface** — one condition, one wording, ~12 call sites.
///
/// Discord had the widest spread of the audit's worst meta-pattern. A press or submit whose
/// `custom_id` this process cannot route was answered by twelve hand-written strings ("That button is
/// from a stale surface this bot build no longer decodes.", "This control isn't recognised by this bot
/// build.", "This menu destination isn't recognised by this bot build.", "No offering with key `x` is
/// mounted in this bot build.", …), and every one of them made the same two mistakes:
///
/// - **"this bot build" is DEPLOYMENT language.** It describes our release process, which the reader
///   has no access to and no interest in — and by framing the answer as a property of the build, it
///   frames the reader's own screen as the problem rather than as merely out of date.
/// - **Most of them gave no next action**, so the press read as the bot being broken.
///
/// The shared stem says what actually happened (this control is not one the live surface offers) and
/// that nothing was changed; the clause says which control does work.
pub fn stale_control_text() -> String {
    dreggnet_offerings::refusal::stale_control(DISCORD_NEXT_STEP)
}

/// ⚑ **THE ONE ANSWER FOR "WE COULD NOT REACH OUR OWN RECORDS"** — the replacement for ~30 sites
/// spelled `error_embed("Database Error", &e.to_string())`.
///
/// Those thirty pasted raw `sqlx` text into a player's embed ("Database Error: error returned from
/// database: database is locked"), and the jargon was the *smaller* problem. **None of them said
/// whether anything was lost** — the one rule this house style otherwise never breaks. A player told
/// "database is locked" after pressing *transfer* has no way to know whether their DEC moved.
///
/// Every site this replaces is a read or a pre-flight check with no mutation behind it, so the
/// sentence can promise what it promises. `#[track_caller]` puts the refusing call site in the log
/// line, which is where the `sqlx` text belongs and where it now goes — the detail is not lost, it is
/// filed with the audience that can act on it.
///
/// ⚑ NOT for a failure *after* a mutation. A site that cannot honestly say "nothing was changed" must
/// say what it does know instead; `pay.rs`'s explicit "this is NOT a zero" copy is the model.
#[track_caller]
pub fn store_unavailable_embed(error: &dyn std::fmt::Display) -> CreateEmbed {
    let at = std::panic::Location::caller();
    tracing::error!(
        target: "dregg::refusal",
        at = %at,
        detail = %error,
        "a store read failed; the player was shown the generic store-failure sentence and nothing \
         was changed"
    );
    CreateEmbed::new()
        .title("Something went wrong")
        .description(dreggnet_offerings::refusal::STORE_FAILED_NOTHING_CHANGED)
        .color(ERROR_COLOR)
}
