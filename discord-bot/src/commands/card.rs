//! `/card` — open your interactive **ViewNode card** inside Discord.
//!
//! Posts the user's tally card (authored once as a `deos_view` [`ViewNode`], rendered
//! to a serenity embed + buttons via the SAME `deos_view::discord` backend the desktop/
//! web/seL4 renderers share). Each button carries its affordance in the component
//! custom-id (`deosturn:<turn>:<arg>`); pressing one fires a REAL cap-gated verified
//! dregg turn and re-renders the card in place — the interactive ViewNode loop, in
//! Discord (`crate::viewnode_applet::handle_deosturn_component`).
//!
//! The card is ephemeral and per-user: each invoking user drives their OWN card cell,
//! its principal bound to their custodial cipherclerk, so the verified turn is cap-gated
//! to the pressing user's dregg identity.

use serenity::all::{
    CommandInteraction, Context, CreateCommand, CreateInteractionResponse,
    CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::viewnode_applet::render_with_footer;

/// Register the `/card` command.
pub fn register() -> CreateCommand {
    CreateCommand::new("card").description(
        "Open your interactive tally card — Discord buttons fire real verified dregg turns",
    )
}

/// Handle `/card` — render + post the user's tally card with its live affordance buttons.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // ACK inside Discord's 3s window FIRST (backlog #31: /card never deferred — a slow render
    // or gateway hiccup showed "This interaction failed"); the card lands as an edit.
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;

    let user_id = command.user.id.get();
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);

    let rendered = state.card_applets.ensure_and_render(user_id, &cclerk);
    let embed = render_with_footer(&rendered);

    let _ = command
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new()
                .embed(embed)
                .components(rendered.card.components),
        )
        .await;
}
