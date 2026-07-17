//! `/descent tournament` — **the weekly no-cheat bracket over The Descent** (backlog #16).
//!
//! A thin Discord face over the committed [`dreggnet_offerings::descent_tournament`] weld:
//! each round is a fresh beacon-seeded daily descent (the SAME day-world for every
//! competitor that round — fair by construction), and a competitor advances ONLY on a
//! VERIFIED win — their run re-executes to the hoard through ugc-dregg's audited no-cheat
//! gate ([`ugc_dregg::verify_completion`]). The champion is the last verified survivor.
//!
//! **Entry is EARNED, not asserted:** the qualifiers are exactly the players holding a
//! VERIFIED win on the live `/descent` no-cheat board
//! ([`crate::commands::descent::verified_players_by_merit`]) — the board only ever holds
//! gate-verified entries, so qualification is a re-executed fact, not a claim. Seeding is
//! by board merit (fewest verified turns first).
//!
//! ## Honest scope (current resolution)
//!
//! REAL here: the earned entry gate, the beacon-derived bracket seed (today's
//! BLS-pairing-verified drand reveal), verify-gated advancement every round, and the
//! champion. NAMED residuals (the crate names them too): each qualifier's round run is
//! the day's honest winning line **auto-played on their behalf** (live per-round human
//! play needs the weekly scheduler / entry windows the crate leaves to an orchestrator),
//! and the LIVE weekly cadence + a boundary announce cron are the follow-up — this
//! command runs the bracket NOW and announces the standings publicly in the channel.

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommandOption, CreateEmbedFooter,
};

use dreggnet_offerings::descent_tournament::{
    DescentStandings, honest_descender, weekly_descent_tournament,
};

use crate::BotState;
use crate::commands::{ack, descent};
use crate::embeds;

/// The most qualifiers a single bracket seats (a 16-slot bracket = 4 verify-gated rounds).
const MAX_QUALIFIERS: usize = 16;

/// The `tournament` subcommand of `/descent` (mounted by `descent::register`).
pub fn register_option() -> CreateCommandOption {
    CreateCommandOption::new(
        CommandOptionType::SubCommand,
        "tournament",
        "Run this week's verify-gated bracket over the board's VERIFIED winners",
    )
}

/// What one bracket run resolved to — computed off the async loop (the rounds deploy +
/// replay real day-worlds).
struct BracketRun {
    standings: DescentStandings,
    qualifiers: usize,
}

/// Route `/descent tournament`: run the bracket over the board's verified winners and
/// ANNOUNCE the standings publicly in the channel.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let _ = state; // entry comes off the verified board, not the invoker's identity
    // Public defer (the announce): the bracket deploys + replays real day-worlds.
    ack::defer_slash(ctx, command, false).await;

    let run = tokio::task::spawn_blocking(run_bracket)
        .await
        .unwrap_or_else(|e| Err(format!("the tournament task did not complete: {e}")));

    match run {
        Ok(BracketRun {
            standings,
            qualifiers,
        }) => {
            let surface = standings.surface();
            let card = deos_view::discord::render_card(
                "The Descent — Weekly Tournament",
                surface.view(),
                &[],
            );
            let champion = standings
                .champion
                .clone()
                .unwrap_or_else(|| "no champion — nobody posted a verified win".to_string());
            let embed = card
                .embed
                .color(0xB3452E)
                .field("Champion", champion, true)
                .field("Rounds", standings.rounds.to_string(), true)
                .field("Qualifiers", qualifiers.to_string(), true)
                .field(
                    "How this is refereed",
                    "Entry is a VERIFIED win on the `/descent` no-cheat board (re-executed, \
                     never trusted). Every round is a fresh day drawn from today's \
                     beacon-verified seed, and advancement passes ugc-dregg's no-cheat gate: \
                     a forged / incomplete run does NOT advance.",
                    false,
                )
                .field(
                    "Honest scope",
                    "Each qualifier's round run is the day's honest winning line, auto-played \
                     on their behalf (seeded by board merit). Live per-round play, entry \
                     windows, and the weekly boundary cron are the named next resolution.",
                    false,
                )
                .footer(CreateEmbedFooter::new(
                    "seeded by today's BLS-verified drand reveal · every advancement re-verified by replay",
                ));
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
        }
        Err(why) => {
            let embed = embeds::warning_embed("No Tournament Today", &why);
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
        }
    }
}

/// Run the bracket synchronously: earned entrants off the live board, today's verified
/// beacon as the base seed, verify-gated rounds to a champion.
fn run_bracket() -> Result<BracketRun, String> {
    let qualifiers = descent::verified_players_by_merit();
    if qualifiers.is_empty() {
        return Err(
            "Nobody holds a verified win on the no-cheat board yet — win `/descent play` \
             to qualify for the weekly bracket."
                .to_string(),
        );
    }

    let beacon = descent::resolve_todays_beacon();
    let seed = beacon
        .seed()
        .map_err(|e| format!("today's beacon did not verify: {e}"))?;

    let mut tournament = weekly_descent_tournament(*seed.as_bytes());
    let seated = qualifiers.len().min(MAX_QUALIFIERS);
    for (name, _best_turns) in qualifiers.iter().take(MAX_QUALIFIERS) {
        tournament.enter(honest_descender(name.clone()));
    }
    let outcome = tournament.run();
    Ok(BracketRun {
        standings: DescentStandings::from_outcome(&outcome),
        qualifiers: seated,
    })
}
