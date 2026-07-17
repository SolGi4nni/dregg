//! `/grain` — a Discord channel drives a **confined grain** (a Sandstorm-style sandboxed app as a
//! cap-gated grain turn-cell on the real dregg substrate): each action is one real cap-bounded
//! grain turn.
//!
//! The offering is [`dreggnet_grain::GrainOffering`] (offering #2), consumed (never
//! re-implemented) through the generic [`crate::commands::offering`] adapter:
//!
//! * **ACT** — one metered grain action, driven as a genuine `dregg_sdk::ToolGateway::invoke`
//!   executor turn on the grain worker cell ([`Outcome::Landed`], a real committed kernel turn).
//!   When the grain has spent its whole grant, the next action is the **executor's own** over-cap
//!   refusal ([`Outcome::Refused`]) — nothing commits. **The grain cannot act beyond its granted
//!   sandbox: the jailer is the kernel** (the `calls_made` caveat), not the bot.
//! * **`/grain verify`** re-witnesses the grain's committed turn chain against the executor's
//!   manifest + the on-ledger `calls_made` counter + the on-ledger action commit (real committed
//!   kernel state, not a mirror).

use std::sync::OnceLock;

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dreggnet_grain::{GrainOffering, GrainSession};
use dreggnet_offerings::SessionConfig;

use crate::BotState;
use crate::commands::offering::{self, DiscordOffering, Store, ValuePrompt};

/// The grain brand colour (a sandbox teal).
const GRAIN_COLOR: u32 = 0x00B4A6;

/// The cap every `/grain` session is confined to — the number of metered turns the executor's
/// `calls_made` grant admits before refusing (a generous demo sandbox).
const GRAIN_BUDGET: i64 = 8;

impl DiscordOffering for GrainOffering {
    const KEY: &'static str = "grain";
    const TITLE: &'static str = "Confined grain";
    const COLOR: u32 = GRAIN_COLOR;
    const TAGLINE: &'static str = "cap-gated to its grant · the executor's calls_made caveat refuses an over-cap turn host-side";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<GrainOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    /// The grain's single affordance carries a fixed cost — no modal.
    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    fn status_line(&self, session: &GrainSession) -> String {
        session.state_line()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register `/grain` (open / status / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("grain")
        .description(
            "Drive a confined grain in this channel — each action one real cap-bounded grain turn",
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "open",
            "Admit a fresh confined grain here (a cap-gated worker cell)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show this channel's grain: its grant, head-room, and committed turns",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-witness the grain's committed turn chain against real kernel state",
        ))
}

/// Route `/grain` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "open" => handle_open(ctx, command, state).await,
        "status" => offering::handle_status::<GrainOffering>(ctx, command, state).await,
        "verify" => offering::handle_verify::<GrainOffering>(ctx, command).await,
        _ => {}
    }
}

/// `/grain open` — admit a fresh confined grain worker cell and post its surface. The channel id
/// is the deterministic confinement domain seed.
async fn handle_open(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    let channel = command.channel_id.get();
    // REFUSE-WITH-CONFIRM (backlog #32): a live grain's chain must not be silently wiped by a
    // re-open; the replacement waits behind an explicit Confirm press.
    if offering::is_open::<GrainOffering>(channel) {
        let status = offering::with_live::<GrainOffering, _>(channel, |live| {
            live.offering.status_line(&live.session)
        });
        crate::commands::open_guard::refuse_with_confirm(
            ctx,
            command,
            GrainOffering::KEY,
            status,
            Box::new(move || {
                offering::open_in(
                    channel,
                    || GrainOffering::new(GRAIN_BUDGET),
                    SessionConfig::with_seed(channel),
                )
                .map_err(|e| e.to_string())?;
                offering::with_live::<GrainOffering, _>(channel, |live| {
                    offering::surface_of::<GrainOffering>(live)
                })
                .ok_or_else(|| "the fresh session did not render".to_string())
            }),
        )
        .await;
        return;
    }
    if let Err(e) = offering::open_in(
        channel,
        || GrainOffering::new(GRAIN_BUDGET),
        SessionConfig::with_seed(channel),
    ) {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(
                            CreateEmbed::new()
                                .title("The grain was not admitted")
                                .description(format!(
                                    "The executor refused to admit the grain worker: {e}"
                                ))
                                .color(0xE63946),
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }
    let rendered = offering::with_live::<GrainOffering, _>(channel, |live| {
        offering::surface_of::<GrainOffering>(live)
    });
    let Some((embed, rows)) = rendered else {
        return;
    };
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
// Tests — the `/grain` surface DRIVEN at the logic level (the SAME `offering::drive`
// a live button press takes), against a REAL confined grain. No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_grain::TURN_ACT;
    use dreggnet_offerings::{DreggIdentity, Outcome};

    use crate::commands::offering::{Driven, close_in, fire_id, with_live};

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// Open a real confined grain of `budget` metered turns in `channel`.
    fn open(channel: u64, budget: i64) {
        close_in::<GrainOffering>(channel);
        offering::open_in(
            channel,
            move || GrainOffering::new(budget),
            SessionConfig::with_seed(channel),
        )
        .expect("the grain is admitted");
    }

    /// Press the grain's ACT affordance, exactly as the live component route does.
    fn act(channel: u64, who: &DreggIdentity) -> Outcome {
        match offering::drive::<GrainOffering>(
            channel,
            &fire_id(GrainOffering::KEY, TURN_ACT, 1),
            who.clone(),
        ) {
            Driven::Fired(o) => o,
            other => panic!("a grain press must fire a real turn, got {other:?}"),
        }
    }

    /// An in-cap action lands a REAL committed kernel turn; an action past the grant is the
    /// executor's OWN over-cap refusal (nothing commits); the chain re-witnesses against real
    /// kernel state.
    #[test]
    fn grain_actions_land_until_the_grant_is_spent_then_the_executor_refuses() {
        let channel = 92_201;
        open(channel, 2); // a two-turn sandbox
        let me = actor("a1");

        for _ in 0..2 {
            match act(channel, &me) {
                Outcome::Landed { receipt, .. } => {
                    assert_ne!(
                        receipt.turn_hash, [0u8; 32],
                        "a genuine committed grain turn"
                    )
                }
                other => panic!("an in-cap grain action must land, got {other:?}"),
            }
        }
        let before = with_live::<GrainOffering, _>(channel, |l| l.session.receipts_len()).unwrap();

        // The third action is past the grant → the executor refuses it host-side.
        match act(channel, &me) {
            Outcome::Refused(_) => {}
            other => {
                panic!("an over-cap grain action must be a real executor refusal, got {other:?}")
            }
        }
        assert_eq!(
            with_live::<GrainOffering, _>(channel, |l| l.session.receipts_len()).unwrap(),
            before,
            "a refused over-cap action commits nothing (anti-ghost)"
        );

        let report = offering::verify_live::<GrainOffering>(channel).expect("a live grain");
        assert!(report.verified, "{}", report.detail);
        close_in::<GrainOffering>(channel);
    }

    /// An illegal affordance (an unknown verb) is a real refusal — nothing committed.
    #[test]
    fn an_illegal_affordance_is_refused() {
        let channel = 92_202;
        open(channel, 4);
        match offering::drive::<GrainOffering>(
            channel,
            &fire_id(GrainOffering::KEY, "bogus", 0),
            actor("b0"),
        ) {
            Driven::Fired(Outcome::Refused(why)) => {
                assert!(why.contains("grain") || why.contains("affordance"), "{why}")
            }
            other => panic!("an unknown affordance must be a real refusal, got {other:?}"),
        }
        close_in::<GrainOffering>(channel);
    }
}
