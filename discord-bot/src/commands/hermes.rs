//! `/hermes` — a Discord channel drives a **hosted, confined Hermes agent**: prompt → one
//! cap-bounded, metered, receipted turn.
//!
//! The offering is [`dreggnet_hermes::HermesOffering`] (offering #1), consumed (never
//! re-implemented) through the generic [`crate::commands::offering`] adapter. Each prompt is one
//! real turn on the PROVEN `dregg_sdk::ToolGateway`:
//!
//! * **PROMPT** — the presser types a message into a modal; the agent's [`Brain`] classifies it
//!   into a proposed tool-call (a class: Read / Search / Fetch / Execute / Edit / Chat), and the
//!   executor referees it through that class's cap-gated worker. An in-mandate call lands a real
//!   `ToolReceipt` ([`Outcome::Landed`]); a rate-exhausted / over-budget / out-of-mandate call is
//!   a real [`Outcome::Refused`] — **the agent CANNOT exceed its cell's mandate**, no matter what
//!   its brain proposes (the confinement tooth is the executor's, not the bot's).
//! * **`/hermes verify`** re-derives a fresh identically-seeded confined agent and re-drives the
//!   recorded inputs, confirming the committed confinement decision chain reproduces (a forged /
//!   reordered / relabeled verdict fails replay).
//!
//! HONEST SCOPE: the live `/hermes open` wires the REAL resident brain
//! ([`HermesOffering::new`] — on-box by default, a live BYO-key brain when a provider key is in
//! the env). The logic tests wire the deterministic scripted mock ([`HermesOffering::scripted`])
//! so the confinement/metering enforcement is proven with no model credentials — the enforcement
//! seam is brain-agnostic (only the producer of the tool-call changes).

use std::sync::OnceLock;

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dreggnet_hermes::{HermesOffering, HermesSession, TURN_PROMPT};
use dreggnet_offerings::SessionConfig;

use crate::BotState;
use crate::commands::offering::{self, DiscordOffering, Store, TextPrompt, ValuePrompt};

/// The Hermes brand colour (a confined-agent violet).
const HERMES_COLOR: u32 = 0x9D4EDD;

impl DiscordOffering for HermesOffering {
    const KEY: &'static str = "hermes";
    const TITLE: &'static str = "Hosted Hermes — a confined agent";
    const COLOR: u32 = HERMES_COLOR;
    const TAGLINE: &'static str =
        "one cap-bounded, metered, receipted turn at a time · it cannot exceed its cell's mandate";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<HermesOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    /// No Hermes affordance takes a numeric arg — a prompt is free text (see [`Self::text_prompt`]).
    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    /// The one Hermes verb ([`TURN_PROMPT`]) takes a **free-text message** the presser types; the
    /// brain classifies it into the tool class the executor meters it under.
    fn text_prompt(turn: &str) -> Option<TextPrompt> {
        (turn == TURN_PROMPT).then_some(TextPrompt {
            title: "Message the confined agent",
            label: "Your prompt (e.g. `read notes.txt`, `search foo`, `run ls`)",
            placeholder: "read notes.txt",
            paragraph: true,
        })
    }

    fn status_line(&self, session: &HermesSession) -> String {
        format!(
            "{} committed turns · brain {}",
            session.committed_turns(),
            self.brain_seam()
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register `/hermes` (open / status / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("hermes")
        .description(
            "Drive a hosted, confined Hermes agent in this channel — one metered turn at a time",
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "open",
            "Open a confined Hermes agent here (a fresh cap-gated session)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show this channel's agent: its tool classes, head-room, and committed turns",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify the agent's confinement chain by replay",
        ))
}

/// Route `/hermes` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "open" => handle_open(ctx, command, state).await,
        "status" => offering::handle_status::<HermesOffering>(ctx, command, state).await,
        "verify" => offering::handle_verify::<HermesOffering>(ctx, command).await,
        _ => {}
    }
}

/// `/hermes open` — deploy a fresh confined agent (the REAL resident brain) and post its surface.
/// The channel id is the deterministic session seed (so `verify`'s replay re-derives it).
async fn handle_open(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    let channel = command.channel_id.get();
    // REFUSE-WITH-CONFIRM (backlog #32): a live agent session's chain must not be silently
    // wiped by a re-open; the replacement waits behind an explicit Confirm press.
    if offering::is_open::<HermesOffering>(channel) {
        let status = offering::with_live::<HermesOffering, _>(channel, |live| {
            live.offering.status_line(&live.session)
        });
        crate::commands::open_guard::refuse_with_confirm(
            ctx,
            command,
            HermesOffering::KEY,
            status,
            Box::new(move || {
                offering::open_in(
                    channel,
                    HermesOffering::new,
                    SessionConfig::with_seed(channel),
                )
                .map_err(|e| e.to_string())?;
                offering::with_live::<HermesOffering, _>(channel, |live| {
                    offering::surface_of::<HermesOffering>(live)
                })
                .ok_or_else(|| "the fresh session did not render".to_string())
            }),
        )
        .await;
        return;
    }
    if let Err(e) = offering::open_in(
        channel,
        HermesOffering::new,
        SessionConfig::with_seed(channel),
    ) {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(
                            CreateEmbed::new()
                                .title("The agent did not deploy")
                                .description(format!(
                                    "The confined agent failed to come alive: {e}"
                                ))
                                .color(0xE63946),
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }
    let rendered = offering::with_live::<HermesOffering, _>(channel, |live| {
        offering::surface_of::<HermesOffering>(live)
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
// Tests — the `/hermes` surface DRIVEN at the logic level (the SAME `offering`
// path a live prompt-modal + press takes), against a hermetic SCRIPTED-brain
// HermesOffering. No env, no network, no key, no live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_hermes::{Confinement, ToolKind};
    use dreggnet_offerings::{DreggIdentity, Outcome};

    use crate::commands::offering::{Driven, close_in, fire_id, with_live};

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// Open a hermetic scripted-brain agent in `channel` (Execute confined to `exec_rate`), the
    /// SAME adapter path `/hermes open` takes — only the brain seam differs from the live default.
    fn open(channel: u64, exec_rate: i64) {
        close_in::<HermesOffering>(channel);
        let make = move || {
            HermesOffering::scripted()
                .with_confinement(Confinement::default().with_rate(ToolKind::Execute, exec_rate))
        };
        offering::open_in(channel, make, SessionConfig::with_seed(channel))
            .expect("the confined agent deploys");
    }

    /// Drive a prompt through the adapter's free-text path (the modal-submit a live press takes).
    fn prompt(channel: u64, text: &str, who: &DreggIdentity) -> Outcome {
        // A Hermes prompt has no anchor arg (the brain classifies the free text); arg is 0.
        match offering::drive_text::<HermesOffering>(channel, TURN_PROMPT, 0, text, who.clone()) {
            Driven::Fired(o) => o,
            other => panic!("a hermes prompt must fire a real turn, got {other:?}"),
        }
    }

    /// A prompt lands a REAL receipted, metered turn on the confined agent; an over-rate prompt is
    /// a real executor refusal (the confinement tooth); the whole chain re-verifies by replay.
    #[test]
    fn a_prompt_drives_a_real_metered_turn_and_the_cap_bites() {
        let channel = 92_101;
        open(channel, 1); // Execute confined to a single call
        let me = actor("a1");

        // A `run …` prompt routes to the Execute class → a real metered turn lands.
        match prompt(channel, "run echo hi", &me) {
            Outcome::Landed { receipt, ended } => {
                assert!(!ended);
                assert_ne!(
                    receipt.turn_hash, [0u8; 32],
                    "a genuine committed metered turn"
                );
            }
            other => panic!("the first Execute prompt must land, got {other:?}"),
        }
        assert_eq!(
            with_live::<HermesOffering, _>(channel, |l| l.session.committed_turns()).unwrap(),
            1
        );

        // The second Execute call exceeds the rate-1 mandate → the executor refuses it (nothing
        // commits): the agent cannot exceed its cell, no matter what the brain proposes.
        let before =
            with_live::<HermesOffering, _>(channel, |l| l.session.committed_turns()).unwrap();
        match prompt(channel, "run echo again", &me) {
            Outcome::Refused(why) => assert!(
                why.to_lowercase().contains("rate") || why.to_lowercase().contains("exhaust"),
                "the executor's own confinement reason: {why}"
            ),
            other => panic!("an over-rate prompt must be refused, got {other:?}"),
        }
        assert_eq!(
            with_live::<HermesOffering, _>(channel, |l| l.session.committed_turns()).unwrap(),
            before,
            "a refused prompt commits nothing (anti-ghost)"
        );

        // The confinement chain (one landed + the refusal) re-verifies by replay.
        let report = offering::verify_live::<HermesOffering>(channel).expect("a live agent");
        assert!(report.verified, "{}", report.detail);
        close_in::<HermesOffering>(channel);
    }

    /// An illegal affordance (an unknown verb, not the prompt turn) is a real refusal — nothing
    /// committed. The adapter fires the typed turn; the offering is the referee.
    #[test]
    fn an_illegal_affordance_is_refused() {
        let channel = 92_102;
        open(channel, 5);
        let driven = offering::drive::<HermesOffering>(
            channel,
            &fire_id(HermesOffering::KEY, "bogus", 0),
            actor("b0"),
        );
        match driven {
            Driven::Fired(Outcome::Refused(why)) => {
                assert!(why.contains("bogus") || why.contains("affordance"), "{why}")
            }
            other => panic!("an unknown affordance must be a real refusal, got {other:?}"),
        }
        close_in::<HermesOffering>(channel);
    }

    /// A prompt in a channel with no agent open reports honestly (no session, no turn).
    #[test]
    fn a_prompt_with_no_session_is_reported() {
        let channel = 92_103;
        close_in::<HermesOffering>(channel);
        assert!(matches!(
            offering::drive_text::<HermesOffering>(channel, TURN_PROMPT, 0, "hi", actor("cc")),
            Driven::NoSession
        ));
    }
}
