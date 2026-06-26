//! **The discord-bot as a CHAIN-REACTOR** — the clean exemplar of
//! [`dregg_app_framework::Reactor`], the reactive twin of `invoke()`.
//!
//! The desktop no longer POSTs a command to the bot over HTTP. Instead it submits
//! a real dregg turn to the on-chain **command cell** ([`deos_drive::command_cell`])
//! — the chain is the message bus. This module is the other half: the bot WATCHES
//! that cell and REACTS.
//!
//! Where the prior lane hand-wired a bespoke event-stream poll + match + decode +
//! reaction-build, this module declares only what a service author should have to
//! declare — the [`Reactor`] front-door does the rest:
//!
//! - [`BotCommandReactor::filter`] — **what it watches**: the command cell, for
//!   the [`COMMAND_METHOD`] op ([`ReceiptFilter`]).
//! - [`BotCommandReactor::react`] — **how it reacts**: decode the on-chain
//!   [`DriveRequest`] from the observed receipt's committed effects and build the
//!   SAME genuine dregg turn the matching Discord command would
//!   ([`deos_drive::build_op_action`]), as a cap-gated [`ReactionPlan`].
//!
//! The framework wires the match → cap-gate → build → sign
//! ([`dregg_app_framework::plan_reaction`] / `react_build`). The bot is to
//! `Reactor` what a `kvstore` cell is to `invoke()`: the first citizen of the
//! abstraction.
//!
//! ## What is on-chain vs. the relegated HTTP
//!
//! - **On-chain (the command path):** the desktop's [`DriveRequest`] rides as the
//!   command cell's committed STATE (a turn, receipted) + an `EmitEvent`
//!   announcement; the bot decodes it off the cell and reacts with its own
//!   receipted turn. The chain is the bus; the bot is a reactor.
//! - **Relegated (HTTP):** `POST /api/op` is NO LONGER the command path. It
//!   survives only as the bot's optional internal reaction-delivery surface (a
//!   peer that already speaks HTTP can still nudge the bot), not as how the
//!   desktop commands the bot.

use std::sync::Arc;
use std::time::Duration;

use serenity::all::{ChannelId, CreateMessage, Http};
use tokio::time;
use tracing::{debug, info, warn};

use dregg_app_framework::{
    AuthRequired, InvokeAuthority, ObservedReceipt, ReactionPlan, Reactor, ReceiptFilter,
    plan_reaction, symbol,
};
use dregg_turn::{Action, Effect};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::StarbridgeActivity;
use crate::deos_drive::{
    self, COMMAND_METHOD, DriveRequest, build_op_action, command_cell, decode_command,
};

/// **The bot's command reactor** — a [`Reactor`] that watches the on-chain
/// command cell and reacts to each committed op with the bot's custodial dregg
/// turn. Holds the bot's custodial root so its [`react`](Reactor::react) can
/// derive the acting user's cipherclerk and build the genuine reaction.
pub struct BotCommandReactor {
    /// The bot's custodial root secret (per-user cipherclerks derive from it).
    bot_secret: [u8; 32],
    /// The federation id the bot binds signatures to.
    federation_id: [u8; 32],
}

impl BotCommandReactor {
    /// Build the reactor from the bot's custodial root + federation id.
    pub fn new(bot_secret: [u8; 32], federation_id: [u8; 32]) -> Self {
        Self {
            bot_secret,
            federation_id,
        }
    }

    /// The reactor for a running bot (from its [`BotState`]).
    pub fn from_state(state: &BotState) -> Self {
        Self::new(state.config.bot_secret, state.federation_id_bytes)
    }

    /// The per-user custodial cipherclerk for a decoded command's actor.
    pub fn cclerk_for(&self, user_id: u64) -> UserCipherclerk {
        UserCipherclerk::derive(&self.bot_secret, user_id, self.federation_id)
    }
}

impl Reactor for BotCommandReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the command cell, for the command op. The reactive
        // analogue of a service-cell's interface descriptor.
        ReceiptFilter::cell_methods(command_cell(), &[COMMAND_METHOD])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the on-chain DriveRequest off the observed turn's committed
        // effects (what the bot reads off the cell's state).
        let (req, _seq) = decode_command(&observed.effects)?;
        // Build the SAME genuine reaction turn the Discord command would, under
        // the acting user's custodial cipherclerk.
        let cclerk = self.cclerk_for(req.user_id);
        // register/presence have a pure builder → a pure reaction. Credential
        // issuance interleaves issuer-key derivation, so it is NOT a pure
        // reaction here — it rides the custodial issue path in [`fire`].
        let action = build_op_action(&cclerk, &req.op, deos_drive::DEFAULT_NAME_LEASE)?;
        Some(ReactionPlan {
            target: action.target,
            method: req.op.method_name().to_string(),
            args: action.args.clone(),
            effects: action.effects,
            // The reaction acts on the user's own cell custodially — it requires
            // (and the bot holds) the user's signature.
            auth_required: AuthRequired::Signature,
        })
    }
}

/// Build the [`ObservedReceipt`] the reactor sees from a command turn's effects.
/// `turn_hash` + `signer` are the provenance handles (from the node's event /
/// receipt, or zero when only the cell state is available).
pub fn observe_command(
    effects: Vec<Effect>,
    turn_hash: [u8; 32],
    signer: [u8; 32],
) -> ObservedReceipt {
    ObservedReceipt {
        cell: command_cell(),
        method: symbol(COMMAND_METHOD),
        effects,
        turn_hash,
        signer,
    }
}

/// Reconstruct the command cell's committed effects from its on-chain state
/// fields (`/api/cell/{id}` → `fields`, hex per slot). The live watcher's bridge
/// from the node's state read to the reactor's [`ObservedReceipt`].
fn setfields_from_state(fields: &[String]) -> Vec<Effect> {
    let cell = command_cell();
    fields
        .iter()
        .enumerate()
        .filter_map(|(index, hex_field)| {
            let bytes = hex::decode(hex_field.trim()).ok()?;
            let value: [u8; 32] = bytes.try_into().ok()?;
            Some(Effect::SetField { cell, index, value })
        })
        .collect()
}

/// **Fire the bot's reaction to one decoded command.** Runs the command through
/// the [`Reactor`] front-door (decode + match + cap-gate), then submits the bot's
/// custodial turn, records it in the activity feed (the bot's state), and reflects
/// it to the configured Discord feed channels. The submit + record reuse the
/// existing custodial [`deos_drive::drive`] path (one effector for all three ops,
/// including the interleaved credential issuance).
async fn fire(
    state: &BotState,
    http: &Http,
    reactor: &BotCommandReactor,
    req: &DriveRequest,
    effects: Vec<Effect>,
) {
    let observed = observe_command(
        effects,
        [0u8; 32],
        reactor.cclerk_for(req.user_id).cell_id_bytes(),
    );

    // The framework reactor: match the filter + cap-gate the reaction. A refusal
    // is a real gate (the bot won't fire a command it can't authorize); a plan
    // (register/presence) or a recognized-but-non-pure command (credential, which
    // decodes to a valid request but yields no pure reaction plan) both proceed to
    // the custodial effector.
    match plan_reaction(reactor, &observed, InvokeAuthority::Signature) {
        Ok(_planned) => match deos_drive::drive(state, req).await {
            Ok(outcome) => {
                info!(
                    action = %outcome.action,
                    accepted = outcome.accepted,
                    "bot reactor fired a custodial turn in response to an on-chain command"
                );
                reflect_to_discord(state, http, req, &outcome).await;
            }
            Err(e) => warn!(error = %e, "bot reactor failed to fire its custodial turn"),
        },
        Err(refused) => {
            warn!(reason = %refused, "bot reactor refused an on-chain command (cap-gate)")
        }
    }
}

/// Reflect a fired reaction to the bot's configured feed channels (the "reflect to
/// Discord" half), best-effort. Uses the SAME [`deos_drive::op_receipt_card`] the
/// HTTP-era reflection used, rendered through the shared `deos_view::discord`
/// backend.
async fn reflect_to_discord(
    state: &BotState,
    http: &Http,
    req: &DriveRequest,
    outcome: &crate::deos_drive::DriveOutcome,
) {
    let channels = match state.db.get_all_feed_channels().await {
        Ok(c) => c,
        Err(_) => return,
    };
    if channels.is_empty() {
        return;
    }
    let card = deos_view::discord::render_card(
        "dregg discord-bot · reacted on-chain",
        &deos_drive::op_receipt_card(&req.op, outcome),
        &[],
    );
    for (_guild, channel_id_str) in &channels {
        if let Ok(id) = channel_id_str.parse::<u64>() {
            let msg = CreateMessage::new().embed(card.embed.clone());
            if let Err(e) = ChannelId::new(id).send_message(http, msg).await {
                debug!("bot reactor failed to reflect to channel {id}: {e}");
            }
        }
    }
}

/// **Start the on-chain command reactor background task.** Polls the command
/// cell's committed state; when a NEW command (advanced seq) lands, decodes the
/// [`DriveRequest`] and fires the bot's reaction. The on-chain analogue of
/// `activity_feed::start` — but reacting, not just reporting.
pub fn start(state: Arc<BotState>, http: Arc<Http>) {
    tokio::spawn(async move {
        info!("Bot command reactor started (watching the on-chain command cell)");
        let reactor = BotCommandReactor::from_state(&state);
        let command_cell_hex = hex::encode(command_cell().0);
        let mut last_seq: u64 = 0;

        // Small initial delay to let the bot finish connecting.
        time::sleep(Duration::from_secs(3)).await;

        loop {
            time::sleep(Duration::from_secs(5)).await;

            let details = match state.devnet.get_cell_details(&command_cell_hex).await {
                Ok(d) => d,
                Err(e) => {
                    debug!("command reactor: command cell not readable yet: {e}");
                    continue;
                }
            };

            let effects = setfields_from_state(&details.fields);
            let Some((req, seq)) = decode_command(&effects) else {
                continue;
            };
            if seq <= last_seq {
                continue; // already handled (dedupe on the monotone command seq)
            }
            last_seq = seq;
            fire(&state, &http, &reactor, &req, effects).await;
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deos_drive::{BotOp, build_command_action};
    use dregg_app_framework::react_build;

    const TEST_SECRET: [u8; 32] = [7u8; 32];
    const TEST_FED: [u8; 32] = [0u8; 32];

    fn reactor() -> BotCommandReactor {
        BotCommandReactor::new(TEST_SECRET, TEST_FED)
    }

    #[test]
    fn reactor_watches_the_command_cell_for_the_command_op() {
        let filter = reactor().filter();
        // A command turn passes the filter; an unrelated cell does not.
        let cmd = build_command_action(
            &DriveRequest {
                user_id: 1,
                guild_id: None,
                op: BotOp::AttestPresence,
            },
            1,
        );
        let observed = observe_command(cmd.effects, [0u8; 32], [0u8; 32]);
        assert!(filter.matches(&observed), "the command turn is watched");

        let mut off = observe_command(vec![], [0u8; 32], [0u8; 32]);
        off.cell = dregg_types::CellId([0x11u8; 32]);
        assert!(!filter.matches(&off), "an off-cell receipt is not watched");
    }

    #[test]
    fn on_chain_command_drives_the_reactor_to_the_bots_resulting_turn() {
        // THE END-TO-END (no HTTP): the desktop's on-chain command turn → the
        // reactor sees it via the observed receipt → the reactor's resulting turn
        // is the GENUINE register_name turn the bot would build.
        let reactor = reactor();
        let req = DriveRequest {
            user_id: 4242,
            guild_id: Some("guild-1".to_string()),
            op: BotOp::RegisterName {
                name: "ember".to_string(),
            },
        };
        // 1) The desktop builds the on-chain command turn to the command cell.
        let command = build_command_action(&req, 1);
        assert_eq!(command.target, command_cell());

        // 2) The bot OBSERVES it (off the committed effects) and reacts — the
        //    framework front-door does match → decode → cap-gate → plan.
        let observed = observe_command(command.effects, [0xAB; 32], [0xCD; 32]);
        let action: Action = plan_reaction(&reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding custodial reactor is authorized")
            .expect("a watched register command produces a reaction");

        // 3) The reaction IS the genuine register_name turn (method + target +
        //    the nameservice SetField/EmitEvent effects), NOT a poke of an HTTP
        //    endpoint.
        assert_eq!(action.method, symbol("register_name"));
        let expected_user_cell = dregg_types::CellId(reactor.cclerk_for(4242).cell_id_bytes());
        assert_eq!(
            action.target, expected_user_cell,
            "the reaction targets the acting user's own registry cell"
        );
        let set_fields = action
            .effects
            .iter()
            .filter(|e| matches!(e, Effect::SetField { .. }))
            .count();
        assert!(set_fields >= 3, "register writes NAME/OWNER/EXPIRY");
        assert!(
            action
                .effects
                .iter()
                .any(|e| matches!(e, Effect::EmitEvent { .. })),
            "register emits the name-registered event"
        );

        // 4) And it signs into a real Turn under the user's custodial cclerk.
        let cclerk = reactor.cclerk_for(4242);
        let turn = react_build(&cclerk.app, &reactor, &observed, InvokeAuthority::Signature)
            .expect("authorized")
            .expect("a reaction turn is produced");
        assert_eq!(
            turn.call_forest.roots[0].action.target, expected_user_cell,
            "the signed reaction turn carries the register action on the user cell"
        );
    }

    #[test]
    fn presence_command_drives_a_setfield_reaction_over_the_stream() {
        // Drive a STREAM of on-chain commands through the reactor (the poll-loop's
        // pure core) — two presence commands → two reaction turns.
        use dregg_app_framework::react_to_stream;
        let reactor = reactor();
        let cclerk = reactor.cclerk_for(7);

        let mk = |seq: u64| {
            let req = DriveRequest {
                user_id: 7,
                guild_id: None,
                op: BotOp::AttestPresence,
            };
            observe_command(
                build_command_action(&req, seq).effects,
                [0u8; 32],
                [0u8; 32],
            )
        };
        let stream = vec![mk(1), mk(2)];
        let turns = react_to_stream(&cclerk.app, &reactor, &stream, InvokeAuthority::Signature)
            .expect("authorized");
        assert_eq!(turns.len(), 2, "two presence commands → two reaction turns");
        for turn in &turns {
            assert_eq!(
                turn.call_forest.roots[0].action.method,
                symbol("attest_presence")
            );
        }
    }

    #[test]
    fn unauthorized_reactor_is_refused_fail_closed() {
        // The cap-gate is real: a reactor presenting only None authority cannot
        // fire a Signature-required reaction.
        let reactor = reactor();
        let req = DriveRequest {
            user_id: 1,
            guild_id: None,
            op: BotOp::AttestPresence,
        };
        let observed = observe_command(build_command_action(&req, 1).effects, [0u8; 32], [0u8; 32]);
        let refused = plan_reaction(&reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(
            refused,
            dregg_app_framework::ReactRefused::Unauthorized { .. }
        ));
    }
}
