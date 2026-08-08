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
use dregg_turn::Effect;

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::deos_drive::{
    self, CMD_SEQ_SLOT, COMMAND_METHOD, DriveRequest, build_op_action, command_cell, decode_command,
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
            Some(Effect::SetField {
                cell,
                index: index as u64,
                value,
            })
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

/// **The committed command sequence** carried by the command cell's state — the
/// value of [`CMD_SEQ_SLOT`]. A readable cell that has never carried a command has
/// every slot zero, so `0` (nothing has ever been commanded) is the honest reading
/// of an absent slot; a cell that could not be read at all is NOT this function's
/// business (the caller passes `None` for that, and the reactor refuses to fire).
fn committed_seq(effects: &[Effect]) -> u64 {
    let cell = command_cell();
    effects
        .iter()
        .find_map(|effect| match effect {
            Effect::SetField {
                cell: c,
                index,
                value,
            } if *c == cell && *index == CMD_SEQ_SLOT as u64 => {
                Some(u64::from_be_bytes(value[24..32].try_into().ok()?))
            }
            _ => None,
        })
        .unwrap_or(0)
}

/// What one poll of the command cell decides. Split out of the loop so the
/// restart behaviour is testable without a node, a runtime or a `BotState`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReactorStep {
    /// Fire NOTHING this tick. Either the cell was unreadable (so the cursor cannot
    /// be trusted — the REFUSE floor) or the command at this seq is already handled.
    Idle,
    /// The cursor was ADOPTED from the cell's committed sequence. No reaction is
    /// fired for it: the bot cannot know whether the pre-restart process already
    /// reacted, and re-firing mints a fresh credential / re-leases a name / writes a
    /// fresh presence epoch. Skipping is the recoverable direction.
    Seeded { cursor: u64 },
    /// A genuinely NEW command (seq beyond the cursor) — react to it.
    Fire { seq: u64 },
}

/// **The reactor's restart rule, as one pure decision.**
///
/// `cursor` is what this process believes it has already handled (`None` = it has
/// not read the chain yet, i.e. it just booted). `committed` is the sequence the
/// command cell currently carries, or `None` when the cell could not be read.
///
/// * unreadable cell ⇒ [`ReactorStep::Idle`] — a boot that cannot reach the node
///   fires nothing at all, rather than falling back to a `0` cursor that makes every
///   standing command look new;
/// * first successful read ⇒ [`ReactorStep::Seeded`] — adopt the on-chain cursor,
///   react to nothing;
/// * afterwards ⇒ react iff the sequence advanced.
fn reactor_step(cursor: Option<u64>, committed: Option<u64>) -> ReactorStep {
    match (cursor, committed) {
        (_, None) => ReactorStep::Idle,
        (None, Some(seq)) => ReactorStep::Seeded { cursor: seq },
        (Some(handled), Some(seq)) if seq > handled => ReactorStep::Fire { seq },
        _ => ReactorStep::Idle,
    }
}

/// **Start the on-chain command reactor background task.** Polls the command
/// cell's committed state; when a NEW command (advanced seq) lands, decodes the
/// [`DriveRequest`] and fires the bot's reaction. The on-chain analogue of
/// `activity_feed::start` — but reacting, not just reporting.
///
/// ⚑ **RESTART: REBUILD, with a REFUSE floor** (see
/// `docs/reference/RESTART-SEMANTICS.md`). The dedupe cursor used to be a plain
/// `let mut last_seq: u64 = 0;` — while the real cursor was already on-chain in
/// [`CMD_SEQ_SLOT`] and simply never read at boot. Every restart therefore saw
/// `seq >= 1 > 0` and re-fired the standing command as a REAL signed turn:
/// `IssueCredential` minted a second credential, `RegisterName` re-leased the name
/// at a fresh expiry, `AttestPresence` wrote a fresh on-ledger epoch. The cursor is
/// now adopted from the cell itself on the first successful read, and until that
/// read succeeds the reactor fires nothing.
///
/// **The trade, named:** a command issued while the bot was DOWN is skipped rather
/// than fired late. The command cell holds exactly one pending command (the slot is
/// overwritten, not queued), so the cost is bounded at one missed command per
/// downtime — against an unbounded, silently-repeating credential mint on every
/// restart. Re-issuing a skipped command is one more `/deos` press; un-minting a
/// duplicate credential is not a thing.
pub fn start(state: Arc<BotState>, http: Arc<Http>) {
    tokio::spawn(async move {
        info!("Bot command reactor started (watching the on-chain command cell)");
        let reactor = BotCommandReactor::from_state(&state);
        let command_cell_hex = hex::encode(command_cell().0);
        // `None` = this process has not yet READ the chain, so it knows nothing about
        // what was already handled and must not fire.
        let mut cursor: Option<u64> = None;

        // Small initial delay to let the bot finish connecting.
        time::sleep(Duration::from_secs(3)).await;

        loop {
            time::sleep(Duration::from_secs(5)).await;

            let effects = match state.devnet.get_cell_details(&command_cell_hex).await {
                Ok(details) => Some(setfields_from_state(&details.fields)),
                Err(e) => {
                    debug!("command reactor: command cell not readable yet: {e}");
                    None
                }
            };
            let committed = effects.as_deref().map(committed_seq);

            match reactor_step(cursor, committed) {
                ReactorStep::Idle => continue,
                ReactorStep::Seeded { cursor: adopted } => {
                    cursor = Some(adopted);
                    info!(
                        seq = adopted,
                        "bot reactor adopted the command cursor from the on-chain CMD_SEQ_SLOT \
                         — nothing is replayed for it"
                    );
                }
                ReactorStep::Fire { seq } => {
                    // Advance FIRST: the committed state at a given seq is immutable, so a
                    // payload this build cannot decode will never decode, and retrying it
                    // forever would only re-warn every tick.
                    cursor = Some(seq);
                    let effects = effects.unwrap_or_default();
                    match decode_command(&effects) {
                        Some((req, _)) => fire(&state, &http, &reactor, &req, effects).await,
                        None => warn!(
                            seq,
                            "command cell advanced but its payload did not decode — skipped"
                        ),
                    }
                }
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deos_drive::{BotOp, build_command_action};
    use dregg_app_framework::react_build;
    use dregg_turn::Action;

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

    // ── RESTART SEMANTICS (docs/reference/RESTART-SEMANTICS.md) ──────────────────
    // The cursor is REBUILT from the committed CMD_SEQ_SLOT, with a REFUSE floor
    // while the chain is unreadable. These drive `reactor_step` — the whole decision
    // the poll loop takes — so the restart behaviour is pinned without a node.

    /// The effects a command turn at `seq` commits (what `/api/cell` exposes and
    /// `setfields_from_state` rebuilds).
    fn command_effects(seq: u64) -> Vec<Effect> {
        build_command_action(
            &DriveRequest {
                user_id: 4242,
                guild_id: None,
                op: BotOp::IssueCredential {
                    schema: "kyc".to_string(),
                    attributes: serde_json::json!({ "verified": true }),
                },
            },
            seq,
        )
        .effects
    }

    /// ⚑ **THE RESTART.** A command at seq 3 is committed on-chain. A FRESH process
    /// (cursor `None` — exactly what `start` begins with) must ADOPT that sequence,
    /// not react to it: the pre-fix loop began at `last_seq = 0`, saw `3 > 0`, and
    /// drove `deos_drive::drive` — minting a second credential / re-leasing a name /
    /// writing a fresh presence epoch on EVERY restart.
    #[test]
    fn a_restart_adopts_the_committed_command_cursor_instead_of_replaying_it() {
        let committed = committed_seq(&command_effects(3));
        assert_eq!(
            committed, 3,
            "the seq rides CMD_SEQ_SLOT of the committed state"
        );

        // Boot: the cursor is unknown, the chain says 3.
        let step = reactor_step(None, Some(committed));
        assert_eq!(
            step,
            ReactorStep::Seeded { cursor: 3 },
            "a fresh process must adopt the on-chain cursor, never fire for it"
        );
        assert!(
            !matches!(step, ReactorStep::Fire { .. }),
            "the standing command must NOT be replayed on restart"
        );

        // The same state on every later tick is already handled.
        assert_eq!(reactor_step(Some(3), Some(3)), ReactorStep::Idle);
        assert_eq!(reactor_step(Some(3), Some(2)), ReactorStep::Idle);

        // NON-VACUOUS: a genuinely new command still fires.
        assert_eq!(
            reactor_step(Some(3), Some(committed_seq(&command_effects(4)))),
            ReactorStep::Fire { seq: 4 },
            "the reactor must still react to a command issued after it booted"
        );
    }

    /// The REFUSE floor: a boot that cannot read the command cell fires NOTHING. It
    /// must not fall back to a `0` cursor, because a `0` cursor makes every standing
    /// command look new — which is the bug this replaces.
    #[test]
    fn an_unreadable_command_cell_fires_nothing_and_never_seeds_a_zero_cursor() {
        assert_eq!(
            reactor_step(None, None),
            ReactorStep::Idle,
            "an unreadable cell at boot fires nothing"
        );
        assert_eq!(
            reactor_step(Some(7), None),
            ReactorStep::Idle,
            "an unreadable cell mid-run fires nothing"
        );
        // And once the cell IS readable, the cursor adopted is the CHAIN's, not 0.
        assert_eq!(
            reactor_step(None, Some(committed_seq(&command_effects(9)))),
            ReactorStep::Seeded { cursor: 9 },
        );
    }

    /// NON-VACUITY of the whole rule: on a node where NO command has ever been
    /// committed, the cell reads as all-zero, the cursor seeds at 0, and the very
    /// first command still fires. Adopting the cursor must not brick a fresh deploy.
    #[test]
    fn a_fresh_command_cell_seeds_at_zero_so_the_first_ever_command_still_fires() {
        // A readable cell with no committed command: `/api/cell` reports zero fields.
        let empty = setfields_from_state(&[]);
        assert_eq!(committed_seq(&empty), 0);
        assert_eq!(
            reactor_step(None, Some(0)),
            ReactorStep::Seeded { cursor: 0 }
        );
        assert_eq!(
            reactor_step(Some(0), Some(committed_seq(&command_effects(1)))),
            ReactorStep::Fire { seq: 1 },
            "the first command ever issued on a fresh cell must fire"
        );
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
