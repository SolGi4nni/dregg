//! `/council` — a Discord channel runs a **real DreggNet council**: propose → vote → enact.
//!
//! The offering is [`dreggnet_council::CouncilOffering`], consumed (never re-implemented)
//! through the generic [`crate::commands::offering`] adapter. What happens when a member
//! presses a button is a REAL governance turn:
//!
//! * **PROPOSE** opens a real `collective-choice` poll (reject/approve, gated on APPROVE) and
//!   commits a council-cell turn (the monotone proposals-opened counter bumps);
//! * **APPROVE / REJECT** casts a real write-once ballot — a second vote from the same identity
//!   is a real executor refusal at the nullifier, not a frontend check;
//! * **ENACT** is refereed by the engine's `AffineLe` quorum gate: below quorum it is a real
//!   [`Outcome::Refused`] and **nothing is applied**; at quorum with APPROVE winning, the
//!   proposal's effect commits as one executor-refereed turn (a `WriteOnce` policy slot).
//! * **`/council verify`** re-checks both substrates: every poll's stored monotone tally equals
//!   the light-client recompute, every enacted proposal's policy slot matches its catalog value
//!   AND has a passing decision, and every UNENACTED proposal's slot is still `0` (the
//!   below-quorum tooth — no phantom effect).
//!
//! * **`/council open weighted:true`** opens a **standing-weighted** council on the engine's
//!   VERIFIED weighted path (backlog #22): every vote press is a `cast_weighted` turn (the
//!   member's whole granted weight on ONE nullifier), quorum is a WEIGHT threshold, and the
//!   surface names the weight source honestly — see [`crate::commands::council_weighted`].
//!
//! The electorate is **cryptographic, not social**: a member is a derived dregg public key
//! (`UserCipherclerk::derive(bot_secret, discord_user_id, federation)`), the same derivation
//! `/dungeon` attributes its ballots to. A press by a Discord user outside the electorate is a
//! real `Refused` ("not a council member") — the bot does not gate it, the offering does.

use std::sync::OnceLock;

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage, ResolvedValue,
};

use dreggnet_council::{CandidateProposal, CouncilOffering, CouncilSession, MAX_CATALOG};
use dreggnet_offerings::SessionConfig;

use crate::BotState;
use crate::commands::council_weighted;
use crate::commands::offering::{
    self, DiscordOffering, Store, ValuePrompt, identity_of, public_key_of,
};

/// The council's brand colour.
const COUNCIL_COLOR: u32 = 0x2A9D8F;

/// The default catalog when `/council open` names no proposals — three pre-declared,
/// enactable effects (each writes its value into its own `WriteOnce` policy slot).
fn default_catalog() -> Vec<CandidateProposal> {
    vec![
        CandidateProposal::new("Fund the commons treasury", 1),
        CandidateProposal::new("Admit a new federation peer", 2),
        CandidateProposal::new("Raise the per-turn fee ceiling", 3),
    ]
}

/// Parse a comma-separated proposal list into a catalog (a proposal's value is its 1-based
/// index — non-zero, since a `WriteOnce` slot reads `0` as *unenacted*). Empty → the default.
fn catalog_from(titles: &str) -> Vec<CandidateProposal> {
    let items: Vec<CandidateProposal> = titles
        .split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .take(MAX_CATALOG)
        .enumerate()
        .map(|(i, t)| CandidateProposal::new(t, (i + 1) as u64))
        .collect();
    if items.is_empty() {
        default_catalog()
    } else {
        items
    }
}

/// The quorum a council of `members` uses when the opener names none: a simple majority.
fn default_quorum(members: usize) -> u64 {
    ((members as u64) / 2) + 1
}

impl DiscordOffering for CouncilOffering {
    const KEY: &'static str = "council";
    const TITLE: &'static str = "DreggNet Council";
    const COLOR: u32 = COUNCIL_COLOR;
    const TAGLINE: &'static str =
        "the members decide · the quorum gate disposes · the chain remembers";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<CouncilOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    /// Every council affordance carries a fixed index (a catalog item / a proposal), so none
    /// takes a typed value — the council's whole surface is buttons.
    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    fn status_line(&self, session: &CouncilSession) -> String {
        let weighted = if session.is_weighted() {
            " · weighted ballots (verified cast_weighted)"
        } else {
            ""
        };
        format!(
            "{} proposals · {} verified turns{weighted}",
            session.proposal_count(),
            session.committed_turns()
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register `/council` (open / status / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("council")
        .description("Run a real DreggNet council in this channel — propose, vote, enact")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "open",
                "Open a council here (you are a member; add up to three more)",
            )
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::User,
                "member2",
                "A second council member",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::User,
                "member3",
                "A third council member",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::User,
                "member4",
                "A fourth council member",
            ))
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Integer,
                    "quorum",
                    "APPROVE votes needed to enact (default: a simple majority)",
                )
                .min_int_value(1)
                .max_int_value(8),
            )
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::String,
                "proposals",
                "Comma-separated candidate proposals (default: the standard three)",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::Boolean,
                "weighted",
                "Weight ballots by standing (1 + run-credits) on the verified weighted engine",
            )),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show this channel's council: proposals, live tallies, affordances",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify the council's decision chain (tallies + enactments)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "close",
            "Close the collective round — resolve the plurality winner as one verified turn",
        ))
}

/// Route `/council` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options().into_iter().next() else {
        return;
    };
    match sub.name {
        "open" => {
            let ResolvedValue::SubCommand(opts) = sub.value else {
                return;
            };
            handle_open(ctx, command, state, &opts).await
        }
        "status" => offering::handle_status::<CouncilOffering>(ctx, command, state).await,
        "verify" => offering::handle_verify::<CouncilOffering>(ctx, command).await,
        // The generic collective close: for a collective offering it resolves the round's
        // plurality winner as ONE real crowd turn ([`offering::handle_close`]); the council is a
        // DIRECT offering today, and the handler says so honestly.
        "close" => offering::handle_close::<CouncilOffering>(ctx, command).await,
        _ => {}
    }
}

/// `/council open` — build the electorate from the invoker + any named members (each a DERIVED
/// dregg key, not a nickname), deploy a real council (its own quorum engine + council cell), and
/// post the surface with its cap-gated affordances.
async fn handle_open(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
    opts: &[serenity::all::ResolvedOption<'_>],
) {
    let channel = command.channel_id.get();

    // The electorate: the invoker plus every named member, de-duplicated by derived key.
    let mut discord_ids = vec![command.user.id.get()];
    for name in ["member2", "member3", "member4"] {
        if let Some(ResolvedValue::User(user, _)) = opts
            .iter()
            .find(|o| o.name == name)
            .map(|o| o.value.clone())
        {
            let id = user.id.get();
            if !discord_ids.contains(&id) {
                discord_ids.push(id);
            }
        }
    }
    let members: Vec<[u8; 32]> = discord_ids
        .iter()
        .map(|id| public_key_of(state, *id))
        .collect();

    // WEIGHTED mode (backlog #22): each member arrives with a standing-derived ballot
    // weight (1 + run-credits at open — the honest source is spelled out on the surface),
    // and every vote press lands on the VERIFIED weighted engine
    // (`collective_choice::cast_weighted`), never the plain cast.
    let weighted = matches!(
        opts.iter().find(|o| o.name == "weighted").map(|o| &o.value),
        Some(ResolvedValue::Boolean(true))
    );
    let weights: Option<Vec<u64>> = if weighted {
        Some(council_weighted::standing_weights(state, &discord_ids).await)
    } else {
        None
    };

    let catalog = match opts
        .iter()
        .find(|o| o.name == "proposals")
        .map(|o| &o.value)
    {
        Some(ResolvedValue::String(s)) => catalog_from(s),
        _ => default_catalog(),
    };
    // A weighted council's quorum is a WEIGHT threshold (defaults to a majority of the
    // total granted weight); an unweighted one counts members.
    let quorum = match opts.iter().find(|o| o.name == "quorum").map(|o| &o.value) {
        Some(ResolvedValue::Integer(n)) => match &weights {
            Some(ws) => {
                (*n as u64).clamp(1, ws.iter().fold(0u64, |a, w| a.saturating_add(*w)).max(1))
            }
            None => (*n as u64).clamp(1, members.len() as u64),
        },
        _ => match &weights {
            Some(ws) => council_weighted::default_weight_quorum(ws),
            None => default_quorum(members.len()),
        },
    };

    // The roster line names the members by their real dregg identity (the electorate is
    // cryptographic — this is exactly what a vote is checked against), plus each member's
    // granted ballot weight when the council is weighted.
    let roster = discord_ids
        .iter()
        .enumerate()
        .map(|(i, id)| {
            let ident = identity_of(state, *id);
            let weight_note = weights
                .as_ref()
                .map(|ws| format!(" · weight {}", ws[i]))
                .unwrap_or_default();
            format!(
                "<@{id}> `{}…`{weight_note}",
                &ident.as_str()[..16.min(ident.as_str().len())]
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    // The honest weight-source line rides WITH the roster (where the weights are shown).
    let roster = match &weights {
        Some(_) => format!("{roster}\n{}", council_weighted::WEIGHT_SOURCE_NOTE),
        None => roster,
    };

    // REFUSE-WITH-CONFIRM (backlog #32): a live council must not be silently wiped by a
    // re-open — its chain (proposals, ballots, enactments) is process-local and unrecoverable.
    // The replacement open is stashed behind an explicit Confirm press.
    if offering::is_open::<CouncilOffering>(channel) {
        let status = offering::with_live::<CouncilOffering, _>(channel, |live| {
            live.offering.status_line(&live.session)
        });
        let cfg = SessionConfig::with_seed(channel);
        let roster_field = offering::truncate(&roster, 1000);
        crate::commands::open_guard::refuse_with_confirm(
            ctx,
            command,
            CouncilOffering::KEY,
            status,
            Box::new(move || {
                offering::open_in(
                    channel,
                    move || council_weighted::make_council(members, weights, catalog, quorum),
                    cfg,
                )
                .map_err(|e| e.to_string())?;
                offering::with_live::<CouncilOffering, _>(channel, |live| {
                    offering::surface_of::<CouncilOffering>(live)
                })
                .map(|(embed, rows)| (embed.field("The electorate", roster_field, false), rows))
                .ok_or_else(|| "the fresh session did not render".to_string())
            }),
        )
        .await;
        return;
    }

    if let Err(e) = offering::open_in(
        channel,
        move || council_weighted::make_council(members, weights, catalog, quorum),
        SessionConfig::with_seed(channel),
    ) {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(
                            CreateEmbed::new()
                                .title("The council did not deploy")
                                .description(format!("The council cell failed to come alive: {e}"))
                                .color(0xE63946),
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }

    let rendered = offering::with_live::<CouncilOffering, _>(channel, |live| {
        offering::surface_of::<CouncilOffering>(live)
    });
    let Some((embed, rows)) = rendered else {
        return;
    };
    let embed = embed.field("The electorate", offering::truncate(&roster, 1000), false);
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
// Tests — the `/council` surface DRIVEN at the logic level: the very same
// `offering::drive` a live button press takes, against the REAL CouncilOffering.
// No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_council::{TURN_APPROVE, TURN_ENACT, TURN_PROPOSE, TURN_REJECT};
    use dreggnet_offerings::Offering;
    use dreggnet_offerings::{DreggIdentity, Outcome};

    use crate::commands::offering::{
        CollectiveClose, Driven, close_in, close_round, fire_id, with_live,
    };

    /// A test electorate of three, and the derived identity of each (exactly what a Discord
    /// member's derived public key produces: `member_identity(pk) == public_key_hex()`).
    fn electorate() -> (Vec<[u8; 32]>, Vec<DreggIdentity>) {
        let pks: Vec<[u8; 32]> = vec![[11u8; 32], [22u8; 32], [33u8; 32]];
        let ids = pks.iter().map(CouncilOffering::member_identity).collect();
        (pks, ids)
    }

    /// Open a council in `channel` through the SAME adapter path `/council open` takes.
    fn open(channel: u64, quorum: u64) -> Vec<DreggIdentity> {
        close_in::<CouncilOffering>(channel);
        let (pks, ids) = electorate();
        offering::open_in(
            channel,
            move || CouncilOffering::new(pks, default_catalog(), quorum),
            SessionConfig::with_seed(channel),
        )
        .expect("the council cell comes alive");
        ids
    }

    /// Press a button, exactly as the live component route does: decode the custom-id, run ONE
    /// real offering turn attributed to the presser's dregg identity.
    fn press(channel: u64, turn: &str, arg: i64, who: &DreggIdentity) -> Outcome {
        match offering::drive::<CouncilOffering>(
            channel,
            &fire_id(CouncilOffering::KEY, turn, arg),
            who.clone(),
        ) {
            Driven::Fired(o) => o,
            other => panic!("a council press must fire a real turn, got {other:?}"),
        }
    }

    fn turns(channel: u64) -> usize {
        with_live::<CouncilOffering, _>(channel, |l| l.session.committed_turns()).unwrap()
    }

    /// The offering's cap-gated actions render as the right Discord components: a PROPOSE per
    /// un-proposed catalog item, each carrying its own `offering:fire:council:<turn>:<arg>` id.
    #[test]
    fn the_council_actions_render_as_discord_affordances() {
        let channel = 90_001;
        open(channel, 2);
        let actions = with_live::<CouncilOffering, _>(channel, |l| l.offering.actions(&l.session))
            .expect("a live council");
        assert_eq!(
            actions.len(),
            default_catalog().len(),
            "a fresh council offers exactly one PROPOSE per catalog item"
        );
        assert!(actions.iter().all(|a| a.turn == TURN_PROPOSE && a.enabled));

        // The buttons are real Discord rows, and each id round-trips back to its typed action.
        let rows = offering::action_rows::<CouncilOffering>(&actions);
        assert_eq!(
            rows.len(),
            2,
            "three affordances fit one action row, plus the standing ⛓ re-verify row"
        );
        for a in &actions {
            let id = fire_id(CouncilOffering::KEY, &a.turn, a.arg);
            assert_eq!(
                offering::parse_press(&id),
                Some(offering::Press::Fire {
                    key: "council".into(),
                    turn: TURN_PROPOSE.into(),
                    arg: a.arg
                })
            );
        }
        close_in::<CouncilOffering>(channel);
    }

    /// **The whole governance flow, driven as button presses.** propose → two approvals →
    /// enact: each is a REAL committed turn (a genuine `turn_hash`), the enactment writes the
    /// real policy slot on the council cell, and the chain re-verifies.
    #[test]
    fn propose_vote_enact_drives_real_council_turns() {
        let channel = 90_002;
        let ids = open(channel, 2);
        assert_eq!(turns(channel), 0, "a fresh council has committed nothing");

        // PROPOSE catalog item 0 → a real poll + a real council-cell turn.
        match press(channel, TURN_PROPOSE, 0, &ids[0]) {
            Outcome::Landed { receipt, ended } => {
                assert!(!ended);
                assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
            }
            other => panic!("PROPOSE must land, got {other:?}"),
        }
        assert_eq!(turns(channel), 1);

        // The surface now offers APPROVE / REJECT / ENACT on proposal 0 — with ENACT shown
        // LOCKED (below quorum), the cap tooth rendered rather than hidden.
        let actions =
            with_live::<CouncilOffering, _>(channel, |l| l.offering.actions(&l.session)).unwrap();
        let enact = actions
            .iter()
            .find(|a| a.turn == TURN_ENACT && a.arg == 0)
            .expect("ENACT is on the surface");
        assert!(!enact.enabled, "ENACT is locked below quorum");
        assert!(
            actions
                .iter()
                .any(|a| a.turn == TURN_APPROVE && a.arg == 0 && a.enabled)
        );
        assert!(actions.iter().any(|a| a.turn == TURN_REJECT && a.arg == 0));

        // ENACT anyway (the locked button IS pressable) → a REAL quorum-gate refusal; the
        // policy slot stays 0 (the anti-ghost tooth: no phantom effect).
        let before = turns(channel);
        match press(channel, TURN_ENACT, 0, &ids[0]) {
            Outcome::Refused(why) => assert!(
                why.contains("quorum") || why.contains("approved"),
                "the executor's own reason: {why}"
            ),
            other => panic!("a below-quorum ENACT must be refused, got {other:?}"),
        }
        assert_eq!(turns(channel), before, "a refusal commits nothing");
        assert_eq!(
            with_live::<CouncilOffering, _>(channel, |l| l.session.policy_value(0)).unwrap(),
            0,
            "no phantom effect below quorum"
        );

        // Two APPROVE ballots — each a real write-once vote turn.
        for who in &ids[..2] {
            match press(channel, TURN_APPROVE, 0, who) {
                Outcome::Landed { receipt, .. } => assert_ne!(receipt.turn_hash, [0u8; 32]),
                other => panic!("a member's APPROVE must land, got {other:?}"),
            }
        }
        assert_eq!(
            with_live::<CouncilOffering, _>(channel, |l| l.session.tally_of(0)).unwrap(),
            Some((0, 2)),
            "the live tally is 0 reject / 2 approve"
        );

        // ENACT is now shown ENABLED, and lands the real effect.
        let actions =
            with_live::<CouncilOffering, _>(channel, |l| l.offering.actions(&l.session)).unwrap();
        assert!(
            actions
                .iter()
                .any(|a| a.turn == TURN_ENACT && a.arg == 0 && a.enabled),
            "at quorum the ENACT affordance unlocks"
        );
        match press(channel, TURN_ENACT, 0, &ids[0]) {
            Outcome::Landed { receipt, .. } => assert_ne!(receipt.turn_hash, [0u8; 32]),
            other => panic!("an at-quorum ENACT must land, got {other:?}"),
        }
        assert!(with_live::<CouncilOffering, _>(channel, |l| l.session.is_enacted(0)).unwrap());
        assert_eq!(
            with_live::<CouncilOffering, _>(channel, |l| l.session.policy_value(0)).unwrap(),
            default_catalog()[0].value,
            "the passed proposal wrote its REAL policy slot on the council cell"
        );

        // The whole decision chain re-verifies (tallies == light-client recompute; every
        // enactment matches a passing decision; every unenacted slot is still 0).
        let report = offering::verify_live::<CouncilOffering>(channel).expect("a live council");
        assert!(report.verified, "{}", report.detail);
        assert!(report.turns >= 4, "genesis-free: propose + 2 votes + enact");
        assert!(offering::verify_note(&report).starts_with('✓'));

        close_in::<CouncilOffering>(channel);
    }

    /// A press by a Discord user OUTSIDE the electorate is a real `Refused` — the bot does not
    /// gate it, the offering does. Nothing commits.
    #[test]
    fn a_non_member_press_is_refused_honestly() {
        let channel = 90_003;
        let ids = open(channel, 2);
        press(channel, TURN_PROPOSE, 0, &ids[0]);
        let before = turns(channel);

        let stranger = DreggIdentity("ff".repeat(32));
        match press(channel, TURN_APPROVE, 0, &stranger) {
            Outcome::Refused(why) => assert!(why.contains("member"), "{why}"),
            other => panic!("a non-member vote must be refused, got {other:?}"),
        }
        assert_eq!(turns(channel), before, "a stranger's vote commits nothing");
        assert!(
            offering::verify_live::<CouncilOffering>(channel)
                .unwrap()
                .verified
        );
        close_in::<CouncilOffering>(channel);
    }

    /// One identity, one ballot: the second vote is a REAL executor refusal at the nullifier
    /// (not a frontend book-keeping check).
    #[test]
    fn a_double_vote_is_a_real_refusal() {
        let channel = 90_004;
        let ids = open(channel, 2);
        press(channel, TURN_PROPOSE, 1, &ids[0]);
        assert!(matches!(
            press(channel, TURN_APPROVE, 0, &ids[1]),
            Outcome::Landed { .. }
        ));
        let before = turns(channel);
        match press(channel, TURN_REJECT, 0, &ids[1]) {
            Outcome::Refused(why) => assert!(
                why.to_lowercase().contains("already voted") || why.to_lowercase().contains("vote"),
                "{why}"
            ),
            other => panic!("a double vote must be refused, got {other:?}"),
        }
        assert_eq!(turns(channel), before);
        close_in::<CouncilOffering>(channel);
    }

    /// A press in a channel with no council open reports honestly (no session, no turn).
    #[test]
    fn a_press_with_no_session_is_reported() {
        let channel = 90_005;
        close_in::<CouncilOffering>(channel);
        let driven = offering::drive::<CouncilOffering>(
            channel,
            &fire_id(CouncilOffering::KEY, TURN_PROPOSE, 0),
            DreggIdentity("aa".repeat(32)),
        );
        assert!(matches!(driven, Driven::NoSession), "got {driven:?}");
    }

    /// The `close` affordance is REGISTERED on the live surface (the generic collective close —
    /// no more scaffold-only crowd machinery), and a DIRECT offering's close finds no round to
    /// resolve (its presses already resolve one-by-one) rather than faking a crowd turn.
    #[test]
    fn the_close_subcommand_is_registered_and_a_direct_council_has_no_round() {
        let cmd = serde_json::to_value(register()).expect("the command serializes");
        let names: Vec<&str> = cmd["options"]
            .as_array()
            .expect("subcommands")
            .iter()
            .map(|o| o["name"].as_str().unwrap())
            .collect();
        assert!(names.contains(&"close"), "registered: {names:?}");

        let channel = 90_006;
        open(channel, 2);
        assert!(
            matches!(
                close_round::<CouncilOffering>(channel),
                CollectiveClose::NoRound
            ),
            "a direct offering opens no collective round, so there is nothing to close"
        );
        close_in::<CouncilOffering>(channel);
    }

    #[test]
    fn the_catalog_parses_and_defaults() {
        assert_eq!(catalog_from("").len(), default_catalog().len());
        let c = catalog_from("Fund the fork, Ban the bot ,");
        assert_eq!(c.len(), 2);
        assert_eq!(c[0].title, "Fund the fork");
        assert_eq!(c[1].value, 2, "a proposal's policy value is non-zero");
        assert_eq!(default_quorum(3), 2, "a majority of three");
        assert_eq!(default_quorum(4), 3);
    }
}
