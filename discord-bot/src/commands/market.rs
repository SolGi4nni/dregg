//! `/market` — a Discord channel runs a **real sealed-bid auction**: list → sealed bid → settle.
//!
//! The offering is [`dreggnet_market::MarketOffering`], consumed (never re-implemented) through
//! the generic [`crate::commands::offering`] adapter. This is the offering where **value
//! actually moves**, and every press is a real turn on the sealed-auction substrate:
//!
//! * **LIST** births a REAL auction cell through the verified executor (a
//!   `CreateCellFromFactory` turn). The born cell carries its `WriteOnce` commit board +
//!   `StrictMonotonic(PHASE)` lifecycle for life. The modal's number is the **reserve**.
//! * **BID** commits a sealed commit-reveal bid: only the seal digest is public during the
//!   commit phase. A second bid from the SAME dregg identity targets its own frozen commit slot
//!   and is a real `WriteOnce` executor refusal — the anti-double-bid tooth is the substrate's,
//!   not the bot's. A bid after the commit phase closes is refused too.
//! * **SETTLE** closes the commit phase, reveals every bid, and clears to the winning sealed bid
//!   through the VERIFIED per-asset ring settlement (Σδ = 0 per asset). A **below-reserve** high
//!   bid does NOT settle: a real `Refused`, no value moves, no WINNER announced.
//! * **`/market verify`** re-derives the clear from the recorded seals: the winner must be the
//!   real high bid, the post-ledger must reproduce, conservation must hold, and the on-ledger
//!   WINNER / HIGH_BID registers must announce the real winner.
//!
//! The bidder is a **derived dregg identity** (`UserCipherclerk::derive(...)`), not a Discord
//! nickname — so "one bidder, one sealed slot" is a cryptographic statement.

use std::sync::OnceLock;

use serenity::all::{
    CommandInteraction, CommandOptionType, Context, CreateCommand, CreateCommandOption,
    CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dreggnet_market::{MarketOffering, MarketSession, TURN_BID, TURN_LIST};
use dreggnet_offerings::SessionConfig;

use crate::BotState;
use crate::commands::offering::{self, DiscordOffering, Store, ValuePrompt};

/// The market's brand colour.
const MARKET_COLOR: u32 = 0xF4A261;

impl DiscordOffering for MarketOffering {
    const KEY: &'static str = "market";
    const TITLE: &'static str = "DreggNet Market — a sealed-bid auction";
    const COLOR: u32 = MARKET_COLOR;
    const TAGLINE: &'static str =
        "sealed bids · the executor clears · conservation checked (Σδ=0) · the chain remembers";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<MarketOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    /// LIST and BID carry a **typed number** the presser supplies (a reserve, a sealed bid), so
    /// their buttons open a modal rather than firing a fixed arg. SETTLE takes none.
    fn value_prompt(turn: &str) -> Option<ValuePrompt> {
        match turn {
            TURN_LIST => Some(ValuePrompt {
                title: "Open a listing",
                label: "Reserve price (the auction will not clear below it)",
                placeholder: "100",
            }),
            TURN_BID => Some(ValuePrompt {
                title: "Place a sealed bid",
                label: "Your bid (sealed until settle)",
                placeholder: "250",
            }),
            _ => None,
        }
    }

    fn status_line(&self, session: &MarketSession) -> String {
        if !session.is_listed() {
            return "nothing listed yet · 0 verified turns".to_string();
        }
        let state = if session.is_settled() {
            "SETTLED"
        } else {
            "open"
        };
        format!(
            "reserve {} · {} sealed bid(s) · {} · {} verified turns",
            session.reserve(),
            session.bid_count(),
            state,
            session.receipts_len()
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register `/market` (open / status / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("market")
        .description("Run a real sealed-bid auction in this channel — list, bid, settle")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "open",
            "Open a market here (a seller then lists; anyone may bid)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "Show this channel's market: the listing, the sealed bids, the affordances",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify the auction: the winner is the real high bid, the clear conserves",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "close",
            "Close the collective round — resolve the plurality winner as one verified turn",
        ))
}

/// Route `/market` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "open" => handle_open(ctx, command, state).await,
        "status" => offering::handle_status::<MarketOffering>(ctx, command, state).await,
        "verify" => offering::handle_verify::<MarketOffering>(ctx, command).await,
        // The generic collective close ([`offering::handle_close`]): the market is a DIRECT
        // offering today, and the handler says so honestly.
        "close" => offering::handle_close::<MarketOffering>(ctx, command).await,
        _ => {}
    }
}

/// `/market open` — deploy a fresh market session (its own embedded verified executor) and post
/// its surface. The channel id is the deterministic seed, so the listing's cell id re-derives.
async fn handle_open(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    let channel = command.channel_id.get();
    // REFUSE-WITH-CONFIRM (backlog #32): a live auction (its listing + sealed bids) must not
    // be silently wiped by a re-open; the replacement waits behind an explicit Confirm press.
    if offering::is_open::<MarketOffering>(channel) {
        let status = offering::with_live::<MarketOffering, _>(channel, |live| {
            live.offering.status_line(&live.session)
        });
        crate::commands::open_guard::refuse_with_confirm(
            ctx,
            command,
            MarketOffering::KEY,
            status,
            Box::new(move || {
                offering::open_in(
                    channel,
                    MarketOffering::new,
                    SessionConfig::with_seed(channel),
                )
                .map_err(|e| e.to_string())?;
                offering::with_live::<MarketOffering, _>(channel, |live| {
                    offering::surface_of::<MarketOffering>(live)
                })
                .ok_or_else(|| "the fresh session did not render".to_string())
            }),
        )
        .await;
        return;
    }
    if let Err(e) = offering::open_in(
        channel,
        MarketOffering::new,
        SessionConfig::with_seed(channel),
    ) {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(
                            CreateEmbed::new()
                                .title("The market did not open")
                                .description(format!("The session failed to deploy: {e}"))
                                .color(0xE63946),
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }
    let rendered = offering::with_live::<MarketOffering, _>(channel, |live| {
        offering::surface_of::<MarketOffering>(live)
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
// Tests — the `/market` surface DRIVEN at the logic level, through the very same
// `offering::drive` / `offering::drive_value` a live button press + modal take.
// No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_market::TURN_SETTLE;
    use dreggnet_offerings::Offering;
    use dreggnet_offerings::{DreggIdentity, Outcome};

    use crate::commands::offering::{Driven, ask_id, close_in, fire_id, with_live};

    fn who(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    fn open(channel: u64) {
        close_in::<MarketOffering>(channel);
        offering::open_in(
            channel,
            MarketOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("the market session deploys");
    }

    /// The modal-submit path: fire `turn` with the typed value the user entered.
    fn submit(channel: u64, turn: &str, value: i64, actor: &DreggIdentity) -> Outcome {
        match offering::drive_value::<MarketOffering>(channel, turn, value, actor.clone()) {
            Driven::Fired(o) => o,
            other => panic!("a market submit must fire a real turn, got {other:?}"),
        }
    }

    /// The fixed-arg button path (SETTLE).
    fn press(channel: u64, turn: &str, arg: i64, actor: &DreggIdentity) -> Outcome {
        match offering::drive::<MarketOffering>(
            channel,
            &fire_id(MarketOffering::KEY, turn, arg),
            actor.clone(),
        ) {
            Driven::Fired(o) => o,
            other => panic!("a market press must fire a real turn, got {other:?}"),
        }
    }

    /// The `close` affordance is REGISTERED on the live surface (the generic collective close).
    #[test]
    fn the_close_subcommand_is_registered() {
        let cmd = serde_json::to_value(register()).expect("the command serializes");
        let names: Vec<&str> = cmd["options"]
            .as_array()
            .expect("subcommands")
            .iter()
            .map(|o| o["name"].as_str().unwrap())
            .collect();
        assert!(names.contains(&"close"), "registered: {names:?}");
    }

    /// The value-taking affordances render as MODAL buttons; pressing one asks for the value
    /// rather than firing a turn (the typed-arg half of the generic adapter).
    #[test]
    fn a_value_taking_affordance_opens_its_modal() {
        let channel = 91_001;
        open(channel);

        let actions = with_live::<MarketOffering, _>(channel, |l| l.offering.actions(&l.session))
            .expect("a live market");
        assert_eq!(actions.len(), 1, "an unlisted market offers only LIST");
        assert_eq!(actions[0].turn, TURN_LIST);
        // The rendered button is the ASK id (the modal), not a fire id.
        assert_eq!(
            offering::parse_press(&ask_id(MarketOffering::KEY, TURN_LIST)),
            Some(offering::Press::Ask {
                key: "market".into(),
                turn: TURN_LIST.into()
            })
        );
        // One affordance row + the standing ⛓ re-verify chain row (backlog Tier-2 #10).
        assert_eq!(offering::action_rows::<MarketOffering>(&actions).len(), 2);

        match offering::drive::<MarketOffering>(
            channel,
            &ask_id(MarketOffering::KEY, TURN_LIST),
            who("aa"),
        ) {
            Driven::NeedsValue { turn, prompt } => {
                assert_eq!(turn, TURN_LIST);
                assert_eq!(prompt.title, "Open a listing");
            }
            other => panic!("LIST must ask for its reserve, got {other:?}"),
        }
        close_in::<MarketOffering>(channel);
    }

    /// **The whole commerce flow, driven as presses.** list → two sealed bids → settle: every
    /// step is a real verified turn, the clear moves value conservation-checked, and the chain
    /// re-verifies (the winner IS the real high bid).
    #[test]
    fn list_bid_settle_moves_real_value() {
        let channel = 91_002;
        open(channel);
        let seller = who("5e");
        let alice = who("a1");
        let bob = who("b0");

        // LIST at reserve 100 — a real factory-birth turn.
        match submit(channel, TURN_LIST, 100, &seller) {
            Outcome::Landed { receipt, ended } => {
                assert!(!ended);
                assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine birth turn");
            }
            other => panic!("LIST must land, got {other:?}"),
        }
        assert!(with_live::<MarketOffering, _>(channel, |l| l.session.is_listed()).unwrap());

        // Two sealed bids — each a real commit turn onto the WriteOnce board.
        assert!(matches!(
            submit(channel, TURN_BID, 250, &alice),
            Outcome::Landed { .. }
        ));
        assert!(matches!(
            submit(channel, TURN_BID, 400, &bob),
            Outcome::Landed { .. }
        ));
        assert_eq!(
            with_live::<MarketOffering, _>(channel, |l| l.session.bid_count()).unwrap(),
            2
        );

        // SETTLE — reveal + clear to the high sealed bid through the verified ring settlement.
        match press(channel, TURN_SETTLE, 0, &seller) {
            Outcome::Landed { receipt, ended } => {
                assert!(ended, "a cleared auction ends the session");
                assert_ne!(receipt.turn_hash, [0u8; 32]);
            }
            other => panic!("SETTLE must land, got {other:?}"),
        }
        let (price, conserved, settled) = with_live::<MarketOffering, _>(channel, |l| {
            let c = l.session.clearing().expect("a cleared auction");
            (c.price(), c.conserved(), l.session.is_settled())
        })
        .unwrap();
        assert!(settled);
        assert_eq!(price, 400, "the clear went to the REAL high sealed bid");
        assert!(conserved, "every asset's supply is preserved (Σδ = 0)");

        // The cleared chain re-verifies (winner == real high bid, post-ledger reproduces,
        // conservation holds, the on-ledger WINNER/HIGH_BID registers agree).
        let report = offering::verify_live::<MarketOffering>(channel).expect("a live market");
        assert!(report.verified, "{}", report.detail);
        assert!(
            report.turns >= 4,
            "birth + 2 commits + close + reveals + resolve"
        );
        close_in::<MarketOffering>(channel);
    }

    /// One identity, one sealed slot: a second bid from the SAME dregg identity is a real
    /// `WriteOnce` executor refusal. Nothing commits (anti-ghost).
    #[test]
    fn a_double_bid_is_a_real_executor_refusal() {
        let channel = 91_003;
        open(channel);
        let seller = who("5e");
        let alice = who("a1");
        submit(channel, TURN_LIST, 10, &seller);
        assert!(matches!(
            submit(channel, TURN_BID, 200, &alice),
            Outcome::Landed { .. }
        ));
        let before = with_live::<MarketOffering, _>(channel, |l| l.session.receipts_len()).unwrap();

        match submit(channel, TURN_BID, 900, &alice) {
            Outcome::Refused(why) => assert!(
                why.to_lowercase().contains("double-bid"),
                "the substrate's own refusal: {why}"
            ),
            other => panic!("a double bid must be refused, got {other:?}"),
        }
        assert_eq!(
            with_live::<MarketOffering, _>(channel, |l| l.session.receipts_len()).unwrap(),
            before,
            "a refused double-bid commits nothing"
        );
        assert_eq!(
            with_live::<MarketOffering, _>(channel, |l| l.session.bid_count()).unwrap(),
            1
        );
        close_in::<MarketOffering>(channel);
    }

    /// **The reserve tooth.** A high sealed bid below the reserve does NOT settle: a real
    /// refusal, no value moves, no winner announced — and the honest chain still re-verifies.
    #[test]
    fn a_below_reserve_auction_does_not_settle() {
        let channel = 91_004;
        open(channel);
        let seller = who("5e");
        let alice = who("a1");
        submit(channel, TURN_LIST, 500, &seller);
        submit(channel, TURN_BID, 100, &alice);

        match press(channel, TURN_SETTLE, 0, &seller) {
            Outcome::Refused(why) => assert!(
                why.contains("reserve"),
                "the substrate's own reserve refusal: {why}"
            ),
            other => panic!("a below-reserve settle must be refused, got {other:?}"),
        }
        assert!(
            !with_live::<MarketOffering, _>(channel, |l| l.session.is_settled()).unwrap(),
            "no sale — nothing settled"
        );
        assert!(
            !with_live::<MarketOffering, _>(channel, |l| l.session.clearing().is_some()).unwrap(),
            "no clearing recorded"
        );
        assert!(
            offering::verify_live::<MarketOffering>(channel)
                .unwrap()
                .verified,
            "the committed (uncleared) board still re-verifies"
        );
        close_in::<MarketOffering>(channel);
    }

    /// An out-of-order affordance (a bid before anything is listed) is a real refusal, surfaced
    /// honestly — the cap tooth is the substrate's.
    #[test]
    fn a_bid_before_the_listing_is_refused() {
        let channel = 91_005;
        open(channel);
        match submit(channel, TURN_BID, 50, &who("a1")) {
            Outcome::Refused(why) => assert!(why.contains("LIST"), "{why}"),
            other => panic!("a bid before listing must be refused, got {other:?}"),
        }
        let note = offering::outcome_note(&Outcome::Refused("nothing is listed yet".into()));
        assert!(note.contains("no receipt"), "{note}");
        close_in::<MarketOffering>(channel);
    }
}
