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

use dreggnet_market::{
    DarkBazaarOffering, DarkBazaarSession, MarketOffering, MarketSession, TURN_BID, TURN_LIST,
};
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

/// The distinct Dark Bazaar CRAWL surface. It deliberately reuses the generic offering adapter:
/// no second slash command and no Discord-side market logic. The title/tagline keep the current
/// grade visible — sealed during commit, operator-visible at settlement, check-level replay.
impl DiscordOffering for DarkBazaarOffering {
    const KEY: &'static str = "bazaar";
    const TITLE: &'static str = "The Dark Bazaar — playable CRAWL";
    const COLOR: u32 = 0x5B3A8E;
    const TAGLINE: &'static str =
        "CRAWL · sealed during commit · operator-visible at settle · replay + conservation checked";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<DarkBazaarOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    fn value_prompt(turn: &str) -> Option<ValuePrompt> {
        match turn {
            TURN_LIST => Some(ValuePrompt {
                title: "Open a Dark Bazaar listing",
                label: "Reserve price (bids reveal to the operator at settle)",
                placeholder: "100",
            }),
            TURN_BID => Some(ValuePrompt {
                title: "Place a sealed crawl bid",
                label: "Your bid (sealed until settle; operator-visible then)",
                placeholder: "250",
            }),
            _ => None,
        }
    }

    fn open_hint() -> String {
        "/play offering:bazaar".to_string()
    }

    fn status_line(&self, session: &DarkBazaarSession) -> String {
        if !session.is_listed() {
            return "CRAWL · nothing listed yet · 0 verified turns · operator-visible at settle"
                .to_string();
        }
        let market = session.market();
        let state = if session.is_settled() {
            "SETTLED"
        } else {
            "open"
        };
        format!(
            "CRAWL · reserve {} · {} sealed bid(s) · {} · {} verified turns · check-level, not Tier0/ZK",
            market.reserve(),
            session.bid_count(),
            state,
            market.receipts_len()
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
    // NEVER A SILENT DROP. The session ALREADY OPENED above; if the render then found nothing
    // (a concurrent close, or the offering store thread refusing the read) this used to `return`
    // without ever answering the interaction — so the player saw "This interaction failed" on a
    // market that was, in fact, live in their channel. Say what happened instead.
    let Some((embed, rows)) = rendered else {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(
                            CreateEmbed::new()
                                .title("The session opened but did not render")
                                .description(
                                    "The session was not there to render (it may have been \
                                     closed the same instant). Run the command again.",
                                )
                                .color(0xE63946),
                        )
                        .ephemeral(true),
                ),
            )
            .await;
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

    use crate::commands::offering::{
        Driven, ask_id_in, close_in, control_stamp_in, fire_id_at, fire_id_in, with_live,
    };

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

    #[test]
    fn dark_bazaar_command_flow_is_sealed_substitution_safe_and_replayable() {
        let channel = 91_050;
        close_in::<DarkBazaarOffering>(channel);
        offering::open_in(
            channel,
            DarkBazaarOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("the Dark Bazaar crawl deploys");

        assert_eq!(
            <DarkBazaarOffering as DiscordOffering>::KEY,
            DarkBazaarOffering::KEY
        );
        assert_eq!(DarkBazaarOffering::open_hint(), "/play offering:bazaar");
        assert!(
            DarkBazaarOffering::TAGLINE.contains("operator-visible at settle"),
            "the current privacy grade is player-visible"
        );
        let list_prompt = DarkBazaarOffering::value_prompt(TURN_LIST).expect("LIST asks a reserve");
        let bid_prompt = DarkBazaarOffering::value_prompt(TURN_BID).expect("BID asks a value");
        assert!(list_prompt.label.contains("operator"));
        assert!(bid_prompt.label.contains("operator-visible"));

        let actions = with_live::<DarkBazaarOffering, _>(channel, |live| {
            live.offering.actions(&live.session)
        })
        .expect("a live Dark Bazaar crawl");
        assert_eq!(actions.len(), 1);
        assert_eq!(actions[0].turn, TURN_LIST);
        assert_eq!(
            offering::parse_press(&ask_id_in::<DarkBazaarOffering>(channel, TURN_LIST).unwrap(),),
            Some(offering::Press::Ask {
                key: "bazaar".into(),
                stamp: control_stamp_in::<DarkBazaarOffering>(channel).unwrap(),
                turn: TURN_LIST.into(),
            })
        );

        let seller = who("seller");
        let alice = who("alice");
        let bob = who("bob");
        match offering::drive_value::<DarkBazaarOffering>(channel, TURN_LIST, 100, seller.clone()) {
            Driven::Fired(Outcome::Landed { .. }) => {}
            other => panic!("the generic modal path must land the real LIST turn, got {other:?}"),
        }

        // A component copied from the ordinary market is not a Bazaar command,
        // even though the two games deliberately share LIST/BID/SETTLE verbs.
        let before_substitution = with_live::<DarkBazaarOffering, _>(channel, |live| {
            live.session.market().receipts_len()
        });
        assert!(matches!(
            offering::drive::<DarkBazaarOffering>(
                channel,
                &fire_id_at(
                    MarketOffering::KEY,
                    control_stamp_in::<DarkBazaarOffering>(channel).unwrap(),
                    TURN_SETTLE,
                    0,
                ),
                seller.clone(),
            ),
            Driven::NotOurs
        ));
        assert_eq!(
            with_live::<DarkBazaarOffering, _>(channel, |live| {
                live.session.market().receipts_len()
            }),
            before_substitution,
            "cross-game custom-id substitution cannot mutate the Bazaar"
        );

        let alice_bid = 731_557;
        let bob_bid = 982_451;
        for (bidder, amount) in [(alice.clone(), alice_bid), (bob.clone(), bob_bid)] {
            assert!(matches!(
                offering::drive_value::<DarkBazaarOffering>(channel, TURN_BID, amount, bidder,),
                Driven::Fired(Outcome::Landed { .. })
            ));
        }

        // The shared Discord projection can announce the number of commitments,
        // never their values or bidder identities while the commit phase is open.
        let public_before_settle = with_live::<DarkBazaarOffering, _>(channel, |live| {
            format!("{:?}", live.offering.render(&live.session).view())
        })
        .expect("the crawl remains live");
        for secret in [
            alice_bid.to_string(),
            bob_bid.to_string(),
            alice.0.clone(),
            bob.0.clone(),
        ] {
            assert!(
                !public_before_settle.contains(&secret),
                "the shared pre-settle surface leaked `{secret}`: {public_before_settle}"
            );
        }

        match offering::drive::<DarkBazaarOffering>(
            channel,
            &fire_id_in::<DarkBazaarOffering>(channel, TURN_SETTLE, 0).unwrap(),
            seller,
        ) {
            Driven::Fired(Outcome::Landed { ended: true, .. }) => {}
            other => panic!("the exact Bazaar SETTLE command must clear, got {other:?}"),
        }
        let report = offering::verify_live::<DarkBazaarOffering>(channel)
            .expect("the settled Bazaar remains available for replay");
        assert!(report.verified, "{}", report.detail);
        assert!(
            report.detail.contains("CRAWL check-level replay"),
            "the replay result keeps the actual privacy/proof grade visible: {}",
            report.detail
        );
        let clearing_price = with_live::<DarkBazaarOffering, _>(channel, |live| {
            live.session.clearing().expect("settled clear").price()
        })
        .unwrap();
        assert_eq!(clearing_price, i128::from(bob_bid));

        let status = with_live::<DarkBazaarOffering, _>(channel, |live| {
            live.offering.status_line(&live.session)
        })
        .expect("the crawl remains live");
        assert!(status.contains("CRAWL"), "{status}");
        assert!(status.contains("not Tier0/ZK"), "{status}");
        close_in::<DarkBazaarOffering>(channel);
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
            &fire_id_in::<MarketOffering>(channel, turn, arg).unwrap(),
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
            offering::parse_press(&ask_id_in::<MarketOffering>(channel, TURN_LIST).unwrap()),
            Some(offering::Press::Ask {
                key: "market".into(),
                stamp: control_stamp_in::<MarketOffering>(channel).unwrap(),
                turn: TURN_LIST.into()
            })
        );
        // One affordance row + the standing ⛓ re-verify chain row (backlog Tier-2 #10).
        assert_eq!(offering::action_rows::<MarketOffering>(&actions).len(), 2);

        match offering::drive::<MarketOffering>(
            channel,
            &ask_id_in::<MarketOffering>(channel, TURN_LIST).unwrap(),
            who("aa"),
        ) {
            Driven::NeedsValue { turn, prompt, .. } => {
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

    /// Discord consumes the same payload-free semantic action and viewer-blind
    /// public receipt as the browser adapter; there is no bot-local Bazaar DTO.
    #[test]
    fn discord_renders_the_shared_private_bazaar_journey_contract() {
        use dreggnet_market::private_bazaar_journey::{
            PrivateBazaarPublicAction, TURN_ENTER_PRIVATE_BAZAAR,
            contract_fixtures::{sample_pending_receipt, sample_settled_receipt},
        };

        // A REAL, crate-authored, viewer-blind pending receipt — never fabricated
        // from external dummy bytes. The removed public `pending(...)` constructor
        // is replaced by the market crate's own `contract-fixtures` receipt.
        let receipt = sample_pending_receipt();
        let surface = receipt.surface();
        let action = PrivateBazaarPublicAction::Enter.offering_action();

        let card = deos_view::discord::render_card(
            <DarkBazaarOffering as DiscordOffering>::TITLE,
            surface.view(),
            &[],
        );
        let embed = serde_json::to_string(&card.embed).expect("Discord embed JSON");
        let rows = offering::action_rows::<DarkBazaarOffering>(std::slice::from_ref(&action));
        let controls = serde_json::to_string(&rows).expect("Discord component JSON");
        assert!(embed.contains("Dark Bazaar raid"), "{embed}");
        assert!(controls.contains(TURN_ENTER_PRIVATE_BAZAAR), "{controls}");
        for forbidden in ["winner", "reserve", "private bid", "proof bytes", "witness"] {
            assert!(
                !embed.contains(forbidden),
                "shared Discord receipt leaked {forbidden}: {embed}"
            );
        }
        assert_eq!(
            PrivateBazaarPublicAction::from_offering_action(&action),
            Ok(PrivateBazaarPublicAction::Enter)
        );
        assert_eq!(action.arg, 0);
        assert!(action.text.is_none());

        // The SETTLED phase is likewise a real, crate-authored, viewer-blind
        // receipt: it can only exist with every committed authority field present
        // (the enum has no public field-mutation path anymore), so we render the
        // market crate's canonical settled contract fixture.
        let settled = sample_settled_receipt();
        let settled_card = deos_view::discord::render_card(
            <DarkBazaarOffering as DiscordOffering>::TITLE,
            settled.surface().view(),
            &[],
        );
        let settled_embed =
            serde_json::to_string(&settled_card.embed).expect("settled Discord embed JSON");
        assert!(settled_embed.contains("settled"), "{settled_embed}");
        // The settled surface still tells the viewer that one authenticated private
        // result caused a real game consequence (codex reworded "real game-engine
        // turn" → "one exact game effect"); assert on the crate's current text.
        assert!(
            settled_embed.contains("exact game effect"),
            "{settled_embed}"
        );
        for forbidden in ["winner", "reserve", "private bid", "proof bytes", "witness"] {
            assert!(
                !settled_embed.contains(forbidden),
                "settled Discord receipt leaked {forbidden}: {settled_embed}"
            );
        }
    }
}
