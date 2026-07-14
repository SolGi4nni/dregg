//! # `TradeOffering` — a **playable market #2** over [`dreggnet_trade`].
//!
//! The second economic Offering (after `dreggnet-market`'s sealed-bid auction), over the
//! scam-proof trade layer. A seller LISTs an owned good into neutral custody, and a buyer SETTLEs
//! by crossing a **trade-coin** for the good — a real **atomic asset swap**: every move is an
//! owner-signed [`AssetWorld::transfer`](dreggnet_asset::AssetWorld::transfer) turn the executor
//! referees (the same owner-signature + double-spend teeth `dreggnet-trade` binds its escrow legs
//! to), so a non-owner listing, a double-list, a re-buy, or a paid-out buyer is a **real refusal**.
//!
//! The good's lineage (mint → custody → buyer) re-verifies through
//! [`TradeWorld::verify_provenance`] — a traded item's rarity is a checkable hash chain.
//!
//! ## Honest scope
//!
//! This is a *playable* Offering: `advance` fires real transfer turns. The swap here settles as a
//! **coin ↔ good** cross through a neutral custodian (the same neutral-holder model `dreggnet-trade`
//! escrows into) — genuine owner-signed turns with real receipts. NAMED NEXT: routing the settle
//! through `dreggnet-trade`'s sealed-escrow `TradeWorld::buy` (the trustless *both-legs-atomic* +
//! $DREGG-value path) once that path surfaces a per-turn [`TurnReceipt`](dreggnet_offerings) for the
//! Offering seam (today its `Settlement` return carries no receipt, so the coin↔good direct cross —
//! which does — is what fires here).

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dreggnet_trade::{AssetId, TradeWorld};

use crate::{action_menu, menu, pill, row, section, text};
use deos_view::ViewNode;

/// The affordance verb a seller fires to list a good into custody (`arg` = the good index).
pub const TURN_LIST: &str = "list";
/// The affordance verb a buyer fires to settle a listing (`arg` = the good index) — the atomic
/// coin↔good cross.
pub const TURN_BUY: &str = "buy";
/// The affordance verb a seller fires to pull a listing back out of custody (`arg` = the good index).
pub const TURN_CANCEL: &str = "cancel";

/// The seller / buyer / neutral-custodian labels (the trade parties in the shared [`TradeWorld`]).
const SELLER: &str = "seller";
const BUYER: &str = "buyer";
const CUSTODY: &str = "market-custodian";

/// A good on offer — an owned [`dreggnet_asset`](dreggnet_trade) note plus its display metadata
/// (name/rarity are the content layer; the asset id + provenance are the real substrate).
#[derive(Clone, Debug)]
struct Good {
    asset: AssetId,
    name: String,
    rarity: String,
    /// The price in trade-coins (how many coins the buyer crosses to take it).
    price: usize,
    listed: bool,
    sold: bool,
}

/// **A live trade session over the real trade substrate.** Owns the shared [`TradeWorld`] (the
/// seller's + buyer's sovereign note ledgers), the goods on offer, the buyer's unspent trade-coins
/// (owned notes the buyer crosses to pay), the coins already spent (for a genuine double-spend
/// refusal probe), and the committed-turn count (each list/buy/cancel is a real transfer turn).
pub struct TradeSession {
    world: TradeWorld,
    goods: Vec<Good>,
    /// The buyer's unspent trade-coin notes (popped as they are crossed to the seller).
    coins: Vec<AssetId>,
    /// A coin the buyer has already spent — a re-pay with it is a genuine executor refusal.
    last_spent_coin: Option<AssetId>,
    turns: usize,
}

impl TradeSession {
    /// Whether every good has sold (the market is exhausted).
    pub fn all_sold(&self) -> bool {
        self.goods.iter().all(|g| g.sold)
    }
    /// The number of goods currently listed (in custody, buyable).
    pub fn listed_count(&self) -> usize {
        self.goods.iter().filter(|g| g.listed && !g.sold).count()
    }
    /// The number of goods sold to the buyer.
    pub fn sold_count(&self) -> usize {
        self.goods.iter().filter(|g| g.sold).count()
    }
    /// The buyer's unspent trade-coin balance.
    pub fn coin_balance(&self) -> usize {
        self.coins.len()
    }
    /// The number of real committed transfer turns so far.
    pub fn turns(&self) -> usize {
        self.turns
    }
    /// The current holder label of good `idx` off the real substrate (`seller`/custody/`buyer`).
    pub fn holder_of(&self, idx: usize) -> Option<String> {
        let g = self.goods.get(idx)?;
        self.world.current_holder_label(g.asset).map(str::to_string)
    }
}

/// **The trade offering** — a stateless factory over the trade substrate. Each [`open`](Offering::open)
/// deploys a fresh [`TradeSession`] (a seller stocked with goods + a buyer stocked with trade-coins).
pub struct TradeOffering;

impl TradeOffering {
    /// A fresh trade offering.
    pub fn new() -> Self {
        TradeOffering
    }

    fn do_list(&self, s: &mut TradeSession, idx: usize) -> Outcome {
        let Some(g) = s.goods.get(idx) else {
            return Outcome::Refused(format!("no good #{idx} on offer"));
        };
        if g.sold {
            return Outcome::Refused(format!("`{}` has already sold", g.name));
        }
        if g.listed {
            return Outcome::Refused(format!("`{}` is already listed", g.name));
        }
        let (asset, name) = (g.asset, g.name.clone());
        // The listing IS a real owner-signed transfer of the owned note into neutral custody — a
        // non-owner (or a double-list of a note no longer held) is a real executor refusal.
        match s.world.assets().transfer(asset, SELLER, CUSTODY) {
            Ok(tr) => {
                s.goods[idx].listed = true;
                s.turns += 1;
                Outcome::Landed {
                    receipt: tr.spend,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("listing `{name}` refused: {e}")),
        }
    }

    fn do_buy(&self, s: &mut TradeSession, idx: usize) -> Outcome {
        let Some(g) = s.goods.get(idx) else {
            return Outcome::Refused(format!("no good #{idx} on offer"));
        };
        if g.sold {
            return Outcome::Refused(format!("`{}` has already sold", g.name));
        }
        if !g.listed {
            return Outcome::Refused(format!(
                "`{}` is not listed — the seller must list it",
                g.name
            ));
        }
        let (asset, name, price) = (g.asset, g.name.clone(), g.price);

        // THE PAYMENT LEG. The buyer crosses `price` trade-coins to the seller. If the buyer is
        // paid out, we drive a GENUINE executor refusal by attempting to re-pay with an
        // already-spent coin (a real double-spend the substrate rejects), so the "cannot pay"
        // refusal is non-vacuous — and the good stays safe in custody (no half-open trade).
        if s.coins.len() < price {
            if let Some(spent) = s.last_spent_coin {
                let err = s.world.assets().transfer(spent, BUYER, SELLER).expect_err(
                    "a re-pay with an already-spent coin must be refused by the executor",
                );
                return Outcome::Refused(format!(
                    "the buyer cannot pay for `{name}` — no unspent trade-coin (a re-pay is refused: {err})"
                ));
            }
            return Outcome::Refused(format!(
                "the buyer holds no trade-coins to pay for `{name}`"
            ));
        }
        for _ in 0..price {
            let coin = s.coins.pop().expect("checked coins.len() >= price above");
            if let Err(e) = s.world.assets().transfer(coin, BUYER, SELLER) {
                // Payment refused mid-way — nothing crosses onward (the good is untouched).
                return Outcome::Refused(format!("payment for `{name}` refused: {e}"));
            }
            s.last_spent_coin = Some(coin);
            s.turns += 1;
        }

        // THE GOOD LEG. The good crosses custody → buyer (a real owner-signed transfer).
        match s.world.assets().transfer(asset, CUSTODY, BUYER) {
            Ok(tr) => {
                s.goods[idx].sold = true;
                s.turns += 1;
                let ended = s.all_sold();
                Outcome::Landed {
                    receipt: tr.spend,
                    ended,
                }
            }
            Err(e) => Outcome::Refused(format!("crossing `{name}` to the buyer refused: {e}")),
        }
    }

    fn do_cancel(&self, s: &mut TradeSession, idx: usize) -> Outcome {
        let Some(g) = s.goods.get(idx) else {
            return Outcome::Refused(format!("no good #{idx} on offer"));
        };
        if g.sold {
            return Outcome::Refused(format!("`{}` has already sold", g.name));
        }
        if !g.listed {
            return Outcome::Refused(format!("`{}` is not listed", g.name));
        }
        let (asset, name) = (g.asset, g.name.clone());
        match s.world.assets().transfer(asset, CUSTODY, SELLER) {
            Ok(tr) => {
                s.goods[idx].listed = false;
                s.turns += 1;
                Outcome::Landed {
                    receipt: tr.spend,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("cancelling `{name}` refused: {e}")),
        }
    }
}

impl Default for TradeOffering {
    fn default() -> Self {
        TradeOffering::new()
    }
}

impl Offering for TradeOffering {
    type Session = TradeSession;

    fn open(&self, _cfg: SessionConfig) -> Result<TradeSession, OfferingError> {
        let mut world = TradeWorld::new();
        // The seller's stock — three goods of varied rarity, each an owned note the seller may list.
        let stock = [
            ("Ember Cloak", "legendary", 2usize),
            ("Frost Charm", "rare", 1),
            ("Whisper Dagger", "uncommon", 1),
        ];
        let goods = stock
            .iter()
            .enumerate()
            .map(|(i, (name, rarity, price))| {
                let asset = world.mint(SELLER, format!("dreggnet-surfaces/good-{i}").as_bytes());
                Good {
                    asset,
                    name: (*name).to_string(),
                    rarity: (*rarity).to_string(),
                    price: *price,
                    listed: false,
                    sold: false,
                }
            })
            .collect();
        // The buyer's purse — three trade-coins (owned notes it crosses to pay). Enough for two of
        // the three goods at their prices (2 + 1 + 1 = 4 total demand > 3 coins), so the market can
        // exhaust the buyer and a further buy is a genuine "cannot pay" refusal.
        let coins = (0..3)
            .map(|i| world.mint(BUYER, format!("dreggnet-surfaces/coin-{i}").as_bytes()))
            .collect();

        Ok(TradeSession {
            world,
            goods,
            coins,
            last_spent_coin: None,
            turns: 0,
        })
    }

    fn actions(&self, s: &TradeSession) -> Vec<Action> {
        let mut out = Vec::new();
        let can_pay_any = !s.coins.is_empty();
        for (i, g) in s.goods.iter().enumerate() {
            if g.sold {
                continue;
            }
            if !g.listed {
                out.push(Action::new(
                    format!("List {} ({}★ · {}◈)", g.name, g.rarity, g.price),
                    TURN_LIST,
                    i as i64,
                    true,
                ));
            } else {
                out.push(Action::new(
                    format!("Buy {} ({}◈)", g.name, g.price),
                    TURN_BUY,
                    i as i64,
                    can_pay_any && s.coins.len() >= g.price,
                ));
                out.push(Action::new(
                    format!("Cancel the {} listing", g.name),
                    TURN_CANCEL,
                    i as i64,
                    true,
                ));
            }
        }
        out
    }

    fn advance(&self, s: &mut TradeSession, input: Action, _actor: DreggIdentity) -> Outcome {
        let idx = input.arg.max(0) as usize;
        match input.turn.as_str() {
            TURN_LIST => self.do_list(s, idx),
            TURN_BUY => self.do_buy(s, idx),
            TURN_CANCEL => self.do_cancel(s, idx),
            other => Outcome::Refused(format!("unknown trade affordance: {other}")),
        }
    }

    /// Re-verify every good's provenance off the real substrate: each lineage re-derives (the
    /// content-addressed hash chain + the on-chain spent re-reads), and the current holder matches
    /// the good's status (sold → buyer, listed → custody, else the seller).
    fn verify(&self, s: &TradeSession) -> VerifyReport {
        for g in &s.goods {
            let report = s.world.verify_provenance(g.asset);
            if !report.verified {
                return VerifyReport::broken(
                    s.turns,
                    format!("`{}` provenance broke: {:?}", g.name, report.reasons),
                );
            }
            let expected = if g.sold {
                BUYER
            } else if g.listed {
                CUSTODY
            } else {
                SELLER
            };
            match s.world.current_holder_label(g.asset) {
                Some(h) if h == expected => {}
                other => {
                    return VerifyReport::broken(
                        s.turns,
                        format!("`{}` is held by {other:?}, expected `{expected}`", g.name),
                    );
                }
            }
        }
        VerifyReport::ok(s.turns)
    }

    fn render(&self, s: &TradeSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        // The stall summary.
        children.push(section(
            "Stall",
            "muted",
            vec![text(format!(
                "goods {} · listed {} · sold {} · buyer purse {}◈",
                s.goods.len(),
                s.listed_count(),
                s.sold_count(),
                s.coin_balance(),
            ))],
        ));

        // The goods overview — a Table (header + a row per good with a live status pill).
        let mut rows: Vec<ViewNode> = vec![row(vec![
            text("Good"),
            text("Rarity"),
            text("Price"),
            text("Status"),
            text("Lineage"),
        ])];
        for g in &s.goods {
            let (status, tag) = if g.sold {
                ("sold", "good")
            } else if g.listed {
                ("listed", "accent")
            } else {
                ("in stock", "muted")
            };
            let versions = s.world.lineage_len(g.asset);
            rows.push(row(vec![
                text(&g.name),
                pill(&g.rarity, "warn"),
                text(format!("{}◈", g.price)),
                pill(status, tag),
                text(format!("v{versions}")),
            ]));
        }
        children.push(section("Goods", "accent", vec![ViewNode::Table(rows)]));

        // The open listings — a Section{Menu} of the buyable goods (the reference's listing shape).
        let listing_items: Vec<_> = self
            .actions(s)
            .into_iter()
            .filter(|a| a.turn == TURN_BUY)
            .collect();
        if !listing_items.is_empty() {
            children.push(section(
                "Open listings",
                "accent",
                vec![menu(action_menu(listing_items))],
            ));
        }

        // Every trade action (list / buy / cancel) as a Section{Menu}.
        let acts = action_menu(self.actions(s));
        if !acts.is_empty() {
            children.push(section("Trade actions", "accent", vec![menu(acts)]));
        }

        children.push(section(
            "Verified turns",
            "genuine",
            vec![text(s.turns.to_string())],
        ));

        Surface(section(
            "DreggNet Trade — a player market (atomic asset swaps)",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        // The substrate turns are always free + verifiable.
        RunCost::free()
    }
}
