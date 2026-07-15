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
//! [`verify_provenance`](dreggnet_asset::AssetWorld::verify_provenance) — a traded item's rarity is
//! a checkable hash chain.
//!
//! ## What the seller can sell
//!
//! [`TradeOffering::in_world`] opens the stall onto a [`SharedWorld`] — the ONE ledger
//! [`crate::craft`] forges into and [`crate::inventory`] lists. The goods are then a LIVE read of
//! the player's shelf, so **anything the player forges is listable the moment it is forged**: the
//! crafted note crosses to a buyer as the EXACT note-cell the forge minted, its provenance lineage
//! CONTINUING (mint(craft) → the crafter's claim → custody → buyer) in one ledger rather than
//! restarting in a second world. The canned stock is exactly what its name says — an initial
//! seeding of that shared world, the player's own notes, sitting beside what they craft.
//! [`TradeOffering::new`] keeps the old siloed shape (a private world per session).
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
use dreggnet_trade::AssetId;

use crate::world::SharedWorld;
use crate::{action_menu, menu, pill, row, section, text};
use deos_view::ViewNode;

/// The affordance verb a seller fires to list a good into custody (`arg` = the good index).
pub const TURN_LIST: &str = "list";
/// The affordance verb a buyer fires to settle a listing (`arg` = the good index) — the atomic
/// coin↔good cross.
pub const TURN_BUY: &str = "buy";
/// The affordance verb a seller fires to pull a listing back out of custody (`arg` = the good index).
pub const TURN_CANCEL: &str = "cancel";

/// The seller label of a SILOED stall ([`TradeOffering::new`]). A shared stall sells as its world's
/// canonical player — the one identity the forge crafts as and the inventory lists for.
const SELLER: &str = "seller";
/// The buyer label (holds the trade-coin purse in the shared ledger).
pub(crate) const BUYER: &str = "buyer";
/// The neutral custodian a listing rests with between the list and the settle.
const CUSTODY: &str = "market-custodian";

/// One good's paintable state, snapshotted out of the shared world for a render.
struct Painted {
    name: String,
    rarity: String,
    price: usize,
    listed: bool,
    sold: bool,
    lineage: usize,
}

/// **A live trade session over the real trade substrate.** A handle on the world holding the one
/// ledger (the seller's + buyer's notes), the seller label, the coin the buyer last spent (for a
/// genuine double-spend refusal probe), and the committed-turn count. The goods on offer are a live
/// read of the seller's shelf — in a shared world, that includes whatever they just forged.
pub struct TradeSession {
    world: SharedWorld,
    seller: String,
    /// A coin the buyer has already spent — a re-pay with it is a genuine executor refusal.
    last_spent_coin: Option<AssetId>,
    turns: usize,
}

impl TradeSession {
    /// The registry indices of the seller's goods, in shelf order.
    fn shelf(&self) -> Vec<usize> {
        self.world.read().shelf(&self.seller)
    }
    /// The number of goods on offer.
    pub fn goods_count(&self) -> usize {
        self.shelf().len()
    }
    /// Whether every good has sold (the market is exhausted).
    pub fn all_sold(&self) -> bool {
        let w = self.world.read();
        let shelf = w.shelf(&self.seller);
        !shelf.is_empty() && shelf.iter().all(|&i| w.items()[i].sold)
    }
    /// The number of goods currently listed (in custody, buyable).
    pub fn listed_count(&self) -> usize {
        let w = self.world.read();
        w.shelf(&self.seller)
            .into_iter()
            .filter(|&i| w.items()[i].listed && !w.items()[i].sold)
            .count()
    }
    /// The number of goods sold to the buyer.
    pub fn sold_count(&self) -> usize {
        let w = self.world.read();
        w.shelf(&self.seller)
            .into_iter()
            .filter(|&i| w.items()[i].sold)
            .count()
    }
    /// The buyer's unspent trade-coin balance.
    pub fn coin_balance(&self) -> usize {
        self.world.read().coins().len()
    }
    /// The number of real committed transfer turns so far.
    pub fn turns(&self) -> usize {
        self.turns
    }
    /// **The real asset ids on offer**, in render order — the same note-cells the inventory surface
    /// lists and the forge minted.
    pub fn asset_ids(&self) -> Vec<AssetId> {
        let w = self.world.read();
        w.shelf(&self.seller)
            .into_iter()
            .map(|i| w.items()[i].asset)
            .collect()
    }
    /// This surface's index for `asset` (its position on the shelf), if the seller offers it.
    pub fn index_of(&self, asset: AssetId) -> Option<usize> {
        self.asset_ids().iter().position(|a| *a == asset)
    }
    /// The current holder label of good `idx` off the real substrate (`seller`/custody/`buyer`).
    pub fn holder_of(&self, idx: usize) -> Option<String> {
        let asset = *self.asset_ids().get(idx)?;
        self.world.write().holder_label(asset)
    }
    /// The world this stall stands on (the handle a sibling surface shares).
    pub fn world(&self) -> &SharedWorld {
        &self.world
    }

    /// The registry index of shelf position `idx`.
    fn reg(&self, idx: usize) -> Option<usize> {
        self.shelf().get(idx).copied()
    }
}

/// **The trade offering** — a factory over the trade substrate. [`new`](Self::new) deploys a
/// private world per session (a seller stocked with canned goods + a buyer stocked with coins);
/// [`in_world`](Self::in_world) opens the stall onto a [`SharedWorld`] the craft + inventory
/// surfaces also stand on.
pub struct TradeOffering {
    world: Option<SharedWorld>,
}

impl TradeOffering {
    /// A SILOED trade offering — each [`open`](Offering::open) stands up its own world with the
    /// canned stock. Nothing here reaches another surface.
    pub fn new() -> Self {
        TradeOffering { world: None }
    }

    /// **A stall onto a SHARED world** — it offers the world's canonical player's shelf off the ONE
    /// ledger, so a note [`crate::CraftOffering::in_world`] forged is listable and sellable here as
    /// the EXACT crafted note-cell (its forge lineage continuing across the sale, not restarting).
    pub fn in_world(world: SharedWorld) -> Self {
        TradeOffering { world: Some(world) }
    }

    fn do_list(&self, s: &mut TradeSession, idx: usize) -> Outcome {
        let Some(reg) = s.reg(idx) else {
            return Outcome::Refused(format!("no good #{idx} on offer"));
        };
        let (asset, name, listed, sold) = {
            let w = s.world.read();
            let r = &w.items()[reg];
            (r.asset, r.name.clone(), r.listed, r.sold)
        };
        if sold {
            return Outcome::Refused(format!("`{name}` has already sold"));
        }
        if listed {
            return Outcome::Refused(format!("`{name}` is already listed"));
        }
        // The listing IS a real owner-signed transfer of the owned note into neutral custody — a
        // non-owner (or a list of a note the player gifted away) is a real executor refusal.
        let seller = s.seller.clone();
        let moved = s.world.write().assets().transfer(asset, &seller, CUSTODY);
        match moved {
            Ok(tr) => {
                s.world.write().item_mut(reg).expect("checked").listed = true;
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
        let Some(reg) = s.reg(idx) else {
            return Outcome::Refused(format!("no good #{idx} on offer"));
        };
        let (asset, name, price, listed, sold) = {
            let w = s.world.read();
            let r = &w.items()[reg];
            (r.asset, r.name.clone(), r.price, r.listed, r.sold)
        };
        if sold {
            return Outcome::Refused(format!("`{name}` has already sold"));
        }
        if !listed {
            return Outcome::Refused(format!("`{name}` is not listed — the seller must list it"));
        }

        // THE PAYMENT LEG. The buyer crosses `price` trade-coins to the seller. If the buyer is
        // paid out, we drive a GENUINE executor refusal by attempting to re-pay with an
        // already-spent coin (a real double-spend the substrate rejects), so the "cannot pay"
        // refusal is non-vacuous — and the good stays safe in custody (no half-open trade).
        let seller = s.seller.clone();
        if s.coin_balance() < price {
            if let Some(spent) = s.last_spent_coin {
                let err = s
                    .world
                    .write()
                    .assets()
                    .transfer(spent, BUYER, &seller)
                    .expect_err(
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
            let coin = s
                .world
                .write()
                .pop_coin()
                .expect("checked coin_balance() >= price above");
            let paid = s.world.write().assets().transfer(coin, BUYER, &seller);
            if let Err(e) = paid {
                // Payment refused mid-way — nothing crosses onward (the good is untouched).
                return Outcome::Refused(format!("payment for `{name}` refused: {e}"));
            }
            s.last_spent_coin = Some(coin);
            s.turns += 1;
        }

        // THE GOOD LEG. The good crosses custody → buyer (a real owner-signed transfer). In a
        // shared world this is the crafted note's OWN cell continuing its lineage to a new owner.
        let crossed = s.world.write().assets().transfer(asset, CUSTODY, BUYER);
        match crossed {
            Ok(tr) => {
                s.world.write().item_mut(reg).expect("checked").sold = true;
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
        let Some(reg) = s.reg(idx) else {
            return Outcome::Refused(format!("no good #{idx} on offer"));
        };
        let (asset, name, listed, sold) = {
            let w = s.world.read();
            let r = &w.items()[reg];
            (r.asset, r.name.clone(), r.listed, r.sold)
        };
        if sold {
            return Outcome::Refused(format!("`{name}` has already sold"));
        }
        if !listed {
            return Outcome::Refused(format!("`{name}` is not listed"));
        }
        let seller = s.seller.clone();
        let moved = s.world.write().assets().transfer(asset, CUSTODY, &seller);
        match moved {
            Ok(tr) => {
                s.world.write().item_mut(reg).expect("checked").listed = false;
                s.turns += 1;
                Outcome::Landed {
                    receipt: tr.spend,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("cancelling `{name}` refused: {e}")),
        }
    }

    /// Snapshot the seller's shelf for a render / an action pass (ONE short borrow).
    fn paint(&self, s: &TradeSession) -> Vec<Painted> {
        let mut w = s.world.write();
        let shelf = w.shelf(&s.seller);
        let base: Vec<(String, String, usize, bool, bool, AssetId)> = shelf
            .into_iter()
            .map(|i| {
                let r = &w.items()[i];
                (
                    r.name.clone(),
                    r.rarity.clone(),
                    r.price,
                    r.listed,
                    r.sold,
                    r.asset,
                )
            })
            .collect();
        base.into_iter()
            .map(|(name, rarity, price, listed, sold, asset)| {
                let lineage = w.assets().lineage_len(asset);
                Painted {
                    name,
                    rarity,
                    price,
                    listed,
                    sold,
                    lineage,
                }
            })
            .collect()
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
        // SHARED: adopt the world (already stocked — and its shelf grows as the player forges).
        // SILOED: stand up a private world with the canned stock + the buyer's purse, exactly as
        // this surface always did.
        let world = match &self.world {
            Some(w) => w.clone(),
            None => {
                let w = SharedWorld::new(SELLER);
                w.seed_trade_stock(BUYER);
                w
            }
        };
        Ok(TradeSession {
            seller: world.player(),
            world,
            last_spent_coin: None,
            turns: 0,
        })
    }

    fn actions(&self, s: &TradeSession) -> Vec<Action> {
        let painted = self.paint(s);
        // A good the player still holds is listable; one they gifted away is not (the executor
        // would refuse it anyway — the affordance just tells the truth up front).
        let held: Vec<bool> = (0..painted.len())
            .map(|i| s.holder_of(i).as_deref() == Some(s.seller.as_str()))
            .collect();
        let coins = s.coin_balance();
        let mut out = Vec::new();
        for (i, g) in painted.iter().enumerate() {
            if g.sold {
                continue;
            }
            if !g.listed {
                out.push(Action::new(
                    format!("List {} ({}★ · {}◈)", g.name, g.rarity, g.price),
                    TURN_LIST,
                    i as i64,
                    held[i],
                ));
            } else {
                out.push(Action::new(
                    format!("Buy {} ({}◈)", g.name, g.price),
                    TURN_BUY,
                    i as i64,
                    coins >= g.price,
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
    /// what this stall did with it — sold → the buyer, listed → custody. An un-listed good must
    /// simply NOT be in custody: in a shared world the player may have gifted it from the inventory
    /// surface, and this stall reports only the notes it actually took (it holds nothing it did not
    /// list).
    fn verify(&self, s: &TradeSession) -> VerifyReport {
        let ids = s.asset_ids();
        let painted = self.paint(s);
        for (i, g) in painted.iter().enumerate() {
            let report = s.world.read().forge().asset_provenance(ids[i]);
            if !report.verified {
                return VerifyReport::broken(
                    s.turns,
                    format!("`{}` provenance broke: {:?}", g.name, report.reasons),
                );
            }
            let holder = s.world.write().holder_label(ids[i]);
            if g.sold {
                if holder.as_deref() != Some(BUYER) {
                    return VerifyReport::broken(
                        s.turns,
                        format!(
                            "`{}` sold but is held by {holder:?}, expected `{BUYER}`",
                            g.name
                        ),
                    );
                }
            } else if g.listed {
                if holder.as_deref() != Some(CUSTODY) {
                    return VerifyReport::broken(
                        s.turns,
                        format!(
                            "`{}` listed but is held by {holder:?}, expected `{CUSTODY}`",
                            g.name
                        ),
                    );
                }
            } else if holder.as_deref() == Some(CUSTODY) {
                return VerifyReport::broken(
                    s.turns,
                    format!(
                        "`{}` is in custody but this stall lists nothing of the sort",
                        g.name
                    ),
                );
            }
        }
        VerifyReport::ok(s.turns)
    }

    fn render(&self, s: &TradeSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();
        let painted = self.paint(s);

        // The stall summary.
        children.push(section(
            "Stall",
            "muted",
            vec![text(format!(
                "goods {} · listed {} · sold {} · buyer purse {}◈",
                painted.len(),
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
        for g in &painted {
            let (status, tag) = if g.sold {
                ("sold", "good")
            } else if g.listed {
                ("listed", "accent")
            } else {
                ("in stock", "muted")
            };
            rows.push(row(vec![
                text(&g.name),
                pill(&g.rarity, "warn"),
                text(format!("{}◈", g.price)),
                pill(status, tag),
                text(format!("v{}", g.lineage)),
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
