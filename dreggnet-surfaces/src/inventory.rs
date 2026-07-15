//! # `InventoryOffering` — an owned-notes surface over [`dreggnet_asset`].
//!
//! A player's owned assets (gear / companions / cards / trophies) rendered as a `Table`:
//! name / rarity / kind / provenance / holder. The name/rarity/kind are the *content layer* (what
//! the item IS); the **provenance** (the content-addressed lineage length + its re-verification)
//! and the **holder** are read off the REAL substrate — a rare drop's rarity is a checkable hash
//! chain ([`AssetWorld::verify_provenance`]), not a database row.
//!
//! ## One interactive move: **gift**
//!
//! The substrate exposes an owner-signed [`AssetWorld::transfer`] (the same teeth the market's
//! atomic swap rides). So this surface is *lightly playable*: a player may **gift** an owned note to
//! a friend — a real committed transfer turn that carries a genuine [`TurnReceipt`]. It is a
//! *personal* hand-off (no price, no custody), distinct from the priced market cross that
//! [`crate::trade::TradeOffering`] settles. The teeth are non-vacuous: once a note is gifted the
//! player no longer holds its tail, so a **re-gift is a real executor refusal** (the
//! signature-vs-owner gate), and the gifted note's holder column flips to the friend on the real
//! substrate. `advance` for any other verb is a read-only refusal; the render is the payload.
//!
//! ## Where the items come from
//!
//! [`InventoryOffering::in_world`] opens onto a [`SharedWorld`] — the ONE ledger [`crate::craft`]
//! forges into and [`crate::trade`] sells across. The item list is then a LIVE read of that world's
//! registry, not a snapshot minted at `open`: forge a Greatblade on the craft surface and the very
//! next render of this surface lists it, because it is the same note on the same ledger. Every
//! column that matters (holder, provenance, lineage) was always a substrate read — the share is
//! what finally makes those reads reach the crafted note. [`InventoryOffering::demo`] /
//! [`InventoryOffering::new`] keep the old siloed shape (a private world per session).

use dreggnet_asset::{AssetId, ProvenanceReport};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::world::SharedWorld;
use crate::{pill, row, section, short_hex, text};
use deos_view::ViewNode;

/// The affordance verb a player fires to gift an owned note to a friend (`arg` = the item index).
pub const TURN_GIFT: &str = "gift";

/// The recipient label a gift crosses to (a friend's sovereign holder in the same [`AssetWorld`]).
const FRIEND: &str = "a friend";

/// **One inventory item spec** — the display metadata (name / rarity / kind) plus the mint seed the
/// owned note is content-addressed by. `open` mints a real [`dreggnet_asset`] note per spec, owned
/// by the player; the substrate then carries the provenance the surface reads back.
#[derive(Clone, Debug)]
pub struct InventoryItem {
    /// The item's display name (`"Ember Cloak"`).
    pub name: String,
    /// The rarity tier (`"legendary"` / `"rare"` / …) — a display badge.
    pub rarity: String,
    /// The kind (`"gear"` / `"companion"` / `"card"` / `"trophy"`).
    pub kind: String,
    /// The mint seed the owned note is content-addressed by (stable per item).
    pub mint_seed: String,
}

impl InventoryItem {
    /// A convenience constructor.
    pub fn new(
        name: impl Into<String>,
        rarity: impl Into<String>,
        kind: impl Into<String>,
        mint_seed: impl Into<String>,
    ) -> Self {
        InventoryItem {
            name: name.into(),
            rarity: rarity.into(),
            kind: kind.into(),
            mint_seed: mint_seed.into(),
        }
    }
}

/// The DEMO item specs — a spread of gear / companion / card / trophy notes across rarities. Shared
/// with [`crate::world::SharedWorld::demo`] so the stocked shared world seeds the same five notes
/// [`InventoryOffering::demo`] does.
pub(crate) fn demo_items() -> Vec<InventoryItem> {
    vec![
        InventoryItem::new("Ember Cloak", "legendary", "gear", "ember-cloak"),
        InventoryItem::new("Frost Charm", "rare", "gear", "frost-charm"),
        InventoryItem::new("Grimalkin", "epic", "companion", "grimalkin"),
        InventoryItem::new("Ace of Vaults", "rare", "card", "ace-of-vaults"),
        InventoryItem::new("Deepdelver's Sigil", "legendary", "trophy", "deepdelver"),
    ]
}

/// **A live inventory session** — a handle on the world holding the owner's notes, plus the owner
/// label. The item list is a LIVE read of the world's registry (shelf order), so a note another
/// surface put on this player's shelf shows up on the next render.
pub struct InventorySession {
    world: SharedWorld,
    owner: String,
}

impl InventorySession {
    /// The registry indices of the owner's items, in shelf order (a fresh craft lands at the END,
    /// so the indices a player is already looking at never renumber).
    fn shelf(&self) -> Vec<usize> {
        self.world.read().shelf(&self.owner)
    }
    /// How many notes the player owns.
    pub fn len(&self) -> usize {
        self.shelf().len()
    }
    /// Whether the inventory is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// The owner label.
    pub fn owner(&self) -> &str {
        &self.owner
    }
    /// **The real asset ids on the player's shelf**, in render order. The object-identity handle: a
    /// crafted note's id appears here because it is the SAME note-cell on the SAME ledger the forge
    /// minted it into — not a look-alike this surface re-derived.
    pub fn asset_ids(&self) -> Vec<AssetId> {
        let w = self.world.read();
        w.shelf(&self.owner)
            .into_iter()
            .filter_map(|i| w.items().get(i).map(|r| r.asset))
            .collect()
    }
    /// This surface's index for `asset` (its position on the shelf), if the player owns it.
    pub fn index_of(&self, asset: AssetId) -> Option<usize> {
        self.asset_ids().iter().position(|a| *a == asset)
    }
    /// The display name of item `idx`.
    pub fn name_of(&self, idx: usize) -> Option<String> {
        let w = self.world.read();
        let reg = *w.shelf(&self.owner).get(idx)?;
        w.items().get(reg).map(|r| r.name.clone())
    }
    /// The current holder LABEL of item `idx` off the real substrate (the owner, `a friend` after a
    /// gift, the custodian/buyer after a market cross). `None` if the index is out of range.
    pub fn holder_of(&self, idx: usize) -> Option<String> {
        let asset = *self.asset_ids().get(idx)?;
        self.world.write().holder_label(asset)
    }
    /// **Re-verify item `idx`'s provenance** off the shared ledger — the content-addressed lineage
    /// the crafted note carries FORWARD from its forge mint (this surface reads the craft's own
    /// chain, because it is one ledger).
    pub fn provenance_of(&self, idx: usize) -> Option<ProvenanceReport> {
        let asset = *self.asset_ids().get(idx)?;
        Some(self.world.read().forge().asset_provenance(asset))
    }
    /// Whether item `idx` is still held by the owner (i.e. giftable — not already gifted or sold).
    pub fn owns(&self, idx: usize) -> bool {
        self.holder_of(idx).as_deref() == Some(self.owner.as_str())
    }
    /// How many owned notes the player still holds.
    pub fn held_count(&self) -> usize {
        (0..self.len()).filter(|i| self.owns(*i)).count()
    }
    /// The world this inventory stands on (the handle a sibling surface shares).
    pub fn world(&self) -> &SharedWorld {
        &self.world
    }
}

/// **The inventory offering** — a factory over a player's owned notes. [`demo`](Self::demo) /
/// [`new`](Self::new) / [`with_items`](Self::with_items) stand up a private world per session;
/// [`in_world`](Self::in_world) reads a [`SharedWorld`] the craft + market surfaces also stand on.
pub struct InventoryOffering {
    owner: String,
    items: Vec<InventoryItem>,
    world: Option<SharedWorld>,
}

impl InventoryOffering {
    /// An EMPTY inventory for `owner` (the empty-state surface).
    pub fn new(owner: impl Into<String>) -> Self {
        InventoryOffering {
            owner: owner.into(),
            items: Vec::new(),
            world: None,
        }
    }

    /// An inventory for `owner` stocked with `items`.
    pub fn with_items(owner: impl Into<String>, items: Vec<InventoryItem>) -> Self {
        InventoryOffering {
            owner: owner.into(),
            items,
            world: None,
        }
    }

    /// A populated DEMO inventory — a spread of gear / companion / card / trophy notes across
    /// rarities (the standalone register state).
    pub fn demo(owner: impl Into<String>) -> Self {
        Self::with_items(owner, demo_items())
    }

    /// **An inventory onto a SHARED world** — it lists the world's canonical player's shelf off the
    /// ONE ledger, so anything [`crate::CraftOffering::in_world`] forges for that player appears
    /// here as the same note-cell, and a gift fired here is a move the craft + market surfaces see.
    pub fn in_world(world: SharedWorld) -> Self {
        InventoryOffering {
            owner: world.player(),
            items: Vec::new(),
            world: Some(world),
        }
    }
}

impl Offering for InventoryOffering {
    type Session = InventorySession;

    fn open(&self, _cfg: SessionConfig) -> Result<InventorySession, OfferingError> {
        // SHARED: adopt the world (its registry already holds this player's shelf, and will hold
        // whatever they forge next). SILOED: stand up a private world and mint this offering's
        // specs into it, exactly as this surface always did.
        let world = match &self.world {
            Some(w) => w.clone(),
            None => {
                let w = SharedWorld::new(self.owner.clone());
                w.seed_items(&self.items);
                w
            }
        };
        Ok(InventorySession {
            owner: world.player(),
            world,
        })
    }

    /// One move per still-held note: **gift** it to a friend (a real owner-signed transfer turn).
    fn actions(&self, s: &InventorySession) -> Vec<Action> {
        (0..s.len())
            .filter(|i| s.owns(*i))
            .filter_map(|i| {
                let name = s.name_of(i)?;
                Some(Action::new(
                    format!("Gift {name} to {FRIEND}"),
                    TURN_GIFT,
                    i as i64,
                    true,
                ))
            })
            .collect()
    }

    /// **Gift** an owned note to a friend — a real owner-signed [`AssetWorld::transfer`] turn. A gift
    /// of a note the player no longer holds (already gifted away) is a genuine executor refusal (the
    /// signature-vs-owner gate), never a silent apply. Any other verb is a read-only refusal (buy /
    /// sell for a price is the market, [`crate::trade::TradeOffering`]).
    fn advance(&self, s: &mut InventorySession, input: Action, _actor: DreggIdentity) -> Outcome {
        if input.turn != TURN_GIFT {
            return Outcome::Refused(format!(
                "the inventory surface only gifts (verb `{TURN_GIFT}`) — trade for a price via the market"
            ));
        }
        let idx = input.arg.max(0) as usize;
        let Some(asset) = s.asset_ids().get(idx).copied() else {
            return Outcome::Refused(format!("no owned item #{idx}"));
        };
        let name = s.name_of(idx).unwrap_or_else(|| "item".into());
        let owner = s.owner.clone();
        // The SAME owner-signed transfer, on the SAME ledger the note was minted or forged into —
        // sharing the world widened what this surface can SEE, never what it may move.
        let moved = s.world.write().assets().transfer(asset, &owner, FRIEND);
        match moved {
            Ok(tr) => Outcome::Landed {
                receipt: tr.spend,
                ended: false,
            },
            Err(e) => Outcome::Refused(format!("gifting `{name}` refused: {e}")),
        }
    }

    /// Re-verify every owned note's provenance (the content-addressed lineage + on-chain re-reads).
    /// In a shared world this re-verifies the CRAFTED notes too, along their real forge lineage.
    fn verify(&self, s: &InventorySession) -> VerifyReport {
        let n = s.len();
        for i in 0..n {
            let Some(report) = s.provenance_of(i) else {
                continue;
            };
            if !report.verified {
                let name = s.name_of(i).unwrap_or_else(|| format!("item #{i}"));
                return VerifyReport::broken(
                    n,
                    format!("`{name}` provenance broke: {:?}", report.reasons),
                );
            }
        }
        VerifyReport::ok(n)
    }

    fn render(&self, s: &InventorySession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(section(
            "Owner",
            "muted",
            vec![text(format!(
                "{} · {} note(s) · {} held · {} gifted",
                s.owner,
                s.len(),
                s.held_count(),
                s.len() - s.held_count(),
            ))],
        ));

        if s.is_empty() {
            children.push(section(
                "Items",
                "muted",
                vec![text(
                    "No items owned yet — clear a run or trade for a drop.",
                )],
            ));
        } else {
            // Snapshot the shelf out from under ONE short borrow, then build the tree.
            struct Painted {
                name: String,
                rarity: String,
                kind: String,
                verified: bool,
                length: usize,
                holder_label: Option<String>,
                holder_key: String,
            }
            let painted: Vec<Painted> = {
                let mut w = s.world.write();
                let shelf = w.shelf(&s.owner);
                let base: Vec<(String, String, String, AssetId)> = shelf
                    .into_iter()
                    .filter_map(|reg| {
                        w.items()
                            .get(reg)
                            .map(|r| (r.name.clone(), r.rarity.clone(), r.kind.clone(), r.asset))
                    })
                    .collect();
                base.into_iter()
                    .map(|(name, rarity, kind, asset)| {
                        let report = w.forge().asset_provenance(asset);
                        let holder_key = w
                            .assets()
                            .current_owner(asset)
                            .map(|pk| short_hex(&pk))
                            .unwrap_or_else(|| "—".into());
                        let holder_label = w.holder_label(asset);
                        Painted {
                            name,
                            rarity,
                            kind,
                            verified: report.verified,
                            length: report.length,
                            holder_label,
                            holder_key,
                        }
                    })
                    .collect()
            };

            let mut rows: Vec<ViewNode> = vec![row(vec![
                text("Item"),
                text("Rarity"),
                text("Kind"),
                text("Provenance"),
                text("Holder"),
            ])];
            for p in &painted {
                let prov = if p.verified {
                    format!("v{} ✓", p.length)
                } else {
                    format!("v{} ✗", p.length)
                };
                // The holder is whatever the LEDGER says — the owner, the friend a gift crossed it
                // to, or (in a shared world) the custodian/buyer a market cross moved it to. This
                // surface reports the move it did not make rather than guessing.
                let holder = match p.holder_label.as_deref() {
                    Some(h) if h == s.owner => pill(format!("owned · {}", p.holder_key), "good"),
                    Some(h) if h == FRIEND => pill(format!("gifted → {FRIEND}"), "muted"),
                    Some(h) => pill(format!("held by {h}"), "muted"),
                    None => pill("no live holder", "muted"),
                };
                rows.push(row(vec![
                    text(&p.name),
                    pill(&p.rarity, "warn"),
                    pill(&p.kind, "accent"),
                    pill(prov, if p.verified { "good" } else { "bad" }),
                    holder,
                ]));
            }
            children.push(section("Items", "accent", vec![ViewNode::Table(rows)]));

            // The one interactive move: gift a still-owned note (a real owner-signed transfer turn).
            let gifts = crate::action_menu(self.actions(s));
            if !gifts.is_empty() {
                children.push(section("Gift", "accent", vec![crate::menu(gifts)]));
            }
        }

        Surface(section(
            format!("Inventory — {}", s.owner),
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
