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

use dreggnet_asset::{AssetId, AssetWorld};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

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

/// **A live inventory session** — the owner's sovereign [`AssetWorld`] with the minted notes, plus
/// the display metadata paired to each note's real [`AssetId`].
pub struct InventorySession {
    world: AssetWorld,
    owner: String,
    items: Vec<(AssetId, InventoryItem)>,
}

impl InventorySession {
    /// How many notes the player owns.
    pub fn len(&self) -> usize {
        self.items.len()
    }
    /// Whether the inventory is empty.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    /// The owner label.
    pub fn owner(&self) -> &str {
        &self.owner
    }
    /// The current holder LABEL of item `idx` off the real substrate (the owner, or `a friend`
    /// after a gift). `None` if the index is out of range.
    pub fn holder_of(&self, idx: usize) -> Option<String> {
        let (asset, _) = self.items.get(idx)?;
        self.world.current_holder_label(*asset).map(str::to_string)
    }
    /// Whether item `idx` is still held by the owner (i.e. giftable — not already gifted away).
    pub fn owns(&self, idx: usize) -> bool {
        self.holder_of(idx).as_deref() == Some(self.owner.as_str())
    }
    /// How many owned notes the player still holds (have not been gifted away).
    pub fn held_count(&self) -> usize {
        (0..self.items.len()).filter(|i| self.owns(*i)).count()
    }
}

/// **The inventory offering** — a read-surface factory over a player's owned notes. Construct it
/// with the items to seed ([`demo`](Self::demo) for a stocked player, [`new`](Self::new) empty).
pub struct InventoryOffering {
    owner: String,
    items: Vec<InventoryItem>,
}

impl InventoryOffering {
    /// An EMPTY inventory for `owner` (the empty-state surface).
    pub fn new(owner: impl Into<String>) -> Self {
        InventoryOffering {
            owner: owner.into(),
            items: Vec::new(),
        }
    }

    /// An inventory for `owner` stocked with `items`.
    pub fn with_items(owner: impl Into<String>, items: Vec<InventoryItem>) -> Self {
        InventoryOffering {
            owner: owner.into(),
            items,
        }
    }

    /// A populated DEMO inventory — a spread of gear / companion / card / trophy notes across
    /// rarities (the web/discord register state).
    pub fn demo(owner: impl Into<String>) -> Self {
        Self::with_items(
            owner,
            vec![
                InventoryItem::new("Ember Cloak", "legendary", "gear", "ember-cloak"),
                InventoryItem::new("Frost Charm", "rare", "gear", "frost-charm"),
                InventoryItem::new("Grimalkin", "epic", "companion", "grimalkin"),
                InventoryItem::new("Ace of Vaults", "rare", "card", "ace-of-vaults"),
                InventoryItem::new("Deepdelver's Sigil", "legendary", "trophy", "deepdelver"),
            ],
        )
    }
}

impl Offering for InventoryOffering {
    type Session = InventorySession;

    fn open(&self, _cfg: SessionConfig) -> Result<InventorySession, OfferingError> {
        let mut world = AssetWorld::new();
        let items = self
            .items
            .iter()
            .map(|spec| {
                let asset = world.mint(&self.owner, spec.mint_seed.as_bytes());
                (asset, spec.clone())
            })
            .collect();
        Ok(InventorySession {
            world,
            owner: self.owner.clone(),
            items,
        })
    }

    /// One move per still-owned note: **gift** it to a friend (a real owner-signed transfer turn).
    fn actions(&self, s: &InventorySession) -> Vec<Action> {
        s.items
            .iter()
            .enumerate()
            .filter(|(i, _)| s.owns(*i))
            .map(|(i, (_, spec))| {
                Action::new(
                    format!("Gift {} to {FRIEND}", spec.name),
                    TURN_GIFT,
                    i as i64,
                    true,
                )
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
        let Some((asset, spec)) = s.items.get(idx) else {
            return Outcome::Refused(format!("no owned item #{idx}"));
        };
        let (asset, name) = (*asset, spec.name.clone());
        let owner = s.owner.clone();
        match s.world.transfer(asset, &owner, FRIEND) {
            Ok(tr) => Outcome::Landed {
                receipt: tr.spend,
                ended: false,
            },
            Err(e) => Outcome::Refused(format!("gifting `{name}` refused: {e}")),
        }
    }

    /// Re-verify every owned note's provenance (the content-addressed lineage + on-chain re-reads).
    fn verify(&self, s: &InventorySession) -> VerifyReport {
        for (asset, spec) in &s.items {
            let report = s.world.verify_provenance(*asset);
            if !report.verified {
                return VerifyReport::broken(
                    s.items.len(),
                    format!("`{}` provenance broke: {:?}", spec.name, report.reasons),
                );
            }
        }
        VerifyReport::ok(s.items.len())
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
            let mut rows: Vec<ViewNode> = vec![row(vec![
                text("Item"),
                text("Rarity"),
                text("Kind"),
                text("Provenance"),
                text("Holder"),
            ])];
            for (i, (asset, spec)) in s.items.iter().enumerate() {
                let report = s.world.verify_provenance(*asset);
                let prov = if report.verified {
                    format!("v{} ✓", report.length)
                } else {
                    format!("v{} ✗", report.length)
                };
                let owned = s.owns(i);
                let holder_key = s
                    .world
                    .current_owner(*asset)
                    .map(|pk| short_hex(&pk))
                    .unwrap_or_else(|| "—".into());
                let holder = if owned {
                    pill(format!("owned · {holder_key}"), "good")
                } else {
                    pill(format!("gifted → {FRIEND}"), "muted")
                };
                rows.push(row(vec![
                    text(&spec.name),
                    pill(&spec.rarity, "warn"),
                    pill(&spec.kind, "accent"),
                    pill(prov, if report.verified { "good" } else { "bad" }),
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
