//! # `InventoryOffering` — a **read-surface** over [`dreggnet_asset`] owned notes.
//!
//! A player's owned assets (gear / companions / cards / trophies) rendered as a `Table`:
//! name / rarity / kind / provenance / owner. The name/rarity/kind are the *content layer* (what
//! the item IS); the **provenance** (the content-addressed lineage length + its re-verification)
//! and the **owner** are read off the REAL substrate — a rare drop's rarity is a checkable hash
//! chain ([`AssetWorld::verify_provenance`]), not a database row.
//!
//! Read-mostly: `advance` is a read-only refusal (an inventory is a view, not a mover — trading is
//! [`crate::trade::TradeOffering`]); the payload is `render`.

use dreggnet_asset::{AssetId, AssetWorld};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::{pill, row, section, short_hex, text};
use deos_view::ViewNode;

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

    /// A read-surface exposes no moves.
    fn actions(&self, _s: &InventorySession) -> Vec<Action> {
        Vec::new()
    }

    /// Read-only: an inventory is a view, not a mover (trade the item via `TradeOffering`).
    fn advance(&self, _s: &mut InventorySession, _input: Action, _actor: DreggIdentity) -> Outcome {
        Outcome::Refused(
            "the inventory is a read-only surface — trade an item via the market".into(),
        )
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
            vec![text(format!("{} · {} note(s) owned", s.owner, s.len()))],
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
                text("Owner"),
            ])];
            for (asset, spec) in &s.items {
                let report = s.world.verify_provenance(*asset);
                let prov = if report.verified {
                    format!("v{} ✓", report.length)
                } else {
                    format!("v{} ✗", report.length)
                };
                let owner = s
                    .world
                    .current_owner(*asset)
                    .map(|pk| short_hex(&pk))
                    .unwrap_or_else(|| "—".into());
                rows.push(row(vec![
                    text(&spec.name),
                    pill(&spec.rarity, "warn"),
                    pill(&spec.kind, "accent"),
                    pill(prov, if report.verified { "good" } else { "bad" }),
                    text(owner),
                ]));
            }
            children.push(section("Items", "accent", vec![ViewNode::Table(rows)]));
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
