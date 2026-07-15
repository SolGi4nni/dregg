//! # `SharedWorld` — the ONE asset ledger the live feature surfaces stand on.
//!
//! Before this module every surface stood up its own universe: [`crate::craft`] opened a fresh
//! [`CraftForge`], [`crate::inventory`] a fresh [`AssetWorld`], [`crate::trade`] a fresh
//! `TradeWorld` with canned stock. So a player could forge a Greatblade on the craft surface and it
//! would **not be in their inventory** — the surfaces agreed by *convention* (matching names in
//! three ledgers), never by *object identity*. [`dreggnet_saga`] already proved the real seam
//! ([`CraftForge::into_assets`] → `TradeWorld::with_assets`: the ledger is MOVED, the crafted note
//! is never re-minted), but the live surfaces did not use it.
//!
//! This is that seam, in the shape live surfaces need.
//!
//! ## Why `assets_mut`, not `into_assets`
//!
//! The saga is SEQUENTIAL: it crafts, then hands the ledger away once
//! ([`CraftForge::into_assets`] consumes the forge). Live surfaces COEXIST — a player keeps the
//! forge open while the inventory renders and the market sells — so a one-shot move would kill the
//! forge. The live shape shares the forge itself behind an `Rc<RefCell<_>>` and reaches the one
//! ledger through [`CraftForge::assets_mut`] (`dreggnet-craft/src/forge.rs:215`), the sibling
//! accessor of `into_assets` and the same `&mut AssetWorld` a `TradeWorld::assets()` hands out.
//! The forge is the ledger's home because it is the only party that can MINT into it and craft
//! against it: `CraftForge` has no `with_assets` constructor, so an `AssetWorld` can flow OUT of a
//! forge but never back in. Every surface therefore borrows the forge's world; nobody re-mints.
//!
//! (`Rc`/`RefCell`, not `Arc`/`Mutex`: an [`OfferingHost`](dreggnet_offerings::OfferingHost) is
//! explicitly not `Send`/`Sync` — it already hosts `!Send` `Rc`-backed sessions — so a frontend
//! confines it to one thread and the cheaper handle is the honest one.)
//!
//! ## What is shared
//!
//! * **The ledger** — one [`AssetWorld`], inside one [`CraftForge`]. Every note (materials, demo
//!   items, market stock, trade-coins, crafted outputs) is minted here and lives here.
//! * **The item registry** — [`ItemRecord`]s pairing a real [`AssetId`] with the display layer
//!   (name / rarity / kind) and the market layer (ask / listed / sold). This is how a surface
//!   *discovers* a note it did not mint: the forge appends the crafted output to the registry and
//!   the inventory's next render finds it. The registry is metadata ONLY — every holder, lineage,
//!   and provenance column each surface renders is read live off the ledger, so the registry can
//!   never conjure an item into existence, only name one that the ledger already carries.
//! * **The bench** — the craft materials + the recipes drawn from the forge's COMMITTED catalog.
//!
//! ## What is NOT weakened
//!
//! Sharing a ledger changes *who can see* a note, never *who can move* it. Every move any surface
//! fires is still the same owner-signed [`AssetWorld::transfer`] the executor referees: a non-owner
//! listing, a re-gift of a note you no longer hold, a double-spent coin are real refusals, exactly
//! as [`dreggnet_asset`] enforces them. The share is a READ reaching further, not a gate relaxing.

use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use dreggnet_asset::{AssetId, AssetWorld};
use dreggnet_craft::{CraftForge, CraftOutcome, CraftQuality, Recipe};

use crate::inventory::InventoryItem;

/// How an [`ItemRecord`] entered the world — the honest distinction between an item the demo
/// STOCKED and one the player actually FORGED on the craft surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Origin {
    /// Minted by a seeding call ([`SharedWorld::seed_items`] / [`SharedWorld::seed_trade_stock`]).
    Seeded,
    /// **Forged on the craft surface** — a real [`CraftForge::craft`] output whose content address
    /// binds the recipe + the consumed inputs + the fair roll. `recipe` is the bench label and
    /// `outcome` the fair-draw band the forge resolved.
    Crafted {
        /// The bench label of the recipe that forged it (`"Greatblade"`).
        recipe: String,
        /// The fair-draw outcome band the forge resolved (a safe recipe always lands `success`).
        outcome: CraftOutcome,
    },
}

impl Origin {
    /// Whether this item was forged on the craft surface (not seeded).
    pub fn is_crafted(&self) -> bool {
        matches!(self, Origin::Crafted { .. })
    }
}

/// **One item in the shared world's registry** — a real [`AssetId`] on the shared ledger, plus the
/// display layer (name / rarity / kind) and the market layer (the ask, and whether it is listed or
/// sold). The record NAMES a note; it never owns it — holder and provenance are always read live
/// off the ledger.
#[derive(Clone, Debug)]
pub struct ItemRecord {
    /// The real note on the shared ledger.
    pub asset: AssetId,
    /// The item's display name (`"Ember Cloak"`, `"Greatblade"`).
    pub name: String,
    /// The rarity tier — for a crafted item this is its fair-draw quality label, not a database row.
    pub rarity: String,
    /// The kind (`"gear"` / `"companion"` / `"card"` / `"trophy"`).
    pub kind: String,
    /// The label this note was minted / forged FOR — the shelf it sits on (whose inventory lists it,
    /// whose market may offer it). The note's CURRENT holder is a ledger read, not this field.
    pub owner: String,
    /// The ask, in trade-coins, if the owner lists it on the market surface.
    pub price: usize,
    /// Whether the market surface currently holds it in neutral custody.
    pub listed: bool,
    /// Whether the market surface has settled it to a buyer.
    pub sold: bool,
    /// How it entered the world.
    pub origin: Origin,
}

/// A raw material on the bench — a real owned note the forge can consume as a craft input.
pub(crate) struct Material {
    pub(crate) asset: AssetId,
    pub(crate) name: String,
}

/// A recipe on the bench — the committed [`Recipe`] (cloned from the forge's catalog), a display
/// label, and the material indices it draws its inputs from.
pub(crate) struct Bench {
    pub(crate) recipe: Recipe,
    pub(crate) label: String,
    pub(crate) inputs: Vec<usize>,
}

/// The default ask for a seeded item of `rarity`, in trade-coins.
fn ask_for(rarity: &str) -> usize {
    match rarity {
        "legendary" => 3,
        "epic" | "rare" => 2,
        _ => 1,
    }
}

/// The ask a freshly-forged item carries, from its FAIR-DRAW quality (a legendary roll is genuinely
/// worth more — the price rides the committed draw, not a marketing tier).
pub(crate) fn ask_for_quality(q: CraftQuality) -> usize {
    match q {
        CraftQuality::Legendary => 3,
        CraftQuality::Rare => 2,
        _ => 1,
    }
}

/// **The one world the live surfaces share** — the forge (which owns THE [`AssetWorld`]), the item
/// registry, the craft bench, and the buyer's purse. Reached through [`SharedWorld`].
pub struct GameWorld {
    forge: CraftForge,
    player: String,
    items: Vec<ItemRecord>,
    materials: Vec<Material>,
    benches: Vec<Bench>,
    coins: Vec<AssetId>,
}

impl GameWorld {
    /// The canonical player label — the ONE identity the craft surface forges as, the inventory
    /// surface lists for, and the market surface sells as. (The composition's whole point: three
    /// surfaces keyed on one label over one ledger, not three look-alikes.)
    pub fn player(&self) -> &str {
        &self.player
    }

    /// The forge (immutable reads: `is_destroyed` / `owner_of` / `asset_provenance` / `quality_of`).
    pub fn forge(&self) -> &CraftForge {
        &self.forge
    }

    /// The forge, mutably — the party that crafts + mints.
    pub fn forge_mut(&mut self) -> &mut CraftForge {
        &mut self.forge
    }

    /// **THE SHARED LEDGER** — the one [`AssetWorld`] every surface's transfers ride
    /// ([`CraftForge::assets_mut`]). This is the seam: it is the same `&mut AssetWorld` the forge
    /// mints crafted outputs into, so a note the craft surface forges is *already* the note the
    /// inventory and market surfaces read. No re-mint, no second universe.
    pub fn assets(&mut self) -> &mut AssetWorld {
        self.forge.assets_mut()
    }

    /// The registry, in append order.
    pub fn items(&self) -> &[ItemRecord] {
        &self.items
    }

    /// The registry index of `asset`, if registered.
    pub fn index_of(&self, asset: AssetId) -> Option<usize> {
        self.items.iter().position(|r| r.asset == asset)
    }

    /// A registry record, mutably (the market flips `listed` / `sold` through this).
    pub fn item_mut(&mut self, idx: usize) -> Option<&mut ItemRecord> {
        self.items.get_mut(idx)
    }

    /// **`owner`'s shelf** — the registry indices of the items minted / forged for `owner`, in
    /// append order. A surface's own item indices are positions in this shelf, so a freshly-forged
    /// item lands at the END and never renumbers what the player was already looking at.
    pub fn shelf(&self, owner: &str) -> Vec<usize> {
        self.items
            .iter()
            .enumerate()
            .filter(|(_, r)| r.owner == owner)
            .map(|(i, _)| i)
            .collect()
    }

    /// Append a record to the registry (the note must already be minted on the ledger).
    pub fn register_item(&mut self, record: ItemRecord) {
        self.items.push(record);
    }

    /// The current holder LABEL of `asset` off the shared ledger (`None` if it has no live holder —
    /// a consumed craft input). The one read that makes the share observable: whatever surface
    /// moved the note, every other surface sees the move here.
    pub fn holder_label(&mut self, asset: AssetId) -> Option<String> {
        self.assets()
            .current_holder_label(asset)
            .map(str::to_string)
    }

    /// Whether material `idx` is still a live, unconsumed note (read off the forge's on-chain
    /// destroyed-set).
    pub(crate) fn material_live(&self, idx: usize) -> bool {
        self.materials
            .get(idx)
            .map(|m| !self.forge.is_destroyed(m.asset))
            .unwrap_or(false)
    }

    /// The bench's materials.
    pub(crate) fn materials(&self) -> &[Material] {
        &self.materials
    }

    /// The bench's recipes.
    pub(crate) fn benches(&self) -> &[Bench] {
        &self.benches
    }

    /// How many of bench `b`'s input materials are still live (the recipe is craftable iff this
    /// meets the recipe's input floor).
    pub(crate) fn live_inputs(&self, b: &Bench) -> usize {
        b.inputs.iter().filter(|&&i| self.material_live(i)).count()
    }

    /// The buyer's unspent trade-coin notes.
    pub(crate) fn coins(&self) -> &[AssetId] {
        &self.coins
    }

    /// Pop an unspent trade-coin from the buyer's purse.
    pub(crate) fn pop_coin(&mut self) -> Option<AssetId> {
        self.coins.pop()
    }
}

/// **A shared handle on one [`GameWorld`]** — cloned into each surface's session so craft,
/// inventory, and trade stand on ONE ledger and ONE registry.
///
/// Construct with [`SharedWorld::demo`] for the full stocked demo world (the state
/// [`crate::register_surfaces`] mounts), or [`SharedWorld::new`] + the `seed_*` calls to build one
/// piece at a time.
#[derive(Clone)]
pub struct SharedWorld(Rc<RefCell<GameWorld>>);

impl SharedWorld {
    /// An empty world for `player` — a fresh [`CraftForge`] over the COMMITTED starter catalog
    /// (so a craft can only ever present a recipe the catalog holds), no items, no bench, no coins.
    pub fn new(player: impl Into<String>) -> Self {
        SharedWorld(Rc::new(RefCell::new(GameWorld {
            forge: CraftForge::new(),
            player: player.into(),
            items: Vec::new(),
            materials: Vec::new(),
            benches: Vec::new(),
            coins: Vec::new(),
        })))
    }

    /// **The stocked demo world** — ONE ledger carrying `player`'s craft bench, `player`'s demo
    /// inventory notes, and `player`'s market stock (plus the buyer's purse). The canned trade
    /// stock is exactly that: an initial SEEDING of this world, not a separate universe — the goods
    /// are `player`'s own notes, listable beside anything `player` forges.
    pub fn demo(player: impl Into<String>) -> Self {
        let world = SharedWorld::new(player);
        world.seed_craft_bench();
        world.seed_items(&crate::inventory::demo_items());
        world.seed_trade_stock(crate::trade::BUYER);
        world
    }

    /// The world's canonical player label.
    pub fn player(&self) -> String {
        self.0.borrow().player.clone()
    }

    /// Borrow the world immutably. Keep the guard SHORT — a surface that holds it across a call
    /// back into itself would panic on the re-borrow.
    pub(crate) fn read(&self) -> Ref<'_, GameWorld> {
        self.0.borrow()
    }

    /// Borrow the world mutably. Keep the guard SHORT (see [`SharedWorld::read`]).
    pub(crate) fn write(&self) -> RefMut<'_, GameWorld> {
        self.0.borrow_mut()
    }

    /// Whether two handles name the SAME world — object identity on the ledger itself.
    pub fn is_same(&self, other: &SharedWorld) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    /// How many items the registry carries.
    pub fn item_count(&self) -> usize {
        self.0.borrow().items.len()
    }

    /// **Seed the craft bench** — the player's typed material notes + three recipes pulled from the
    /// forge's committed catalog. Greatblade (2× iron + haft) and Charm (frost + silver) are fully
    /// stocked and craftable; Aegis needs 2× iron + `hide:drake`, which is never wired, so a real
    /// typed-floor refusal stays reachable.
    pub fn seed_craft_bench(&self) {
        let mut w = self.write();
        let player = w.player.clone();
        let specs: [(&str, &str); 7] = [
            ("Iron Ore", "ore:iron"),
            ("Iron Ore", "ore:iron"),
            ("Oak Haft", "haft:oak"),
            ("Frost Essence", "essence:frost"),
            ("Silver Leaf", "silver:leaf"),
            ("Iron Ore", "ore:iron"),
            ("Iron Ore", "ore:iron"),
        ];
        for (i, (name, kind)) in specs.iter().enumerate() {
            let asset = w.forge.mint_material(
                &player,
                kind,
                format!("dreggnet-surfaces/mat-{i}").as_bytes(),
            );
            w.materials.push(Material {
                asset,
                name: (*name).to_string(),
            });
        }
        let benches = vec![
            (
                w.forge.recipe("forge:greatblade").expect("starter").clone(),
                "Greatblade",
                vec![0usize, 1, 2],
            ),
            (
                w.forge.recipe("forge:charm").expect("starter").clone(),
                "Charm",
                vec![3, 4],
            ),
            (
                w.forge.recipe("forge:aegis").expect("starter").clone(),
                "Aegis",
                vec![5, 6],
            ),
        ];
        for (recipe, label, inputs) in benches {
            w.benches.push(Bench {
                recipe,
                label: label.to_string(),
                inputs,
            });
        }
    }

    /// **Seed the player's owned item notes** — one real minted note per spec, registered on the
    /// player's shelf with an ask derived from its rarity.
    pub fn seed_items(&self, items: &[InventoryItem]) {
        let mut w = self.write();
        let player = w.player.clone();
        for spec in items {
            let asset = w.assets().mint(&player, spec.mint_seed.as_bytes());
            w.register_item(ItemRecord {
                asset,
                name: spec.name.clone(),
                rarity: spec.rarity.clone(),
                kind: spec.kind.clone(),
                owner: player.clone(),
                price: ask_for(&spec.rarity),
                listed: false,
                sold: false,
                origin: Origin::Seeded,
            });
        }
    }

    /// **Seed the market stock + the buyer's purse** — the player's three canned goods (registered
    /// on the player's shelf like any other owned item) and `buyer`'s three trade-coins. The purse
    /// is deliberately short of total demand, so the market can exhaust the buyer and a further buy
    /// is a genuine "cannot pay" refusal.
    pub fn seed_trade_stock(&self, buyer: &str) {
        let mut w = self.write();
        let player = w.player.clone();
        let stock = [
            ("Ember Cloak", "legendary", 2usize),
            ("Frost Charm", "rare", 1),
            ("Whisper Dagger", "uncommon", 1),
        ];
        for (i, (name, rarity, price)) in stock.iter().enumerate() {
            let asset = w
                .assets()
                .mint(&player, format!("dreggnet-surfaces/good-{i}").as_bytes());
            w.register_item(ItemRecord {
                asset,
                name: (*name).to_string(),
                rarity: (*rarity).to_string(),
                kind: "gear".to_string(),
                owner: player.clone(),
                price: *price,
                listed: false,
                sold: false,
                origin: Origin::Seeded,
            });
        }
        for i in 0..3 {
            let coin = w
                .assets()
                .mint(buyer, format!("dreggnet-surfaces/coin-{i}").as_bytes());
            w.coins.push(coin);
        }
    }
}
