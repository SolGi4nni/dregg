//! # `statblock` — a gear item's stat/trait block, DECLARED via `dregg-schema` and
//! CONTENT-ADDRESSED into the asset identity.
//!
//! A piece of gear is not a flat "+5 sword" — it carries a **stat block**: a rarity, a
//! slot (weapon / armor / trinket), and a small vector of stat traits (might / ward /
//! guile / a rune id). Two things make this a real dregg construction rather than a
//! server row:
//!
//! * **Declared, not hand-rolled.** [`stat_block_schema`] is a [`dregg_schema::Schema`]
//!   of the block's components, lowered by the VERIFIED allocator
//!   ([`dregg_schema::allocate_checked`]) to a Legal (disjoint + in-bounds) register
//!   layout — the same keystone `dreggnet-asset`'s note layout rides. Declaring the
//!   block proves it is a legal cell-state layout; we do not hand-roll a slot map.
//! * **Content-addressed into the asset.** [`StatBlock::traits_root`] is a `blake3`
//!   digest over the whole block. Minting the gear asset with this root as the mint
//!   seed makes the [`dreggnet_asset::AssetId`] a content commitment to the exact stat
//!   block: the rarity + traits are provably BOUND to the asset id, carried `WriteOnce`
//!   across the lineage (the `dreggnet-asset` E1 `traits_root` shape). A tampered block
//!   yields a different root → a different asset id → a broken lineage.
//!
//! ## Honest scope
//!
//! REAL: the declared + allocator-checked schema, the content-addressed `traits_root`,
//! and the rarity/slot/traits carried on it. NAMED SEAM: the *provably-fair weighted
//! DRAW* of a rarity (a CDF over a committed-seed `dregg-dice` stream) is `loot.rs` /
//! the E2 `DrawStream::weighted` frontier — here the rarity is a declared field whose
//! *commitment* is real; the fair roll that PRODUCES it is the named add.

use dregg_schema::{Schema, Slot, allocate_checked};

/// A gear item's rarity tier. A rarer tier is the provable tail a fair drop lands on
/// (the DRAW is `loot.rs`'s frontier; here the tier is a declared, content-bound field).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rarity {
    /// The common floor.
    Common,
    /// An uncommon drop.
    Uncommon,
    /// A rare drop.
    Rare,
    /// A legendary — the provable ~3% tail.
    Legendary,
}

impl Rarity {
    /// The wire tag folded into the traits_root (stable across builds).
    pub fn tag(self) -> u8 {
        match self {
            Rarity::Common => 0,
            Rarity::Uncommon => 1,
            Rarity::Rare => 2,
            Rarity::Legendary => 3,
        }
    }
}

/// Which equipment slot a piece of gear occupies. Named residual: multi-slot loadouts
/// (weapon + armor + trinket held simultaneously) and set bonuses (a multi-peer
/// conjunction of `ObservedFieldEquals`) build on this field.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GearSlot {
    /// A weapon (the flaming sword).
    Weapon,
    /// Armor.
    Armor,
    /// A trinket / accessory.
    Trinket,
}

impl GearSlot {
    /// The wire tag folded into the traits_root.
    pub fn tag(self) -> u8 {
        match self {
            GearSlot::Weapon => 0,
            GearSlot::Armor => 1,
            GearSlot::Trinket => 2,
        }
    }
}

/// The immutable stat/trait block of a piece of gear. Its [`Self::traits_root`] is the
/// content commitment carried into the asset id, so the block is provably bound to the
/// owned asset.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StatBlock {
    /// The rarity tier (a fair-drop tail; here a declared, content-bound field).
    pub rarity: Rarity,
    /// The equipment slot this gear occupies.
    pub slot: GearSlot,
    /// Offensive stat (e.g. the flaming sword's bite).
    pub might: u64,
    /// Defensive stat.
    pub ward: u64,
    /// Utility stat.
    pub guile: u64,
    /// A rune / affix id (the ability the gear unlocks keys off this).
    pub rune: u64,
}

impl StatBlock {
    /// A weapon stat block (the flaming sword archetype).
    pub fn weapon(rarity: Rarity, might: u64, rune: u64) -> Self {
        StatBlock {
            rarity,
            slot: GearSlot::Weapon,
            might,
            ward: 0,
            guile: 0,
            rune,
        }
    }

    /// The content-addressed **traits_root** — a `blake3` digest over the whole block.
    /// Used as the mint seed so the [`dreggnet_asset::AssetId`] commits to this exact
    /// block (rarity + traits provably bound to the asset). A single changed field
    /// yields a different root.
    pub fn traits_root(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dreggnet-gear-traits-root-v1");
        h.update(&[self.rarity.tag(), self.slot.tag()]);
        h.update(&self.might.to_le_bytes());
        h.update(&self.ward.to_le_bytes());
        h.update(&self.guile.to_le_bytes());
        h.update(&self.rune.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

/// **The gear stat-block component schema** — declared + lowered by the VERIFIED
/// allocator to a Legal register layout. `rarity` / `slot` / `rune` are write-once
/// identity components (frozen at forge); `might` / `ward` / `guile` are bounded stats.
/// Declaring the block proves it is a legal cell-state layout (the keystone owns layout
/// legality); the block's *values* ride the content-addressed [`StatBlock::traits_root`].
pub fn stat_block_schema() -> Schema {
    Schema::new("dreggnet-gear-statblock")
        .identity("rarity")
        .identity("slot")
        .identity("rune")
        .stat("might", 0, 1_000_000)
        .stat("ward", 0, 1_000_000)
        .stat("guile", 0, 1_000_000)
}

/// The allocator-resolved register index of each stat-block component — proof the block
/// lowers to a Legal (disjoint + in-bounds) layout via the verified keystone.
pub fn stat_block_layout() -> Vec<(String, u8)> {
    let layout = allocate_checked(&stat_block_schema())
        .expect("the gear stat-block schema is a legal register layout");
    stat_block_schema()
        .components
        .iter()
        .map(|c| {
            let reg = match layout.resolve(&c.name).expect("component resolves") {
                Slot::Register(r) => r,
                Slot::Heap(_) => panic!("stat-block fields are register-placed"),
            };
            (c.name.clone(), reg)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The stat block is DECLARED + allocator-checked: every component lowers to a
    /// distinct in-bounds register (the verified-allocator keystone accepts it).
    #[test]
    fn stat_block_lowers_to_a_legal_layout() {
        let layout = stat_block_layout();
        assert_eq!(layout.len(), 6, "six declared components");
        let regs: Vec<u8> = layout.iter().map(|(_, r)| *r).collect();
        let mut sorted = regs.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), regs.len(), "register slots are disjoint");
        assert!(
            regs.iter().all(|r| (*r as usize) < 16),
            "every slot is in the 16-register budget"
        );
    }

    /// The traits_root is a real content commitment: a changed field (rarer tier, more
    /// might, a different rune) yields a DIFFERENT root — the sprite/rarity is provably
    /// bound to the block.
    #[test]
    fn traits_root_is_content_addressed() {
        let common = StatBlock::weapon(Rarity::Common, 5, 7);
        let legendary = StatBlock::weapon(Rarity::Legendary, 5, 7);
        let stronger = StatBlock::weapon(Rarity::Common, 9, 7);
        let other_rune = StatBlock::weapon(Rarity::Common, 5, 8);

        assert_ne!(
            common.traits_root(),
            legendary.traits_root(),
            "rarity changes the root"
        );
        assert_ne!(
            common.traits_root(),
            stronger.traits_root(),
            "might changes the root"
        );
        assert_ne!(
            common.traits_root(),
            other_rune.traits_root(),
            "rune changes the root"
        );
        // Identical blocks hash identically (deterministic commitment).
        assert_eq!(
            common.traits_root(),
            StatBlock::weapon(Rarity::Common, 5, 7).traits_root()
        );
    }
}
