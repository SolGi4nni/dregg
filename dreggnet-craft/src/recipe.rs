//! The **recipe catalog** — typed, multi-input, tiered recipes, and what a craft
//! produces. A [`Recipe`] names the exact multiset of material *kinds* it consumes, the
//! committed outcome/quality weight tables its draws are taken over, and the
//! [`OutputSpec`] it forges — a real [`dreggnet_gear::StatBlock`] or a companion egg. A
//! [`RecipeBook`] is the registered set a forge crafts against; a craft can only present a
//! recipe the book holds, so the weight tables (the rarity odds) are committed, not
//! per-craft.

use std::collections::HashMap;

use dreggnet_gear::{GearSlot, StatBlock};
use dungeon_on_dregg::loot::Rarity as LootRarity;

use crate::quality::CraftQuality;

/// A material's **kind** — the semantic type a recipe requires (e.g. `"ore:iron"`,
/// `"essence:frost"`). A material asset carries its kind in the forge; a recipe consumes a
/// *multiset* of kinds, so "a greatblade needs two iron and one oak-hilt" is a typed
/// requirement, not merely "three of anything".
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct MaterialKind(pub String);

impl MaterialKind {
    /// A kind from a label.
    pub fn new(kind: &str) -> MaterialKind {
        MaterialKind(kind.to_string())
    }

    /// The kind's label.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for MaterialKind {
    fn from(s: &str) -> MaterialKind {
        MaterialKind::new(s)
    }
}

/// A gear **template** — the base stat block a recipe forges, before the quality tier
/// scales it. The crafted [`StatBlock`]'s stats are `base * quality.stat_percent() / 100`,
/// and its rarity is the fair tier, so a legendary craft is a materially stronger, real,
/// equippable item.
#[derive(Clone, Debug)]
pub struct GearTemplate {
    /// The slot the forged gear occupies.
    pub slot: GearSlot,
    /// The rune / affix id the forged gear carries (fixed by the recipe).
    pub rune: u64,
    /// The base offensive stat (scaled by the quality tier).
    pub base_might: u64,
    /// The base defensive stat (scaled by the quality tier).
    pub base_ward: u64,
    /// The base utility stat (scaled by the quality tier).
    pub base_guile: u64,
}

impl GearTemplate {
    /// The real [`dreggnet_gear::StatBlock`] this template forges at `quality` — the shared
    /// gear schema (rarity is the tier's [`CraftQuality::gear_rarity`], stats scaled by the
    /// tier's [`CraftQuality::stat_percent`]).
    pub fn stat_block(&self, quality: CraftQuality) -> StatBlock {
        let pct = quality.stat_percent();
        StatBlock {
            rarity: quality.gear_rarity(),
            slot: self.slot,
            might: self.base_might * pct / 100,
            ward: self.base_ward * pct / 100,
            guile: self.base_guile * pct / 100,
            rune: self.rune,
        }
    }
}

/// What a recipe forges. A crafted output is a REAL cross-crate artifact, not an opaque
/// note: either a [`dreggnet_gear::StatBlock`] (equippable by the `Armory`) or a companion
/// egg (a species + granted rarity `dreggnet_companion` hatches from).
#[derive(Clone, Debug)]
pub enum OutputSpec {
    /// A piece of gear — a scaled [`StatBlock`] from this template.
    Gear(GearTemplate),
    /// A companion egg of `species` — hatched (elsewhere) at the granted rarity.
    CompanionEgg {
        /// The species label (e.g. `"companion:frostwyrm"`).
        species: String,
    },
}

/// The concrete artifact a resolved craft produces — a real [`StatBlock`] or a species+
/// rarity egg. Purely a function of `(recipe output, granted quality)`, so there is no
/// forgery surface on the artifact itself: the forge derives it, the crafter never supplies
/// it. Its [`Self::content_digest`] binds into the output asset's content address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CraftedArtifact {
    /// A forged piece of gear carrying a real, equippable stat block.
    Gear(StatBlock),
    /// A forged companion egg — the species + the shared-schema rarity it hatches at.
    CompanionEgg {
        /// The species label.
        species: String,
        /// The rarity the egg hatches at (the shared `dungeon_on_dregg::loot::Rarity`).
        rarity: dungeon_on_dregg::loot::Rarity,
    },
}

impl CraftedArtifact {
    /// A stable content digest of the artifact — the gear block's own
    /// [`StatBlock::traits_root`] (the exact commitment `dreggnet-gear` mints under), or a
    /// domain-separated hash of the egg's species + rarity. Folded into the craft commitment
    /// so the output asset id binds the concrete item, not just its tier tag.
    pub fn content_digest(&self) -> [u8; 32] {
        match self {
            CraftedArtifact::Gear(block) => block.traits_root(),
            CraftedArtifact::CompanionEgg { species, rarity } => {
                let mut h = blake3::Hasher::new_derive_key("dreggnet-craft-egg-artifact-v1");
                h.update(&(species.len() as u64).to_le_bytes());
                h.update(species.as_bytes());
                // The loot layer's OWN canonical tag byte, not a parallel table here — the
                // egg's committed rarity and a loot drop's are the same encoding.
                h.update(&[rarity.tag()]);
                *h.finalize().as_bytes()
            }
        }
    }
}

/// A **recipe** — a typed, tiered forging plan. Its `id` binds into the craft seed + the
/// output's content address; its `inputs` are the exact multiset of material kinds it
/// consumes (the real sink); its committed `outcome_weights` / `quality_weights` fix the
/// odds; its `output` is what it forges.
#[derive(Clone, Debug)]
pub struct Recipe {
    /// The recipe's stable id (e.g. `"forge:greatblade"`).
    pub id: String,
    /// The exact multiset of material kinds this recipe consumes (order-independent).
    pub inputs: Vec<MaterialKind>,
    /// The committed `[Botch, Partial, Success]` outcome weights (must sum `> 0`).
    pub outcome_weights: [u64; 3],
    /// The committed `[Common, Uncommon, Rare, Legendary]` quality weights (must sum `> 0`).
    pub quality_weights: [u64; 4],
    /// What this recipe forges.
    pub output: OutputSpec,
}

impl Recipe {
    /// A **safe** gear recipe — always succeeds (outcome weights all on `Success`), default
    /// rarity odds (`~3%` legendary). The minimal shape the crate shipped, now typed +
    /// output-bound.
    pub fn gear(id: &str, inputs: &[&str], template: GearTemplate) -> Recipe {
        Recipe {
            id: id.to_string(),
            inputs: inputs.iter().map(|k| MaterialKind::new(k)).collect(),
            outcome_weights: [0, 0, 1],
            quality_weights: DEFAULT_QUALITY_WEIGHTS,
            output: OutputSpec::Gear(template),
        }
    }

    /// A **risky** recipe — the given `[botch, partial, success]` odds. A botch eats the
    /// materials for nothing; a partial forges one tier down. The gamble a deeper sink adds.
    pub fn risky(
        id: &str,
        inputs: &[&str],
        outcome_weights: [u64; 3],
        quality_weights: [u64; 4],
        output: OutputSpec,
    ) -> Recipe {
        Recipe {
            id: id.to_string(),
            inputs: inputs.iter().map(|k| MaterialKind::new(k)).collect(),
            outcome_weights,
            quality_weights,
            output,
        }
    }

    /// The number of inputs (the real sink floor) this recipe consumes.
    pub fn input_count(&self) -> usize {
        self.inputs.len()
    }

    /// The required input kinds as a sorted-count multiset (for the atomic input match).
    pub fn required_kinds(&self) -> HashMap<MaterialKind, usize> {
        let mut m: HashMap<MaterialKind, usize> = HashMap::new();
        for k in &self.inputs {
            *m.entry(k.clone()).or_insert(0) += 1;
        }
        m
    }

    /// Is this recipe well-formed — at least one input, and both weight tables non-degenerate
    /// (sum `> 0`)? A degenerate recipe would make the fair draw ill-defined.
    pub fn is_well_formed(&self) -> bool {
        !self.inputs.is_empty()
            && self.outcome_weights.iter().sum::<u64>() > 0
            && self.quality_weights.iter().sum::<u64>() > 0
    }
}

/// The default `[Common, Uncommon, Rare, Legendary]` quality weights — the crate's original
/// flat-band feel (`60 / 25 / 12 / 3`), now a committed CDF over
/// [`procgen_dregg`]'s provably-fair `weighted` draw.
pub const DEFAULT_QUALITY_WEIGHTS: [u64; 4] = [60, 25, 12, 3];

// ── the DUNGEON-SOURCED material vocabulary ──────────────────────────────────────────
//
// These kinds are not free labels a faucet stamps on: `dungeon_on_dregg::loot`'s
// `LootDraw::material_kind` DERIVES `"{class}:{rarity}"` from the drop's chest and its FAIR
// DRAW's rarity, so a material's kind is fixed by the run that dropped it. A recipe naming
// `relic:legendary` therefore demands a genuinely legendary banked relic — the ~3% tail of a
// real run — and cannot be satisfied by relabelling a common drop.

/// The material kind a **banked descent relic** of `rarity` presents as a craft input —
/// the kind `dungeon_on_dregg::loot::LootDraw::material_kind` derives for a
/// `descent:banked-relic:*` drop. The vocabulary that ties the forge's catalog to the
/// dungeon's actual output.
pub fn relic_kind(rarity: LootRarity) -> String {
    format!("relic:{}", rarity.label())
}

/// The material kind an ordinary chest **salvage** drop of `rarity` presents as a craft input.
pub fn salvage_kind(rarity: LootRarity) -> String {
    format!("salvage:{}", rarity.label())
}

/// The material kind a named-boss **trophy** drop of `rarity` presents as a craft input.
pub fn trophy_kind(rarity: LootRarity) -> String {
    format!("trophy:{}", rarity.label())
}

/// The catalog id of the relic-sigil forge at `rarity` — the tier ladder's rung for relics of
/// that tier (see [`RecipeBook::reliquary`]).
pub fn relic_sigil_id(rarity: LootRarity) -> String {
    format!("forge:relic-sigil:{}", rarity.label())
}

/// One rung of the relic ladder: TWO banked relics of `rarity` forge a sigil.
///
/// Both the reward and the risk climb with the tier — a legendary pair carries the fattest
/// legendary quality tail AND the steepest botch chance, so spending the ~3% tail of two real
/// runs is a genuine gamble rather than a guaranteed upgrade. The odds are committed to the
/// catalog, so a crafter cannot bring their own.
fn relic_sigil(rarity: LootRarity) -> Recipe {
    let kind = relic_kind(rarity);
    let (outcome, quality, base) = match rarity {
        //                botch/partial/success      C   U   R   L      base stat
        LootRarity::Common => ([10, 30, 60], [70, 22, 7, 1], 8),
        LootRarity::Uncommon => ([10, 30, 60], [45, 33, 17, 5], 14),
        LootRarity::Rare => ([15, 30, 55], [20, 35, 32, 13], 22),
        LootRarity::Legendary => ([20, 30, 50], [5, 20, 40, 35], 34),
    };
    Recipe::risky(
        &relic_sigil_id(rarity),
        &[kind.as_str(), kind.as_str()],
        outcome,
        quality,
        OutputSpec::Gear(GearTemplate {
            slot: GearSlot::Trinket,
            rune: 0x40 + rarity.tag() as u64,
            base_might: base,
            base_ward: base,
            base_guile: base * 2,
        }),
    )
}

/// The **recipe catalog** — the registered set a forge crafts against. A craft can only
/// present a recipe the book holds (by id), so the weight tables (the odds) and the typed
/// input requirements are committed to the catalog, never chosen per-craft.
#[derive(Clone, Debug, Default)]
pub struct RecipeBook {
    recipes: HashMap<String, Recipe>,
}

impl RecipeBook {
    /// An empty catalog.
    pub fn new() -> RecipeBook {
        RecipeBook {
            recipes: HashMap::new(),
        }
    }

    /// The **starter catalog** — a real, varied set: safe and risky gear recipes across the
    /// three slots + a companion-egg recipe. Every recipe is well-formed.
    pub fn starter() -> RecipeBook {
        let mut book = RecipeBook::new();
        book.register(Recipe::gear(
            "forge:greatblade",
            &["ore:iron", "ore:iron", "haft:oak"],
            GearTemplate {
                slot: GearSlot::Weapon,
                rune: 0x01,
                base_might: 40,
                base_ward: 0,
                base_guile: 4,
            },
        ));
        book.register(Recipe::gear(
            "forge:aegis",
            &["ore:iron", "ore:iron", "hide:drake"],
            GearTemplate {
                slot: GearSlot::Armor,
                rune: 0x02,
                base_might: 0,
                base_ward: 36,
                base_guile: 6,
            },
        ));
        book.register(Recipe::gear(
            "forge:charm",
            &["essence:frost", "silver:leaf"],
            GearTemplate {
                slot: GearSlot::Trinket,
                rune: 0x07,
                base_might: 6,
                base_ward: 6,
                base_guile: 24,
            },
        ));
        // A risky relic forge: a real chance to botch (lose the materials) or forge a flawed
        // partial, with a fatter legendary tail as the reward for the risk.
        book.register(Recipe::risky(
            "forge:relic",
            &["ore:star-iron", "essence:void", "essence:void"],
            [20, 30, 50],
            [30, 30, 25, 15],
            OutputSpec::Gear(GearTemplate {
                slot: GearSlot::Weapon,
                rune: 0x1f,
                base_might: 60,
                base_ward: 10,
                base_guile: 10,
            }),
        ));
        // A companion egg — a real cross-crate output (species + shared-schema rarity).
        book.register(Recipe::risky(
            "forge:frostwyrm-egg",
            &["essence:frost", "essence:frost", "shell:ancient"],
            [10, 20, 70],
            DEFAULT_QUALITY_WEIGHTS,
            OutputSpec::CompanionEgg {
                species: "companion:frostwyrm".to_string(),
            },
        ));
        // The DUNGEON-SOURCED half of the catalog — recipes over kinds the fair loot draw
        // actually produces, so a real run's output has somewhere to go.
        book.extend(RecipeBook::reliquary());
        book
    }

    /// **The reliquary catalog** — the recipes that consume REAL dungeon output.
    ///
    /// Every input kind here is one the loot layer *derives* from a verified drop
    /// (`dungeon_on_dregg::loot::LootDraw::material_kind`), never one a faucet stamps on:
    ///
    /// * **the relic ladder** — [`relic_sigil_id`]`(t)` for each tier, `2 × relic:t → a sigil`.
    ///   Reward and risk both climb with the tier, so a legendary pair is a real gamble;
    /// * **the Warden's Reliquary** — the aspirational sink: two legendary relics AND a rare
    ///   one, forging a weapon. Costs the tail of several real runs;
    /// * **the salvage bench** — three common salvage drops into a modest charm, so the
    ///   bottom of the drop table is not pure dead weight (an economy needs a floor sink, not
    ///   only a jackpot one);
    /// * **the trophy mount** — a rare boss trophy plus salvage, the cosmetic-ish middle.
    pub fn reliquary() -> RecipeBook {
        let mut book = RecipeBook::new();
        for rarity in [
            LootRarity::Common,
            LootRarity::Uncommon,
            LootRarity::Rare,
            LootRarity::Legendary,
        ] {
            book.register(relic_sigil(rarity));
        }
        let leg = relic_kind(LootRarity::Legendary);
        let rare = relic_kind(LootRarity::Rare);
        book.register(Recipe::risky(
            "forge:wardens-reliquary",
            &[leg.as_str(), leg.as_str(), rare.as_str()],
            [25, 25, 50],
            [0, 10, 40, 50],
            OutputSpec::Gear(GearTemplate {
                slot: GearSlot::Weapon,
                rune: 0x4f,
                base_might: 70,
                base_ward: 18,
                base_guile: 18,
            }),
        ));
        let com_salvage = salvage_kind(LootRarity::Common);
        book.register(Recipe::gear(
            "forge:salvaged-charm",
            &[
                com_salvage.as_str(),
                com_salvage.as_str(),
                com_salvage.as_str(),
            ],
            GearTemplate {
                slot: GearSlot::Trinket,
                rune: 0x41,
                base_might: 3,
                base_ward: 3,
                base_guile: 9,
            },
        ));
        book.register(Recipe::risky(
            "forge:trophy-mount",
            &[
                trophy_kind(LootRarity::Rare).as_str(),
                salvage_kind(LootRarity::Uncommon).as_str(),
            ],
            [5, 25, 70],
            [30, 35, 25, 10],
            OutputSpec::Gear(GearTemplate {
                slot: GearSlot::Armor,
                rune: 0x42,
                base_might: 4,
                base_ward: 26,
                base_guile: 8,
            }),
        ));
        book
    }

    /// Register (or replace) a recipe. Returns `false` (and does not register) if the recipe
    /// is not well-formed — a degenerate recipe never enters the catalog.
    pub fn register(&mut self, recipe: Recipe) -> bool {
        if !recipe.is_well_formed() {
            return false;
        }
        self.recipes.insert(recipe.id.clone(), recipe);
        true
    }

    /// Fold every recipe of `other` into this catalog (later registrations win, as with
    /// [`Self::register`]).
    pub fn extend(&mut self, other: RecipeBook) {
        for (_, recipe) in other.recipes {
            self.register(recipe);
        }
    }

    /// The recipe with `id`, if the catalog holds it.
    pub fn get(&self, id: &str) -> Option<&Recipe> {
        self.recipes.get(id)
    }

    /// Every recipe whose required multiset mentions `kind` — "what is this material FOR?",
    /// the lookup a bench UI does when a player selects a relic they just banked.
    pub fn recipes_using(&self, kind: &str) -> Vec<&Recipe> {
        let want = MaterialKind::new(kind);
        let mut hits: Vec<&Recipe> = self
            .recipes
            .values()
            .filter(|r| r.inputs.contains(&want))
            .collect();
        hits.sort_by(|a, b| a.id.cmp(&b.id));
        hits
    }

    /// Every registered recipe id (sorted, for a stable listing).
    pub fn ids(&self) -> Vec<String> {
        let mut ids: Vec<String> = self.recipes.keys().cloned().collect();
        ids.sort();
        ids
    }

    /// How many recipes the catalog holds.
    pub fn len(&self) -> usize {
        self.recipes.len()
    }

    /// Is the catalog empty?
    pub fn is_empty(&self) -> bool {
        self.recipes.is_empty()
    }
}
