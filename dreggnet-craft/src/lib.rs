//! # `dreggnet-craft` — a provably-fair FORGE: the economy's first real SINK.
//!
//! CRAFTING (GAME-INFRA-ROADMAP progression #2). Every other economy motion so far
//! is a FAUCET — loot drops, echoes, quest rewards MINT assets into circulation. A
//! forge is the inverse and the thing an economy actually needs: it **CONSUMES** N
//! owned material assets (the inputs) and produces ONE new output asset. The inputs
//! are genuinely destroyed on-chain — the first real **sink**, the tooth that keeps
//! the supply from only ever growing.
//!
//! ## The forge, end to end
//!
//! 1. **The fair outcome.** A craft's quality is one indexed draw of a VERIFIED
//!    procgen stream ([`procgen_dregg::verified_stream`]) seeded by a committed
//!    **craft seed** ([`derive_craft_seed`]) — a domain-separated hash of a committed
//!    beacon value, the recipe id, and the (sorted) input [`AssetId`]s. The quality is
//!    the draw's distribution ([`quality_of_roll`]): a [`CraftQuality::Legendary`] is
//!    the ~3% tail — a *provable* flex. Because the seed is committed and the draw is a
//!    pure verified function of it, anyone re-derives the identical outcome (the
//!    fairness anchor is procgen's), so a legendary craft cannot be fabricated.
//! 2. **The inputs are SPENT.** Before minting anything the forge checks every input
//!    is a real asset the crafter owns and that is still *live* (not already spent /
//!    consumed). It then **destroys each input on-chain** through the asset layer's own
//!    spend tooth ([`dreggnet_asset::AssetWorld::attempt_respend`] on the live tail: a
//!    genuine committed owner-signed spend, after which the asset layer's own
//!    [`dreggnet_asset::AssetWorld::verify_provenance`] reports the note *gone*). The
//!    materials are consumed — there is no dupe-then-craft, because a spent note cannot
//!    be spent again.
//! 3. **The output binds its provenance.** A verified craft MINTS a
//!    [`dreggnet_asset`] note owned by the crafter under a **mint seed = the craft's
//!    content commitment** ([`craft_commitment`], binding the recipe id, the input
//!    [`AssetId`]s, the fair roll, and the quality). The output's content address
//!    ([`AssetId`]) therefore itself encodes "forged from THESE inputs, THAT recipe, a
//!    1% roll" — the flex is baked into the item's identity, not a side note.
//!
//! ## A forged craft mints NOTHING
//!
//! [`CraftForge::craft`] gates the whole motion on [`reverify_craft`] + the input
//! liveness check. A fabricated outcome — a craft claiming a legendary the seed never
//! produced (a rewritten roll/quality) — fails [`reverify_craft`] and **no input is
//! spent and no asset is minted**. A craft claiming inputs the crafter does not own, or
//! inputs already consumed, is **Refused** with no mint. So a crafted item cannot be
//! conjured; its inputs must be *really destroyed* and its outcome must be the *fair
//! draw*.
//!
//! ## Honest scope
//!
//! REAL here: the input-consuming sink (materials provably destroyed on-chain, not
//! merely bookkept), the committed-seed fair quality draw, the recipe/inputs/roll-bound
//! output identity, and the forged-craft refusal — all DRIVEN in [`mod tests`] against
//! the real [`dreggnet_asset`] executor-refereed asset layer. NAMED, not built:
//! **recipe trees** (a recipe here is an id + a minimum input count, not a typed
//! material graph), **catalysts** (an input that shifts the odds), **weighted quality
//! tiers** (the flat `d100` bands here become a [`procgen_dregg`] E2
//! `DrawStream::weighted` CDF over a committed weight table), and **commissioned
//! crafts** (a craft paid for through the `escrow-market` swap). This module is the
//! sink primitive those surfaces deepen.

use std::collections::{HashMap, HashSet};

use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport};
use procgen_dregg::CommittedSeed;

/// The index of the craft quality draw within the verified procgen stream (well under
/// the committed `DRAW_COUNT` budget, so the draw is always in range).
const CRAFT_DRAW_INDEX: u32 = 0;

/// The face count of a craft draw — a `d100` (`0..100`), so the quality tiers below
/// carve a clean percentage distribution.
const QUALITY_FACES: u64 = 100;

/// The domain tag folded into a craft seed derivation (so a craft draw stream can
/// never collide with the loot / dungeon-generation streams that share the beacon).
const DOMAIN_CRAFT_SEED: &[u8] = b"dreggnet-craft/craft-seed/v1";

/// The domain tag for a craft's content commitment (the output asset's mint seed).
const DOMAIN_CRAFT_COMMIT: &[u8] = b"dreggnet-craft/craft-commitment/v1";

/// A crafted item's **quality** — the tier of the fair draw. Rarer tiers are a smaller
/// slice of the `0..100` draw, so a [`CraftQuality::Legendary`] is a genuine ~3% flex
/// whose provenance (the recipe + inputs + seed it was forged from) anyone re-derives.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CraftQuality {
    /// The baseline craft — `60%` of draws (`0..=59`). A serviceable output.
    Common,
    /// A fine craft — `25%` of draws (`60..=84`).
    Uncommon,
    /// A masterwork — `12%` of draws (`85..=96`).
    Rare,
    /// A legendary forging — the ~`3%` tail (`97..=99`). A provable flex.
    Legendary,
}

impl CraftQuality {
    /// A stable byte tag (folded into the craft commitment so the quality is bound into
    /// the output's content address).
    fn tag(self) -> u8 {
        match self {
            CraftQuality::Common => 0,
            CraftQuality::Uncommon => 1,
            CraftQuality::Rare => 2,
            CraftQuality::Legendary => 3,
        }
    }

    /// The human label.
    pub fn label(self) -> &'static str {
        match self {
            CraftQuality::Common => "common",
            CraftQuality::Uncommon => "uncommon",
            CraftQuality::Rare => "rare",
            CraftQuality::Legendary => "legendary",
        }
    }
}

/// The quality a `0..100` fair-draw face maps to — the craft outcome distribution. A
/// legendary is the `97..=99` tail (~3%), so it is a provable outcome, not a claim.
pub fn quality_of_roll(roll: u64) -> CraftQuality {
    match roll {
        97..=99 => CraftQuality::Legendary,
        85..=96 => CraftQuality::Rare,
        60..=84 => CraftQuality::Uncommon,
        _ => CraftQuality::Common,
    }
}

/// A **recipe** — an id and the minimum number of input materials it consumes. The
/// recipe id binds into the craft seed + the output's content address (so a craft's
/// identity records which recipe forged it). Typed material graphs / catalysts are a
/// named residual; this is the minimal honest recipe.
#[derive(Clone, Debug)]
pub struct Recipe {
    /// The recipe's stable id (e.g. `"forge:greatblade"`).
    pub id: String,
    /// The fewest inputs a craft of this recipe must consume (a real sink floor).
    pub min_inputs: usize,
}

impl Recipe {
    /// A recipe consuming at least `min_inputs` materials.
    pub fn new(id: &str, min_inputs: usize) -> Recipe {
        Recipe {
            id: id.to_string(),
            min_inputs,
        }
    }
}

/// Derive the **craft seed** for an attempt from a committed beacon value, the recipe
/// id, and the (sorted) input asset ids — a domain-separated hash, so the outcome is a
/// reproducible, input-bound draw a verifier who holds the same context re-derives. The
/// input ids are sorted so the seed is independent of the order the inputs are listed.
pub fn derive_craft_seed(
    beacon: &CommittedSeed,
    recipe_id: &str,
    input_ids: &[[u8; 32]],
) -> CommittedSeed {
    let mut sorted = input_ids.to_vec();
    sorted.sort_unstable();
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_CRAFT_SEED.len() as u64).to_le_bytes());
    h.update(DOMAIN_CRAFT_SEED);
    h.update(beacon.as_bytes());
    h.update(&(recipe_id.len() as u64).to_le_bytes());
    h.update(recipe_id.as_bytes());
    h.update(&(sorted.len() as u64).to_le_bytes());
    for id in &sorted {
        h.update(id);
    }
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// A resolved, provably-fair craft outcome: the beacon + recipe + (sorted) input ids it
/// came from, the committed craft seed it was drawn from, the raw fair-draw face, and
/// the quality that face fixes. This is the receipt of a real draw —
/// [`reverify_craft`] re-derives it from the committed context alone, so a forged
/// (fabricated / rewritten) outcome is caught before any input is spent.
#[derive(Clone, Debug)]
pub struct CraftDraw {
    /// The committed beacon value the outcome is anchored to (its unpredictability
    /// root; in the flagship this is the verified drand-beacon day-seed).
    pub beacon: CommittedSeed,
    /// The recipe id the craft was forged under.
    pub recipe_id: String,
    /// The input asset ids consumed, SORTED (order-independent).
    pub input_ids: Vec<[u8; 32]>,
    /// The committed craft seed the fair draw was taken from ([`derive_craft_seed`]).
    pub craft_seed: CommittedSeed,
    /// The raw fair-draw face (`0..100`).
    pub roll: u64,
    /// The quality the roll fixes.
    pub quality: CraftQuality,
}

impl CraftDraw {
    /// The display line for a craft outcome (the roll/quality are content-bound).
    pub fn describe(&self) -> String {
        format!(
            "{} craft of `{}` from {} inputs (roll {}/{})",
            self.quality.label(),
            self.recipe_id,
            self.input_ids.len(),
            self.roll,
            QUALITY_FACES,
        )
    }
}

/// **Roll a real, provably-fair craft outcome** for a recipe over a set of input
/// assets under a committed beacon. Derives the committed craft seed, runs the VERIFIED
/// procgen stream, and reads the fair-draw face + its quality. Deterministic in
/// `(beacon, recipe_id, input_ids)` — the same context always re-derives the identical
/// outcome (the fairness anchor is the committed seed; a crafter cannot grind a
/// favourable result without different inputs or a different beacon).
pub fn roll_craft(beacon: &CommittedSeed, recipe: &Recipe, inputs: &[AssetId]) -> CraftDraw {
    let mut input_ids: Vec<[u8; 32]> = inputs.iter().map(|a| a.bytes()).collect();
    input_ids.sort_unstable();
    let craft_seed = derive_craft_seed(beacon, &recipe.id, &input_ids);
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&craft_seed);
    let roll = stream
        .draw_bounded(CRAFT_DRAW_INDEX, QUALITY_FACES)
        .expect("the craft draw index is within the committed budget and QUALITY_FACES > 0");
    CraftDraw {
        beacon: *beacon,
        recipe_id: recipe.id.clone(),
        input_ids,
        craft_seed,
        roll,
        quality: quality_of_roll(roll),
    }
}

/// **Re-verify a craft outcome is a real fair draw** — the tooth that refuses a forged
/// craft. Recomputes the craft seed from the claimed beacon + recipe + input ids (a
/// mismatch = a forged context), re-derives the honest roll from the committed seed
/// through the same verified procgen stream, and confirms the claimed roll + quality
/// are exactly the fair draw's. A fabricated legendary — a claim with no real draw, or
/// a rewritten roll/quality — fails here.
pub fn reverify_craft(draw: &CraftDraw) -> Result<(), CraftError> {
    // 1. The craft seed must be the honest binding of the claimed context.
    let expect_seed = derive_craft_seed(&draw.beacon, &draw.recipe_id, &draw.input_ids);
    if expect_seed != draw.craft_seed {
        return Err(CraftError::Forged(
            "the craft seed is not bound to the claimed beacon/recipe/inputs".to_string(),
        ));
    }
    // 2. Re-derive the honest roll from the committed seed (the fair, reproducible draw).
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&draw.craft_seed);
    let true_roll = stream
        .draw_bounded(CRAFT_DRAW_INDEX, QUALITY_FACES)
        .map_err(|e| CraftError::Forged(format!("the fair draw did not re-derive: {e:?}")))?;
    // 3. The claimed roll + quality must be the fair draw's — a rewritten flex is caught.
    if true_roll != draw.roll {
        return Err(CraftError::Forged(format!(
            "the claimed roll {} is not the fair draw {true_roll}",
            draw.roll
        )));
    }
    if quality_of_roll(true_roll) != draw.quality {
        return Err(CraftError::Forged(format!(
            "the claimed quality {:?} is not the roll's",
            draw.quality
        )));
    }
    Ok(())
}

/// The craft's **content commitment** — the mint seed the output asset is minted under,
/// binding the recipe id, the (sorted) input ids, the fair roll, and the quality. The
/// output [`AssetId`] is derived from `blake3(crafter_pk ‖ this)`, so the item's content
/// address itself encodes the inputs + recipe + roll it was forged from (its
/// provenance).
pub fn craft_commitment(draw: &CraftDraw) -> Vec<u8> {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_CRAFT_COMMIT.len() as u64).to_le_bytes());
    h.update(DOMAIN_CRAFT_COMMIT);
    h.update(draw.beacon.as_bytes());
    h.update(&(draw.recipe_id.len() as u64).to_le_bytes());
    h.update(draw.recipe_id.as_bytes());
    h.update(&(draw.input_ids.len() as u64).to_le_bytes());
    for id in &draw.input_ids {
        h.update(id);
    }
    h.update(&draw.roll.to_le_bytes());
    h.update(&[draw.quality.tag()]);
    h.finalize().as_bytes().to_vec()
}

/// A forged output — a real owned [`dreggnet_asset`] note. Its [`AssetId`] is
/// content-addressed to the craft (recipe + inputs + roll) + the crafter's key.
#[derive(Clone, Debug)]
pub struct CraftOutput {
    /// The stable, content-addressed asset id of the crafted item.
    pub asset_id: AssetId,
    /// The output's quality (the fair-draw tier).
    pub quality: CraftQuality,
    /// The crafter's pubkey (at mint, the owner of the output).
    pub owner: [u8; 32],
}

/// The provenance of a crafted item — the recipe + inputs + fair draw it was forged
/// from, and the asset layer's own on-chain provenance re-verification.
#[derive(Clone, Debug)]
pub struct CraftProvenance {
    /// The recipe id the item was forged under.
    pub recipe_id: String,
    /// The input asset ids consumed to forge it (sorted).
    pub input_ids: Vec<[u8; 32]>,
    /// The fair-draw face.
    pub roll: u64,
    /// The output's quality.
    pub quality: CraftQuality,
    /// The asset layer's provenance report for the output (its lineage re-verifies).
    pub asset: ProvenanceReport,
}

/// Why a craft operation could not complete.
#[derive(Clone, Debug)]
pub enum CraftError {
    /// The claimed outcome is not a real fair draw (a fabricated / rewritten craft) — no
    /// input is spent and no asset is minted. Carries the exact mismatch.
    Forged(String),
    /// The recipe's input floor is not met (too few materials for a real sink).
    RecipeUnsatisfied { need: usize, got: usize },
    /// An input is not a real asset the crafter owns + can still spend (unknown, not
    /// owned, or already consumed), or the same input was listed twice — no input is
    /// spent and no asset is minted. Carries the reason.
    InputsUnavailable(String),
    /// This exact craft (recipe + inputs + roll) has already been forged once.
    AlreadyCrafted,
    /// The asset layer refused a spend/mint turn (an unexpected executor refusal).
    Asset(AssetError),
}

impl std::fmt::Display for CraftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CraftError::Forged(why) => write!(f, "forged craft refused: {why}"),
            CraftError::RecipeUnsatisfied { need, got } => {
                write!(f, "recipe needs {need} inputs, got {got}")
            }
            CraftError::InputsUnavailable(why) => write!(f, "craft inputs unavailable: {why}"),
            CraftError::AlreadyCrafted => write!(f, "this craft was already forged"),
            CraftError::Asset(e) => write!(f, "asset layer refused: {e}"),
        }
    }
}

impl std::error::Error for CraftError {}

/// **The craft forge** — the mint-material / craft / provenance surface over a real
/// [`dreggnet_asset::AssetWorld`]. A material is a real owned asset; a craft re-verifies
/// the fair draw, DESTROYS the input materials on-chain (the sink), and mints a real
/// owned output whose id binds the recipe + inputs + roll. A forged craft or an
/// unavailable-input craft is refused before any spend or mint.
pub struct CraftForge {
    world: AssetWorld,
    /// Output AssetId bytes -> the craft it was forged from (its provenance record).
    crafts: HashMap<[u8; 32], CraftDraw>,
    /// The craft commitments already forged (a craft mints exactly once).
    claimed: HashSet<Vec<u8>>,
    /// Input AssetId bytes the forge has destroyed (the consumed materials — a witness
    /// alongside the asset layer's own on-chain "note gone" truth).
    destroyed: HashSet<[u8; 32]>,
}

impl Default for CraftForge {
    fn default() -> Self {
        Self::new()
    }
}

impl CraftForge {
    /// A fresh forge (no crafters, no materials, no outputs).
    pub fn new() -> Self {
        CraftForge {
            world: AssetWorld::new(),
            crafts: HashMap::new(),
            claimed: HashSet::new(),
            destroyed: HashSet::new(),
        }
    }

    /// The deterministic pubkey of a crafter label (creating the identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.world.pubkey_of(label)
    }

    /// **Faucet a material asset** owned by `player` — a real owned [`dreggnet_asset`]
    /// note the forge can later consume as a craft input (in the flagship these come
    /// from loot / gathering, already owned assets; here it is the input side of the
    /// sink). Returns the material's stable [`AssetId`].
    pub fn mint_material(&mut self, player: &str, seed: &[u8]) -> AssetId {
        self.world.mint(player, seed)
    }

    /// Is `asset_id` a live asset the crafter `player` owns (owned by their key AND not
    /// yet consumed on-chain)? The forge only spends inputs that pass this — an
    /// unavailable input is a refusal, not a silent no-op.
    pub fn owns_live(&mut self, player: &str, asset_id: AssetId) -> bool {
        let pk = self.world.pubkey_of(player);
        self.world.current_owner(asset_id) == Some(pk)
            && self.world.verify_provenance(asset_id).verified
    }

    /// Has `asset_id` been consumed by the forge — destroyed on-chain (its note is
    /// spent with no successor, so the asset layer's own [`AssetWorld::verify_provenance`]
    /// reports it gone)?
    pub fn is_destroyed(&self, asset_id: AssetId) -> bool {
        self.destroyed.contains(&asset_id.bytes())
    }

    /// The asset layer's provenance report for any asset id (a passthrough so a caller
    /// can read the ON-CHAIN truth — a destroyed input verifies `false` with a
    /// "note gone" reason; a live output verifies `true`).
    pub fn asset_provenance(&self, asset_id: AssetId) -> ProvenanceReport {
        self.world.verify_provenance(asset_id)
    }

    /// **Forge a craft** — the forged-outcome gate + the input sink + the output mint.
    ///
    /// The outcome is re-verified as a real fair draw ([`reverify_craft`]); a fabricated
    /// craft is refused with NO spend and NO mint. The recipe's input floor is enforced,
    /// and every input is checked to be a real live asset `player` owns (a duplicate or
    /// unavailable input is refused before any state changes). Then each input is
    /// **destroyed on-chain** (the sink), and a [`dreggnet_asset`] output note owned by
    /// `player` is minted under the craft's content commitment — so the output's
    /// [`AssetId`] binds the recipe + inputs + roll it was forged from.
    pub fn craft(
        &mut self,
        player: &str,
        draw: &CraftDraw,
        recipe: &Recipe,
    ) -> Result<CraftOutput, CraftError> {
        // The tooth #1: a forged outcome (no real / a rewritten draw) is refused BEFORE
        // anything is spent or minted.
        reverify_craft(draw)?;

        // The recipe id the draw was rolled under must be this recipe (a craft cannot
        // present one recipe's draw as another's).
        if draw.recipe_id != recipe.id {
            return Err(CraftError::Forged(format!(
                "the draw's recipe `{}` is not the presented recipe `{}`",
                draw.recipe_id, recipe.id
            )));
        }

        // The sink floor: enough materials to actually consume.
        if draw.input_ids.len() < recipe.min_inputs {
            return Err(CraftError::RecipeUnsatisfied {
                need: recipe.min_inputs,
                got: draw.input_ids.len(),
            });
        }

        // A craft mints exactly once (recipe + inputs + roll commitment).
        let commit = craft_commitment(draw);
        if self.claimed.contains(&commit) {
            return Err(CraftError::AlreadyCrafted);
        }

        // Tooth #2: ATOMIC input check — every input must be distinct and a live asset
        // `player` owns. This runs BEFORE any spend, so a bad input consumes nothing.
        let mut seen: HashSet<[u8; 32]> = HashSet::new();
        let inputs: Vec<AssetId> = draw.input_ids.iter().map(|b| AssetId(*b)).collect();
        for id in &inputs {
            if !seen.insert(id.bytes()) {
                return Err(CraftError::InputsUnavailable(
                    "the same input asset was listed twice".to_string(),
                ));
            }
            if !self.owns_live(player, *id) {
                return Err(CraftError::InputsUnavailable(format!(
                    "input {} is not a live asset the crafter owns",
                    hex4(&id.bytes())
                )));
            }
        }

        // The SINK: destroy every input on-chain. Spending the live tail marks the note
        // spent with no successor, so the asset layer's own verify_provenance reports the
        // note gone — a genuine committed owner-signed spend, not host bookkeeping.
        for id in &inputs {
            let tail = self.world.lineage_len(*id);
            debug_assert!(tail >= 1, "a checked-live input has a lineage");
            self.world
                .attempt_respend(*id, tail - 1)
                .map_err(CraftError::Asset)?;
            self.destroyed.insert(id.bytes());
        }

        // The mint: the mint seed IS the craft commitment, so the output id encodes the
        // recipe + inputs + roll it was forged from.
        self.claimed.insert(commit.clone());
        let asset_id = self.world.mint(player, &commit);
        self.crafts.insert(asset_id.bytes(), draw.clone());
        let owner = self
            .world
            .current_owner(asset_id)
            .expect("a freshly-minted output has an owner");
        Ok(CraftOutput {
            asset_id,
            quality: draw.quality,
            owner,
        })
    }

    /// The current owner's pubkey of a crafted output (or any asset).
    pub fn owner_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.world.current_owner(asset_id)
    }

    /// The quality of a crafted output (from its recorded craft).
    pub fn quality_of(&self, asset_id: AssetId) -> Option<CraftQuality> {
        self.crafts.get(&asset_id.bytes()).map(|d| d.quality)
    }

    /// The full provenance of a crafted output — the recipe + inputs + fair draw it was
    /// forged from, plus the asset layer's own lineage re-verification (`None` if this
    /// asset was not forged here).
    pub fn provenance(&self, asset_id: AssetId) -> Option<CraftProvenance> {
        let draw = self.crafts.get(&asset_id.bytes())?;
        Some(CraftProvenance {
            recipe_id: draw.recipe_id.clone(),
            input_ids: draw.input_ids.clone(),
            roll: draw.roll,
            quality: draw.quality,
            asset: self.world.verify_provenance(asset_id),
        })
    }

    /// How many distinct outputs this forge has minted (the anti-ghost witness: a
    /// refused forged / unavailable-input craft mints NOTHING, so it does not move this
    /// count).
    pub fn output_count(&self) -> usize {
        self.crafts.len()
    }
}

/// A short hex fingerprint of an id's first four bytes (for a display line).
fn hex4(bytes: &[u8; 32]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    //! THE FORGE, DRIVEN on the real asset layer: a craft CONSUMES its input materials
    //! (provably destroyed on-chain — the first real sink) and MINTS a new owned output
    //! whose id binds the recipe + inputs + roll; a legendary vs a common is decided by
    //! the fair draw; a forged craft (a fabricated roll / an unavailable input) mints
    //! NOTHING.
    use super::*;

    /// A committed beacon standing in for a Descent day (the verified drand day-seed).
    fn beacon(byte: u8) -> CommittedSeed {
        CommittedSeed::from_bytes([byte; 32])
    }

    /// Search for a beacon whose craft of `recipe` over `inputs` draws the target
    /// quality (the draw is a pure function of the context, so this scans the
    /// deterministic distribution).
    fn find_beacon_for(recipe: &Recipe, inputs: &[AssetId], want: CraftQuality) -> CommittedSeed {
        for b in 0u16..=255 {
            let s = beacon(b as u8);
            if roll_craft(&s, recipe, inputs).quality == want {
                return s;
            }
        }
        panic!("no beacon in 0..256 crafts {want:?} for `{}`", recipe.id);
    }

    /// A craft CONSUMES its inputs (they are provably DESTROYED on-chain — not still a
    /// live asset the crafter owns) and MINTS a new owned output whose provenance binds
    /// the recipe + inputs + roll, and which re-verifies on the asset layer.
    #[test]
    fn a_craft_consumes_its_inputs_and_mints_a_bound_output() {
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:greatblade", 2);
        let smith_pk = forge.pubkey_of("smith");

        // Two owned material inputs.
        let ore = forge.mint_material("smith", b"iron-ore");
        let hilt = forge.mint_material("smith", b"oak-hilt");
        assert!(
            forge.owns_live("smith", ore),
            "the ore is a live owned input"
        );
        assert!(
            forge.owns_live("smith", hilt),
            "the hilt is a live owned input"
        );

        let inputs = vec![ore, hilt];
        let draw = roll_craft(&beacon(7), &recipe, &inputs);
        let out = forge
            .craft("smith", &draw, &recipe)
            .expect("a real craft mints");

        // The crafter OWNS the output.
        assert_eq!(
            out.owner, smith_pk,
            "the output is owned by the crafter's key"
        );
        assert_eq!(forge.owner_of(out.asset_id), Some(smith_pk));

        // THE SINK: both inputs are provably destroyed on-chain — no longer a live
        // owned asset, and the asset layer's own re-verify reports each note gone.
        for id in [ore, hilt] {
            assert!(forge.is_destroyed(id), "the input was consumed");
            assert!(
                !forge.owns_live("smith", id),
                "a destroyed input is not still a live owned asset"
            );
            let ap = forge.asset_provenance(id);
            assert!(
                !ap.verified,
                "the asset layer reports the consumed input gone: {:?}",
                ap.reasons
            );
            assert!(
                ap.reasons.iter().any(|r| r.contains("gone")),
                "the on-chain refusal is the spent-note tooth: {:?}",
                ap.reasons
            );
        }

        // The output binds its provenance (recipe + inputs + fair roll), and the output
        // lineage re-verifies live.
        let prov = forge.provenance(out.asset_id).expect("provenance recorded");
        assert_eq!(prov.recipe_id, "forge:greatblade");
        assert_eq!(prov.roll, draw.roll, "provenance binds the fair draw");
        let mut want_inputs = vec![ore.bytes(), hilt.bytes()];
        want_inputs.sort_unstable();
        assert_eq!(
            prov.input_ids, want_inputs,
            "provenance binds the input ids"
        );
        assert!(
            prov.asset.verified,
            "the crafted output's asset lineage re-verifies: {:?}",
            prov.asset.reasons
        );
        assert_eq!(prov.asset.length, 1, "a fresh output is a length-1 lineage");
    }

    /// A LEGENDARY vs a COMMON craft is decided by the FAIR DRAW — the quality is the
    /// draw's distribution off the committed seed, re-derivable by anyone, not a claim.
    #[test]
    fn a_legendary_vs_a_common_craft_is_the_fair_draw() {
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:relic", 2);

        // The legendary craft: fresh inputs + a beacon the draw makes legendary.
        let la = forge.mint_material("smith", b"star-iron");
        let lb = forge.mint_material("smith", b"void-glass");
        let leg_inputs = vec![la, lb];
        let leg_beacon = find_beacon_for(&recipe, &leg_inputs, CraftQuality::Legendary);
        let leg_draw = roll_craft(&leg_beacon, &recipe, &leg_inputs);
        assert_eq!(leg_draw.quality, CraftQuality::Legendary);
        assert!(
            leg_draw.roll >= 97,
            "a genuine legendary draw: {}",
            leg_draw.roll
        );
        // The outcome re-derives from the committed context — un-fakeable.
        reverify_craft(&leg_draw).expect("the legendary is a real fair draw");

        // The common craft: different fresh inputs + a beacon the draw makes common.
        let ca = forge.mint_material("smith", b"scrap-tin");
        let cb = forge.mint_material("smith", b"rot-wood");
        let com_inputs = vec![ca, cb];
        let com_beacon = find_beacon_for(&recipe, &com_inputs, CraftQuality::Common);
        let com_draw = roll_craft(&com_beacon, &recipe, &com_inputs);
        assert_eq!(com_draw.quality, CraftQuality::Common);
        assert!(
            com_draw.roll < 60,
            "a genuine common draw: {}",
            com_draw.roll
        );
        reverify_craft(&com_draw).expect("the common is a real fair draw");

        // Both forge real owned outputs; their recorded quality is the re-derivable tier.
        let leg = forge
            .craft("smith", &leg_draw, &recipe)
            .expect("the legendary forges");
        let com = forge
            .craft("smith", &com_draw, &recipe)
            .expect("the common forges");
        assert_eq!(
            forge.quality_of(leg.asset_id),
            Some(CraftQuality::Legendary)
        );
        assert_eq!(forge.quality_of(com.asset_id), Some(CraftQuality::Common));
        assert_ne!(
            leg.asset_id.bytes(),
            com.asset_id.bytes(),
            "different crafts are different items"
        );
    }

    /// A FORGED craft — an outcome with a rewritten roll (a fabricated legendary the
    /// seed never produced) — is REFUSED with NO input spent and NO mint. Non-vacuous:
    /// the same inputs then forge honestly.
    #[test]
    fn a_forged_craft_mints_nothing() {
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:blade", 2);
        let a = forge.mint_material("cheater", b"m-a");
        let b = forge.mint_material("cheater", b"m-b");
        let inputs = vec![a, b];
        let honest = roll_craft(&beacon(3), &recipe, &inputs);

        // FORGE a legendary: rewrite the roll + quality to a flex the seed never made.
        let forged_roll = if honest.roll == 99 { 98 } else { 99 };
        let mut forged = honest.clone();
        forged.roll = forged_roll;
        forged.quality = CraftQuality::Legendary;

        let out = forge.craft("cheater", &forged, &recipe);
        assert!(
            matches!(out, Err(CraftError::Forged(_))),
            "a fabricated legendary is refused, got {out:?}"
        );
        // Anti-ghost: no output minted, AND the inputs were NOT spent (still live).
        assert_eq!(forge.output_count(), 0, "no output for the forged craft");
        assert!(
            !forge.is_destroyed(a) && !forge.is_destroyed(b),
            "no input was consumed"
        );
        assert!(
            forge.owns_live("cheater", a) && forge.owns_live("cheater", b),
            "the inputs survive a refused forged craft"
        );

        // The HONEST craft over the same inputs still forges (the tooth is not vacuous).
        let item = forge
            .craft("cheater", &honest, &recipe)
            .expect("the honest craft forges");
        assert_eq!(forge.quality_of(item.asset_id), Some(honest.quality));
        assert_eq!(
            forge.output_count(),
            1,
            "exactly the honest craft is an output"
        );
        assert!(
            forge.is_destroyed(a) && forge.is_destroyed(b),
            "now the inputs are consumed"
        );
    }

    /// A craft claiming UN-SPENDABLE inputs is REFUSED with no mint: an input the
    /// crafter does not own, and (the anti-dupe edge) an already-consumed input.
    #[test]
    fn a_craft_over_unavailable_inputs_is_refused() {
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:trinket", 2);

        // An input owned by SOMEONE ELSE — the crafter cannot spend it.
        let mine = forge.mint_material("smith", b"my-mat");
        let theirs = forge.mint_material("rival", b"their-mat");
        let bad = vec![mine, theirs];
        let bad_draw = roll_craft(&beacon(1), &recipe, &bad);
        let out = forge.craft("smith", &bad_draw, &recipe);
        assert!(
            matches!(out, Err(CraftError::InputsUnavailable(_))),
            "a craft over an un-owned input is refused, got {out:?}"
        );
        assert_eq!(forge.output_count(), 0, "no output was minted");
        assert!(
            !forge.is_destroyed(mine) && !forge.is_destroyed(theirs),
            "no input was consumed by the refused craft"
        );
        assert!(
            forge.owns_live("smith", mine),
            "the crafter's own input survives"
        );

        // NO DUPE-THEN-CRAFT: consume a pair honestly, then try to re-craft the SAME
        // (already-destroyed) inputs — refused, because a spent note cannot be respent.
        let x = forge.mint_material("smith", b"x");
        let y = forge.mint_material("smith", b"y");
        let good = vec![x, y];
        let good_draw = roll_craft(&beacon(2), &recipe, &good);
        forge
            .craft("smith", &good_draw, &recipe)
            .expect("the first craft forges");
        assert!(
            forge.is_destroyed(x) && forge.is_destroyed(y),
            "the inputs are consumed"
        );

        let redraw = roll_craft(&beacon(9), &recipe, &good);
        let reuse = forge.craft("smith", &redraw, &recipe);
        assert!(
            matches!(reuse, Err(CraftError::InputsUnavailable(_))),
            "re-crafting already-consumed inputs is refused, got {reuse:?}"
        );
        assert_eq!(forge.output_count(), 1, "the dupe craft minted nothing");
    }

    /// A craft mints exactly once: presenting the same craft (recipe + inputs + roll)
    /// twice is refused. (The input-liveness tooth already blocks re-spend; this asserts
    /// the explicit once-only commitment as well.)
    #[test]
    fn a_craft_forges_exactly_once() {
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:once", 1);
        let m = forge.mint_material("p", b"only-mat");
        let draw = roll_craft(&beacon(5), &recipe, &[m]);
        let first = forge
            .craft("p", &draw, &recipe)
            .expect("first craft forges");
        let second = forge.craft("p", &draw, &recipe);
        assert!(
            matches!(
                second,
                Err(CraftError::AlreadyCrafted) | Err(CraftError::InputsUnavailable(_))
            ),
            "re-presenting the same craft is refused, got {second:?}"
        );
        assert!(forge.owner_of(first.asset_id).is_some());
        assert_eq!(
            forge.output_count(),
            1,
            "the double craft minted no second output"
        );
    }

    /// The recipe input floor is enforced — too few materials for a real sink is refused.
    #[test]
    fn a_recipe_below_its_input_floor_is_refused() {
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:needs-three", 3);
        let a = forge.mint_material("p", b"a");
        let b = forge.mint_material("p", b"b");
        let draw = roll_craft(&beacon(4), &recipe, &[a, b]);
        let out = forge.craft("p", &draw, &recipe);
        assert!(
            matches!(out, Err(CraftError::RecipeUnsatisfied { need: 3, got: 2 })),
            "a craft below the input floor is refused, got {out:?}"
        );
        assert_eq!(forge.output_count(), 0);
        assert!(
            !forge.is_destroyed(a) && !forge.is_destroyed(b),
            "no input consumed"
        );
    }
}
