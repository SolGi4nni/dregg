//! **The craft forge** — the material / craft / provenance surface over a real
//! [`dreggnet_asset::AssetWorld`], crafting against a committed [`RecipeBook`]. A material
//! is a real owned asset carrying a typed [`MaterialKind`] (faucet-minted, or SOURCED from a
//! verified [`dungeon_on_dregg::loot`] drop); a craft re-verifies the fair draw against the
//! catalog's committed weights, checks the typed inputs, DESTROYS them on-chain (the sink),
//! and — on a minting outcome — mints a real output whose id binds the recipe + inputs +
//! band + quality + the concrete [`CraftedArtifact`]. A forged craft, an unknown recipe, or
//! a wrong-input craft is refused before any spend or mint.

use std::collections::{HashMap, HashSet};

use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport};
use dungeon_on_dregg::loot::{LootDraw, Rarity as LootRarity, expected_asset_id, reverify_drop};
use procgen_dregg::CommittedSeed;

use crate::draw::{CraftDraw, craft_commitment, resolve_artifact, reverify_craft};
use crate::quality::{CraftOutcome, CraftQuality};
use crate::recipe::{CraftedArtifact, MaterialKind, Recipe, RecipeBook};

/// The domain tag for a loot-sourced material's mint seed (so a material minted FROM a
/// verified drop content-addresses that drop's provenance).
const DOMAIN_LOOT_MATERIAL: &[u8] = b"dreggnet-craft/loot-material/v1";

/// Why a craft operation could not complete.
#[derive(Clone, Debug)]
pub enum CraftError {
    /// The claimed outcome is not a real fair draw (a fabricated / rewritten craft) — no
    /// input is spent and no asset is minted. Carries the exact mismatch.
    Forged(String),
    /// The draw's recipe id is not in the forge's committed catalog — a craft can only be
    /// forged against a registered recipe (whose odds are committed).
    UnknownRecipe(String),
    /// The presented inputs are not the recipe's required typed multiset (wrong count, or
    /// wrong kinds) — the typed sink was not satisfied. Carries the mismatch.
    InputKindMismatch(String),
    /// An input is not a real asset the crafter owns + can still spend (unknown, not owned,
    /// or already consumed), or the same input was listed twice — no input is spent and no
    /// asset is minted. Carries the reason.
    InputsUnavailable(String),
    /// A loot-sourced material was presented with a forged / rewritten loot draw — it cannot
    /// become a material. Carries the loot layer's own refusal.
    ForgedLoot(String),
    /// This exact craft (recipe + inputs + band + quality + artifact) has already been
    /// forged once.
    AlreadyCrafted,
    /// The asset layer refused a spend/mint turn (an unexpected executor refusal).
    Asset(AssetError),
}

impl std::fmt::Display for CraftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CraftError::Forged(why) => write!(f, "forged craft refused: {why}"),
            CraftError::UnknownRecipe(id) => write!(f, "unknown recipe `{id}`"),
            CraftError::InputKindMismatch(why) => write!(f, "craft inputs mismatch: {why}"),
            CraftError::InputsUnavailable(why) => write!(f, "craft inputs unavailable: {why}"),
            CraftError::ForgedLoot(why) => write!(f, "forged loot material refused: {why}"),
            CraftError::AlreadyCrafted => write!(f, "this craft was already forged"),
            CraftError::Asset(e) => write!(f, "asset layer refused: {e}"),
        }
    }
}

impl std::error::Error for CraftError {}

/// A forged output — a real owned [`dreggnet_asset`] note. Its [`AssetId`] is
/// content-addressed to the craft (recipe + inputs + band + quality + artifact) + the
/// crafter's key.
#[derive(Clone, Debug)]
pub struct CraftOutput {
    /// The stable, content-addressed asset id of the crafted item.
    pub asset_id: AssetId,
    /// The outcome band (a success or a flawed partial — never a botch, which mints nothing).
    pub outcome: CraftOutcome,
    /// The output's GRANTED quality (the fair tier, downgraded one step on a partial).
    pub quality: CraftQuality,
    /// The concrete artifact forged — a real gear stat block or a companion egg.
    pub artifact: CraftedArtifact,
    /// The crafter's pubkey (at mint, the owner of the output).
    pub owner: [u8; 32],
}

/// The receipt of a **botched** craft — the outcome band was a botch: the materials were
/// still consumed (the sink fired) but NO output was minted. Distinct from a forged refusal,
/// which spends nothing.
#[derive(Clone, Debug)]
pub struct BotchReceipt {
    /// The recipe the botched craft was under.
    pub recipe_id: String,
    /// The input asset ids consumed by the botch (destroyed on-chain, no output).
    pub consumed: Vec<[u8; 32]>,
    /// The tier that WOULD have been forged had the outcome not botched (the fair draw).
    pub tier: CraftQuality,
}

/// How a craft resolved once it passed every gate (the outcome band decides): either a real
/// minted [`CraftOutput`], or a [`BotchReceipt`] (materials consumed, nothing minted).
#[derive(Clone, Debug)]
pub enum CraftResolution {
    /// The forge produced a real owned output (a success or a flawed partial).
    Crafted(CraftOutput),
    /// The forge botched: the materials were consumed, no output minted.
    Botched(BotchReceipt),
}

impl CraftResolution {
    /// The minted output, if this resolution crafted one (`None` on a botch).
    pub fn output(&self) -> Option<&CraftOutput> {
        match self {
            CraftResolution::Crafted(o) => Some(o),
            CraftResolution::Botched(_) => None,
        }
    }

    /// Did this resolution mint an output?
    pub fn is_crafted(&self) -> bool {
        matches!(self, CraftResolution::Crafted(_))
    }
}

/// A recorded craft — the draw + the concrete artifact + granted quality it minted.
#[derive(Clone, Debug)]
struct CraftRecord {
    draw: CraftDraw,
    artifact: CraftedArtifact,
    quality: CraftQuality,
    /// The dungeon runs the consumed inputs came from, snapshotted at craft time — the
    /// inputs themselves are destroyed by the sink, so this is the only surviving link.
    material_origins: Vec<MaterialOrigin>,
}

/// Where one consumed craft input came from, when it was a real, verified dungeon drop
/// rather than a faucet material — the hop that carries a crafted item's provenance back
/// PAST its own mint to the RUN the materials were banked on.
#[derive(Clone, Debug)]
pub struct MaterialOrigin {
    /// The consumed input's asset id.
    pub input_id: [u8; 32],
    /// The committed day-seed of the run the material dropped from (its provenance root).
    pub run_seed: CommittedSeed,
    /// The chest / boss / banked-custody slot it dropped from.
    pub chest: String,
    /// The fair draw's rarity.
    pub rarity: LootRarity,
    /// The typed material kind the drop fixed (`"{class}:{rarity}"`).
    pub kind: String,
}

/// The provenance of a crafted item — the recipe + inputs + fair draw + artifact it was
/// forged from, and the asset layer's own on-chain provenance re-verification.
#[derive(Clone, Debug)]
pub struct CraftProvenance {
    /// The recipe id the item was forged under.
    pub recipe_id: String,
    /// The input asset ids consumed to forge it (sorted).
    pub input_ids: Vec<[u8; 32]>,
    /// The outcome band.
    pub outcome: CraftOutcome,
    /// The output's granted quality.
    pub quality: CraftQuality,
    /// The concrete artifact forged.
    pub artifact: CraftedArtifact,
    /// The asset layer's provenance report for the output (its lineage re-verifies).
    pub asset: ProvenanceReport,
    /// For each consumed input that was a real dungeon drop, the run + chest + rarity it came
    /// from — recorded at craft time, since the inputs themselves are destroyed by the sink.
    /// Empty for a craft over faucet materials. This is what makes "forged from two relics
    /// banked on day X" a checkable statement about a burned object.
    pub material_origins: Vec<MaterialOrigin>,
}

/// **The craft forge** — see the module doc. Crafts against a committed [`RecipeBook`]; a
/// material is a real owned asset carrying a typed kind.
pub struct CraftForge {
    world: AssetWorld,
    book: RecipeBook,
    /// Material AssetId bytes -> the typed kind it satisfies in a recipe.
    material_kinds: HashMap<[u8; 32], MaterialKind>,
    /// Material AssetId bytes -> the verified dungeon drop it came from, for materials the
    /// forge ADOPTED ([`CraftForge::adopt_loot_material`]) or sourced
    /// ([`CraftForge::mint_loot_material`]). The link that lets a crafted item's provenance
    /// name the RUN its materials were banked on, not merely their ids.
    loot_sources: HashMap<[u8; 32], LootDraw>,
    /// Output AssetId bytes -> the craft it was forged from (its provenance record).
    crafts: HashMap<[u8; 32], CraftRecord>,
    /// The craft commitments already forged (a minting craft mints exactly once).
    claimed: HashSet<Vec<u8>>,
    /// Input AssetId bytes the forge has destroyed (the consumed materials — a witness
    /// alongside the asset layer's own on-chain "note gone" truth).
    destroyed: HashSet<[u8; 32]>,
    /// How many crafts botched (materials consumed, no output).
    botched: usize,
}

impl Default for CraftForge {
    fn default() -> Self {
        Self::new()
    }
}

impl CraftForge {
    /// A fresh forge over the **starter** recipe catalog.
    pub fn new() -> Self {
        Self::with_book(RecipeBook::starter())
    }

    /// A fresh forge over a given recipe catalog (an empty [`RecipeBook`] for a forge whose
    /// recipes are all registered by the caller).
    pub fn with_book(book: RecipeBook) -> Self {
        Self::with_book_and_assets(book, AssetWorld::new())
    }

    /// **A forge that ADOPTS an existing note ledger** — the shared-world seam on the INPUT
    /// side, mirroring [`dreggnet_trade::TradeWorld::with_assets`] on the output side.
    ///
    /// Hand it [`dungeon_on_dregg::loot::LootVault::into_assets`] and the player's real banked
    /// relics are already live notes in the forge's own world: the forge can then
    /// [`adopt_loot_material`](Self::adopt_loot_material) them as typed inputs and BURN the
    /// exact notes the dungeon minted. Without this, the only way to feed dungeon loot to a
    /// forge was [`mint_loot_material`](Self::mint_loot_material), which mints a *second*
    /// note in a *second* ledger — a look-alike, and a duplication of the item.
    pub fn with_assets(assets: AssetWorld) -> Self {
        Self::with_book_and_assets(RecipeBook::starter(), assets)
    }

    /// A forge over a given catalog AND an existing note ledger — the union of
    /// [`Self::with_book`] and [`Self::with_assets`].
    pub fn with_book_and_assets(book: RecipeBook, assets: AssetWorld) -> Self {
        CraftForge {
            world: assets,
            book,
            material_kinds: HashMap::new(),
            loot_sources: HashMap::new(),
            crafts: HashMap::new(),
            claimed: HashSet::new(),
            destroyed: HashSet::new(),
            botched: 0,
        }
    }

    /// Register (or replace) a recipe in the forge's catalog (returns `false` for a
    /// degenerate recipe, which never enters the book).
    pub fn register_recipe(&mut self, recipe: Recipe) -> bool {
        self.book.register(recipe)
    }

    /// The recipe with `id`, if the catalog holds it.
    pub fn recipe(&self, id: &str) -> Option<&Recipe> {
        self.book.get(id)
    }

    /// The forge's recipe catalog.
    pub fn book(&self) -> &RecipeBook {
        &self.book
    }

    /// The deterministic pubkey of a crafter label (creating the identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.world.pubkey_of(label)
    }

    /// **Access the underlying asset world** — the SHARED-world seam mirroring
    /// [`dreggnet_trade::TradeWorld::assets`]. The forge mints its output as a real note in
    /// THIS world; exposing it lets the EXACT crafted note-cell continue its lineage into a
    /// trade with no re-mint (object-identity at the note-cell, not merely at the [`AssetId`]).
    pub fn assets_mut(&mut self) -> &mut AssetWorld {
        &mut self.world
    }

    /// **Consume the forge, yielding its asset world** — the live ledger carrying the crafted
    /// output note (and every destroyed-input tombstone). Hand it to
    /// [`dreggnet_trade::TradeWorld::with_assets`] so the crafted note deposits into a trade in
    /// ONE ledger: its provenance lineage CONTINUES rather than restarting in a second world.
    pub fn into_assets(self) -> AssetWorld {
        self.world
    }

    /// **Faucet a typed material asset** owned by `player` — a real owned [`dreggnet_asset`]
    /// note carrying `kind`, the forge can later consume as a craft input. Returns the
    /// material's stable [`AssetId`].
    pub fn mint_material(&mut self, player: &str, kind: &str, seed: &[u8]) -> AssetId {
        let id = self.world.mint(player, seed);
        self.material_kinds
            .insert(id.bytes(), MaterialKind::new(kind));
        id
    }

    /// **ADOPT a player's EXISTING loot note as a typed craft material** — the identity-
    /// preserving loot → craft wire, and the reason a banked relic and the material it becomes
    /// are ONE object rather than two.
    ///
    /// Nothing is minted. The forge's world must already carry the note (open the forge over
    /// the vault's ledger with [`Self::with_assets`] /
    /// [`dungeon_on_dregg::loot::LootVault::into_assets`]); this call only *types* it. Three
    /// gates, all before any bookkeeping:
    ///
    /// 1. **the drop is a real fair draw** — [`reverify_drop`], the loot layer's own tooth: a
    ///    fabricated or rewritten drop is [`CraftError::ForgedLoot`];
    /// 2. **the presented note IS that drop's note** — the forge recomputes
    ///    [`expected_asset_id`]`(drop, player_pk)`, the exact address
    ///    [`LootVault::claim`](dungeon_on_dregg::loot::LootVault::claim) mints at, and refuses
    ///    any other id. So a player cannot point a genuine legendary draw at a *different*
    ///    note they happen to own; the drop and the note are bound to each other;
    /// 3. **the player really holds it, live** — [`Self::owns_live`] over the real ledger.
    ///
    /// The material's typed kind is then **derived from the drop**
    /// ([`LootDraw::material_kind`]), never supplied: the fair draw decides whether this is a
    /// `relic:legendary` or a `salvage:common`, so a recipe demanding legendary relics cannot
    /// be satisfied by relabelling a common one.
    pub fn adopt_loot_material(
        &mut self,
        player: &str,
        asset_id: AssetId,
        drop: &LootDraw,
    ) -> Result<MaterialKind, CraftError> {
        // (1) a forged / rewritten drop is not a material.
        reverify_drop(drop).map_err(|e| CraftError::ForgedLoot(e.to_string()))?;
        // (2) the note must be the one THIS drop mints for THIS player.
        let player_pk = self.world.pubkey_of(player);
        let expected = expected_asset_id(drop, &player_pk);
        if expected.bytes() != asset_id.bytes() {
            return Err(CraftError::ForgedLoot(format!(
                "note {} is not the note this drop mints for `{player}` (expected {})",
                hex4(&asset_id.bytes()),
                hex4(&expected.bytes()),
            )));
        }
        // (3) and it must be a live asset the player actually holds in THIS ledger.
        if !self.owns_live(player, asset_id) {
            return Err(CraftError::InputsUnavailable(format!(
                "looted note {} is not a live asset `{player}` holds in this forge's ledger",
                hex4(&asset_id.bytes())
            )));
        }
        let kind = MaterialKind::new(&drop.material_kind());
        self.material_kinds.insert(asset_id.bytes(), kind.clone());
        self.loot_sources.insert(asset_id.bytes(), drop.clone());
        Ok(kind)
    }

    /// **FAUCET a material from a verified loot drop, in this forge's OWN ledger.** The
    /// [`LootDraw`] is re-verified through the loot layer's own [`reverify_drop`] tooth — a
    /// forged / rewritten drop is refused with [`CraftError::ForgedLoot`] and no material is
    /// minted — and a genuine drop mints a material of `kind` for `player` whose content
    /// address binds the drop's provenance (loot seed + roll + rarity + chest).
    ///
    /// ⚠ **This MINTS a new note; it does not adopt the player's looted one.** The address it
    /// derives is deliberately its own (`DOMAIN_LOOT_MATERIAL`), NOT the loot vault's
    /// [`dungeon_on_dregg::loot::drop_commitment`] address, so calling this on a drop the
    /// player already banked leaves *two* notes in existence — the vault's and this one. It is
    /// the right call when a forge stands alone with no vault behind it (a demo bench, a
    /// standalone offering); when the player's real loot note exists, use
    /// [`adopt_loot_material`](Self::adopt_loot_material), which types the EXACT note and
    /// duplicates nothing.
    pub fn mint_loot_material(
        &mut self,
        player: &str,
        kind: &str,
        drop: &LootDraw,
    ) -> Result<AssetId, CraftError> {
        reverify_drop(drop).map_err(|e| CraftError::ForgedLoot(e.to_string()))?;
        let mut h = blake3::Hasher::new();
        h.update(&(DOMAIN_LOOT_MATERIAL.len() as u64).to_le_bytes());
        h.update(DOMAIN_LOOT_MATERIAL);
        h.update(drop.loot_seed.as_bytes());
        h.update(&drop.roll.to_le_bytes());
        h.update(&(drop.chest.len() as u64).to_le_bytes());
        h.update(drop.chest.as_bytes());
        h.update(&(kind.len() as u64).to_le_bytes());
        h.update(kind.as_bytes());
        let seed = h.finalize();
        let id = self.world.mint(player, seed.as_bytes());
        self.material_kinds
            .insert(id.bytes(), MaterialKind::new(kind));
        self.loot_sources.insert(id.bytes(), drop.clone());
        Ok(id)
    }

    /// The typed kind of a material asset (if the forge minted it as one).
    pub fn material_kind(&self, asset_id: AssetId) -> Option<&MaterialKind> {
        self.material_kinds.get(&asset_id.bytes())
    }

    /// The verified dungeon drop a material came from, for materials the forge adopted or
    /// sourced from loot — the link that lets a crafted item's provenance name the RUN
    /// (day-seed + custody slot) its materials were banked on.
    pub fn loot_source(&self, asset_id: AssetId) -> Option<&LootDraw> {
        self.loot_sources.get(&asset_id.bytes())
    }

    /// **What `player` can actually forge right now** — every catalog recipe whose required
    /// typed multiset is covered by the live materials they hold, in sorted id order. The
    /// bench read a UI renders and the answer to "what are my relics good for?"; previously a
    /// caller had to enumerate the catalog and re-derive the multiset itself.
    pub fn craftable_by(&self, player: &str) -> Vec<String> {
        let held: Vec<AssetId> = self.world.assets_held_by(player);
        let mut have: HashMap<MaterialKind, usize> = HashMap::new();
        for id in &held {
            if let Some(kind) = self.material_kinds.get(&id.bytes()) {
                *have.entry(kind.clone()).or_insert(0) += 1;
            }
        }
        let mut ids: Vec<String> = self
            .book
            .ids()
            .into_iter()
            .filter(|id| {
                self.book.get(id).is_some_and(|r| {
                    r.required_kinds()
                        .iter()
                        .all(|(kind, n)| have.get(kind).copied().unwrap_or(0) >= *n)
                })
            })
            .collect();
        ids.sort();
        ids
    }

    /// Is `asset_id` a live asset the crafter `player` owns (owned by their key AND not yet
    /// consumed on-chain)?
    pub fn owns_live(&mut self, player: &str, asset_id: AssetId) -> bool {
        let pk = self.world.pubkey_of(player);
        self.world.current_owner(asset_id) == Some(pk)
            && self.world.verify_provenance(asset_id).verified
    }

    /// Has `asset_id` been consumed by the forge — destroyed on-chain?
    pub fn is_destroyed(&self, asset_id: AssetId) -> bool {
        self.destroyed.contains(&asset_id.bytes())
    }

    /// The asset layer's provenance report for any asset id (the ON-CHAIN truth — a destroyed
    /// input verifies `false` with a "note gone" reason; a live output verifies `true`).
    pub fn asset_provenance(&self, asset_id: AssetId) -> ProvenanceReport {
        self.world.verify_provenance(asset_id)
    }

    /// **Forge a craft** — the forged-outcome gate + the typed input sink + (on a minting
    /// band) the output mint.
    ///
    /// The recipe is looked up in the forge's committed catalog by `draw.recipe_id` (an
    /// unknown recipe is refused — a craft cannot bring its own odds). The outcome is
    /// re-verified against the catalog's committed weight tables ([`reverify_craft`]); a
    /// fabricated craft is refused with NO spend and NO mint. The presented inputs must be the
    /// recipe's exact typed multiset, each a distinct live asset `player` owns (checked BEFORE
    /// any state change). Then every input is **burned on-chain** by a real `player`-signed
    /// spend turn (the owner-signed sink — the executor admits the burn only under the crafter's
    /// own owner signature, so the authorization to consume is an ISA gate, not host bookkeeping).
    /// On a
    /// [`CraftOutcome::Success`] / [`CraftOutcome::Partial`] a real output note is minted under
    /// the craft's content commitment; on a [`CraftOutcome::Botch`] the materials are consumed
    /// and nothing is minted ([`CraftResolution::Botched`]).
    pub fn craft(&mut self, player: &str, draw: &CraftDraw) -> Result<CraftResolution, CraftError> {
        // The recipe (and its committed odds) comes from the catalog, not the caller.
        let recipe = self
            .book
            .get(&draw.recipe_id)
            .ok_or_else(|| CraftError::UnknownRecipe(draw.recipe_id.clone()))?
            .clone();

        // Tooth #1: a forged outcome (no real / a rewritten draw) is refused BEFORE anything
        // is spent or minted — re-verified against the catalog's committed weights.
        reverify_craft(draw, &recipe)?;

        // The typed sink: the presented inputs must be the recipe's exact multiset of kinds,
        // each distinct, and a live asset `player` owns. This runs BEFORE any spend.
        let inputs: Vec<AssetId> = draw.input_ids.iter().map(|b| AssetId(*b)).collect();
        self.check_inputs(player, &recipe, &inputs)?;

        // The granted quality + the concrete artifact (only meaningful on a minting band).
        let granted = draw.granted_quality();

        // On a minting band, the once-only commitment check runs BEFORE any spend.
        let mint_plan = match granted {
            Some(quality) => {
                let artifact = resolve_artifact(&recipe, quality);
                let commit = craft_commitment(draw, &artifact);
                if self.claimed.contains(&commit) {
                    return Err(CraftError::AlreadyCrafted);
                }
                Some((quality, artifact, commit))
            }
            None => None,
        };

        // The SINK: burn every input on-chain (fires on BOTH a mint and a botch). The burn is
        // an OWNER-SIGNED spend: `AssetWorld::burn` drives a real `player`-signed executor turn
        // on the input note, admitted only because `player`'s signature verifies against the
        // note cell's own owner key (the ISA owner-signature gate). So crafter-authorization to
        // consume the materials is enforced at the executor — not merely by the host-side
        // `owns_live` pre-flight in `check_inputs`.
        //
        // `burn` and not `revoke`: revoke additionally demands the burner be the original
        // MINTER, which silently made every material a player *acquired* uncraftable — a
        // relic looted by a friend and traded over, or an adopted note whose minter is the
        // loot vault's claimer, could pass every input check and then fail at the sink. The
        // asset layer's owner-gated burn is the primitive an economy needs here.
        // Snapshot where the inputs CAME FROM before the sink destroys them — a crafted item's
        // provenance must be able to name the runs its materials were banked on, and after the
        // burn the inputs are gone.
        let material_origins = self.origins_of(&inputs);

        for id in &inputs {
            self.world.burn(*id, player).map_err(CraftError::Asset)?;
            self.destroyed.insert(id.bytes());
        }

        match mint_plan {
            Some((quality, artifact, commit)) => {
                self.claimed.insert(commit.clone());
                // Fail-closed: the craft commitment is once-only (checked above), so a
                // duplicate content address here would mean two distinct crafts collided —
                // minting over the existing lineage would silently break it.
                let asset_id = self
                    .world
                    .try_mint(player, &commit)
                    .map_err(CraftError::Asset)?;
                self.crafts.insert(
                    asset_id.bytes(),
                    CraftRecord {
                        draw: draw.clone(),
                        artifact: artifact.clone(),
                        quality,
                        material_origins,
                    },
                );
                let owner = self
                    .world
                    .current_owner(asset_id)
                    .expect("a freshly-minted output has an owner");
                Ok(CraftResolution::Crafted(CraftOutput {
                    asset_id,
                    outcome: draw.outcome,
                    quality,
                    artifact,
                    owner,
                }))
            }
            None => {
                self.botched += 1;
                Ok(CraftResolution::Botched(BotchReceipt {
                    recipe_id: draw.recipe_id.clone(),
                    consumed: draw.input_ids.clone(),
                    tier: draw.tier,
                }))
            }
        }
    }

    /// The dungeon origins of whichever of `inputs` were real loot drops, in input order.
    fn origins_of(&self, inputs: &[AssetId]) -> Vec<MaterialOrigin> {
        inputs
            .iter()
            .filter_map(|id| {
                let drop = self.loot_sources.get(&id.bytes())?;
                Some(MaterialOrigin {
                    input_id: id.bytes(),
                    run_seed: drop.run_seed,
                    chest: drop.chest.clone(),
                    rarity: drop.rarity,
                    kind: drop.material_kind(),
                })
            })
            .collect()
    }

    /// The atomic typed-input check: exact count, distinct ids, each a live asset `player`
    /// owns, and the kinds forming the recipe's exact required multiset. No state changes.
    fn check_inputs(
        &mut self,
        player: &str,
        recipe: &Recipe,
        inputs: &[AssetId],
    ) -> Result<(), CraftError> {
        if inputs.len() != recipe.input_count() {
            return Err(CraftError::InputKindMismatch(format!(
                "recipe `{}` consumes {} inputs, got {}",
                recipe.id,
                recipe.input_count(),
                inputs.len()
            )));
        }
        let mut seen: HashSet<[u8; 32]> = HashSet::new();
        let mut have: HashMap<MaterialKind, usize> = HashMap::new();
        for id in inputs {
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
            let kind = self.material_kinds.get(&id.bytes()).ok_or_else(|| {
                CraftError::InputKindMismatch(format!(
                    "input {} is not a typed material",
                    hex4(&id.bytes())
                ))
            })?;
            *have.entry(kind.clone()).or_insert(0) += 1;
        }
        let need = recipe.required_kinds();
        if have != need {
            return Err(CraftError::InputKindMismatch(format!(
                "recipe `{}` requires {:?}, got {:?}",
                recipe.id,
                kind_summary(&need),
                kind_summary(&have),
            )));
        }
        Ok(())
    }

    /// The current owner's pubkey of a crafted output (or any asset).
    pub fn owner_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.world.current_owner(asset_id)
    }

    /// The granted quality of a crafted output (from its recorded craft).
    pub fn quality_of(&self, asset_id: AssetId) -> Option<CraftQuality> {
        self.crafts.get(&asset_id.bytes()).map(|r| r.quality)
    }

    /// The concrete artifact a crafted output carries (a real gear stat block or a companion
    /// egg), from its recorded craft.
    pub fn artifact_of(&self, asset_id: AssetId) -> Option<&CraftedArtifact> {
        self.crafts.get(&asset_id.bytes()).map(|r| &r.artifact)
    }

    /// The full provenance of a crafted output — the recipe + inputs + fair draw + artifact it
    /// was forged from, plus the asset layer's own lineage re-verification (`None` if this
    /// asset was not forged here).
    pub fn provenance(&self, asset_id: AssetId) -> Option<CraftProvenance> {
        let rec = self.crafts.get(&asset_id.bytes())?;
        Some(CraftProvenance {
            recipe_id: rec.draw.recipe_id.clone(),
            input_ids: rec.draw.input_ids.clone(),
            outcome: rec.draw.outcome,
            quality: rec.quality,
            artifact: rec.artifact.clone(),
            asset: self.world.verify_provenance(asset_id),
            material_origins: rec.material_origins.clone(),
        })
    }

    /// How many distinct outputs this forge has minted (a refused / botched craft mints
    /// NOTHING, so neither moves this count).
    pub fn output_count(&self) -> usize {
        self.crafts.len()
    }

    /// How many crafts botched (materials consumed, no output minted).
    pub fn botch_count(&self) -> usize {
        self.botched
    }
}

/// A short hex fingerprint of an id's first four bytes (for a display line).
fn hex4(bytes: &[u8; 32]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

/// A stable, sorted `(kind, count)` summary for an error message.
fn kind_summary(m: &HashMap<MaterialKind, usize>) -> Vec<(String, usize)> {
    let mut v: Vec<(String, usize)> = m.iter().map(|(k, n)| (k.0.clone(), *n)).collect();
    v.sort();
    v
}
