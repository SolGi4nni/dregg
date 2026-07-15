//! # `dreggnet-craft` — a provably-fair FORGE: the economy's first real SINK.
//!
//! CRAFTING (GAME-INFRA-ROADMAP progression #2). Every other economy motion so far is a
//! FAUCET — loot drops, echoes, quest rewards MINT assets into circulation. A forge is the
//! inverse and the thing an economy actually needs: it **CONSUMES** a typed multiset of
//! owned material assets (the inputs) and produces ONE new output asset. The inputs are
//! genuinely destroyed on-chain — the first real **sink**, the tooth that keeps the supply
//! from only ever growing.
//!
//! ## The forge, end to end
//!
//! 1. **A committed catalog.** A [`RecipeBook`] is the registered set of [`Recipe`]s the
//!    forge crafts against. A recipe names the exact typed multiset of [`MaterialKind`]s it
//!    consumes, the committed `outcome_weights` / `quality_weights` its draws are taken over,
//!    and the [`OutputSpec`] it forges. A craft can only present a recipe the book holds, so
//!    the odds are committed to the catalog, never chosen per-craft.
//! 2. **Two fair draws.** A craft's outcome is TWO indexed selections of a VERIFIED procgen
//!    stream ([`procgen_dregg::verified_stream`]) seeded by a committed **craft seed**
//!    ([`derive_craft_seed`]) — a domain-separated hash of the beacon, the recipe id, and the
//!    (sorted) input [`dreggnet_asset::AssetId`]s. The first draw is the *outcome band*
//!    ([`CraftOutcome`] — botch / partial / success), the second the *quality tier*
//!    ([`CraftQuality`]), each a provably-fair `DrawStream::weighted` CDF over the recipe's
//!    committed weight table. Because the seed is committed and the draws are pure verified
//!    functions of it and the public weights, anyone re-derives the identical outcome, so a
//!    legendary craft cannot be fabricated.
//! 3. **The typed inputs are SPENT.** Before minting anything the forge checks the presented
//!    inputs are the recipe's exact typed multiset, each a real live asset the crafter owns.
//!    It then **burns each input on-chain** with a real `player`-signed spend through the asset
//!    layer's owner-gated burn ([`dreggnet_asset::AssetWorld::revoke`]) — the executor admits
//!    the burn only under the crafter's own owner signature, so the authorization to consume is
//!    an ISA owner-signature gate, not a host `owns_live` check. The materials are consumed —
//!    there is no dupe-then-craft, because a spent note cannot be spent again. On a **botch** the
//!    materials are still consumed and nothing is minted (the gamble a risky recipe carries).
//! 4. **The output binds its provenance + is a REAL artifact.** A minting craft MINTS a
//!    [`dreggnet_asset`] note owned by the crafter under a **mint seed = the craft's content
//!    commitment** ([`craft_commitment`]), binding the recipe, the inputs, the band, the
//!    quality, and the concrete [`CraftedArtifact`] — a real [`dreggnet_gear::StatBlock`]
//!    (equippable by the `Armory`) or a companion egg. The output's content address therefore
//!    encodes exactly what was forged from what.
//!
//! ## Wired to the real economy
//!
//! Inputs can be SOURCED from real dungeon loot: [`CraftForge::mint_loot_material`] gates a
//! material on the loot layer's own [`dungeon_on_dregg::loot::reverify_drop`] tooth, so a
//! material is provably a real, fair drop — not a demo faucet. Outputs are the SHARED gear /
//! companion schemas, so a forged item is a real, equippable [`dreggnet_gear::StatBlock`],
//! not a craft-local shadow of one.
//!
//! ## A forged craft mints NOTHING
//!
//! [`CraftForge::craft`] gates the whole motion on [`reverify_craft`] (against the catalog's
//! committed weights) + the typed input check. A fabricated outcome fails re-verification and
//! **no input is spent and no asset is minted**. A craft with inputs the crafter does not
//! own, or the wrong kinds, is refused with no mint. So a crafted item cannot be conjured; its
//! inputs must be *really destroyed* and its outcome must be the *fair draw*. (A **botch** is
//! distinct: an honest failed forge that DOES consume its materials.)

mod draw;
mod forge;
mod quality;
mod recipe;

pub use draw::{
    CraftDraw, craft_commitment, derive_craft_seed, resolve_artifact, reverify_craft, roll_craft,
};
pub use forge::{
    BotchReceipt, CraftError, CraftForge, CraftOutput, CraftProvenance, CraftResolution,
};
pub use quality::{CraftOutcome, CraftQuality};
pub use recipe::{
    CraftedArtifact, DEFAULT_QUALITY_WEIGHTS, GearTemplate, MaterialKind, OutputSpec, Recipe,
    RecipeBook,
};

// Re-exported from siblings so callers name the shared schemas through the forge.
pub use dreggnet_asset::AssetId;
pub use dreggnet_gear::{GearSlot, Rarity as GearRarity, StatBlock};
pub use dungeon_on_dregg::loot::Rarity as LootRarity;
pub use procgen_dregg::CommittedSeed;
