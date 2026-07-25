//! # `loot` — LOOT-AS-ASSETS: a Descent reward is a real OWNED, TRANSFERABLE item
//!
//! Every other reward in this crate is a flat **stat bump** — a chest is `~ gold += 500`,
//! a committed field write on the dungeon cell that the player can never carry off the
//! run. This module makes a reward a real THING the player OWNS: a rare chest / a boss
//! drop is a **provably-fair draw** ([`dregg_dice`] over a [`procgen_dregg`]-committed
//! seed) that **mints a real [`dreggnet_asset`] item** owned by the player's own key —
//! an item they can then TRANSFER (the asset layer's cryptographic owner-gate), whose
//! **provenance is bound to the run + seed it dropped from**.
//!
//! ## The fair drop -> an owned asset
//!
//! 1. **The fair draw.** A drop is one indexed draw of a VERIFIED procgen stream
//!    ([`procgen_dregg::verified_stream`]) seeded by a committed [`CommittedSeed`] derived
//!    from the RUN's day-seed + the chest label + a sequence
//!    ([`derive_loot_seed`]). The rarity is the draw's distribution
//!    ([`rarity_of_roll`]): a [`Rarity::Legendary`] is a ~3% tail — a *provable* flex,
//!    not a claim. Because the seed is committed and the draw is a pure verified function
//!    of it, anyone re-derives the identical roll (the fairness anchor is procgen's, not
//!    ours) — a run cannot grind a favourable drop.
//! 2. **The mint.** A verified drop MINTS a [`dreggnet_asset`] note owned by the player,
//!    under a **mint seed = the drop's content commitment** ([`drop_commitment`], binding
//!    the run-seed, the loot-seed, the roll, and the rarity). The asset's content address
//!    ([`dreggnet_asset::AssetId`]) is therefore itself derived from the drop — the
//!    provenance "this legendary dropped from THAT run + seed" is baked into the item's
//!    identity, not a side note.
//! 3. **The owner-gate.** The player now holds a real asset: they can [`transfer`] it, and
//!    the asset layer's executor **signature gate** refuses a non-owner transfer
//!    cryptographically (not app bookkeeping).
//!
//! ## A forged loot claim is REFUSED
//!
//! [`LootVault::claim`] gates the mint on [`reverify_drop`]: it recomputes the loot-seed
//! from the claimed run/chest/seq (a mismatch = a run-provenance forgery), re-derives the
//! honest roll from that committed seed, and confirms the claimed roll + rarity are the
//! fair draw's. A fabricated legendary — an item claimed WITHOUT a real drop, or with a
//! roll/rarity that is not what the seed produces — fails reverify and **no asset is
//! minted** ([`LootError::Forged`]). So "loot" cannot be conjured; it must be *drawn*.
//!
//! ## What a drop IS, downstream — the typed material kind
//!
//! A drop is not just a rarity badge: [`LootDraw::material_kind`] derives the item's typed
//! crafting kind, `"{class}:{rarity}"` (`"relic:legendary"`, `"salvage:common"`), from the
//! chest's [`drop_class`] and the FAIR DRAW's rarity. It is **derived, never declared** — a
//! player cannot present a common drop as a legendary crafting input, because relabelling the
//! chest changes the loot seed and fails [`reverify_drop`]. That is what lets a forge recipe
//! demand real dungeon output ("two legendary relics") instead of a faucet label.
//!
//! ## Adoption, not re-minting
//!
//! [`expected_asset_id`] recomputes the exact address a claimed drop mints at
//! (`blake3(player_pk ‖ `[`drop_commitment`]`)`), so a downstream sink can ADOPT the
//! player's existing note by identity — checking the note it was handed is the one this run
//! really dropped — rather than minting a look-alike in its own ledger. Paired with
//! [`LootVault::into_assets`] / [`LootVault::assets_mut`] (which hand over the live note
//! ledger), a relic banked in a run stays ONE object all the way through crafting and trade.
//!
//! ## Honest scope
//!
//! REAL here: the fair-draw -> owned-transferable-asset mint, the run/seed-bound
//! provenance, the owner-gated transfer, and the forged-claim refusal — all DRIVEN in
//! [`mod tests`]. Reproducibility (not unpredictability) is the [`procgen_dregg`]
//! `Deterministic` property the seed leans on; supplying a real beacon day-seed (as The
//! Descent does) is where the *unpredictable-until-revealed* guarantee enters. NAMED, not
//! built: a market / inventory FRONTEND over the owned items (the asset layer names the
//! `escrow-market` swap seam), CROSS-GAME use of a dropped [`AssetId`] as a foreign
//! holding, and drop-rate tuning / set bonuses. This module is the earning primitive
//! those surfaces render.

use std::collections::{HashMap, HashSet};

use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport, TransferReceipt};
use procgen_dregg::CommittedSeed;

/// The index of the loot rarity draw within the verified procgen stream (well under the
/// committed `DRAW_COUNT` budget, so the draw is always in range).
const LOOT_DRAW_INDEX: u32 = 0;

/// The face count of a loot draw — a d100 (`0..100`), so the rarity tiers below carve a
/// clean percentage distribution.
const RARITY_FACES: u64 = 100;

/// The domain tag folded into a loot seed derivation (so a loot draw stream can never
/// collide with the day-dungeon generation stream that shares the run's seed).
const DOMAIN_LOOT_SEED: &[u8] = b"dungeon-on-dregg/loot-seed/v1";

/// The domain tag for a drop's content commitment (the asset mint seed).
const DOMAIN_LOOT_COMMIT: &[u8] = b"dungeon-on-dregg/loot-drop-commitment/v1";

/// A dropped item's **rarity** — the tier of the fair draw. Rarer tiers are a smaller
/// slice of the `0..100` draw, so a [`Rarity::Legendary`] is a genuine ~3% flex whose
/// provenance (the seed + run it dropped from) anyone can re-derive.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rarity {
    /// The common tail — `60%` of draws (`0..=59`).
    Common,
    /// An uncommon drop — `25%` of draws (`60..=84`).
    Uncommon,
    /// A rare drop — `12%` of draws (`85..=96`).
    Rare,
    /// A legendary drop — the ~`3%` tail (`97..=99`). A provable flex.
    Legendary,
}

impl Rarity {
    /// A stable byte tag (folded into the drop commitment so the rarity is bound into the
    /// asset's content address). Because it is already the committed byte, it is also THE
    /// canonical wire encoding of a rarity — see [`from_tag`](Self::from_tag).
    pub fn tag(self) -> u8 {
        match self {
            Rarity::Common => 0,
            Rarity::Uncommon => 1,
            Rarity::Rare => 2,
            Rarity::Legendary => 3,
        }
    }

    /// The rarity a canonical [`tag`](Self::tag) byte denotes; `None` for a non-canonical byte
    /// (a decoder must fail closed rather than invent a tier).
    pub fn from_tag(tag: u8) -> Option<Rarity> {
        match tag {
            0 => Some(Rarity::Common),
            1 => Some(Rarity::Uncommon),
            2 => Some(Rarity::Rare),
            3 => Some(Rarity::Legendary),
            _ => None,
        }
    }

    /// The human label.
    pub fn label(self) -> &'static str {
        match self {
            Rarity::Common => "common",
            Rarity::Uncommon => "uncommon",
            Rarity::Rare => "rare",
            Rarity::Legendary => "legendary",
        }
    }
}

/// The rarity a `0..100` fair-draw face maps to — the drop distribution. A legendary is
/// the `97..=99` tail (~3%), so it is a provable rarity, not a claim.
pub fn rarity_of_roll(roll: u64) -> Rarity {
    match roll {
        97..=99 => Rarity::Legendary,
        85..=96 => Rarity::Rare,
        60..=84 => Rarity::Uncommon,
        _ => Rarity::Common,
    }
}

/// Derive the **loot seed** for a drop from the run's committed day-seed, the chest label,
/// and a sequence — a domain-separated hash, so every chest/boss on a run draws a fresh,
/// reproducible, run-bound stream (and a verifier who holds the run seed re-derives it).
pub fn derive_loot_seed(run_seed: &CommittedSeed, chest: &str, seq: u64) -> CommittedSeed {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_LOOT_SEED.len() as u64).to_le_bytes());
    h.update(DOMAIN_LOOT_SEED);
    h.update(run_seed.as_bytes());
    h.update(&(chest.len() as u64).to_le_bytes());
    h.update(chest.as_bytes());
    h.update(&seq.to_le_bytes());
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// A resolved, provably-fair drop: the run/chest/seq it came from, the committed loot seed
/// it was drawn from, the raw fair-draw face, and the rarity that face fixes. This is the
/// receipt of a real draw — [`reverify_drop`] re-derives it from the committed seed alone,
/// so a forged (fabricated / rewritten) drop is caught.
#[derive(Clone, Debug)]
pub struct LootDraw {
    /// The RUN's committed day-seed the drop is bound to (its provenance root).
    pub run_seed: CommittedSeed,
    /// The chest / boss the drop came from (a label — e.g. `"boss:the Tide-Warden"`).
    pub chest: String,
    /// The drop's sequence within the run (distinct drops on one run use distinct seqs).
    pub seq: u64,
    /// The committed loot seed the fair draw was taken from ([`derive_loot_seed`]).
    pub loot_seed: CommittedSeed,
    /// The raw fair-draw face (`0..100`).
    pub roll: u64,
    /// The rarity the roll fixes.
    pub rarity: Rarity,
}

impl LootDraw {
    /// The verified turns/roll are content-bound; this is the display line.
    pub fn describe(&self) -> String {
        format!(
            "{} drop from `{}` (roll {}/{} on run seed {})",
            self.rarity.label(),
            self.chest,
            self.roll,
            RARITY_FACES,
            hex4(self.run_seed.as_bytes())
        )
    }
}

/// **Roll a real, provably-fair drop** from a chest/boss on a run. Derives the committed
/// loot seed, runs the VERIFIED procgen stream, and reads the fair-draw face + its rarity.
/// Deterministic in `(run_seed, chest, seq)` — the same drop context always re-derives the
/// identical draw (the fairness anchor is the committed run seed).
pub fn roll_drop(run_seed: &CommittedSeed, chest: &str, seq: u64) -> LootDraw {
    let loot_seed = derive_loot_seed(run_seed, chest, seq);
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&loot_seed);
    let roll = stream
        .draw_bounded(LOOT_DRAW_INDEX, RARITY_FACES)
        .expect("the loot draw index is within the committed budget and RARITY_FACES > 0");
    LootDraw {
        run_seed: *run_seed,
        chest: chest.to_string(),
        seq,
        loot_seed,
        roll,
        rarity: rarity_of_roll(roll),
    }
}

/// The chest label a **BANKED descent relic** mints its loot note under. It encodes the
/// relic's custody SLOT (its identity on the run), so the drop's provenance names the exact
/// banked relic — NOT a hand-typed boss/chest string. Paired with the run's committed
/// day-seed (the provenance root), `(day_seed, slot)` fixes the drop.
pub fn banked_relic_chest(slot: usize) -> String {
    format!("descent:banked-relic:{slot}")
}

/// **Roll the drop a BANKED descent relic mints under** — the bank → asset binding. The run's
/// committed day-seed is the provenance root (unpredictable-until-revealed when it is a real
/// beacon day-seed); the chest + seq encode the exact custody SLOT the relic banked in. The
/// draw is a pure verified function of `(day_seed, slot)` through the same [`roll_drop`] path,
/// so re-running the banked run re-derives the identical draw → the identical
/// content-addressed [`AssetId`]: the minted note's provenance **replays to the banked run**,
/// not to a manufactured `roll_drop("boss:…")`. A relic that banked in slot `s` on the run
/// seeded by `day_seed` always mints THIS drop, and only this drop.
pub fn banked_relic_drop(day_seed: &CommittedSeed, slot: usize) -> LootDraw {
    roll_drop(day_seed, &banked_relic_chest(slot), slot as u64)
}

/// **Re-verify a drop is a real fair draw** — the tooth that refuses a forged loot claim.
/// Recomputes the loot seed from the claimed run/chest/seq (a mismatch = a forged
/// provenance), re-derives the honest roll from the committed seed through the same
/// verified procgen stream, and confirms the claimed roll + rarity are exactly the fair
/// draw's. A fabricated legendary — a claim with no real draw, or a rewritten roll/rarity
/// — fails here.
pub fn reverify_drop(draw: &LootDraw) -> Result<(), LootError> {
    // 1. The loot seed must be the honest binding of the claimed run + chest + seq.
    let expect_seed = derive_loot_seed(&draw.run_seed, &draw.chest, draw.seq);
    if expect_seed != draw.loot_seed {
        return Err(LootError::Forged(
            "the loot seed is not bound to the claimed run/chest/seq".to_string(),
        ));
    }
    // 2. Re-derive the honest roll from the committed seed (the fair, reproducible draw).
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&draw.loot_seed);
    let true_roll = stream
        .draw_bounded(LOOT_DRAW_INDEX, RARITY_FACES)
        .map_err(|e| LootError::Forged(format!("the fair draw did not re-derive: {e:?}")))?;
    // 3. The claimed roll + rarity must be the fair draw's — a rewritten flex is caught.
    if true_roll != draw.roll {
        return Err(LootError::Forged(format!(
            "the claimed roll {} is not the fair draw {true_roll}",
            draw.roll
        )));
    }
    if rarity_of_roll(true_roll) != draw.rarity {
        return Err(LootError::Forged(format!(
            "the claimed rarity {:?} is not the roll's",
            draw.rarity
        )));
    }
    Ok(())
}

/// The drop's **content commitment** — the mint seed the asset is minted under, binding
/// the run-seed, the loot-seed, the fair roll, the rarity, and the chest. The
/// [`dreggnet_asset::AssetId`] is derived from `blake3(player_pk ‖ this)`, so the item's
/// content address itself encodes the drop it came from (its provenance).
///
/// Public because it is half of [`expected_asset_id`]: a downstream layer that ADOPTS an
/// already-minted loot note (rather than re-minting a look-alike) must be able to recompute
/// the address the presented note is obliged to have.
pub fn drop_commitment(draw: &LootDraw) -> Vec<u8> {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_LOOT_COMMIT.len() as u64).to_le_bytes());
    h.update(DOMAIN_LOOT_COMMIT);
    h.update(draw.run_seed.as_bytes());
    h.update(draw.loot_seed.as_bytes());
    h.update(&draw.roll.to_le_bytes());
    h.update(&[draw.rarity.tag()]);
    h.update(&(draw.chest.len() as u64).to_le_bytes());
    h.update(draw.chest.as_bytes());
    h.finalize().as_bytes().to_vec()
}

/// **The [`AssetId`] a drop MUST have** if `owner_pk` claimed it — `blake3(owner_pk ‖
/// [`drop_commitment`]`(draw))`, exactly what [`LootVault::claim`] mints under.
///
/// This is the tooth that lets a downstream sink (the forge, a market, a second game) ADOPT
/// a player's existing loot note by identity instead of re-minting a look-alike from its
/// display metadata: the adopter recomputes this address from the claimed drop and the
/// claiming player's key and refuses any note that is not it. Combined with
/// [`reverify_drop`] (which pins the drop to the run's committed seed), an adopted note is
/// provably "the item THAT run dropped for THAT player" — a claim recomputable by anyone
/// holding the run seed, with no access to the ledger.
pub fn expected_asset_id(draw: &LootDraw, owner_pk: &[u8; 32]) -> AssetId {
    AssetId::derive(owner_pk, &drop_commitment(draw))
}

/// The **class** of a drop, read off its chest label — the coarse semantic type the drop's
/// material kind is built from. A banked descent relic ([`banked_relic_chest`]) is a
/// `relic`; a named boss kill is a `trophy`; anything else is `salvage`.
///
/// A pure function of the (committed, provenance-bound) chest string, so it carries no
/// forgery surface of its own: a claimant cannot relabel a salvage drop as a relic without
/// changing the chest, which changes the loot seed, which fails [`reverify_drop`].
pub fn drop_class(chest: &str) -> &'static str {
    if chest.starts_with("descent:banked-relic:") {
        "relic"
    } else if chest.starts_with("boss:") {
        "trophy"
    } else {
        "salvage"
    }
}

impl LootDraw {
    /// **The typed MATERIAL KIND this drop is, as a crafting input** — `"{class}:{rarity}"`,
    /// e.g. `"relic:legendary"` for a legendary banked descent relic, `"salvage:common"` for
    /// an ordinary chest drop.
    ///
    /// A pure function of the drop ([`drop_class`] of its chest + the fair draw's rarity), so
    /// **the fair draw decides what a material IS**. A player cannot present a common drop as
    /// a legendary crafting input: the kind is derived, never declared. This is what lets a
    /// recipe demand real dungeon output ("two legendary relics") rather than a faucet label.
    pub fn material_kind(&self) -> String {
        format!("{}:{}", drop_class(&self.chest), self.rarity.label())
    }
}

/// A minted loot item — a real owned [`dreggnet_asset`] note. Its [`AssetId`] is
/// content-addressed to the drop it came from + the player's key.
#[derive(Clone, Debug)]
pub struct LootItem {
    /// The stable, content-addressed asset id (the cross-cell handle a market names it by).
    pub asset_id: AssetId,
    /// The drop's rarity (the fair-draw tier).
    pub rarity: Rarity,
    /// The current owner's pubkey (at mint, the player's key).
    pub owner: [u8; 32],
}

/// The provenance of a looted item — the run/seed it dropped from, its fair draw, and the
/// asset layer's own on-chain provenance re-verification.
#[derive(Clone, Debug)]
pub struct LootProvenance {
    /// The RUN's committed day-seed the item dropped from.
    pub run_seed: CommittedSeed,
    /// The chest / boss it dropped from.
    pub chest: String,
    /// The fair-draw face + rarity.
    pub roll: u64,
    /// The drop's rarity.
    pub rarity: Rarity,
    /// The asset layer's provenance report (the note lineage re-verifies, current owner).
    pub asset: ProvenanceReport,
}

/// Why a loot operation could not complete.
#[derive(Clone, Debug)]
pub enum LootError {
    /// The claimed drop is not a real fair draw (a fabricated / rewritten claim) — no
    /// asset is minted. Carries the exact mismatch.
    Forged(String),
    /// This exact drop has already been claimed (a drop mints exactly once).
    AlreadyClaimed,
    /// The underlying asset layer refused the operation (a non-owner / double-spend
    /// transfer, or an unknown asset). Carries the asset error.
    Asset(AssetError),
}

impl std::fmt::Display for LootError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LootError::Forged(why) => write!(f, "forged loot claim refused: {why}"),
            LootError::AlreadyClaimed => write!(f, "this drop was already claimed"),
            LootError::Asset(e) => write!(f, "asset layer refused: {e}"),
        }
    }
}

impl std::error::Error for LootError {}

/// **The loot vault** — the mint / transfer / provenance surface over a set of sovereign
/// player ledgers ([`dreggnet_asset::AssetWorld`]). A verified drop mints a real owned
/// item; the player transfers it under the asset layer's cryptographic owner-gate; a
/// forged claim is refused before any mint.
pub struct LootVault {
    world: AssetWorld,
    /// AssetId bytes -> the drop it was minted from (its provenance record).
    drops: HashMap<[u8; 32], LootDraw>,
    /// The drop commitments already claimed (a drop mints exactly once).
    claimed: HashSet<Vec<u8>>,
}

impl Default for LootVault {
    fn default() -> Self {
        Self::new()
    }
}

impl LootVault {
    /// A fresh loot vault (no players, no items).
    pub fn new() -> Self {
        LootVault {
            world: AssetWorld::new(),
            drops: HashMap::new(),
            claimed: HashSet::new(),
        }
    }

    /// Hand the exact live owned-note world to another engine organ.
    ///
    /// This is the Descent → inventory/trade/Bazaar bridge: every minted loot
    /// [`AssetId`] keeps its existing note lineage and current owner. Consumers such
    /// as `dreggnet_trade::TradeWorld::with_assets` adopt this world directly; they
    /// must not re-mint the item from display metadata.
    pub fn into_assets(self) -> AssetWorld {
        self.world
    }

    /// Borrow the live owned-note world — the same bridge as [`Self::into_assets`] for a
    /// consumer that must keep the vault (and so its per-item drop records) alive alongside.
    pub fn assets_mut(&mut self) -> &mut AssetWorld {
        &mut self.world
    }

    /// The deterministic pubkey of a player label (creating the identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.world.pubkey_of(label)
    }

    /// The drop a looted item was minted from — the record a downstream sink needs to
    /// re-verify the item's run provenance ([`reverify_drop`] + [`expected_asset_id`]) when it
    /// adopts the note.
    pub fn drop_of(&self, asset_id: AssetId) -> Option<&LootDraw> {
        self.drops.get(&asset_id.bytes())
    }

    /// **A player's live looted inventory** — every item they still hold, in a stable
    /// content-address order (items transferred away or consumed by a sink are gone).
    pub fn inventory_of(&self, player: &str) -> Vec<AssetId> {
        self.world
            .assets_held_by(player)
            .into_iter()
            .filter(|id| self.drops.contains_key(&id.bytes()))
            .collect()
    }

    /// The typed crafting **material kind** of a looted item — the kind its fair draw fixes
    /// ([`LootDraw::material_kind`]), not a label anyone declared.
    pub fn material_kind_of(&self, asset_id: AssetId) -> Option<String> {
        self.drops.get(&asset_id.bytes()).map(|d| d.material_kind())
    }

    /// **Claim a drop as a real owned item** — the forged-claim gate + the mint. The drop
    /// is re-verified as a real fair draw ([`reverify_drop`]); a forged claim is refused
    /// with NO mint. A verified drop mints a [`dreggnet_asset`] note owned by `player`
    /// under the drop's content commitment, so the item's [`AssetId`] is bound to the run
    /// + seed it dropped from.
    pub fn claim(&mut self, player: &str, draw: &LootDraw) -> Result<LootItem, LootError> {
        // The tooth: a forged loot claim (no real / a rewritten draw) is refused BEFORE mint.
        reverify_drop(draw)?;

        let commit = drop_commitment(draw);
        if !self.claimed.insert(commit.clone()) {
            return Err(LootError::AlreadyClaimed);
        }

        // The mint seed IS the drop commitment, so the asset id encodes the drop. Minted
        // fail-closed: if this world ALREADY carries that content address (e.g. the vault was
        // opened over a ledger a previous run's notes live in), a second "mint" would append a
        // bogus origin and break the note's lineage — refuse instead of corrupting it.
        let asset_id = self.world.try_mint(player, &commit).map_err(|e| match e {
            AssetError::DuplicateMint => LootError::AlreadyClaimed,
            other => LootError::Asset(other),
        })?;
        debug_assert_eq!(
            asset_id.bytes(),
            expected_asset_id(draw, &self.world.pubkey_of(player)).bytes(),
            "a claimed drop lands on the address a third party recomputes for it"
        );
        self.drops.insert(asset_id.bytes(), draw.clone());
        let owner = self
            .world
            .current_owner(asset_id)
            .expect("a freshly-minted asset has an owner");
        Ok(LootItem {
            asset_id,
            rarity: draw.rarity,
            owner,
        })
    }

    /// **Transfer a looted item** from `from` to `to` — the asset layer's owner-gated
    /// transfer. A non-owner `from` (a forged owner) is a real cryptographic refusal
    /// ([`LootError::Asset`] wrapping [`AssetError::Refused`]); an owner's transfer spends
    /// the current version and mints a successor owned by `to`.
    pub fn transfer(
        &mut self,
        asset_id: AssetId,
        from: &str,
        to: &str,
    ) -> Result<TransferReceipt, LootError> {
        self.world
            .transfer(asset_id, from, to)
            .map_err(LootError::Asset)
    }

    /// The current owner's pubkey of a looted item.
    pub fn owner_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.world.current_owner(asset_id)
    }

    /// The rarity of a looted item (from its recorded drop).
    pub fn rarity_of(&self, asset_id: AssetId) -> Option<Rarity> {
        self.drops.get(&asset_id.bytes()).map(|d| d.rarity)
    }

    /// The full provenance of a looted item — the run/seed + fair draw it dropped from,
    /// plus the asset layer's own lineage re-verification (`None` if unknown here).
    pub fn provenance(&self, asset_id: AssetId) -> Option<LootProvenance> {
        let draw = self.drops.get(&asset_id.bytes())?;
        Some(LootProvenance {
            run_seed: draw.run_seed,
            chest: draw.chest.clone(),
            roll: draw.roll,
            rarity: draw.rarity,
            asset: self.world.verify_provenance(asset_id),
        })
    }

    /// Re-verify the item's asset-layer provenance chain (the note lineage + on-chain
    /// spent re-reads) — the same executor-refereed check `dreggnet-asset` exposes.
    pub fn verify_asset_provenance(&self, asset_id: AssetId) -> ProvenanceReport {
        self.world.verify_provenance(asset_id)
    }

    /// How many distinct looted items this vault has minted (the anti-ghost witness: a
    /// refused forged claim mints NOTHING, so it does not move this count).
    pub fn item_count(&self) -> usize {
        self.drops.len()
    }
}

/// A short hex fingerprint of a seed's first four bytes (for a display line).
fn hex4(bytes: &[u8; 32]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    //! LOOT-AS-ASSETS, DRIVEN on the real asset layer: a fair drop mints a real OWNED,
    //! content-addressed item whose provenance binds the run/seed; a legendary vs a common
    //! is decided by the fair draw; the player TRANSFERS it under the owner-gate (a
    //! non-owner cannot); a forged loot claim is REFUSED with no mint.
    use super::*;

    /// A committed run seed standing in for a Descent day (in the flagship this is the
    /// verified drand-beacon day-seed the run was played on).
    fn run_seed(byte: u8) -> CommittedSeed {
        CommittedSeed::from_bytes([byte; 32])
    }

    /// Search for a run seed whose named chest drops the target rarity (the draw is a pure
    /// function of the seed, so this just scans the deterministic distribution).
    fn find_seed_for(chest: &str, want: Rarity) -> CommittedSeed {
        for b in 0u16..=255 {
            let s = run_seed(b as u8);
            if roll_drop(&s, chest, 0).rarity == want {
                return s;
            }
        }
        panic!("no run seed in 0..256 drops {want:?} from `{chest}`");
    }

    /// A fair drop MINTS a real owned, content-addressed asset whose provenance binds the
    /// run + seed it dropped from — and it re-verifies on the asset layer.
    #[test]
    fn a_fair_drop_mints_a_real_owned_asset_bound_to_the_run() {
        let mut vault = LootVault::new();
        let seed = run_seed(7);
        let chest = "boss:the-tide-warden";
        let draw = roll_drop(&seed, chest, 0);

        let alice_pk = vault.pubkey_of("alice");
        let item = vault.claim("alice", &draw).expect("a real drop mints");

        // The player OWNS it (their key), and it is content-addressed.
        assert_eq!(
            item.owner, alice_pk,
            "the item is owned by the player's key"
        );
        assert_eq!(
            vault.owner_of(item.asset_id),
            Some(alice_pk),
            "the asset layer agrees the player is the owner"
        );

        // Provenance binds the run/seed + the fair draw, and the asset lineage verifies.
        let prov = vault
            .provenance(item.asset_id)
            .expect("provenance recorded");
        assert_eq!(
            prov.run_seed, seed,
            "provenance binds the run it dropped from"
        );
        assert_eq!(prov.chest, chest);
        assert_eq!(prov.roll, draw.roll, "provenance binds the fair draw");
        assert!(
            prov.asset.verified,
            "the asset-layer lineage re-verifies: {:?}",
            prov.asset.reasons
        );
        assert_eq!(prov.asset.length, 1, "a fresh mint is a length-1 lineage");
    }

    /// A LEGENDARY vs a COMMON is decided by the FAIR DRAW — the rarity is the draw's
    /// distribution, not a claim. Both mint real owned assets; their recorded rarity is the
    /// re-derivable draw tier (a legendary is a provable ~3% flex).
    #[test]
    fn a_legendary_vs_a_common_is_the_fair_draw() {
        let chest = "chest:reliquary";
        let leg_seed = find_seed_for(chest, Rarity::Legendary);
        let com_seed = find_seed_for(chest, Rarity::Common);

        let leg = roll_drop(&leg_seed, chest, 0);
        let com = roll_drop(&com_seed, chest, 0);
        assert_eq!(leg.rarity, Rarity::Legendary, "a genuine legendary draw");
        assert_eq!(com.rarity, Rarity::Common, "a genuine common draw");
        // The rarity is exactly the fair-draw distribution, re-derivable by anyone.
        reverify_drop(&leg).expect("the legendary is a real fair draw");
        reverify_drop(&com).expect("the common is a real fair draw");
        assert!(
            leg.roll >= 97 && com.roll < 60,
            "the tiers reflect the draw faces: legendary {} vs common {}",
            leg.roll,
            com.roll
        );

        let mut vault = LootVault::new();
        let li = vault.claim("hero", &leg).expect("the legendary mints");
        let ci = vault.claim("hero", &com).expect("the common mints");
        assert_eq!(vault.rarity_of(li.asset_id), Some(Rarity::Legendary));
        assert_eq!(vault.rarity_of(ci.asset_id), Some(Rarity::Common));
        // Distinct drops -> distinct content-addressed assets.
        assert_ne!(
            li.asset_id.bytes(),
            ci.asset_id.bytes(),
            "different drops are different items"
        );
    }

    /// The player can TRANSFER a looted item — the asset layer's owner-gate. An owner's
    /// transfer moves it (a non-owner now holds it); a NON-OWNER transfer is a real
    /// cryptographic refusal.
    #[test]
    fn the_looted_item_transfers_owner_gated_and_a_non_owner_cannot() {
        let mut vault = LootVault::new();
        let draw = roll_drop(&run_seed(9), "chest:hoard", 0);
        let alice_pk = vault.pubkey_of("alice");
        let bob_pk = vault.pubkey_of("bob");

        let item = vault.claim("alice", &draw).expect("alice loots it");
        assert_eq!(vault.owner_of(item.asset_id), Some(alice_pk));

        // A NON-OWNER (mallory) cannot transfer alice's item — a real refusal.
        let forged = vault.transfer(item.asset_id, "mallory", "eve");
        assert!(
            matches!(forged, Err(LootError::Asset(AssetError::Refused(_)))),
            "a non-owner transfer is refused by the owner-gate, got {forged:?}"
        );
        assert_eq!(
            vault.owner_of(item.asset_id),
            Some(alice_pk),
            "anti-ghost: the item still belongs to alice"
        );

        // The OWNER can transfer it — it moves to bob.
        vault
            .transfer(item.asset_id, "alice", "bob")
            .expect("the owner's transfer commits");
        assert_eq!(
            vault.owner_of(item.asset_id),
            Some(bob_pk),
            "the item is now bob's"
        );
        // The provenance chain still re-verifies after the transfer (a 2-version lineage).
        let prov = vault.verify_asset_provenance(item.asset_id);
        assert!(
            prov.verified,
            "post-transfer lineage verifies: {:?}",
            prov.reasons
        );
        assert_eq!(prov.length, 2, "mint + one transfer = two versions");
    }

    /// A FORGED loot claim — an item claimed WITHOUT a real drop — is REFUSED with no
    /// mint. Non-vacuous: the honest drop mints; the same drop with a rewritten roll (a
    /// fabricated legendary) is refused, and its would-be asset never exists.
    #[test]
    fn a_forged_loot_claim_is_refused_with_no_mint() {
        let mut vault = LootVault::new();
        let honest = roll_drop(&run_seed(3), "chest:vault", 0);

        // FORGE a legendary: rewrite the roll + rarity to a natural flex the seed never
        // produced. (Pick a roll DIFFERENT from the honest one so the tooth actually bites.)
        let forged_roll = if honest.roll == 99 { 98 } else { 99 };
        let mut forged = honest.clone();
        forged.roll = forged_roll;
        forged.rarity = Rarity::Legendary;

        let out = vault.claim("cheater", &forged);
        assert!(
            matches!(out, Err(LootError::Forged(_))),
            "a fabricated legendary is refused, got {out:?}"
        );
        // Anti-ghost: the refused forged claim minted NOTHING.
        assert_eq!(
            vault.item_count(),
            0,
            "no asset was minted for the forged claim"
        );

        // The HONEST drop still mints (the tooth is not vacuously rejecting everything).
        let item = vault
            .claim("cheater", &honest)
            .expect("the honest drop mints");
        assert_eq!(vault.rarity_of(item.asset_id), Some(honest.rarity));
        assert_eq!(vault.item_count(), 1, "exactly the honest drop is an item");
    }

    /// **The claimed note sits where a third party computes it will.** `expected_asset_id`
    /// recomputes the mint address from the drop + the claimant's public key alone, so a
    /// downstream sink can ADOPT the player's real note by identity instead of re-minting a
    /// look-alike. Sensitive to both halves: another player's key, or a different drop, lands
    /// somewhere else.
    #[test]
    fn a_claimed_note_sits_at_the_address_anyone_recomputes_for_it() {
        let mut vault = LootVault::new();
        let draw = roll_drop(&run_seed(11), "chest:strongbox", 0);
        let alice_pk = vault.pubkey_of("alice");
        let bob_pk = vault.pubkey_of("bob");

        let item = vault.claim("alice", &draw).expect("the drop mints");
        assert_eq!(
            item.asset_id.bytes(),
            expected_asset_id(&draw, &alice_pk).bytes(),
            "the note is exactly where (drop, claimant key) says it is"
        );
        assert_ne!(
            expected_asset_id(&draw, &bob_pk).bytes(),
            item.asset_id.bytes(),
            "a different claimant would hold a different note"
        );
        let other = roll_drop(&run_seed(12), "chest:strongbox", 0);
        assert_ne!(
            expected_asset_id(&other, &alice_pk).bytes(),
            item.asset_id.bytes(),
            "and a different drop is a different note"
        );
    }

    /// **The FAIR DRAW decides what a material IS.** A drop's crafting kind is derived from its
    /// chest class and the draw's rarity — never declared — so a common drop cannot be
    /// presented as legendary crafting stock. Relabelling the chest to claim a different class
    /// changes the loot seed, so the relabelled draw fails `reverify_drop`.
    #[test]
    fn a_drops_material_kind_is_derived_from_the_fair_draw_not_declared() {
        // `find_seed_for` scans at seq 0, so the drops below must be rolled at seq 0 too — a
        // different seq is a different loot seed and so a different draw.
        let chest = "descent:banked-relic:2";
        let leg = roll_drop(&find_seed_for(chest, Rarity::Legendary), chest, 0);
        let com = roll_drop(&find_seed_for(chest, Rarity::Common), chest, 0);
        assert_eq!(leg.material_kind(), "relic:legendary");
        assert_eq!(com.material_kind(), "relic:common");

        // The class comes off the chest, and the three classes are distinct.
        assert_eq!(drop_class("descent:banked-relic:7"), "relic");
        assert_eq!(drop_class("boss:the-tide-warden"), "trophy");
        assert_eq!(drop_class("chest:reliquary"), "salvage");
        let boss = roll_drop(&run_seed(4), "boss:the-tide-warden", 0);
        assert!(boss.material_kind().starts_with("trophy:"));

        // A claimant who rewrites the chest to upgrade the class is caught: the loot seed no
        // longer binds the claimed run/chest/seq.
        let mut relabelled = com.clone();
        relabelled.chest = "descent:banked-relic:0".to_string();
        assert_eq!(relabelled.material_kind(), "relic:common");
        assert!(
            matches!(reverify_drop(&relabelled), Err(LootError::Forged(_))),
            "relabelling the chest breaks the seed binding"
        );
    }

    /// The vault answers "what does this player still hold?" off the real ledger — the
    /// inventory read a bench or a market renders, which follows transfers.
    #[test]
    fn the_vault_reports_a_players_live_inventory() {
        let mut vault = LootVault::new();
        let one = roll_drop(&run_seed(31), "chest:a", 0);
        let two = roll_drop(&run_seed(32), "chest:b", 1);
        let a = vault.claim("alice", &one).expect("a").asset_id;
        let b = vault.claim("alice", &two).expect("b").asset_id;
        assert_eq!(vault.inventory_of("alice").len(), 2);
        assert!(vault.inventory_of("bob").is_empty());
        assert_eq!(
            vault.material_kind_of(a),
            Some(one.material_kind()),
            "each held item reports the kind its draw fixed"
        );

        vault.transfer(a, "alice", "bob").expect("a gift");
        assert_eq!(vault.inventory_of("alice"), vec![b]);
        assert_eq!(vault.inventory_of("bob"), vec![a]);
        assert_eq!(vault.drop_of(a).map(|d| d.roll), Some(one.roll));
    }

    /// A drop mints exactly once: re-claiming the same drop is refused (no lineage
    /// corruption).
    #[test]
    fn a_drop_mints_exactly_once() {
        let mut vault = LootVault::new();
        let draw = roll_drop(&run_seed(5), "chest:cache", 0);
        let first = vault.claim("p", &draw).expect("first claim mints");
        let second = vault.claim("p", &draw);
        assert!(
            matches!(second, Err(LootError::AlreadyClaimed)),
            "re-claiming the same drop is refused, got {second:?}"
        );
        assert!(vault.owner_of(first.asset_id).is_some());
        assert_eq!(
            vault.item_count(),
            1,
            "the double-claim minted no second item"
        );
    }
}
