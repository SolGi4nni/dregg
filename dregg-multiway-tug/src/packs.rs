//! # Phase 1 — CARDS-AS-ASSETS + provably-fair PACKS (the COLLECTIBLE layer).
//!
//! Phase 0 ([`crate::game`]) is the in-PLAY layer: a round's deck/hand/board is the
//! executor's heap collection, the favors only *counted* (a card is a slot value, not a
//! thing anyone owns). This module is the **collectible layer that rides alongside it**: a
//! *printed favor card* — a specific guild's card with an art/rarity trait root — is a
//! real **owned [`dreggnet_asset`] note**, content-addressed by the draw it came from,
//! transferable under the asset layer's cryptographic owner-gate, and provenance-bound to
//! the pack that produced it. It sharpens the loot-as-assets pattern
//! ([`dungeon_on_dregg::loot`], mirrored by [`dreggnet_craft`]) to a TCG surface.
//!
//! ## Opening a pack is a provably-fair draw
//!
//! 1. **The fair draw.** A booster's contents are a pure verified function of a committed
//!    **pack seed** ([`derive_pack_seed`] — a domain-separated hash of a committed beacon
//!    value, the pack label, and a sequence). Each of the [`PACK_SIZE`] cards is a small
//!    fixed run of indexed draws over the VERIFIED procgen stream
//!    ([`procgen_dregg::verified_stream`]): the **guild** (which favor is printed), the
//!    collectible **rarity** ([`CardRarity`], a *committed-weight* draw — the E2 shape,
//!    [`weighted_index`]), and an **art variant**, folded into a [`CardDraw::traits_root`].
//!    A [`CardRarity::Foil`] is the committed ~3% tail — a *provable* rarity, not a claim.
//!    Because the seed is committed and the draw is pure, anyone re-derives the identical
//!    pack (the fairness anchor is procgen's), so no one can grind a favourable pull.
//! 2. **The mint.** Opening a verified pack MINTS one [`dreggnet_asset`] note per card,
//!    owned by the **opener**, under a **mint seed = the card's content commitment**
//!    ([`card_commitment`], binding the pack seed, the slot, the guild, the rarity, the art
//!    variant, and the traits root). The card's [`dreggnet_asset::AssetId`] is therefore
//!    derived from the drawn card itself — the trait root is bound into the owned identity
//!    *through the mint seed* (the spec's E1 "derivable into `AssetId` via `mint_seed`"),
//!    with `dreggnet-asset` left unmodified.
//! 3. **The owner-gate.** The opener now holds real owned cards: each can be transferred
//!    ([`CardVault::transfer`]), and a non-owner transfer is a real cryptographic refusal
//!    (the asset layer's signature-vs-birth-key gate) — not app bookkeeping. The trustless
//!    asset↔asset / asset↔value SWAP over these cards is `dreggnet-trade` (a named surface;
//!    the owner-gated transfer here is the primitive it binds).
//!
//! ## Two cards are "the same card" — the print identity
//!
//! A card carries an owner-and-pack-independent **content id** ([`CardDraw::content_id`] —
//! a hash of just the guild, rarity, art variant, and traits root). Two cards with the
//! same printed content share a content id (they are "the same card", as two copies of one
//! TCG print are), while each owned copy has its own distinct [`AssetId`]. The card content
//! is content-addressed by the draw: the same pack re-derives byte-identical cards; a
//! different seed yields different cards.
//!
//! ## A forged pack-open mints NOTHING
//!
//! [`CardVault::open`] gates every mint on [`reverify_pack`]: it recomputes the pack seed
//! from the claimed beacon/label/seq (a mismatch = a forged context) and re-derives every
//! card from that committed seed, requiring the claimed pack to be *exactly* the fair
//! draw's. A fabricated pull — a card rewritten to a foil the seed never produced — fails
//! reverify and **no card is minted** ([`PackError::Forged`]). So a rare card cannot be
//! conjured; it must be *pulled*.
//!
//! ## Honest scope
//!
//! REAL here: cards as owned, transferable, content-addressed [`dreggnet_asset`] notes; the
//! committed-seed fair pack draw with a committed-weight (provable) rarity; the
//! pack-provenance-bound identity; the owner-gated transfer; and the forged-pack refusal —
//! all DRIVEN in [`mod tests`] against the real executor-refereed asset layer. The rarity
//! draw uses a crate-local committed-weight CDF over one bounded draw ([`weighted_index`]) —
//! the spec's E2 shape without modifying `dregg-dice`; promoting it to a first-class
//! `DrawStream::weighted` is a named `dregg-dice` residual. Reproducibility (not
//! unpredictability) is the [`procgen_dregg`] `Deterministic` property the seed leans on;
//! a real beacon value is where the unpredictable-until-revealed guarantee enters. NAMED,
//! not built: the trustless market/swap over these cards (`dreggnet-trade`), the trait ->
//! sprite render (E3 `traitsJson` + `<dregg-sprite>`), and a card's on-note trait FIELD
//! (E1 as an added `dreggnet-asset` `.identity`, a change owned by that crate — here the
//! traits bind through the mint seed instead).

use std::collections::{HashMap, HashSet};

use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport, TransferReceipt};
use procgen_dregg::CommittedSeed;
use procgen_dregg::dregg_dice::DrawStream;

use crate::reference::{INFLUENCE, N_GUILDS};

/// The number of cards a pack (a booster) contains.
pub const PACK_SIZE: usize = 5;

/// The number of art variants a printed card can take (a small fixed trait axis; the
/// sprite renderer draws off the traits root E1/E2 name).
pub const ART_VARIANTS: u64 = 4;

/// The per-card draw stride within the pack's verified stream. Each card consumes three
/// indexed draws (guild, rarity, art); `PACK_SIZE * CARD_STRIDE` stays well under
/// procgen's fixed `DRAW_COUNT` budget, so every draw index is in range.
const CARD_STRIDE: u32 = 3;
const C_GUILD: u32 = 0;
const C_RARITY: u32 = 1;
const C_ART: u32 = 2;

/// The domain tag folded into a pack seed derivation (so a pack draw stream can never
/// collide with the loot / craft / dungeon-generation streams that share a beacon).
const DOMAIN_PACK_SEED: &[u8] = b"dregg-multiway-tug/pack-seed/v1";

/// The domain tag for a card's content commitment (the owned asset's mint seed).
const DOMAIN_CARD_COMMIT: &[u8] = b"dregg-multiway-tug/card-commitment/v1";

/// The domain tag for a card's owner-independent PRINT identity (its content id).
const DOMAIN_CARD_CONTENT: &[u8] = b"dregg-multiway-tug/card-content/v1";

/// The domain tag for a card's traits root (the deterministic sprite-binding root).
const DOMAIN_CARD_TRAITS: &[u8] = b"dregg-multiway-tug/card-traits/v1";

/// The COMMITTED rarity weight table (a Rust const, so the distribution cannot be swapped
/// after the seed). One entry per [`CardRarity`], in tier order; sums to 100 so a foil is
/// the ~3% tail. This is the E2 "committed weight table" — provable rarity, not a claim.
pub const RARITY_WEIGHTS: [u64; 4] = [60, 25, 12, 3];

/// A printed card's collectible **rarity** — the tier of the committed-weight fair draw.
/// The rarity is a cosmetic/provenance trait, independent of the card's in-game influence
/// (that is fixed by its guild); a [`CardRarity::Foil`] is a genuine ~3% flex whose
/// provenance (the pack it was pulled from) anyone re-derives.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CardRarity {
    /// The common pull — `60%` of cards.
    Common,
    /// An uncommon pull — `25%` of cards.
    Uncommon,
    /// A rare pull — `12%` of cards.
    Rare,
    /// A foil pull — the ~`3%` tail. A provable flex.
    Foil,
}

impl CardRarity {
    /// The tier index into [`RARITY_WEIGHTS`] (and back, [`CardRarity::from_index`]).
    fn from_index(i: usize) -> CardRarity {
        match i {
            0 => CardRarity::Common,
            1 => CardRarity::Uncommon,
            2 => CardRarity::Rare,
            _ => CardRarity::Foil,
        }
    }

    /// A stable byte tag (folded into the commitments so the rarity is bound into the
    /// card's content address).
    fn tag(self) -> u8 {
        match self {
            CardRarity::Common => 0,
            CardRarity::Uncommon => 1,
            CardRarity::Rare => 2,
            CardRarity::Foil => 3,
        }
    }

    /// The human label.
    pub fn label(self) -> &'static str {
        match self {
            CardRarity::Common => "common",
            CardRarity::Uncommon => "uncommon",
            CardRarity::Rare => "rare",
            CardRarity::Foil => "foil",
        }
    }
}

/// A committed-weight draw — a CDF over ONE bounded draw at `index`, so a weighted tier
/// still costs exactly one draw inside the fixed procgen transcript. Crate-local (the
/// spec's E2 shape) so `dregg-dice` is untouched; the weights come from a committed const.
fn weighted_index(stream: &DrawStream, index: u32, weights: &[u64]) -> usize {
    let total: u64 = weights.iter().sum();
    debug_assert!(total > 0, "a committed weight table is non-empty");
    let roll = stream
        .draw_bounded(index, total)
        .expect("the rarity draw index is within the committed budget and the total > 0");
    let mut acc = 0u64;
    for (i, &w) in weights.iter().enumerate() {
        acc += w;
        if roll < acc {
            return i;
        }
    }
    weights.len() - 1
}

/// The deterministic **traits root** for a printed card — a domain-separated hash of the
/// guild, rarity, and art variant. This is the sprite-binding root the deterministic
/// renderer draws off (E1/E2): the same card content always yields the same root, so a
/// stranger re-renders the identical card.
pub fn card_traits_root(guild: u8, rarity: CardRarity, art_variant: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_CARD_TRAITS.len() as u64).to_le_bytes());
    h.update(DOMAIN_CARD_TRAITS);
    h.update(&[guild, rarity.tag()]);
    h.update(&art_variant.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Derive the **pack seed** for a booster from a committed beacon value, the pack label,
/// and a sequence — a domain-separated hash, so every booster draws a fresh, reproducible,
/// context-bound stream (and a verifier who holds the beacon + label + seq re-derives it).
pub fn derive_pack_seed(beacon: &CommittedSeed, pack_label: &str, seq: u64) -> CommittedSeed {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_PACK_SEED.len() as u64).to_le_bytes());
    h.update(DOMAIN_PACK_SEED);
    h.update(beacon.as_bytes());
    h.update(&(pack_label.len() as u64).to_le_bytes());
    h.update(pack_label.as_bytes());
    h.update(&seq.to_le_bytes());
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// A single printed card pulled from a pack: which guild it prints (and that guild's
/// in-game influence), its collectible rarity, its art variant, and the traits root those
/// fix. Content-addressed by the draw — [`reverify_pack`] re-derives it from the committed
/// pack seed alone, so a forged (fabricated / rewritten) card is caught.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CardDraw {
    /// The committed pack seed this card was drawn from ([`derive_pack_seed`]).
    pub pack_seed: CommittedSeed,
    /// The card's slot within the pack (`0..PACK_SIZE`).
    pub slot: u32,
    /// The guild this card prints (`0..N_GUILDS`) — the in-play favor it is a copy of.
    pub guild: u8,
    /// The guild's in-game influence weight (fixed by the guild; carried for convenience).
    pub influence: u8,
    /// The collectible rarity tier (the committed-weight fair draw).
    pub rarity: CardRarity,
    /// The art variant (`0..ART_VARIANTS`).
    pub art_variant: u64,
    /// The deterministic sprite-binding traits root ([`card_traits_root`]).
    pub traits_root: [u8; 32],
}

impl CardDraw {
    /// The card's **print identity** — an owner-and-pack-independent content id over just
    /// the guild, rarity, art variant, and traits root. Two cards of the same printed
    /// content share this id ("the same card"), while each owned copy has its own
    /// [`AssetId`]. The same card content addresses identically.
    pub fn content_id(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(&(DOMAIN_CARD_CONTENT.len() as u64).to_le_bytes());
        h.update(DOMAIN_CARD_CONTENT);
        h.update(&[self.guild, self.influence, self.rarity.tag()]);
        h.update(&self.art_variant.to_le_bytes());
        h.update(&self.traits_root);
        *h.finalize().as_bytes()
    }

    /// The display line for a card (the guild/rarity are content-bound).
    pub fn describe(&self) -> String {
        format!(
            "{} card of guild {} (influence {}, art {}) from pack {}",
            self.rarity.label(),
            self.guild,
            self.influence,
            self.art_variant,
            hex4(self.pack_seed.as_bytes())
        )
    }
}

/// Draw the card in `slot` from a pack's verified stream (a pure function of the seed).
fn draw_card(pack_seed: CommittedSeed, stream: &DrawStream, slot: u32) -> CardDraw {
    let base = slot * CARD_STRIDE;
    let guild = stream
        .draw_bounded(base + C_GUILD, N_GUILDS as u64)
        .expect("the guild draw index is within the committed budget and N_GUILDS > 0")
        as u8;
    let rarity = CardRarity::from_index(weighted_index(stream, base + C_RARITY, &RARITY_WEIGHTS));
    let art_variant = stream
        .draw_bounded(base + C_ART, ART_VARIANTS)
        .expect("the art draw index is within the committed budget and ART_VARIANTS > 0");
    let traits_root = card_traits_root(guild, rarity, art_variant);
    CardDraw {
        pack_seed,
        slot,
        guild,
        influence: INFLUENCE[guild as usize],
        rarity,
        art_variant,
        traits_root,
    }
}

/// A resolved, provably-fair pack: the beacon + label + seq it came from, the committed
/// pack seed it was drawn from, and its ordered [`CardDraw`]s. [`reverify_pack`] re-derives
/// the whole thing from the committed context alone, so a forged pull is caught before any
/// mint.
#[derive(Clone, Debug)]
pub struct Pack {
    /// The committed beacon value the pack is anchored to (its unpredictability root; in
    /// the flagship this is the verified drand-beacon day-seed).
    pub beacon: CommittedSeed,
    /// The pack label (e.g. `"season-1-booster"`), binding the product the cards came from.
    pub pack_label: String,
    /// The pack's sequence (distinct boosters under one beacon/label use distinct seqs).
    pub seq: u64,
    /// The committed pack seed the fair draws were taken from ([`derive_pack_seed`]).
    pub pack_seed: CommittedSeed,
    /// The pack's cards, slot-ordered.
    pub cards: Vec<CardDraw>,
}

impl Pack {
    /// The display line for a pack.
    pub fn describe(&self) -> String {
        format!(
            "pack `{}` #{} ({} cards) from beacon {}",
            self.pack_label,
            self.seq,
            self.cards.len(),
            hex4(self.beacon.as_bytes())
        )
    }
}

/// **Roll a real, provably-fair pack** under a committed beacon. Derives the committed pack
/// seed, runs the VERIFIED procgen stream, and draws [`PACK_SIZE`] cards. Deterministic in
/// `(beacon, pack_label, seq)` — the same context always re-derives the identical pack.
pub fn roll_pack(beacon: &CommittedSeed, pack_label: &str, seq: u64) -> Pack {
    let pack_seed = derive_pack_seed(beacon, pack_label, seq);
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&pack_seed);
    let cards = (0..PACK_SIZE as u32)
        .map(|slot| draw_card(pack_seed, &stream, slot))
        .collect();
    Pack {
        beacon: *beacon,
        pack_label: pack_label.to_string(),
        seq,
        pack_seed,
        cards,
    }
}

/// **Re-verify a pack is a real fair draw** — the tooth that refuses a forged pack-open.
/// Recomputes the pack seed from the claimed beacon/label/seq (a mismatch = a forged
/// context) and re-derives every card from that committed seed, requiring the claimed pack
/// to be EXACTLY the fair draw's (its seed, its card count, and every card). A fabricated
/// pull — a card rewritten to a foil the seed never made — fails here.
pub fn reverify_pack(pack: &Pack) -> Result<(), PackError> {
    let honest = roll_pack(&pack.beacon, &pack.pack_label, pack.seq);
    if honest.pack_seed != pack.pack_seed {
        return Err(PackError::Forged(
            "the pack seed is not bound to the claimed beacon/label/seq".to_string(),
        ));
    }
    if pack.cards.len() != honest.cards.len() {
        return Err(PackError::Forged(format!(
            "the pack has {} cards, the fair draw has {}",
            pack.cards.len(),
            honest.cards.len()
        )));
    }
    for (i, (claimed, real)) in pack.cards.iter().zip(honest.cards.iter()).enumerate() {
        if claimed != real {
            return Err(PackError::Forged(format!(
                "card {i} is not the fair draw (claimed {} of guild {}, real {} of guild {})",
                claimed.rarity.label(),
                claimed.guild,
                real.rarity.label(),
                real.guild
            )));
        }
    }
    Ok(())
}

/// A card's **content commitment** — the mint seed the owned asset is minted under, binding
/// the pack seed, the slot, the guild, the rarity, the art variant, and the traits root.
/// The [`dreggnet_asset::AssetId`] is derived from `blake3(opener_pk ‖ this)`, so the owned
/// card's content address itself encodes the drawn card (its provenance + its traits).
fn card_commitment(card: &CardDraw) -> Vec<u8> {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_CARD_COMMIT.len() as u64).to_le_bytes());
    h.update(DOMAIN_CARD_COMMIT);
    h.update(card.pack_seed.as_bytes());
    h.update(&card.slot.to_le_bytes());
    h.update(&[card.guild, card.influence, card.rarity.tag()]);
    h.update(&card.art_variant.to_le_bytes());
    h.update(&card.traits_root);
    h.finalize().as_bytes().to_vec()
}

/// A minted card — a real owned [`dreggnet_asset`] note. Its [`AssetId`] is content-
/// addressed to the drawn card + the opener's key; its [`content_id`](CardItem::content_id)
/// is the owner-independent print identity.
#[derive(Clone, Debug)]
pub struct CardItem {
    /// The stable, content-addressed asset id (the cross-cell handle a market names it by).
    pub asset_id: AssetId,
    /// The guild the card prints.
    pub guild: u8,
    /// The card's collectible rarity.
    pub rarity: CardRarity,
    /// The owner-independent print identity (two copies of one card share it).
    pub content_id: [u8; 32],
    /// The current owner's pubkey (at mint, the opener's key).
    pub owner: [u8; 32],
}

/// The provenance of a minted card — the committed pack seed + slot it was pulled from,
/// the guild/rarity it prints, its print identity, and the asset layer's own on-chain
/// provenance re-verification.
#[derive(Clone, Debug)]
pub struct CardProvenance {
    /// The committed pack seed the card was drawn from (its booster provenance root — a
    /// verifier who holds the beacon/label/seq re-derives it via [`derive_pack_seed`]).
    pub pack_seed: CommittedSeed,
    /// The card's slot within the pack.
    pub slot: u32,
    /// The guild the card prints.
    pub guild: u8,
    /// The card's rarity.
    pub rarity: CardRarity,
    /// The owner-independent print identity.
    pub content_id: [u8; 32],
    /// The asset layer's provenance report (the note lineage re-verifies, current owner).
    pub asset: ProvenanceReport,
}

/// Why a pack / card operation could not complete.
#[derive(Clone, Debug)]
pub enum PackError {
    /// The claimed pack is not a real fair draw (a fabricated / rewritten pull) — no card
    /// is minted. Carries the exact mismatch.
    Forged(String),
    /// This exact pack has already been opened (a pack mints its cards exactly once).
    AlreadyOpened,
    /// The underlying asset layer refused the operation (a non-owner / double-spend
    /// transfer, or an unknown asset). Carries the asset error.
    Asset(AssetError),
}

impl std::fmt::Display for PackError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PackError::Forged(why) => write!(f, "forged pack-open refused: {why}"),
            PackError::AlreadyOpened => write!(f, "this pack was already opened"),
            PackError::Asset(e) => write!(f, "asset layer refused: {e}"),
        }
    }
}

impl std::error::Error for PackError {}

/// **The card vault** — the open / transfer / provenance surface over a set of sovereign
/// player ledgers ([`dreggnet_asset::AssetWorld`]). Opening a verified pack mints real owned
/// cards; the player transfers them under the asset layer's cryptographic owner-gate; a
/// forged pack-open is refused before any mint.
pub struct CardVault {
    world: AssetWorld,
    /// AssetId bytes -> the (card, content id) it was minted from (its provenance record).
    cards: HashMap<[u8; 32], (CardDraw, [u8; 32])>,
    /// The pack seeds already opened (a pack mints its cards exactly once).
    opened: HashSet<[u8; 32]>,
}

impl Default for CardVault {
    fn default() -> Self {
        Self::new()
    }
}

impl CardVault {
    /// A fresh card vault (no players, no cards).
    pub fn new() -> Self {
        CardVault {
            world: AssetWorld::new(),
            cards: HashMap::new(),
            opened: HashSet::new(),
        }
    }

    /// The deterministic pubkey of a player label (creating the identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.world.pubkey_of(label)
    }

    /// **Open a pack as real owned cards** — the forged-pack gate + the mint. The pack is
    /// re-verified as a real fair draw ([`reverify_pack`]); a forged pack-open is refused
    /// with NO mint. A verified pack mints one [`dreggnet_asset`] note per card, owned by
    /// `opener`, under each card's content commitment — so a card's [`AssetId`] is bound to
    /// the pack + slot it was pulled from. A pack opens exactly once.
    pub fn open(&mut self, opener: &str, pack: &Pack) -> Result<Vec<CardItem>, PackError> {
        // The tooth: a forged pack-open (a rewritten / fabricated pull) is refused BEFORE
        // any mint.
        reverify_pack(pack)?;

        if !self.opened.insert(*pack.pack_seed.as_bytes()) {
            return Err(PackError::AlreadyOpened);
        }

        let mut items = Vec::with_capacity(pack.cards.len());
        for card in &pack.cards {
            // The mint seed IS the card's content commitment, so the asset id encodes the
            // drawn card (its pack provenance + its traits).
            let commit = card_commitment(card);
            let asset_id = self.world.mint(opener, &commit);
            let content_id = card.content_id();
            self.cards
                .insert(asset_id.bytes(), (card.clone(), content_id));
            let owner = self
                .world
                .current_owner(asset_id)
                .expect("a freshly-minted card has an owner");
            items.push(CardItem {
                asset_id,
                guild: card.guild,
                rarity: card.rarity,
                content_id,
                owner,
            });
        }
        Ok(items)
    }

    /// **Transfer a card** from `from` to `to` — the asset layer's owner-gated transfer (the
    /// tradeable primitive; the trustless swap over it is `dreggnet-trade`). A non-owner
    /// `from` is a real cryptographic refusal ([`PackError::Asset`] wrapping
    /// [`AssetError::Refused`]); an owner's transfer spends the current version and mints a
    /// successor owned by `to`.
    pub fn transfer(
        &mut self,
        asset_id: AssetId,
        from: &str,
        to: &str,
    ) -> Result<TransferReceipt, PackError> {
        self.world
            .transfer(asset_id, from, to)
            .map_err(PackError::Asset)
    }

    /// The current owner's pubkey of a card.
    pub fn owner_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.world.current_owner(asset_id)
    }

    /// The rarity of a card (from its recorded draw).
    pub fn rarity_of(&self, asset_id: AssetId) -> Option<CardRarity> {
        self.cards.get(&asset_id.bytes()).map(|(c, _)| c.rarity)
    }

    /// The guild a card prints (from its recorded draw).
    pub fn guild_of(&self, asset_id: AssetId) -> Option<u8> {
        self.cards.get(&asset_id.bytes()).map(|(c, _)| c.guild)
    }

    /// The owner-independent print identity of a card (two copies of one card share it).
    pub fn content_id_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.cards.get(&asset_id.bytes()).map(|(_, cid)| *cid)
    }

    /// The full provenance of a card — the pack + fair draw it was pulled from, plus the
    /// asset layer's own lineage re-verification (`None` if this asset was not minted here).
    pub fn provenance(&self, asset_id: AssetId) -> Option<CardProvenance> {
        let (card, content_id) = self.cards.get(&asset_id.bytes())?;
        Some(CardProvenance {
            pack_seed: card.pack_seed,
            slot: card.slot,
            guild: card.guild,
            rarity: card.rarity,
            content_id: *content_id,
            asset: self.world.verify_provenance(asset_id),
        })
    }

    /// Re-verify a card's asset-layer provenance chain (the note lineage + on-chain spent
    /// re-reads) — the same executor-refereed check `dreggnet-asset` exposes.
    pub fn verify_asset_provenance(&self, asset_id: AssetId) -> ProvenanceReport {
        self.world.verify_provenance(asset_id)
    }

    /// How many distinct cards this vault has minted (the anti-ghost witness: a refused
    /// forged pack-open mints NOTHING, so it does not move this count).
    pub fn card_count(&self) -> usize {
        self.cards.len()
    }
}

/// A short hex fingerprint of a seed's first four bytes (for a display line).
fn hex4(bytes: &[u8; 32]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    //! CARDS-AS-ASSETS + PROVABLY-FAIR PACKS, DRIVEN on the real asset layer: opening a
    //! pack mints real OWNED, content-addressed cards whose provenance binds the pack; a
    //! foil vs a common is decided by the committed-weight fair draw; a card TRANSFERS
    //! under the owner-gate (a non-owner cannot); a forged pack-open is REFUSED with no
    //! mint; the same card content addresses identically and a different seed yields
    //! different cards.
    use super::*;

    /// A committed beacon standing in for a season day-seed (the verified drand day-seed in
    /// the flagship).
    fn beacon(byte: u8) -> CommittedSeed {
        CommittedSeed::from_bytes([byte; 32])
    }

    /// Scan for a (beacon, seq) whose pack contains at least one card of the target rarity
    /// (the draw is a pure function of the context, so this scans the deterministic space).
    fn find_pack_with(label: &str, want: CardRarity) -> Pack {
        for b in 0u16..=255 {
            for seq in 0u64..8 {
                let p = roll_pack(&beacon(b as u8), label, seq);
                if p.cards.iter().any(|c| c.rarity == want) {
                    return p;
                }
            }
        }
        panic!("no pack in the scanned space contains a {want:?}");
    }

    /// Opening a pack MINTS real owned, content-addressed cards whose provenance binds the
    /// pack, and each re-verifies on the asset layer.
    #[test]
    fn opening_a_pack_mints_real_owned_cards() {
        let mut vault = CardVault::new();
        let pack = roll_pack(&beacon(7), "season-1-booster", 0);
        assert_eq!(pack.cards.len(), PACK_SIZE, "a full pack");

        let alice_pk = vault.pubkey_of("alice");
        let items = vault.open("alice", &pack).expect("a real pack opens");
        assert_eq!(items.len(), PACK_SIZE, "one card minted per slot");

        for (item, card) in items.iter().zip(pack.cards.iter()) {
            // The opener OWNS each card (their key), and it is content-addressed.
            assert_eq!(
                item.owner, alice_pk,
                "the card is owned by the opener's key"
            );
            assert_eq!(
                vault.owner_of(item.asset_id),
                Some(alice_pk),
                "the asset layer agrees the opener is the owner"
            );
            assert_eq!(item.guild, card.guild, "the minted card is the drawn guild");
            assert_eq!(
                item.rarity, card.rarity,
                "the minted card is the drawn rarity"
            );

            // The asset lineage re-verifies (a fresh mint is a length-1 lineage).
            let prov = vault.verify_asset_provenance(item.asset_id);
            assert!(
                prov.verified,
                "the card lineage re-verifies: {:?}",
                prov.reasons
            );
            assert_eq!(prov.length, 1, "a fresh mint is a length-1 lineage");
        }
        // Every slot minted a distinct owned asset (distinct copies).
        let ids: HashSet<[u8; 32]> = items.iter().map(|i| i.asset_id.bytes()).collect();
        assert_eq!(ids.len(), PACK_SIZE, "distinct owned assets per card");
    }

    /// A FOIL vs a COMMON is decided by the committed-weight FAIR DRAW — the rarity is the
    /// draw's distribution off the committed seed, re-derivable by anyone, not a claim.
    #[test]
    fn a_foil_vs_a_common_is_the_fair_draw() {
        let label = "rarity-probe";
        let foil_pack = find_pack_with(label, CardRarity::Foil);
        let common_pack = find_pack_with(label, CardRarity::Common);

        // The pulls re-derive from the committed context — un-fakeable.
        reverify_pack(&foil_pack).expect("the foil pack is a real fair draw");
        reverify_pack(&common_pack).expect("the common pack is a real fair draw");

        let foil = foil_pack
            .cards
            .iter()
            .find(|c| c.rarity == CardRarity::Foil)
            .expect("a genuine foil pull");
        let common = common_pack
            .cards
            .iter()
            .find(|c| c.rarity == CardRarity::Common)
            .expect("a genuine common pull");

        // Both mint real owned cards; their recorded rarity is the re-derivable tier.
        let mut vault = CardVault::new();
        let foils = vault
            .open("collector", &foil_pack)
            .expect("the foil pack opens");
        let commons = vault
            .open("collector", &common_pack)
            .expect("the common pack opens");
        let foil_item = foils
            .iter()
            .find(|i| i.rarity == CardRarity::Foil)
            .expect("the foil minted");
        let common_item = commons
            .iter()
            .find(|i| i.rarity == CardRarity::Common)
            .expect("the common minted");
        assert_eq!(vault.rarity_of(foil_item.asset_id), Some(CardRarity::Foil));
        assert_eq!(
            vault.rarity_of(common_item.asset_id),
            Some(CardRarity::Common)
        );
        assert_eq!(foil.guild, foil_item.guild);
        assert_eq!(common.guild, common_item.guild);
        // Distinct pulls -> distinct content-addressed assets.
        assert_ne!(
            foil_item.asset_id.bytes(),
            common_item.asset_id.bytes(),
            "different cards are different owned assets"
        );
    }

    /// A minted card TRANSFERS under the asset layer's owner-gate (the tradeable primitive):
    /// an owner's transfer moves it; a NON-OWNER transfer is a real cryptographic refusal.
    #[test]
    fn a_card_transfers_owner_gated_and_a_non_owner_cannot() {
        let mut vault = CardVault::new();
        let pack = roll_pack(&beacon(9), "trade-booster", 0);
        let alice_pk = vault.pubkey_of("alice");
        let bob_pk = vault.pubkey_of("bob");

        let items = vault.open("alice", &pack).expect("alice opens the pack");
        let card = &items[0];
        assert_eq!(vault.owner_of(card.asset_id), Some(alice_pk));

        // A NON-OWNER (mallory) cannot transfer alice's card — a real refusal.
        let forged = vault.transfer(card.asset_id, "mallory", "eve");
        assert!(
            matches!(forged, Err(PackError::Asset(AssetError::Refused(_)))),
            "a non-owner transfer is refused by the owner-gate, got {forged:?}"
        );
        assert_eq!(
            vault.owner_of(card.asset_id),
            Some(alice_pk),
            "anti-ghost: the card still belongs to alice"
        );

        // The OWNER can transfer it — it moves to bob.
        vault
            .transfer(card.asset_id, "alice", "bob")
            .expect("the owner's transfer commits");
        assert_eq!(
            vault.owner_of(card.asset_id),
            Some(bob_pk),
            "the card is now bob's"
        );
        // The provenance chain still re-verifies after the transfer (a 2-version lineage).
        let prov = vault.verify_asset_provenance(card.asset_id);
        assert!(
            prov.verified,
            "post-transfer lineage verifies: {:?}",
            prov.reasons
        );
        assert_eq!(prov.length, 2, "mint + one transfer = two versions");
    }

    /// A FORGED pack-open — a pull rewritten to a foil the seed never produced — is REFUSED
    /// with no mint. Non-vacuous: the honest pack then opens.
    #[test]
    fn a_forged_pack_open_mints_nothing() {
        let mut vault = CardVault::new();
        let honest = roll_pack(&beacon(3), "vault-booster", 0);

        // FORGE a foil: rewrite one card to a foil tier the seed never gave it (and rebuild
        // its traits root so the card is internally consistent — only the fair draw is not).
        let mut forged = honest.clone();
        let victim = forged
            .cards
            .iter_mut()
            .find(|c| c.rarity != CardRarity::Foil)
            .expect("some non-foil card to fake");
        victim.rarity = CardRarity::Foil;
        victim.traits_root = card_traits_root(victim.guild, victim.rarity, victim.art_variant);

        let out = vault.open("cheater", &forged);
        assert!(
            matches!(out, Err(PackError::Forged(_))),
            "a fabricated foil is refused, got {out:?}"
        );
        // Anti-ghost: the refused forged pack minted NOTHING.
        assert_eq!(
            vault.card_count(),
            0,
            "no card was minted for the forged pack"
        );

        // The HONEST pack still opens (the tooth is not vacuously rejecting everything).
        let items = vault
            .open("cheater", &honest)
            .expect("the honest pack opens");
        assert_eq!(items.len(), PACK_SIZE);
        assert_eq!(
            vault.card_count(),
            PACK_SIZE,
            "exactly the honest pack's cards"
        );
    }

    /// A pack opens exactly once: re-opening the same pack is refused (no double-mint).
    #[test]
    fn a_pack_opens_exactly_once() {
        let mut vault = CardVault::new();
        let pack = roll_pack(&beacon(5), "once-booster", 0);
        let first = vault.open("p", &pack).expect("first open mints");
        assert_eq!(first.len(), PACK_SIZE);
        let second = vault.open("p", &pack);
        assert!(
            matches!(second, Err(PackError::AlreadyOpened)),
            "re-opening the same pack is refused, got {second:?}"
        );
        assert_eq!(
            vault.card_count(),
            PACK_SIZE,
            "the re-open minted no extra cards"
        );
    }

    /// The SAME card content addresses identically, and DIFFERENT seeds yield different
    /// cards. Re-rolling the same pack re-derives byte-identical cards; two copies of one
    /// printed card share a content id while holding distinct owned asset ids.
    #[test]
    fn same_card_content_addresses_identically_different_seed_differs() {
        // (a) Re-rolling the same pack re-derives byte-identical cards.
        let p1 = roll_pack(&beacon(11), "id-booster", 2);
        let p2 = roll_pack(&beacon(11), "id-booster", 2);
        assert_eq!(
            p1.cards, p2.cards,
            "the same pack re-derives identical cards"
        );

        // (b) A different seed (a different seq) yields different cards.
        let mut differ = None;
        for seq in 0u64..64 {
            let q = roll_pack(&beacon(11), "id-booster", seq);
            if q.cards != p1.cards {
                differ = Some(q);
                break;
            }
        }
        let q = differ.expect("some other seq yields a different pack");
        let ids1: Vec<[u8; 32]> = p1.cards.iter().map(|c| c.content_id()).collect();
        let idsq: Vec<[u8; 32]> = q.cards.iter().map(|c| c.content_id()).collect();
        assert_ne!(ids1, idsq, "a different seed yields different card content");

        // (c) Two copies of ONE printed card share a content id but hold distinct asset ids.
        // Find two cards (across the deterministic space) of identical printed content.
        let mut vault = CardVault::new();
        let mut by_content: HashMap<[u8; 32], CardDraw> = HashMap::new();
        let mut pair: Option<(CardDraw, CardDraw)> = None;
        'scan: for b in 0u16..=255 {
            let pk = roll_pack(&beacon(b as u8), "id-booster", 0);
            for c in &pk.cards {
                let cid = c.content_id();
                if let Some(prev) = by_content.get(&cid) {
                    if prev.pack_seed != c.pack_seed {
                        pair = Some((prev.clone(), c.clone()));
                        break 'scan;
                    }
                } else {
                    by_content.insert(cid, c.clone());
                }
            }
        }
        let (c_a, c_b) = pair.expect("two copies of one printed card exist in the space");
        assert_eq!(
            c_a.content_id(),
            c_b.content_id(),
            "two copies of one card share a content id"
        );
        // Mint both (as single-card packs would; open their real packs) and confirm the
        // owned copies are DISTINCT assets sharing the print identity.
        let pack_a = roll_pack_containing(&c_a);
        let pack_b = roll_pack_containing(&c_b);
        let items_a = vault.open("owner-a", &pack_a).expect("pack a opens");
        let items_b = vault.open("owner-b", &pack_b).expect("pack b opens");
        let mint_a = items_a
            .iter()
            .find(|i| i.content_id == c_a.content_id())
            .expect("copy a minted");
        let mint_b = items_b
            .iter()
            .find(|i| i.content_id == c_b.content_id())
            .expect("copy b minted");
        assert_eq!(
            mint_a.content_id, mint_b.content_id,
            "the two owned copies share the print identity"
        );
        assert_ne!(
            mint_a.asset_id.bytes(),
            mint_b.asset_id.bytes(),
            "each owned copy is a distinct asset"
        );
    }

    /// Re-roll the pack a card came from (its pack_seed identifies the booster; we recover
    /// the beacon/label/seq by the scan that found it — here we just re-roll the whole
    /// space to locate the matching pack for minting).
    fn roll_pack_containing(card: &CardDraw) -> Pack {
        for b in 0u16..=255 {
            let pk = roll_pack(&beacon(b as u8), "id-booster", 0);
            if pk.pack_seed == card.pack_seed {
                return pk;
            }
        }
        panic!("the card's pack is in the scanned space");
    }
}
