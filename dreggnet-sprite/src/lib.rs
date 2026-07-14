//! # `dreggnet-sprite` — the deterministic generative asset → SVG sprite renderer.
//!
//! The visual layer, in-house. A [`dreggnet_asset::AssetId`] (a blake3 content
//! address, `dreggnet-asset/src/lib.rs:101`) is turned into a composed **vector SVG**
//! sprite by a pure, deterministic function:
//!
//! ```text
//!   AssetId bytes ──derive_key──▶ Seed ──dregg-dice DrawStream──▶ trait vector ──▶ layered SVG
//! ```
//!
//! ## Why deterministic (the whole point)
//!
//! The house norm is byte-identical replay — a stranger re-executes and re-derives
//! the same bytes. A sprite must ride that: **same asset ⇒ byte-identical SVG**, so
//! anyone re-renders the identical art and can *verify* it, and **a different
//! [`AssetId`] ⇒ a (near-certainly) different sprite**. There are no floats or
//! trig in the geometry and no unordered iteration, so the emitted string is a pure
//! function of the trait vector on every platform.
//!
//! ## The trait vector (derived, not stored)
//!
//! Traits are derived FROM the asset's existing content address — the [`AssetId`]
//! bytes seed a real [`dregg_dice::DrawStream`], and each trait axis is one indexed
//! draw off it. **No `NoteDesc` field is added this pass** (the AssetId derivation is
//! TCB; the first-class `trait_root` identity field is the named **E1** follow-up).
//! Rarity is the one axis drawn by the **E2** provably-fair [`DrawStream::weighted`]
//! draw over the committed [`RARITY_WEIGHTS`] table — so "this is a legendary" is
//! re-derivable from the committed seed + committed weights, not a claim. Rarity
//! visibly drives the art: [`Rarity::glows`] adds a colored glow, [`Rarity::gilds`]
//! gilds a legendary.
//!
//! ## Kinds
//!
//! Two tasteful, parametric sprite kinds ship: a **gear** (a weapon/blade emblem,
//! [`render_gear`]) and a **card** (a sigil/emblem card, [`render_card`]). Each is a
//! composed stack of layered `<g>` groups (background, shape, detail, glow, gild), and
//! each trait axis measurably changes the geometry.
//!
//! ## Honest scope
//!
//! REAL here: the deterministic Rust `trait → SVG` renderer (ours, reproducible),
//! ≥2 kinds, parametric, plus the E2 weighted rarity draw (`dregg-dice`). NAMED NEXT:
//! **E1** the first-class asset `trait_root` field (a careful TCB pass, riding the
//! `mint_seed`, non-breaking); **E3** a wasm `traitsJson()` getter + a `<dregg-sprite>`
//! custom element rendering the SVG in a closed shadow; wiring the sprite into the
//! deos `Tile{handle}` node (`deos-view/src/tree.rs:223`) / the inventory surface;
//! and richer art.

use dregg_dice::{DrawStream, Seed};
use dreggnet_asset::AssetId;

mod card;
mod gear;
mod svg;

pub use card::{CardTraits, render_card_from};
pub use gear::{GearTraits, render_gear_from};

/// The domain tag separating the sprite Seed derivation from every other use of the
/// AssetId bytes (so the sprite draw stream is independent of any game randomness).
pub const SPRITE_SEED_DOMAIN: &str = "dreggnet-sprite-seed-v1";

/// The number of draw indices the sprite stream exposes — headroom over the trait axes
/// either kind consumes (gear/card use `< 12`).
pub const SPRITE_DRAW_COUNT: u32 = 16;

/// The **committed** rarity weight table (E2). Tier `i` is drawn with probability
/// `RARITY_WEIGHTS[i] / Σ`. A `const` so the weights cannot be swapped after the seed
/// is fixed — the commitment that makes rarity *provable*. Legendary sits at the tail
/// (`6 / 1616 ≈ 0.37%`), re-derivable by anyone from the seed + this table.
pub const RARITY_WEIGHTS: [u64; 5] = [1000, 420, 150, 40, 6];

/// The five rarity tiers, in ascending order. Drawn by the committed provably-fair
/// [`DrawStream::weighted`] draw over [`RARITY_WEIGHTS`]; drives the sprite's glow/gild.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rarity {
    Common,
    Uncommon,
    Rare,
    Epic,
    Legendary,
}

impl Rarity {
    /// The tier for a weighted-draw result index (`0..5`), saturating at legendary.
    pub fn from_index(i: usize) -> Rarity {
        match i {
            0 => Rarity::Common,
            1 => Rarity::Uncommon,
            2 => Rarity::Rare,
            3 => Rarity::Epic,
            _ => Rarity::Legendary,
        }
    }

    /// The tier index (`0` = common … `4` = legendary).
    pub fn tier(self) -> u8 {
        self as u8
    }

    /// A stable lowercase tier name (used as the `data-rarity` attribute + in tests).
    pub fn name(self) -> &'static str {
        svg::RARITY_NAMES[self as usize]
    }

    /// The tier's signature color (border / glow / gild accents).
    pub fn color(self) -> &'static str {
        svg::RARITY_COLORS[self as usize]
    }

    /// Whether the sprite carries a colored glow layer (rare and above).
    pub fn glows(self) -> bool {
        (self as u8) >= (Rarity::Rare as u8)
    }

    /// Whether the sprite is gilded (a legendary — the gold outline overlay).
    pub fn gilds(self) -> bool {
        self == Rarity::Legendary
    }
}

/// The sprite kind a given asset renders as.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AssetKind {
    /// A weapon / blade emblem.
    Gear,
    /// A sigil / emblem card.
    Card,
}

/// Build the sprite draw stream for an asset: the [`AssetId`] bytes are domain-separated
/// into a [`Seed`] and expanded into a [`SPRITE_DRAW_COUNT`]-index [`DrawStream`]. Pure
/// function of the content address, so the whole trait vector is re-derivable.
fn sprite_stream(asset: &AssetId) -> DrawStream {
    let seed = Seed::from_bytes(blake3::derive_key(SPRITE_SEED_DOMAIN, &asset.bytes()));
    DrawStream::new(seed, SPRITE_DRAW_COUNT)
}

/// A single bounded draw off the sprite stream. Infallible by construction: every
/// caller uses an index `< SPRITE_DRAW_COUNT` and a bound `> 0`.
fn axis(stream: &DrawStream, index: u32, n: u64) -> u64 {
    stream
        .draw_bounded(index, n)
        .expect("sprite axis index < SPRITE_DRAW_COUNT and bound > 0")
}

/// Draw the rarity tier for an asset: the E2 provably-fair [`DrawStream::weighted`]
/// draw at index 0 over the committed [`RARITY_WEIGHTS`]. Re-derivable by anyone from
/// the seed + the committed table.
pub fn rarity_of(asset: &AssetId) -> Rarity {
    let stream = sprite_stream(asset);
    let i = stream
        .weighted(0, &RARITY_WEIGHTS)
        .expect("RARITY_WEIGHTS is a non-empty, non-overflowing committed table");
    Rarity::from_index(i)
}

/// Derive the full **gear** trait vector for an asset (see [`GearTraits`]).
pub fn gear_traits(asset: &AssetId) -> GearTraits {
    let s = sprite_stream(asset);
    GearTraits {
        rarity: rarity_of(asset),
        blade: axis(&s, 1, gear::BLADE_SHAPES) as u8,
        material: axis(&s, 2, svg::GEAR_MATERIALS.len() as u64) as u8,
        rune: axis(&s, 3, gear::RUNE_GLYPHS + 1) as u8, // 0 = no rune
        guard: axis(&s, 4, gear::GUARD_STYLES) as u8,
        notches: axis(&s, 5, gear::MAX_NOTCHES + 1) as u8, // 0..=MAX_NOTCHES
        gem: axis(&s, 6, svg::GEM_COLORS.len() as u64) as u8,
        mark: axis(&s, 7, 16) as u8, // a 4-bit maker's mark
    }
}

/// Derive the full **card** trait vector for an asset (see [`CardTraits`]).
pub fn card_traits(asset: &AssetId) -> CardTraits {
    let s = sprite_stream(asset);
    CardTraits {
        rarity: rarity_of(asset),
        frame: axis(&s, 1, card::FRAME_STYLES) as u8,
        emblem: axis(&s, 2, card::EMBLEMS) as u8,
        palette: axis(&s, 3, svg::CARD_PALETTES.len() as u64) as u8,
        pips: (axis(&s, 4, card::MAX_PIPS - card::MIN_PIPS + 1) + card::MIN_PIPS) as u8,
        accent: axis(&s, 5, svg::GEM_COLORS.len() as u64) as u8,
    }
}

/// Render an asset as a **gear** SVG sprite — the deterministic composed vector art.
pub fn render_gear(asset: &AssetId) -> String {
    render_gear_from(&gear_traits(asset))
}

/// Render an asset as a **card** SVG sprite — the deterministic composed vector art.
pub fn render_card(asset: &AssetId) -> String {
    render_card_from(&card_traits(asset))
}

/// Render an asset as the requested [`AssetKind`].
pub fn render(kind: AssetKind, asset: &AssetId) -> String {
    match kind {
        AssetKind::Gear => render_gear(asset),
        AssetKind::Card => render_card(asset),
    }
}
