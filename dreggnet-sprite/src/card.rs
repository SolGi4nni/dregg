//! The **card** sprite: a sigil / emblem card, composed from the card trait vector.

use crate::Rarity;
use crate::svg::{self, CARD_PALETTES, GEM_COLORS};

/// Number of frame styles (plain, ornate, jagged).
pub const FRAME_STYLES: u64 = 3;
/// Number of central emblems (star, diamond, moon, flame, eye, sunburst).
pub const EMBLEMS: u64 = 6;
/// Minimum rank pips along the base.
pub const MIN_PIPS: u64 = 2;
/// Maximum rank pips along the base.
pub const MAX_PIPS: u64 = 6;

/// The card (emblem) trait vector — each axis is one indexed draw off the asset's sprite
/// stream (`rarity` via the committed weighted draw). Every field visibly changes the SVG.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CardTraits {
    /// The provably-fair rarity tier (drives glow + gild).
    pub rarity: Rarity,
    /// Frame style, `0..FRAME_STYLES`.
    pub frame: u8,
    /// Central emblem, `0..EMBLEMS`.
    pub emblem: u8,
    /// Panel palette, indexes [`CARD_PALETTES`].
    pub palette: u8,
    /// Rank pips along the base, `MIN_PIPS..=MAX_PIPS`.
    pub pips: u8,
    /// Emblem accent color, indexes [`GEM_COLORS`].
    pub accent: u8,
}

impl CardTraits {
    /// A stable hex fingerprint of the trait vector (the `data-traits` attribute).
    pub fn fingerprint(&self) -> String {
        svg::hex(&[
            self.rarity.tier(),
            self.frame,
            self.emblem,
            self.palette,
            self.pips,
            self.accent,
        ])
    }
}

/// The frame fragment (border geometry) for the given style.
fn frame_fragment(frame: u8, rarity_c: &str) -> String {
    match frame % (FRAME_STYLES as u8) {
        // plain — single rounded border
        0 => format!(
            "<rect x=\"10\" y=\"10\" width=\"108\" height=\"108\" rx=\"12\" fill=\"none\" stroke=\"{rarity_c}\" stroke-width=\"3\"/>"
        ),
        // ornate — double border with corner studs
        1 => format!(
            "<rect x=\"8\" y=\"8\" width=\"112\" height=\"112\" rx=\"14\" fill=\"none\" stroke=\"{rarity_c}\" stroke-width=\"3\"/>\
<rect x=\"15\" y=\"15\" width=\"98\" height=\"98\" rx=\"9\" fill=\"none\" stroke=\"{rarity_c}\" stroke-width=\"1\" opacity=\"0.7\"/>\
<circle cx=\"15\" cy=\"15\" r=\"3\" fill=\"{rarity_c}\"/><circle cx=\"113\" cy=\"15\" r=\"3\" fill=\"{rarity_c}\"/>\
<circle cx=\"15\" cy=\"113\" r=\"3\" fill=\"{rarity_c}\"/><circle cx=\"113\" cy=\"113\" r=\"3\" fill=\"{rarity_c}\"/>"
        ),
        // jagged — a zigzag/beveled border outline
        _ => format!(
            "<path d=\"M22 10 L106 10 L118 22 L118 106 L106 118 L22 118 L10 106 L10 22 Z\" fill=\"none\" stroke=\"{rarity_c}\" stroke-width=\"3\" stroke-linejoin=\"round\"/>"
        ),
    }
}

/// The central emblem fragment (centered ≈ (64,58)).
fn emblem_fragment(emblem: u8, color: &str, accent: &str) -> String {
    match emblem % (EMBLEMS as u8) {
        // 5-point star
        0 => format!(
            "<path d=\"M64 30 L71 51 L93 51 L75 64 L82 85 L64 72 L46 85 L53 64 L35 51 L57 51 Z\" fill=\"{color}\" stroke=\"{accent}\" stroke-width=\"1.5\" stroke-linejoin=\"round\"/>"
        ),
        // diamond / gem
        1 => format!(
            "<path d=\"M64 28 L86 58 L64 92 L42 58 Z\" fill=\"{color}\" stroke=\"{accent}\" stroke-width=\"1.5\" stroke-linejoin=\"round\"/>\
<path d=\"M42 58 L86 58 M64 28 L64 92\" stroke=\"{accent}\" stroke-width=\"1\" opacity=\"0.7\"/>"
        ),
        // crescent moon
        2 => format!(
            "<path d=\"M80 34 A 26 26 0 1 0 80 82 A 20 20 0 1 1 80 34 Z\" fill=\"{color}\" stroke=\"{accent}\" stroke-width=\"1.5\"/>"
        ),
        // flame
        3 => format!(
            "<path d=\"M64 28 C 50 46 74 54 64 70 C 60 62 54 74 62 86 C 80 78 84 54 72 44 C 72 54 68 48 64 28 Z\" fill=\"{color}\" stroke=\"{accent}\" stroke-width=\"1.5\" stroke-linejoin=\"round\"/>"
        ),
        // eye
        4 => format!(
            "<path d=\"M34 58 Q64 32 94 58 Q64 84 34 58 Z\" fill=\"{color}\" stroke=\"{accent}\" stroke-width=\"1.5\"/>\
<circle cx=\"64\" cy=\"58\" r=\"11\" fill=\"{accent}\"/><circle cx=\"64\" cy=\"58\" r=\"5\" fill=\"#0d1017\"/>"
        ),
        // sunburst
        _ => format!(
            "<circle cx=\"64\" cy=\"58\" r=\"16\" fill=\"{color}\" stroke=\"{accent}\" stroke-width=\"1.5\"/>\
<path d=\"M64 30 L64 40 M64 76 L64 86 M36 58 L46 58 M82 58 L92 58 M44 38 L51 45 M84 72 L77 65 M84 44 L77 51 M44 78 L51 71\" stroke=\"{accent}\" stroke-width=\"2\" stroke-linecap=\"round\"/>"
        ),
    }
}

/// The rank-pip row along the base (horizontal, integer-spaced — no trig).
fn pips_fragment(pips: u8, color: &str) -> String {
    let n = (pips as u64).clamp(MIN_PIPS, MAX_PIPS) as u32;
    let start = 64 - (n - 1) * 5; // integer-centered, 10px spacing
    let mut out = String::new();
    for i in 0..n {
        let cx = start + i * 10;
        out.push_str(&format!(
            "<circle cx=\"{cx}\" cy=\"104\" r=\"2.5\" fill=\"{color}\"/>"
        ));
    }
    out
}

/// Render a card sprite from an explicit trait vector — the deterministic composed SVG.
pub fn render_card_from(t: &CardTraits) -> String {
    let pal = &CARD_PALETTES[(t.palette as usize) % CARD_PALETTES.len()];
    let accent = GEM_COLORS[(t.accent as usize) % GEM_COLORS.len()];
    let rarity_c = t.rarity.color();

    let mut s = String::with_capacity(2048);
    s.push_str(&svg::open_root("card", t.rarity.name(), &t.fingerprint()));

    // defs: panel radial gradient + optional glow.
    s.push_str("<defs>");
    s.push_str(&svg::radial_gradient("panel", pal.light, pal.dark));
    if t.rarity.glows() {
        s.push_str(&svg::glow_filter("glow", rarity_c, 3));
    }
    s.push_str("</defs>");

    // background panel.
    s.push_str(&format!(
        "<g id=\"bg\"><rect x=\"6\" y=\"6\" width=\"116\" height=\"116\" rx=\"14\" fill=\"url(#panel)\"/></g>"
    ));

    // frame.
    s.push_str(&format!(
        "<g id=\"frame\">{}</g>",
        frame_fragment(t.frame, rarity_c)
    ));

    // emblem (glows for rare+).
    let glow_attr = if t.rarity.glows() {
        " filter=\"url(#glow)\""
    } else {
        ""
    };
    s.push_str(&format!(
        "<g id=\"emblem\"{glow_attr}>{}</g>",
        emblem_fragment(t.emblem, accent, pal.accent)
    ));

    // rank pips.
    s.push_str(&format!(
        "<g id=\"pips\">{}</g>",
        pips_fragment(t.pips, pal.accent)
    ));

    // gild overlay — a legendary gets a gold inner frame.
    if t.rarity.gilds() {
        s.push_str(&format!(
            "<g id=\"gild\"><rect x=\"18\" y=\"18\" width=\"92\" height=\"92\" rx=\"8\" fill=\"none\" stroke=\"{rarity_c}\" stroke-width=\"2\" opacity=\"0.95\"/></g>"
        ));
    }

    s.push_str("</svg>");
    s
}
