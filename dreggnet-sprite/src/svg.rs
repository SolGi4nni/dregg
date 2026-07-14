//! Deterministic SVG composition primitives — fixed palettes and small string helpers.
//!
//! Everything here builds SVG by appending fixed strings and integer-formatted numbers
//! (no floats, no trig, no unordered iteration), so the emitted document is a pure
//! function of the trait vector on every platform.

/// A four-tone material palette (base fill, highlight, shadow, edge accent).
pub struct Palette {
    pub base: &'static str,
    pub light: &'static str,
    pub dark: &'static str,
    pub accent: &'static str,
}

/// Gear blade materials, indexed by the `material` trait: iron, steel, bronze, obsidian.
pub const GEAR_MATERIALS: [Palette; 4] = [
    Palette {
        base: "#6b7280",
        light: "#9aa3af",
        dark: "#3f4652",
        accent: "#c7ccd4",
    }, // iron
    Palette {
        base: "#94a3b8",
        light: "#cbd5e1",
        dark: "#556072",
        accent: "#e2e8f0",
    }, // steel
    Palette {
        base: "#a86b2e",
        light: "#d9a05b",
        dark: "#6e4318",
        accent: "#f0c886",
    }, // bronze
    Palette {
        base: "#2b2f3a",
        light: "#4b5263",
        dark: "#12141b",
        accent: "#7c86a0",
    }, // obsidian
];

/// Card panel palettes, indexed by the `palette` trait: crimson, teal, violet, amber.
pub const CARD_PALETTES: [Palette; 4] = [
    Palette {
        base: "#7f1d2e",
        light: "#c0394f",
        dark: "#3f0e17",
        accent: "#f4b6c0",
    }, // crimson
    Palette {
        base: "#0f5b57",
        light: "#2ea79f",
        dark: "#07302e",
        accent: "#a7e8e1",
    }, // teal
    Palette {
        base: "#3f2b7f",
        light: "#7657c8",
        dark: "#1f153f",
        accent: "#c9baf0",
    }, // violet
    Palette {
        base: "#7a5310",
        light: "#c99524",
        dark: "#3d2907",
        accent: "#f0d494",
    }, // amber
];

/// Gem / accent colors used for pommels, card sigil accents, and pips.
pub const GEM_COLORS: [&str; 6] = [
    "#e04b58", // ruby
    "#3b82f6", // sapphire
    "#3fb950", // emerald
    "#a855f7", // amethyst
    "#f5b301", // topaz
    "#e2e8f0", // diamond
];

/// The rarity tier signature colors (glow / border / gild), ascending.
pub const RARITY_COLORS: [&str; 5] = ["#9ca3af", "#3fb950", "#3b82f6", "#a855f7", "#f5b301"];

/// The rarity tier names, ascending (the `data-rarity` attribute value).
pub const RARITY_NAMES: [&str; 5] = ["common", "uncommon", "rare", "epic", "legendary"];

/// A 128×128 SVG canvas.
pub const CANVAS: u32 = 128;

/// A `<linearGradient>` def running top→bottom.
pub fn linear_gradient(id: &str, top: &str, bottom: &str) -> String {
    format!(
        "<linearGradient id=\"{id}\" x1=\"0\" y1=\"0\" x2=\"0\" y2=\"1\">\
<stop offset=\"0\" stop-color=\"{top}\"/>\
<stop offset=\"1\" stop-color=\"{bottom}\"/></linearGradient>"
    )
}

/// A `<radialGradient>` def (center bright → edge dark).
pub fn radial_gradient(id: &str, inner: &str, outer: &str) -> String {
    format!(
        "<radialGradient id=\"{id}\" cx=\"0.5\" cy=\"0.42\" r=\"0.62\">\
<stop offset=\"0\" stop-color=\"{inner}\"/>\
<stop offset=\"1\" stop-color=\"{outer}\"/></radialGradient>"
    )
}

/// A soft colored glow filter (a `feDropShadow`), used for rare-and-above sprites.
pub fn glow_filter(id: &str, color: &str, blur: u32) -> String {
    format!(
        "<filter id=\"{id}\" x=\"-50%\" y=\"-50%\" width=\"200%\" height=\"200%\">\
<feDropShadow dx=\"0\" dy=\"0\" stdDeviation=\"{blur}\" flood-color=\"{color}\" flood-opacity=\"0.85\"/></filter>"
    )
}

/// Fixed-order lowercase-hex encode of trait bytes (2 chars per byte) — the
/// `data-traits` fingerprint. Deterministic and order-preserving.
pub fn hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0xf) as usize] as char);
    }
    out
}

/// Open the root `<svg>` with the canonical namespace, viewBox, and derived data
/// attributes (kind, rarity, and a hex trait fingerprint — the E3-facing metadata).
pub fn open_root(kind: &str, rarity: &str, fingerprint: &str) -> String {
    format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {CANVAS} {CANVAS}\" \
width=\"{CANVAS}\" height=\"{CANVAS}\" role=\"img\" \
data-kind=\"{kind}\" data-rarity=\"{rarity}\" data-traits=\"{fingerprint}\">"
    )
}
