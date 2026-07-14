//! The **gear** sprite: a weapon / blade emblem, composed from the gear trait vector.

use crate::Rarity;
use crate::svg::{self, GEAR_MATERIALS, GEM_COLORS};

/// Number of blade silhouettes (straight, saber, serrated, cleaver).
pub const BLADE_SHAPES: u64 = 4;
/// Number of non-empty rune glyphs (a `rune` trait of `0` means "no rune").
pub const RUNE_GLYPHS: u64 = 4;
/// Number of crossguard styles (bar, swept, spiked).
pub const GUARD_STYLES: u64 = 3;
/// Maximum edge notches carved into the blade (the `notches` trait is `0..=MAX_NOTCHES`).
pub const MAX_NOTCHES: u64 = 4;

/// The gear (weapon) trait vector — each axis is one indexed draw off the asset's
/// sprite stream (`rarity` via the committed weighted draw). Every field visibly
/// changes the composed SVG.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct GearTraits {
    /// The provably-fair rarity tier (drives glow + gild).
    pub rarity: Rarity,
    /// Blade silhouette, `0..BLADE_SHAPES`.
    pub blade: u8,
    /// Material palette, indexes [`GEAR_MATERIALS`].
    pub material: u8,
    /// Rune glyph on the blade, `0` = none, else `1..=RUNE_GLYPHS`.
    pub rune: u8,
    /// Crossguard style, `0..GUARD_STYLES`.
    pub guard: u8,
    /// Number of edge notches carved into the blade, `0..=MAX_NOTCHES`.
    pub notches: u8,
    /// Pommel gem color, indexes [`GEM_COLORS`].
    pub gem: u8,
    /// A 4-bit maker's mark (up to four dots at the hilt).
    pub mark: u8,
}

impl GearTraits {
    /// A stable hex fingerprint of the trait vector — the `data-traits` attribute and a
    /// compact identity for the sprite (distinct trait vectors ⇒ distinct fingerprints).
    pub fn fingerprint(&self) -> String {
        svg::hex(&[
            self.rarity.tier(),
            self.blade,
            self.material,
            self.rune,
            self.guard,
            self.notches,
            self.gem,
            self.mark,
        ])
    }
}

/// The blade silhouette path (centered on x=64, tip at y≈14, meeting the guard at y≈80).
fn blade_path(blade: u8) -> &'static str {
    match blade % (BLADE_SHAPES as u8) {
        // straight, tapered
        0 => "M64 14 L72 70 L69 80 L59 80 L56 70 Z",
        // saber — swept to one side
        1 => "M64 14 C 80 34 78 64 70 80 L60 80 C 60 58 58 36 64 14 Z",
        // serrated — straight back, toothed edge
        2 => {
            "M60 80 L60 16 L64 14 L68 22 L64 28 L68 34 L64 40 L68 46 L64 52 L68 58 L64 64 L68 70 L68 80 Z"
        }
        // cleaver — broad
        _ => "M58 16 L74 22 L74 78 L58 80 Z",
    }
}

/// A crossguard fragment for the given style.
fn guard_fragment(guard: u8, mat: &svg::Palette) -> String {
    // The crossguard is the mid-tone base metal (the blade takes the bright light/dark
    // gradient); `dark` outlines it.
    let (base, dark) = (mat.base, mat.dark);
    match guard % (GUARD_STYLES as u8) {
        // straight bar
        0 => format!(
            "<rect x=\"42\" y=\"78\" width=\"44\" height=\"7\" rx=\"3\" fill=\"{base}\" stroke=\"{dark}\" stroke-width=\"1\"/>"
        ),
        // swept — dipped ends
        1 => format!(
            "<path d=\"M42 88 Q64 74 86 88 L84 82 Q64 72 44 82 Z\" fill=\"{base}\" stroke=\"{dark}\" stroke-width=\"1\"/>"
        ),
        // spiked — bar plus outward barbs
        _ => format!(
            "<rect x=\"46\" y=\"78\" width=\"36\" height=\"7\" rx=\"2\" fill=\"{base}\" stroke=\"{dark}\" stroke-width=\"1\"/>\
<path d=\"M46 78 L38 81 L46 85 Z\" fill=\"{base}\"/>\
<path d=\"M82 78 L90 81 L82 85 Z\" fill=\"{base}\"/>"
        ),
    }
}

/// A rune glyph on the blade (empty when `rune == 0`).
fn rune_fragment(rune: u8, color: &str) -> String {
    if rune == 0 {
        return String::new();
    }
    let d = match (rune - 1) % (RUNE_GLYPHS as u8) {
        0 => "M60 40 L68 40 M64 40 L64 56 M60 56 L68 56", // ci: I-bar
        1 => "M64 38 L70 48 L64 58 L58 48 Z",             // diamond
        2 => "M60 40 L64 50 L68 40 M62 52 L66 52",        // arrow-ish
        _ => "M60 42 L68 42 L60 54 L68 54",               // zig
    };
    format!(
        "<path d=\"{d}\" fill=\"none\" stroke=\"{color}\" stroke-width=\"2\" stroke-linecap=\"round\" stroke-linejoin=\"round\" opacity=\"0.9\"/>"
    )
}

/// Edge notches carved into the blade (small triangles along the right edge).
fn notches_fragment(notches: u8, color: &str) -> String {
    let mut out = String::new();
    let n = (notches as u64).min(MAX_NOTCHES) as u8;
    for k in 0..n {
        let y = 28 + (k as u32) * 12;
        out.push_str(&format!(
            "<path d=\"M69 {y} L74 {y1} L69 {y2} Z\" fill=\"{color}\"/>",
            y1 = y + 3,
            y2 = y + 6
        ));
    }
    out
}

/// The maker's mark — up to four hilt dots encoding the 4-bit `mark` trait.
fn mark_fragment(mark: u8, color: &str) -> String {
    let mut out = String::new();
    for bit in 0..4u8 {
        if mark & (1 << bit) != 0 {
            let cx = 52 + (bit as u32) * 8;
            out.push_str(&format!(
                "<circle cx=\"{cx}\" cy=\"118\" r=\"2\" fill=\"{color}\"/>"
            ));
        }
    }
    out
}

/// Render a gear sprite from an explicit trait vector — the deterministic composed SVG.
pub fn render_gear_from(t: &GearTraits) -> String {
    let mat = &GEAR_MATERIALS[(t.material as usize) % GEAR_MATERIALS.len()];
    let gem = GEM_COLORS[(t.gem as usize) % GEM_COLORS.len()];
    let rarity_c = t.rarity.color();
    let blade = blade_path(t.blade);

    let mut s = String::with_capacity(2048);
    s.push_str(&svg::open_root("gear", t.rarity.name(), &t.fingerprint()));

    // defs: blade gradient + optional glow filter.
    s.push_str("<defs>");
    s.push_str(&svg::linear_gradient("blade", mat.light, mat.dark));
    if t.rarity.glows() {
        s.push_str(&svg::glow_filter("glow", rarity_c, 3));
    }
    s.push_str("</defs>");

    // background plate — faintly tinted by rarity.
    s.push_str(&format!(
        "<g id=\"bg\"><rect x=\"6\" y=\"6\" width=\"116\" height=\"116\" rx=\"18\" \
fill=\"#0d1017\" stroke=\"{rarity_c}\" stroke-width=\"2\" opacity=\"0.9\"/></g>"
    ));

    // blade group (glows for rare+).
    let glow_attr = if t.rarity.glows() {
        " filter=\"url(#glow)\""
    } else {
        ""
    };
    s.push_str(&format!("<g id=\"blade\"{glow_attr}>"));
    s.push_str(&format!(
        "<path d=\"{blade}\" fill=\"url(#blade)\" stroke=\"{}\" stroke-width=\"1\" stroke-linejoin=\"round\"/>",
        mat.dark
    ));
    // fuller (center line down the blade).
    s.push_str(&format!(
        "<path d=\"M64 20 L64 76\" stroke=\"{}\" stroke-width=\"1.5\" opacity=\"0.55\"/>",
        mat.accent
    ));
    s.push_str(&notches_fragment(t.notches, mat.dark));
    s.push_str("</g>");

    // crossguard.
    s.push_str(&format!(
        "<g id=\"guard\">{}</g>",
        guard_fragment(t.guard, mat)
    ));

    // grip + wrap.
    s.push_str(&format!(
        "<g id=\"grip\"><rect x=\"60\" y=\"85\" width=\"8\" height=\"20\" rx=\"3\" fill=\"#5b3a21\" stroke=\"#2f1d10\" stroke-width=\"1\"/>\
<path d=\"M60 90 L68 92 M60 95 L68 97 M60 100 L68 102\" stroke=\"#2f1d10\" stroke-width=\"1\" opacity=\"0.7\"/></g>"
    ));

    // pommel + gem.
    s.push_str(&format!(
        "<g id=\"pommel\"><circle cx=\"64\" cy=\"108\" r=\"6\" fill=\"{}\" stroke=\"#2f1d10\" stroke-width=\"1\"/>\
<circle cx=\"64\" cy=\"108\" r=\"3\" fill=\"{gem}\"/></g>",
        mat.accent
    ));

    // rune (optional).
    let rune = rune_fragment(t.rune, mat.accent);
    if !rune.is_empty() {
        s.push_str(&format!("<g id=\"rune\">{rune}</g>"));
    }

    // maker's mark (optional).
    let mark = mark_fragment(t.mark, mat.light);
    if !mark.is_empty() {
        s.push_str(&format!("<g id=\"mark\">{mark}</g>"));
    }

    // gild overlay — a legendary gets a gold blade outline.
    if t.rarity.gilds() {
        s.push_str(&format!(
            "<g id=\"gild\"><path d=\"{blade}\" fill=\"none\" stroke=\"{rarity_c}\" stroke-width=\"2\" stroke-linejoin=\"round\" opacity=\"0.95\"/></g>"
        ));
    }

    s.push_str("</svg>");
    s
}
