//! Driving the deterministic generative asset → SVG sprite renderer.
//!
//! Verifies: byte-identical determinism, a different AssetId ⇒ a different sprite,
//! traits visibly vary the SVG, well-formed XML, ≥2 asset kinds, and the E2 provably-
//! fair rarity draw (a legendary re-derives from the committed seed and gilds).

use std::collections::HashSet;

use dreggnet_asset::{AssetId, AssetWorld};
use dreggnet_sprite::{
    AssetKind, CardTraits, GearTraits, Rarity, card_traits, gear_traits, rarity_of, render,
    render_card, render_card_from, render_gear, render_gear_from,
};

/// A distinct content address, modeling the uniform blake3 AssetId with a counter.
fn asset(n: u64) -> AssetId {
    AssetId(*blake3::hash(&n.to_le_bytes()).as_bytes())
}

#[test]
fn same_asset_renders_byte_identical() {
    let id = asset(42);
    // Same asset ⇒ byte-identical SVG, both kinds, across repeated calls.
    assert_eq!(render_gear(&id), render_gear(&id));
    assert_eq!(render_card(&id), render_card(&id));
    assert_eq!(render(AssetKind::Gear, &id), render_gear(&id));
    assert_eq!(render(AssetKind::Card, &id), render_card(&id));
}

#[test]
fn different_assets_render_different_sprites() {
    // 64 distinct assets ⇒ 64 distinct gear sprites and 64 distinct card sprites
    // (byte-inequality asserted via a set of the emitted strings).
    let mut gears = HashSet::new();
    let mut cards = HashSet::new();
    for n in 0..64u64 {
        let id = asset(n);
        gears.insert(render_gear(&id));
        cards.insert(render_card(&id));
    }
    assert_eq!(
        gears.len(),
        64,
        "distinct assets must give distinct gear sprites"
    );
    assert_eq!(
        cards.len(),
        64,
        "distinct assets must give distinct card sprites"
    );
}

#[test]
fn real_minted_asset_renders_deterministically() {
    // Drive the REAL owned note: mint through the asset layer, render its content
    // address. Same asset ⇒ same sprite; two different mints ⇒ two different sprites.
    let mut world = AssetWorld::new();
    let excalibur = world.mint("alice", b"excalibur");
    let durendal = world.mint("alice", b"durendal");

    assert_eq!(render_gear(&excalibur), render_gear(&excalibur));
    assert_ne!(render_gear(&excalibur), render_gear(&durendal));
    // The trait vector is bound to the content address.
    assert_eq!(gear_traits(&excalibur), gear_traits(&excalibur));
}

#[test]
fn gear_traits_visibly_vary_the_svg() {
    let base = GearTraits {
        rarity: Rarity::Common,
        blade: 0,
        material: 0,
        rune: 0,
        guard: 0,
        notches: 0,
        gem: 0,
        mark: 0,
    };
    // Varying the blade changes the silhouette path ⇒ different bytes.
    let mut curved = base;
    curved.blade = 1;
    assert_ne!(render_gear_from(&base), render_gear_from(&curved));

    // Notches add path elements (structural, not just a recolor).
    let mut notched = base;
    notched.notches = 4;
    let base_paths = render_gear_from(&base).matches("<path").count();
    let notched_paths = render_gear_from(&notched).matches("<path").count();
    assert!(
        notched_paths > base_paths,
        "notches must add path elements: {base_paths} -> {notched_paths}"
    );

    // A rune adds its own layer group.
    let mut runed = base;
    runed.rune = 2;
    assert!(render_gear_from(&runed).contains("id=\"rune\""));
    assert!(!render_gear_from(&base).contains("id=\"rune\""));
}

#[test]
fn rarity_drives_glow_and_gild() {
    let common = GearTraits {
        rarity: Rarity::Common,
        blade: 0,
        material: 1,
        rune: 0,
        guard: 0,
        notches: 0,
        gem: 0,
        mark: 0,
    };
    let mut legendary = common;
    legendary.rarity = Rarity::Legendary;

    let c = render_gear_from(&common);
    let l = render_gear_from(&legendary);
    assert_ne!(c, l);
    // Common: no glow filter, no gild layer.
    assert!(!c.contains("url(#glow)"));
    assert!(!c.contains("id=\"gild\""));
    // Legendary: glows and gilds.
    assert!(l.contains("<filter"));
    assert!(l.contains("url(#glow)"));
    assert!(l.contains("id=\"gild\""));

    // Same for the card kind.
    let card_common = CardTraits {
        rarity: Rarity::Common,
        frame: 0,
        emblem: 0,
        palette: 0,
        pips: 3,
        accent: 0,
    };
    let mut card_legendary = card_common;
    card_legendary.rarity = Rarity::Legendary;
    assert!(!render_card_from(&card_common).contains("id=\"gild\""));
    assert!(render_card_from(&card_legendary).contains("id=\"gild\""));
}

#[test]
fn card_emblems_are_structurally_different() {
    let base = CardTraits {
        rarity: Rarity::Common,
        frame: 0,
        emblem: 0,
        palette: 0,
        pips: 3,
        accent: 0,
    };
    // Each of the 6 emblems yields a distinct SVG.
    let mut seen = HashSet::new();
    for e in 0..6u8 {
        let mut t = base;
        t.emblem = e;
        seen.insert(render_card_from(&t));
    }
    assert_eq!(seen.len(), 6, "the six emblems must render distinctly");

    // The pip count changes the number of pip circles.
    let mut few = base;
    few.pips = 2;
    let mut many = base;
    many.pips = 6;
    let few_c = render_card_from(&few).matches("<circle").count();
    let many_c = render_card_from(&many).matches("<circle").count();
    assert!(
        many_c > few_c,
        "more pips ⇒ more circles: {few_c} -> {many_c}"
    );
}

#[test]
fn both_kinds_are_well_formed_xml_with_expected_layers() {
    let id = asset(7);
    for (kind, expect_layer) in [
        (AssetKind::Gear, "id=\"blade\""),
        (AssetKind::Card, "id=\"emblem\""),
    ] {
        let svg = render(kind, &id);
        // Real XML parse — well-formed, single <svg> root.
        let doc = roxmltree::Document::parse(&svg)
            .unwrap_or_else(|e| panic!("emitted SVG must be well-formed XML: {e}"));
        assert_eq!(doc.root_element().tag_name().name(), "svg");
        // Carries the derived metadata + the expected content layers.
        assert!(svg.contains("data-kind="));
        assert!(svg.contains("data-rarity="));
        assert!(svg.contains("data-traits="));
        assert!(svg.contains("id=\"bg\""));
        assert!(svg.contains(expect_layer));
    }
}

#[test]
fn rarity_is_provably_fair_and_re_derivable() {
    // Scan the content-address space: the committed weighted draw (E2) yields the full
    // tier ladder, with commons dominating and a legendary at the tail — and any
    // claimed tier re-derives from the AssetId alone.
    let mut counts = [0u32; 5];
    let mut a_legendary: Option<AssetId> = None;
    for n in 0..4000u64 {
        let id = asset(n);
        let r = rarity_of(&id);
        // Re-derivation: the tier is a pure function of the content address.
        assert_eq!(rarity_of(&id), r);
        counts[r.tier() as usize] += 1;
        if r == Rarity::Legendary {
            a_legendary = Some(id);
        }
    }
    assert!(counts[0] > counts[4], "commons must dominate legendaries");
    let leg = a_legendary.expect("a legendary appears within 4000 assets (committed tail)");
    // A claimed legendary re-derives to the legendary tier and its sprite gilds.
    assert_eq!(rarity_of(&leg), Rarity::Legendary);
    assert!(render_gear(&leg).contains("id=\"gild\""));
    // The rarity carried into both kinds' trait vectors agrees with the draw.
    assert_eq!(gear_traits(&leg).rarity, Rarity::Legendary);
    assert_eq!(card_traits(&leg).rarity, Rarity::Legendary);
}
