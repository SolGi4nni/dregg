//! THE LAYOUT CARD, PROVEN BY RUNNING — the cockpit's own STRUCTURE (its mode→surface
//! arrangement) reborn as a deos-js card. Rung 3 of the reflective cockpit: the layout that
//! was hardcoded Rust (`starbridge-v2/src/cockpit/frame.rs` `CockpitMode::surfaces()`) is now
//! editable DATA — a cell the cockpit READS to render its rail + sub-navs, and that reshapes
//! from within as receipted cap-gated patches.
//!
//! The chain proven here:
//!   (a) DEFAULT → the layout card's data mirrors the real five-mode arrangement EXACTLY (the
//!       data the cockpit reads in place of `CockpitMode::surfaces()`).
//!   (b) VIEW → the layout renders as a section per mode + a row per surface (a `move`
//!       affordance each) — the data-defined chrome a renderer paints.
//!   (c) RESHAPE FROM WITHIN → a `MoveSurface` patch relocates a surface to another mode,
//!       live → the arrangement changes, the edit a RECEIPTED PATCH attributed by BLAME,
//!       the surface set conserved.
//!   (d) THE CAP TOOTH → an unauthorized reshape is refused in-band (no patch, no receipt).

use deos_js::card_editor::ViewTree;
use deos_js::{LayoutCard, LayoutModel, LayoutPatch};
use dregg_cell::AuthRequired;
use dregg_doc::Author;

/// A layout card seeded with the real cockpit arrangement, authorized to reshape itself
/// (held=None admits edit_authority=Signature).
fn layout_card() -> LayoutCard {
    LayoutCard::open(
        [0xA7; 32],
        Author(42),
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ AuthRequired::Signature,
    )
}

// ── (a) DEFAULT — the layout card mirrors the real cockpit five-mode arrangement. ─────────
#[test]
fn the_default_layout_is_the_cockpit_arrangement_as_data() {
    let card = layout_card();
    let layout = card.layout();

    // The five modes, in rail order (Inhabit first — the landing).
    assert_eq!(
        layout.mode_order(),
        vec!["Inhabit", "Author", "Dev", "Inspect", "Operate"],
        "the five fixed rooms in rail order"
    );

    // Each mode's surface count matches `CockpitMode::surfaces()`; together they partition the
    // full 30-surface set (= the cockpit's `Tab::ALL.len()`), no surface in two modes.
    let counts = [
        ("Inhabit", 4),
        ("Author", 7),
        ("Dev", 6),
        ("Inspect", 8),
        ("Operate", 5),
    ];
    for (mode, n) in counts {
        assert_eq!(
            layout.surfaces_of(mode).len(),
            n,
            "{mode} carries {n} surfaces (matching CockpitMode::surfaces())"
        );
    }
    let all = layout.all_surfaces();
    assert_eq!(all.len(), 30, "the modes' surfaces sum to the full set");
    let mut uniq = all.clone();
    uniq.sort();
    uniq.dedup();
    assert_eq!(uniq.len(), 30, "a partition — no surface lives in two modes");

    // The forward map (surface → its mode) — what the cockpit uses to move the rail on a jump.
    assert_eq!(layout.mode_of("HOME").as_deref(), Some("Inhabit"));
    assert_eq!(layout.mode_of("COMPOSER").as_deref(), Some("Author"));
    assert_eq!(layout.mode_of("TERMINAL").as_deref(), Some("Dev"));
    assert_eq!(layout.mode_of("INSPECTOR").as_deref(), Some("Inspect"));
    assert_eq!(layout.mode_of("SWARM").as_deref(), Some("Operate"));
}

// ── (b) VIEW — a section per mode + a row per surface, each with a `move` affordance. ─────
#[test]
fn the_layout_renders_the_arrangement_with_a_move_affordance_per_surface() {
    let card = layout_card();
    let tree = card.view_tree().expect("the layout view parses");

    assert!(
        tree.walk()
            .iter()
            .any(|n| n.label() == Some("Cockpit layout · 5 modes · 30 surfaces")),
        "the header counts the live arrangement"
    );
    // Every mode is a labeled section, and every surface carries a `move` affordance the
    // cockpit wires to relocation.
    for mode in ["Inhabit", "Author", "Dev", "Inspect", "Operate"] {
        assert!(
            card.layout()
                .surfaces_of(mode)
                .iter()
                .all(|s| tree.has_button_for(&format!("move:{s}"))),
            "every {mode} surface carries a `move` affordance"
        );
    }
}

// ── (c) RESHAPE FROM WITHIN — relocate a surface, live: a receipted patch with blame. ─────
#[test]
fn moving_a_surface_to_another_mode_is_a_receipted_patch_with_blame() {
    let mut card = layout_card();
    let source_before = card.view_source();
    assert_eq!(card.layout().mode_of("GRAPH").as_deref(), Some("Inhabit"));

    // MOVE the GRAPH surface from Inhabit to Inspect (re-home it across the five rooms).
    let edit = card
        .reshape(LayoutPatch::MoveSurface {
            surface: "GRAPH".into(),
            to_mode: "Inspect".into(),
        })
        .expect("the authorized move-surface reshape is admitted");

    // The arrangement (the data the cockpit reads) changed.
    assert_eq!(
        card.layout().mode_of("GRAPH").as_deref(),
        Some("Inspect"),
        "GRAPH was re-homed under Inspect (the cockpit reads this for the sub-nav)"
    );
    assert!(
        !card
            .layout()
            .surfaces_of("Inhabit")
            .contains(&"GRAPH".to_string()),
        "GRAPH left Inhabit"
    );

    // The surface set is CONSERVED across the move.
    let all = card.layout().all_surfaces();
    assert_eq!(all.len(), 30, "the move conserved the surface count");
    let mut uniq = all.clone();
    uniq.sort();
    uniq.dedup();
    assert_eq!(uniq.len(), 30, "no surface duplicated by the move");

    // The view reshaped, and the reshape is a RECEIPTED PATCH with BLAME.
    assert_ne!(
        card.view_source(),
        source_before,
        "the layout view-source changed (the chrome reshaped from within)"
    );
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the structural reshape left a real provenance receipt"
    );
    assert!(
        card.blame().iter().any(|l| l.author == Author(42)),
        "the layout reshape is blamed on its author (the accountable patch)"
    );
    assert_eq!(
        card.card().receipt_count(),
        1,
        "exactly one provenance receipt for the reshape"
    );

    // The reshaped layout round-trips through its view-source (the cockpit can persist +
    // reload the arrangement cell).
    let reloaded =
        LayoutModel::from_json(&card.view_source()).expect("the reshaped view-source parses");
    assert_eq!(
        &reloaded,
        card.layout(),
        "the reshaped layout round-trips through its serialized view-source"
    );
    // (use ViewTree so the import is load-bearing — the re-folded tree still has the surface)
    let tree: ViewTree = edit.tree;
    assert!(tree.has_button_for("move:GRAPH"));
}

// ── (d) THE CAP TOOTH — an unauthorized reshape is refused in-band (no patch, no receipt). ─
#[test]
fn an_unauthorized_reshape_is_refused_in_band() {
    // held=Signature does NOT satisfy edit_authority=Proof → the authoring tooth refuses.
    let mut card = LayoutCard::open(
        [0xCD; 32],
        Author(7),
        /*held=*/ AuthRequired::Signature,
        /*edit_authority=*/ AuthRequired::Proof,
    );
    let before = card.view_source();
    let err = card.reshape(LayoutPatch::MoveSurface {
        surface: "GRAPH".into(),
        to_mode: "Inspect".into(),
    });
    assert!(
        matches!(err, Err(deos_js::card_editor::EditError::Unauthorized)),
        "an over-reach reshape is refused by the cap tooth"
    );
    assert_eq!(
        card.view_source(),
        before,
        "nothing changed (no patch on an unauthorized reshape)"
    );
    assert_eq!(
        card.layout().mode_of("GRAPH").as_deref(),
        Some("Inhabit"),
        "the arrangement is unchanged (GRAPH still in Inhabit)"
    );
    assert_eq!(
        card.card().receipt_count(),
        0,
        "no receipt on an unauthorized reshape"
    );
}
