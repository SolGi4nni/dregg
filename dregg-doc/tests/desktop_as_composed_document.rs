//! # THE DESKTOP IS A COMPOSED DOCUMENT (tests-as-spec, crate-boundary)
//!
//! The reflexive weld of `docs/deos/DOC-CELL-COMPOSITION.md §6`: "the whole
//! starbridge is kinda like a cell document." This proves it as a WIRE FACT
//! reachable from OUTSIDE the crate (through the public `dregg_doc::composition`
//! API) — the live workspace projects to a COMPOSED document (each window an
//! `Op::Embed` of its owner cell) that round-trips through the REAL
//! `content_composed` fold, where editing the projected document drives a real
//! workspace change and an out-of-cap window darkens through the membrane.
//!
//! Unlike the flat `dregg_doc::desktop` projection (surfaces = TEXT atoms), this
//! reads the desktop through the COMPOSITION algebra — a graph of cells — so the
//! desktop inherits, through the SAME fold, the per-viewer membrane (fog-of-war on
//! the desktop), the forkable layout pushout, and the cycle guard.

use dregg_doc::Author;
use dregg_doc::composition::{
    CellId, ChildRef, ChildResolution, DesktopSurface, EmbedRole, Op, Segment, Viewer,
    close_surface, content_composed, scene_to_composed, surface_embed_id, workspace_resolver,
};

fn win(tag: u128, z: i64) -> DesktopSurface {
    DesktopSurface::new(CellId::from_u128(tag), z)
}

/// (POSITIVE) The live workspace projects to a composed document whose embedded
/// surfaces RESOLVE in paint order through the real membrane-gated fold — a
/// round-trip from workspace to document and back to a per-viewer render.
#[test]
fn the_live_workspace_projects_and_round_trips_through_the_real_fold() {
    let surfaces = vec![win(0xA1, 0), win(0xB2, 1).focused(), win(0xC3, 2)];
    let layout = scene_to_composed(&surfaces, Author(1));
    let resolver = workspace_resolver(&surfaces);
    let viewer = Viewer::able(surfaces.iter().map(|s| s.owner));

    let r = content_composed(&layout, &viewer, &resolver);
    assert_eq!(
        r.embedded_cells(),
        vec![
            CellId::from_u128(0xA1),
            CellId::from_u128(0xB2),
            CellId::from_u128(0xC3)
        ],
        "the composed desktop embeds each window's owner cell in paint order"
    );
    assert!(
        !r.has_darkened(),
        "a full-authority viewer reads every window"
    );
    // Each embedded surface genuinely RESOLVED (the fold recursed into its cell).
    let rendered = r
        .segments
        .iter()
        .filter(|s| {
            matches!(
                s,
                Segment::Embedded {
                    resolution: ChildResolution::Rendered(_),
                    ..
                }
            )
        })
        .count();
    assert_eq!(
        rendered, 3,
        "all three windows resolved through the membrane fold"
    );
}

/// (EDIT DRIVES A WORKSPACE CHANGE) Closing a window is an `Op::Remove` authored on
/// the projected layout — a real layout edit through the embed grammar — and the
/// re-folded desktop no longer embeds it (the reflexive editor editing the desktop).
#[test]
fn closing_a_window_is_a_real_edit_that_changes_the_rendered_desktop() {
    let surfaces = vec![win(0xA1, 0), win(0xB2, 1), win(0xC3, 2)];
    let mut layout = scene_to_composed(&surfaces, Author(1));
    let resolver = workspace_resolver(&surfaces);
    let viewer = Viewer::able(surfaces.iter().map(|s| s.owner));

    assert_eq!(
        content_composed(&layout, &viewer, &resolver)
            .embedded_cells()
            .len(),
        3
    );

    layout.apply_patch(Author(1), &[close_surface(&surfaces[1])]);
    let after = content_composed(&layout, &viewer, &resolver);
    assert_eq!(
        after.embedded_cells(),
        vec![CellId::from_u128(0xA1), CellId::from_u128(0xC3)],
        "the closed window drops off the desktop; order conducts through the tombstone"
    );
}

/// (NEGATIVE) An out-of-cap window DARKENS through the per-viewer membrane — the
/// fog-of-war on the desktop. The citation survives (which cell), the content is
/// withheld (never forged), and the rest of the desktop stays usable.
#[test]
fn an_out_of_cap_window_darkens_while_the_rest_of_the_desktop_renders() {
    let surfaces = vec![win(0xA1, 0), win(0x5EC, 1), win(0xC3, 2)];
    let layout = scene_to_composed(&surfaces, Author(1));
    let resolver = workspace_resolver(&surfaces);
    // The viewer lacks the secret window's owner cap.
    let viewer = Viewer::able([CellId::from_u128(0xA1), CellId::from_u128(0xC3)]);

    let r = content_composed(&layout, &viewer, &resolver);
    assert!(r.has_darkened(), "the out-of-cap window darkens");
    assert_eq!(
        r.embedded_cells(),
        vec![
            CellId::from_u128(0xA1),
            CellId::from_u128(0x5EC),
            CellId::from_u128(0xC3)
        ],
        "every window's citation survives — the secret is darkened, not erased"
    );
    let darkened = r
        .segments
        .iter()
        .find_map(|s| match s {
            Segment::Embedded {
                resolved_cell: Some(c),
                resolution: ChildResolution::Darkened { .. },
                ..
            } => Some(*c),
            _ => None,
        })
        .expect("the secret window is darkened");
    assert_eq!(
        darkened,
        CellId::from_u128(0x5EC),
        "exactly the out-of-cap window darkened"
    );

    // The membrane is the ONLY gate: a fully-capped viewer reads the whole desktop.
    let cleared = Viewer::able(surfaces.iter().map(|s| s.owner));
    assert!(!content_composed(&layout, &cleared, &resolver).has_darkened());
}

/// (FORKABLE) Two devices each open a window at the same anchor concurrently — the
/// layout pushout (merge) keeps both, surfaced as a first-class layout conflict
/// (the desktop is mergeable/forkable through the SAME pushout a prose doc is).
#[test]
fn two_devices_opening_windows_merge_as_a_layout_pushout_with_a_first_class_fork() {
    use dregg_doc::composition::merge_layout;
    let base_surfaces = vec![win(0xA1, 0)];
    let base = scene_to_composed(&base_surfaces, Author(1));
    let a1 = surface_embed_id(&base_surfaces[0]);

    let mut d1 = base.clone();
    d1.apply_patch(
        Author(1),
        &[Op::Embed {
            id: surface_embed_id(&win(0xB2, 1)),
            child: ChildRef::live(CellId::from_u128(0xB2)),
            after: a1,
            role: EmbedRole::Section,
        }],
    );
    let mut d2 = base.clone();
    d2.apply_patch(
        Author(2),
        &[Op::Embed {
            id: surface_embed_id(&win(0xC3, 1)),
            child: ChildRef::live(CellId::from_u128(0xC3)),
            after: a1,
            role: EmbedRole::Section,
        }],
    );

    let merged = merge_layout(&d1, &d2);
    let all = vec![win(0xA1, 0), win(0xB2, 1), win(0xC3, 2)];
    let resolver = workspace_resolver(&all);
    let viewer = Viewer::able([
        CellId::from_u128(0xA1),
        CellId::from_u128(0xB2),
        CellId::from_u128(0xC3),
    ]);
    let r = content_composed(&merged, &viewer, &resolver);
    assert!(
        r.segments
            .iter()
            .any(|s| matches!(s, Segment::LayoutConflict { .. })),
        "two windows opened at the same position are a first-class layout fork, never lost"
    );
}
