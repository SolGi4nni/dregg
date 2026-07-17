//! THE DESKTOP IS A DOCUMENT — the cockpit adapter that maps the live scene onto
//! the green, isolation-tested `dregg_doc::desktop` projection.
//!
//! ember's reading: *"the whole starbridge is kinda like a cell document."* The
//! WELD logic + its both-polarity tests live in `dregg_doc::desktop` (the document
//! crate, which builds standalone — so the projection is verified against the REAL
//! `substrate_commit` without the gpui toolchain). THIS module is the thin
//! cockpit-side adapter: it converts the cockpit's live
//! [`compositor::CompositedSurface`] + [`view_cell::WorkspaceCell`] into the
//! renderer-agnostic [`dregg_doc::desktop::DesktopSurface`] and delegates.
//!
//! Why this is the *reflexive* reading (not a gimmick): the cockpit's scene is
//! ALREADY an ordered graph of cells — [`compositor::CompositorScene`] is an
//! ordered list of [`compositor::CompositedSurface`], each `(owner: CellId, …,
//! z_layer, focus_flag)`, and the workspace's UI state is ALREADY cell-backed
//! ([`view_cell::WorkspaceCell`] / [`view_cell::ViewCell`], each itself
//! `Presentable`). Projecting it as a document just *names* that graph as a
//! `dregg_doc` document, so the desktop becomes shareable / rehydratable /
//! branchable / diffable / time-travellable through the SAME machinery a prose
//! document is, and a multi-device focus/tab contention becomes a *first-class
//! conflict state* (the firmament dual of the compositor's T3 focus-exclusive
//! refusal). See `docs/deos/DOC-CELL-COMPOSITION.md`.
//!
//! The reflexive loop's executor cut-over (a layout edit as a witnessed turn)
//! rides [`view_cell::WorkspaceCell::commit`], already a real `Effect::SetField`
//! turn — so authoring the desktop-document closes back into the live image.

use dregg_doc::desktop::{self, DesktopSurface};
use dregg_doc::{Author, DocGraph, Rendered};

use crate::compositor::{CompositedSurface, CompositorScene};
use crate::view_cell::WorkspaceCell;

pub use dregg_doc::desktop::{FIELD_ACTIVE_TAB, FIELD_FOCUS};

/// Map one live cockpit surface onto the renderer-agnostic projection shape.
fn to_desktop_surface(s: &CompositedSurface) -> DesktopSurface {
    DesktopSurface {
        owner: *s.owner.as_bytes(),
        source_state_root: s.source_state_root,
        content_digest: s.content_digest,
        z_layer: s.z_layer,
        focus_flag: s.focus_flag,
    }
}

/// The live scene's surfaces in paint order, as projection shapes.
fn surfaces_of(scene: &CompositorScene) -> Vec<DesktopSurface> {
    scene.surfaces.iter().map(to_desktop_surface).collect()
}

/// Project a live cockpit **scene + workspace** into a `dregg_doc` document (the
/// WELD; delegates to the verified [`desktop::scene_to_doc`]).
pub fn scene_to_doc(
    scene: &CompositorScene,
    workspace: &WorkspaceCell,
    author: Author,
) -> DocGraph {
    desktop::scene_to_doc(&surfaces_of(scene), workspace.active_tab(), author)
}

/// The REAL desktop commitment (the production sorted-Poseidon2 heap root): two
/// parties agree they see the same desktop iff this matches; a forged surface
/// changes it (the anti-forge tooth, inherited from the document).
pub fn desktop_commit(
    scene: &CompositorScene,
    workspace: &WorkspaceCell,
    author: Author,
) -> [u8; 32] {
    desktop::desktop_commit(&surfaces_of(scene), workspace.active_tab(), author)
}

/// Render the desktop-document content (the linearized walk + any first-class
/// conflict regions — a contended desktop renders the conflict honestly).
pub fn render_desktop(
    scene: &CompositorScene,
    workspace: &WorkspaceCell,
    author: Author,
) -> Rendered {
    desktop::render(&surfaces_of(scene), workspace.active_tab(), author)
}

// ── THE COMPOSED READING — the desktop as a GRAPH OF CELLS ────────────────────
//
// The delegation above (`scene_to_doc` / `desktop_commit`) reads the live scene as
// the FLAT projection: text atoms `owner ‖ root ‖ digest` chained in z-order, with
// the tab/focus as single-valued fields. That is the right shape for the *commitment*
// (two parties agree on one heap root) but it flattens every window into bytes.
//
// THIS is the sharper convergence ember named — *"documents composed FROM cells:
// include WHOLE cells, nest cells, be a composition of cells."* The cockpit's scene is
// ALREADY a graph of cells (`CompositorScene` = ordered `CompositedSurface`, each an
// `(owner: CellId, z_layer, focus_flag)`), so we project it through the SAME
// `Op::Embed` composition algebra a composed prose document uses
// ([`dregg_doc::composition`], §6). Each window becomes an `Op::Embed` of its OWNER
// cell — the desktop is a layout graph PLUS, by reference, each window's cell. It
// therefore inherits, through the SAME fold ([`composition::content_composed`]):
//
//   · the per-viewer membrane — an out-of-cap window DARKENS (citation kept, content
//     withheld, never forged), the firmament fog-of-war ON the desktop;
//   · forkability / time-travel — the layout graph is a `merge`-able pushout, so two
//     devices' window placements merge (a same-position fork is a first-class layout
//     conflict, not a silent loss);
//   · the cycle guard — a window mirroring the whole desktop trips it, never a stack
//     overflow (the reflexive self-hosting image is a *state*, not a crash);
//   · the reflexive edit — closing a window is an `Op::Remove` on the projected layout
//     ([`composition::close_surface`]), the embed grammar editing the document that IS
//     the desktop.
//
// The bridge is the `CellId` reduction: the cockpit's 32-byte `dregg_cell::CellId`
// folds to the composition crate's `composition::CellId(u128)` deterministically (a
// full-width fold — every byte participates, so the anti-forge tooth survives: two
// distinct windows do not collide). The window's CONTENT (its cell's sub-document) is
// resolved by a `ChildResolver`; here we use the standalone `workspace_resolver` shape
// (the substrate resolver plugs the real `dregg://` read + `Membrane::project` in its
// place, exactly as `cell_transclusion.rs` does for a single whole-cell embed).

use dregg_doc::composition::{
    self, content_composed, scene_to_composed, surface_embed_id, workspace_resolver,
    DesktopSurface as ComposedSurface, LayoutGraph, MapResolver, Op, Rendered as ComposedRendered,
    Viewer,
};

/// Reduce the cockpit's 32-byte `dregg_cell::CellId` to the composition crate's
/// `composition::CellId` (a `u128`) — a FULL-WIDTH fold so every byte of the cell's
/// identity participates (two distinct windows do not collide into one embed; the
/// anti-forge tooth the composition algebra proves over `CellId` is preserved across
/// the reduction). Deterministic + stable: the same window always projects to the same
/// embed-atom, so a later reorder/close targets the SAME atom.
pub fn composed_cell_id(owner: &dregg_cell::CellId) -> composition::CellId {
    let bytes = owner.as_bytes();
    // Fold the 32 bytes into two u128 halves, then mix — every byte contributes.
    let mut hi: u128 = 0;
    let mut lo: u128 = 0;
    for (i, b) in bytes.iter().enumerate() {
        if i < 16 {
            hi = hi.wrapping_mul(0x0100_0000_01b3).wrapping_add(*b as u128);
        } else {
            lo = lo.wrapping_mul(0x0100_0000_01b3).wrapping_add(*b as u128);
        }
    }
    composition::CellId(hi ^ lo.rotate_left(64))
}

/// Map one live cockpit surface onto the COMPOSED projection shape (vs.
/// [`to_desktop_surface`], which targets the flat reading). The window IS an embed of
/// its owner cell, ordered by its z-layer, focus-flag carried so the focus holder is
/// the active block.
fn to_composed_surface(s: &CompositedSurface) -> ComposedSurface {
    let base = ComposedSurface::new(composed_cell_id(&s.owner), s.z_layer);
    if s.focus_flag {
        base.focused()
    } else {
        base
    }
}

/// The live scene's surfaces in paint order, as COMPOSED projection shapes.
fn composed_surfaces_of(scene: &CompositorScene) -> Vec<ComposedSurface> {
    scene.surfaces.iter().map(to_composed_surface).collect()
}

/// Project a live cockpit **scene** into a COMPOSED document layout — THE WELD: each
/// window an [`Op::Embed`] of its owner cell, chained in paint (z) order. The desktop
/// is a *graph of cells*, authored by exactly the embed grammar a composed prose
/// document uses. The returned [`LayoutGraph`] is editable by the same ops
/// ([`Op::Remove`] to close a window, [`Op::Order`] to reorder, [`Op::Embed`] to open
/// one) — the reflexive loop closes back into the live image.
pub fn scene_to_composed_doc(scene: &CompositorScene, author: Author) -> LayoutGraph {
    scene_to_composed(&composed_surfaces_of(scene), author)
}

/// A resolver over the live workspace — each window's owner cell resolves to its
/// content sub-document. The standalone shape; the substrate adapter plugs the real
/// `dregg://` fetch + `Membrane::project` in (see [`crate::cell_transclusion`]).
pub fn scene_resolver(scene: &CompositorScene) -> MapResolver {
    workspace_resolver(&composed_surfaces_of(scene))
}

/// Build the per-viewer read membrane (a [`Viewer`]) from the set of owner cells the
/// caller's caps clear — the cockpit-side membrane. A window whose owner is NOT in
/// `readable` will DARKEN in the composed render (citation kept, content withheld).
pub fn viewer_over(readable: impl IntoIterator<Item = dregg_cell::CellId>) -> Viewer {
    Viewer::able(readable.into_iter().map(|c| composed_cell_id(&c)))
}

/// A viewer that clears EVERY window in the scene (a full-authority desktop) — the
/// owning operator's own view.
pub fn full_authority_viewer(scene: &CompositorScene) -> Viewer {
    viewer_over(scene.surfaces.iter().map(|s| s.owner))
}

/// **Render the live desktop as a COMPOSED document, PER-VIEWER** — the reflexive
/// reading. Walks the projected layout, resolving each window's owner cell through the
/// `viewer`'s membrane: in-cap windows render (recursing into their content), an
/// out-of-cap window DARKENS (the firmament fog-of-war ON the desktop), a window-mirror
/// cycle is a state. Two operators with different caps see the SAME desktop differently.
pub fn render_composed(scene: &CompositorScene, viewer: &Viewer) -> ComposedRendered {
    let layout = scene_to_composed_doc(scene, Author(1));
    let resolver = scene_resolver(scene);
    content_composed(&layout, viewer, &resolver)
}

/// **Close (tombstone) one live window in the composed reading** — an [`Op::Remove`] on
/// the window's embed-atom. The reflexive edit: closing a window is the embed grammar
/// editing the document that IS the desktop. Apply it to a [`scene_to_composed_doc`]
/// layout and re-fold to see the window drop off; the order conducts through it.
pub fn close_window_op(s: &CompositedSurface) -> Op {
    composition::close_surface(&to_composed_surface(s))
}

/// The embed-atom id a live window projects to (so the cockpit can target the SAME atom
/// for a later reorder/close).
pub fn window_embed_id(s: &CompositedSurface) -> dregg_doc::AtomId {
    surface_embed_id(&to_composed_surface(s))
}

#[cfg(test)]
mod composed_tests {
    use super::*;
    use crate::compositor::CompositedSurface;
    use dregg_cell::CellId;
    use dregg_doc::composition::{ChildResolution, Segment};

    fn cell(tag: u8) -> CellId {
        CellId::from_bytes([tag; 32])
    }

    fn surface(tag: u8, z: i64, focus: bool) -> CompositedSurface {
        CompositedSurface {
            owner: cell(tag),
            regions: vec![z as u64],
            content_digest: 100 + z as u64,
            source_state_root: 10 + z as u64,
            z_layer: z,
            focus_flag: focus,
        }
    }

    fn three_window_scene() -> CompositorScene {
        CompositorScene {
            surfaces: vec![
                surface(0xA1, 0, false),
                surface(0xB2, 1, true),
                surface(0xC3, 2, false),
            ],
        }
    }

    // (POSITIVE) The LIVE cockpit scene projects to a composed document that
    // ROUND-TRIPS: each window's owner cell resolves through the REAL fold, in paint
    // (z) order — over the cockpit's own `CompositedSurface`/`CompositorScene`, not a
    // fixture.
    #[test]
    fn the_live_scene_projects_to_a_composed_doc_that_round_trips() {
        let scene = three_window_scene();
        let viewer = full_authority_viewer(&scene);
        let r = render_composed(&scene, &viewer);

        // ROUND-TRIP: the embedded cells are exactly the window owners, IN z-ORDER.
        let expected: Vec<composition::CellId> = scene
            .surfaces
            .iter()
            .map(|s| composed_cell_id(&s.owner))
            .collect();
        assert_eq!(
            r.embedded_cells(),
            expected,
            "the composed desktop embeds each live window's owner cell in paint order"
        );
        assert!(
            !r.has_conflict(),
            "a single-operator desktop layout is conflict-free"
        );
        assert!(
            !r.has_darkened(),
            "a full-authority operator reads every window"
        );
        // Each window resolved (the fold recursed into the window's content cell).
        for seg in &r.segments {
            if let Segment::Embedded { resolution, .. } = seg {
                assert!(
                    matches!(resolution, ChildResolution::Rendered(_)),
                    "each live window resolves to a rendered child, got {resolution:?}"
                );
            }
        }
    }

    // (EDITING DRIVES A REAL WORKSPACE CHANGE) Closing a live window is an `Op::Remove`
    // on the projected layout — a REAL layout edit through the embed grammar — and the
    // re-folded desktop no longer embeds that window. The reflexive loop over the live
    // cockpit types.
    #[test]
    fn closing_a_live_window_drives_a_composed_desktop_change() {
        let scene = three_window_scene();
        let viewer = full_authority_viewer(&scene);
        let mut layout = scene_to_composed_doc(&scene, Author(1));
        let resolver = scene_resolver(&scene);

        let before = content_composed(&layout, &viewer, &resolver);
        assert_eq!(
            before.embedded_cells().len(),
            3,
            "three live windows before"
        );

        // EDIT: close the focused middle window (an Op::Remove on its embed-atom).
        layout.apply_patch(Author(1), &[close_window_op(&scene.surfaces[1])]);
        let after = content_composed(&layout, &viewer, &resolver);
        assert_eq!(
            after.embedded_cells(),
            vec![composed_cell_id(&cell(0xA1)), composed_cell_id(&cell(0xC3)),],
            "the closed window drops off the desktop; the order conducts through it"
        );

        // REORDER: place C3 before A1 (an Op::Order — the layout resolution primitive).
        let a1 = window_embed_id(&scene.surfaces[0]);
        let c3 = window_embed_id(&scene.surfaces[2]);
        layout.apply_patch(Author(2), &[Op::Order { from: c3, to: a1 }]);
        let reordered = content_composed(&layout, &viewer, &resolver);
        assert_eq!(
            reordered.embedded_cells().len(),
            2,
            "the reorder kept both windows"
        );
    }

    // (NEGATIVE) An OUT-OF-CAP live window DARKENS — the per-viewer membrane through
    // the REAL fold over the cockpit scene. An operator who lacks one window's owner
    // cap sees that window darkened (citation kept, content withheld), never forged,
    // while the rest of the desktop stays usable. The firmament fog-of-war ON the
    // live desktop.
    #[test]
    fn an_out_of_cap_live_window_darkens() {
        let scene = three_window_scene(); // windows A1, B2, C3
                                          // The operator holds A1 and C3, but NOT B2 (the secret window).
        let viewer = viewer_over([cell(0xA1), cell(0xC3)]);
        let r = render_composed(&scene, &viewer);

        assert!(r.has_darkened(), "the out-of-cap live window darkens");
        // Every window's citation survives — only B2's content is withheld.
        assert_eq!(
            r.embedded_cells().len(),
            3,
            "every live window's citation survives (the secret is darkened, not erased)"
        );
        let secret = composed_cell_id(&cell(0xB2));
        for seg in &r.segments {
            if let Segment::Embedded {
                resolved_cell: Some(c),
                resolution,
                ..
            } = seg
            {
                if *c == secret {
                    assert!(
                        matches!(resolution, ChildResolution::Darkened { .. }),
                        "the out-of-cap window is darkened, got {resolution:?}"
                    );
                } else {
                    assert!(
                        matches!(resolution, ChildResolution::Rendered(_)),
                        "the in-cap windows render"
                    );
                }
            }
        }

        // The owning operator (full authority) sees the WHOLE desktop — the membrane is
        // the only gate. Two operators, the SAME live scene, DIFFERENT views.
        let owner = full_authority_viewer(&scene);
        assert!(
            !render_composed(&scene, &owner).has_darkened(),
            "a full-authority operator reads every live window"
        );
    }

    // The CellId reduction preserves identity: two distinct windows project to two
    // distinct embeds (the anti-forge tooth survives the 32→128-bit fold).
    #[test]
    fn distinct_windows_do_not_collide_under_the_reduction() {
        assert_ne!(composed_cell_id(&cell(0xA1)), composed_cell_id(&cell(0xB2)));
        assert_ne!(
            window_embed_id(&surface(0xA1, 0, false)),
            window_embed_id(&surface(0xB2, 0, false))
        );
        // Stable: the same window always projects to the same embed-atom.
        assert_eq!(composed_cell_id(&cell(0xA1)), composed_cell_id(&cell(0xA1)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compositor::CompositedSurface;
    use dregg_cell::CellId;

    fn cell(tag: u8) -> CellId {
        CellId::from_bytes([tag; 32])
    }

    fn two_surface_scene() -> (CompositorScene, WorkspaceCell) {
        let scene = CompositorScene {
            surfaces: vec![
                CompositedSurface {
                    owner: cell(0xA1),
                    regions: vec![0],
                    content_digest: 100,
                    source_state_root: 10,
                    z_layer: 0,
                    focus_flag: false,
                },
                CompositedSurface {
                    owner: cell(0xB2),
                    regions: vec![1],
                    content_digest: 200,
                    source_state_root: 20,
                    z_layer: 1,
                    focus_flag: true,
                },
            ],
        };
        (scene, WorkspaceCell::new(cell(0x5E), 3))
    }

    #[test]
    fn the_live_scene_adapts_and_commits() {
        // The cockpit adapter projects the LIVE scene onto the verified core and
        // commits to a real heap root (the delegation is wired correctly).
        let (scene, ws) = two_surface_scene();
        let root = desktop_commit(&scene, &ws, Author(1));
        assert_ne!(
            root,
            dregg_cell::empty_heap_root().to_bytes32(),
            "a populated live desktop commits non-empty"
        );

        // The projected document carries the cockpit's tab + focus as fields.
        let doc = scene_to_doc(&scene, &ws, Author(1));
        assert_eq!(
            doc.field(FIELD_ACTIVE_TAB)[0].value,
            "3",
            "the cockpit's active tab is the field"
        );
        assert_eq!(
            doc.field(FIELD_FOCUS).len(),
            1,
            "the focused surface is the focus field"
        );
    }

    #[test]
    fn a_forged_live_surface_changes_the_commitment() {
        let (scene, ws) = two_surface_scene();
        let honest = desktop_commit(&scene, &ws, Author(1));
        let mut forged = scene.clone();
        forged.surfaces[1].owner = cell(0xFF);
        assert_ne!(
            desktop_commit(&forged, &ws, Author(1)),
            honest,
            "a forged live surface changes the root"
        );
    }
}
