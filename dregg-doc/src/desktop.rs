//! THE DESKTOP IS A DOCUMENT — projecting a live cockpit workspace (an ordered
//! set of surfaces + a tab/focus selector) as a `dregg_doc` document.
//!
//! ember's reading: *"the whole starbridge is kinda like a cell document."* This
//! module makes that literal and **green-verifiable in isolation**: it lives in
//! the document crate (which builds standalone) over a tiny renderer-agnostic
//! [`DesktopSurface`] value, so the WELD logic + the real `substrate_commit` are
//! tested here without dragging the gpui cockpit's heavy toolchain in. The cockpit
//! side (`starbridge-v2/src/desktop_doc.rs`) is the thin adapter that maps its
//! live `compositor::CompositedSurface` onto [`DesktopSurface`].
//!
//! The projection is almost mechanical because the two shapes ARE the same shape:
//!
//! | desktop notion | document notion |
//! |---|---|
//! | a surface (a window onto a cell) | an **atom** (content = owner ‖ root ‖ digest) |
//! | the z-order (paint order) | the **order relation** (chained `Add` edges) |
//! | the active tab | a single-valued **field** `"active_tab"` |
//! | the focus holder | a single-valued **field** `"focus"` |
//! | a minimized surface | a **tombstoned** atom (off the walk, kept in the graph) |
//! | the whole workspace | a **document** committed by its heap root |
//!
//! Once the desktop IS a document, every document affordance applies to the
//! desktop itself: **transclude** a remote desktop's surface as a verified live
//! tile; **branch/fork** a layout into a confined virtual branch then `Stitch` the
//! good arrangement back; **time-travel** a past layout via `History::replay_to`;
//! and — the reflexive payoff — two devices contending the same single-valued
//! desktop field (focus, active tab) produce a **first-class conflict state**, the
//! firmament dual of the compositor's T3 focus-exclusive *refusal*: instead of
//! refusing the contended scene, the document *represents* it as a resolvable
//! clash (the right semantics for the multi-device "one cap across distance" case).

use crate::{AtomId, Author, DocGraph, Op, Patch, Rendered, content};

/// A renderer-agnostic description of one cockpit surface — the minimal shape the
/// desktop→document projection needs. The cockpit's `compositor::CompositedSurface`
/// maps onto this (owner id bytes, the state-root it projects, its frame digest,
/// its z-layer, and whether it holds focus).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DesktopSurface {
    /// The owning cell's identity (its 32-byte id) — the authority lineage the
    /// content-addressed atom binds (a window cannot describe a cell it is not
    /// without changing the commitment).
    pub owner: [u8; 32],
    /// The cell state-root this surface is a genuine projection of.
    pub source_state_root: u64,
    /// The frame digest currently shown.
    pub content_digest: u64,
    /// The z-layer (paint order; back-to-front).
    pub z_layer: i64,
    /// Whether this surface holds input focus.
    pub focus_flag: bool,
}

/// The document field carrying the workspace's ACTIVE TAB selector — single-valued
/// (non-monotone), so two concurrent tab selections CLASH (a first-class
/// `Regime::Field` conflict) rather than silently last-writer-win.
pub const FIELD_ACTIVE_TAB: &str = "active_tab";

/// The document field carrying the workspace's FOCUS holder — single-valued for
/// the same reason the compositor's T3 gate is focus-exclusive: at most one
/// surface holds input. Two devices both claiming focus is a *resolvable conflict*
/// in the document reading.
pub const FIELD_FOCUS: &str = "focus";

/// The seed domain for surface-atom ids (so a desktop atom never collides with a
/// prose atom derived from the same content).
const SURFACE_SEED: u64 = 0xDE5C_0DE5;

/// A short hex of the leading id bytes (renderer-agnostic; just for legible,
/// stable atom content — the full id is what binds, via the content-address).
fn short_owner(owner: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in &owner[..8] {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Canonical, light-client-checkable content for a surface atom: it binds the
/// surface's OWNER, the SOURCE-STATE-ROOT it projects, and its frame DIGEST.
fn surface_content(s: &DesktopSurface) -> String {
    format!(
        "surface owner={} root={} digest={} z={}",
        short_owner(&s.owner),
        s.source_state_root,
        s.content_digest,
        s.z_layer,
    )
}

/// The content-addressed id a given surface projects to (so a `tombstone_surface`
/// targets the same atom `scene_to_doc` created).
pub fn surface_atom_id(s: &DesktopSurface) -> AtomId {
    AtomId::derive(SURFACE_SEED, &surface_content(s))
}

/// Project a workspace (ordered, paint-order `surfaces` + the `active_tab`
/// selector) into a `dregg_doc` document. THE WELD: each surface becomes an atom
/// chained after the previous (so a walk IS the paint order); the active tab + the
/// focused surface become single-valued fields. Built by APPLYING a [`Patch`] of
/// the ordinary document grammar — a desktop layout is authored by exactly the same
/// `Add`/`SetField` ops a prose edit is. `author` binds into the commitment.
pub fn scene_to_doc(surfaces: &[DesktopSurface], active_tab: usize, author: Author) -> DocGraph {
    let mut ops: Vec<Op> = Vec::new();

    ops.push(Op::SetField {
        name: FIELD_ACTIVE_TAB.to_string(),
        value: active_tab.to_string(),
        superseding: false,
    });
    if let Some(focus) = surfaces.iter().find(|s| s.focus_flag) {
        ops.push(Op::SetField {
            name: FIELD_FOCUS.to_string(),
            value: short_owner(&focus.owner),
            superseding: false,
        });
    }

    let mut prev = AtomId::ROOT;
    for s in surfaces {
        let (id, add) = Patch::add(SURFACE_SEED, &surface_content(s), prev);
        ops.push(add);
        prev = id;
    }

    Patch::by(author, ops).apply_to(&DocGraph::new())
}

/// Tombstone (minimize) one surface in the document reading: a `Delete` patch. The
/// surface-atom stays in the graph (provenance retained, time-travellable —
/// un-minimize = the inverse) but drops off the rendered walk.
pub fn tombstone_surface(surface: &DesktopSurface, author: Author) -> Patch {
    Patch::by(
        author,
        [Op::Delete {
            id: surface_atom_id(surface),
        }],
    )
}

/// Author a layout edit as a *superseding* `SetField` patch on the active tab —
/// the reflexive loop: the document grammar editing the document that IS the
/// desktop. (On the cockpit substrate this rides `WorkspaceCell::commit`, already a
/// real `Effect::SetField` turn, so a layout edit is a witnessed turn.)
pub fn set_active_tab(new_active_tab: usize, author: Author) -> Patch {
    Patch::by(
        author,
        [Op::SetField {
            name: FIELD_ACTIVE_TAB.to_string(),
            value: new_active_tab.to_string(),
            superseding: true,
        }],
    )
}

/// Author a *superseding* focus resolution (one device wins a contended focus by an
/// explicit decision — never a silent loss).
pub fn resolve_focus(winner: &[u8; 32], author: Author) -> Patch {
    Patch::by(
        author,
        [Op::SetField {
            name: FIELD_FOCUS.to_string(),
            value: short_owner(winner),
            superseding: true,
        }],
    )
}

/// Render the desktop-document (the linearized walk + any first-class conflict
/// regions). A clean desktop renders as an ordered surface list; a contended one
/// renders with a first-class conflict region.
pub fn render(surfaces: &[DesktopSurface], active_tab: usize, author: Author) -> Rendered {
    content(&scene_to_doc(surfaces, active_tab, author))
}

/// The REAL desktop commitment: the production sorted-Poseidon2 heap root over the
/// projected document. This is what makes a desktop layout shareable +
/// light-client-checkable: two parties agree they see the same desktop iff this
/// root matches; a forged surface changes it (the anti-forge tooth, inherited).
pub fn desktop_commit(surfaces: &[DesktopSurface], active_tab: usize, author: Author) -> [u8; 32] {
    crate::substrate_commit(&scene_to_doc(surfaces, active_tab, author))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn surface(tag: u8, z: i64, focus: bool) -> DesktopSurface {
        DesktopSurface {
            owner: [tag; 32],
            source_state_root: tag as u64 * 10,
            content_digest: tag as u64 * 100,
            z_layer: z,
            focus_flag: focus,
        }
    }

    /// A two-surface desktop: A (z=0) under B (z=1, focused), active tab 3.
    fn two_surface() -> Vec<DesktopSurface> {
        vec![surface(0xA1, 0, false), surface(0xB2, 1, true)]
    }

    #[test]
    fn the_desktop_projects_to_a_document_walk_in_z_order() {
        let r = render(&two_surface(), 3, Author(1));
        let walk = r.to_marked_string();
        let a = short_owner(&[0xA1; 32]);
        let b = short_owner(&[0xB2; 32]);
        let pa = walk.find(&a).expect("surface A in the desktop document");
        let pb = walk.find(&b).expect("surface B in the desktop document");
        assert!(
            pa < pb,
            "the document walk IS the paint order (A under B): {walk}"
        );
        assert!(
            !r.has_conflict(),
            "a single-operator desktop is conflict-free"
        );
    }

    #[test]
    fn the_active_tab_and_focus_are_single_valued_fields() {
        let doc = scene_to_doc(&two_surface(), 3, Author(1));
        assert_eq!(doc.field(FIELD_ACTIVE_TAB).len(), 1);
        assert_eq!(doc.field(FIELD_ACTIVE_TAB)[0].value, "3");
        assert_eq!(doc.field(FIELD_FOCUS).len(), 1);
        assert_eq!(doc.field(FIELD_FOCUS)[0].value, short_owner(&[0xB2; 32]));
    }

    #[test]
    fn the_desktop_commits_to_a_real_heap_root() {
        let root = desktop_commit(&two_surface(), 3, Author(1));
        assert_ne!(
            root,
            dregg_cell::empty_heap_root(),
            "a populated desktop is not the empty root"
        );
        assert_eq!(
            root,
            desktop_commit(&two_surface(), 3, Author(1)),
            "the same desktop commits equal"
        );
    }

    #[test]
    fn a_rearranged_desktop_has_a_different_commitment() {
        let root0 = desktop_commit(&two_surface(), 3, Author(1));
        let root1 = desktop_commit(&two_surface(), 7, Author(1)); // a layout edit (tab)
        assert_ne!(
            root0, root1,
            "a different desktop layout -> a different commitment"
        );
    }

    #[test]
    fn a_forged_surface_owner_changes_the_commitment() {
        let honest = desktop_commit(&two_surface(), 3, Author(1));
        let mut forged = two_surface();
        forged[1].owner = [0xFF; 32]; // B claims to be a cell it is not
        assert_ne!(
            desktop_commit(&forged, 3, Author(1)),
            honest,
            "a forged surface owner changes the desktop commitment"
        );
    }

    #[test]
    fn two_devices_contending_focus_is_a_first_class_conflict_not_a_clobber() {
        // THE REFLEXIVE PAYOFF (firmament dual of the compositor's T3 refusal): two
        // devices arrange the SAME desktop and each claims focus on a DIFFERENT
        // surface. The compositor REFUSES that scene (DoubleFocus). The DOCUMENT
        // reading represents it as a resolvable first-class conflict.
        let base = scene_to_doc(&two_surface(), 3, Author(1));
        let a = short_owner(&[0xA1; 32]);
        let b = short_owner(&[0xB2; 32]);
        let d1 = Patch::by(
            Author(1),
            [Op::SetField {
                name: FIELD_FOCUS.into(),
                value: a.clone(),
                superseding: false,
            }],
        )
        .apply_to(&base);
        let d2 = Patch::by(
            Author(2),
            [Op::SetField {
                name: FIELD_FOCUS.into(),
                value: b.clone(),
                superseding: false,
            }],
        )
        .apply_to(&base);
        let merged = crate::merge(&d1, &d2);

        let vals: Vec<&str> = merged
            .field(FIELD_FOCUS)
            .iter()
            .map(|x| x.value.as_str())
            .collect();
        assert!(
            vals.contains(&a.as_str()),
            "device 1's focus claim survives: {vals:?}"
        );
        assert!(
            vals.contains(&b.as_str()),
            "device 2's focus claim survives: {vals:?}"
        );
        assert!(
            vals.len() >= 2,
            "the contended focus is a first-class clash, not a clobber"
        );
        assert!(
            content(&merged)
                .field_conflicts()
                .any(|c| c.alternatives.len() >= 2),
            "the desktop renders a first-class focus conflict (both claims kept)"
        );

        // RESOLUTION: a superseding patch collapses the clash (one device wins, by an
        // EXPLICIT decision — never a silent loss).
        let resolved = resolve_focus(&[0xB2; 32], Author(1)).apply_to(&merged);
        assert_eq!(
            resolved.field(FIELD_FOCUS).len(),
            1,
            "the resolution collapses the clash"
        );
        assert_eq!(
            resolved.field(FIELD_FOCUS)[0].value,
            b,
            "B wins by an explicit resolving patch"
        );
    }

    #[test]
    fn minimizing_a_surface_tombstones_it_off_the_walk_but_keeps_it_in_the_graph() {
        let base = scene_to_doc(&two_surface(), 3, Author(1));
        let b = short_owner(&[0xB2; 32]);
        assert!(
            content(&base).to_marked_string().contains(&b),
            "B is on the walk before minimize"
        );

        let minimized = tombstone_surface(&surface(0xB2, 1, true), Author(1)).apply_to(&base);
        assert!(
            !content(&minimized).to_marked_string().contains(&b),
            "B drops off the rendered desktop after minimize"
        );
        assert_eq!(
            minimized.atom_count(),
            base.atom_count(),
            "the minimized surface is tombstoned, not deleted from the graph"
        );
    }

    #[test]
    fn a_concurrent_tab_selection_clashes_then_resolves() {
        // The active tab is single-valued too: two devices selecting different tabs
        // concurrently clash, and a superseding patch resolves it.
        let base = scene_to_doc(&two_surface(), 3, Author(1));
        let d1 = Patch::by(
            Author(1),
            [Op::SetField {
                name: FIELD_ACTIVE_TAB.into(),
                value: "5".into(),
                superseding: false,
            }],
        )
        .apply_to(&base);
        let d2 = Patch::by(
            Author(2),
            [Op::SetField {
                name: FIELD_ACTIVE_TAB.into(),
                value: "9".into(),
                superseding: false,
            }],
        )
        .apply_to(&base);
        let merged = crate::merge(&d1, &d2);
        // base set "3", then both concurrently set 5 and 9 -> the clash carries the
        // concurrent values (the base "3" is superseded by neither alone; both 5,9 live).
        let vals: Vec<&str> = merged
            .field(FIELD_ACTIVE_TAB)
            .iter()
            .map(|x| x.value.as_str())
            .collect();
        assert!(
            vals.contains(&"5") && vals.contains(&"9"),
            "both tab selections clash: {vals:?}"
        );

        let resolved = set_active_tab(9, Author(1)).apply_to(&merged);
        assert_eq!(
            resolved.field(FIELD_ACTIVE_TAB).len(),
            1,
            "the resolution collapses the tab clash"
        );
        assert_eq!(resolved.field(FIELD_ACTIVE_TAB)[0].value, "9");
    }
}
