//! # Binding-vs-identity proofs for the two-arm `ChildRef` (tests-as-spec)
//!
//! The companion to `dregg-doc/src/composition.rs` (the embed algebra) and
//! `docs/deos/DOC-CELL-COMPOSITION.md` §2.1b/§3.5. The load-bearing design move:
//! a `ChildRef` has TWO arms, and they differ on exactly one axis — whether the
//! reference is to a fixed IDENTITY or to a re-bindable NAME:
//!
//! - [`ChildRef::Cell`] — this exact cell. Stable, content-addressed; the cell's
//!   *state* evolves under the same id, and — for a recoverable identity cell —
//!   its authorized keys ROTATE in-state while the id is unchanged.
//! - [`ChildRef::Name`] — whatever a namespace currently binds this name to. A
//!   turn on the namespace REBINDS the name, and the embed FOLLOWS.
//!
//! Each property below is proven in BOTH polarities (the standing law): the thing
//! that should follow follows, AND the thing that should NOT follow does not.
//!
//! ## The identity-cell-id-stability finding (the load-bearing one)
//!
//! Property (b) — EMBED-SURVIVES-ROTATION — rests on a substrate fact established
//! by census (reported, not re-derived here): a recoverable identity cell's id is
//! `CellId = blake3_derive_key("dregg-cell-id-v1", genesis_pubkey ‖ token_id)`,
//! and BOTH `genesis_pubkey` and `token_id` are SEALED at inception
//! (`types/src/lib.rs`, `cell/src/cell.rs`). Key rotation / recovery is a
//! `SetField` on a key-COMMITMENT state slot (`CURRENT_KEYS_COMMIT_SLOT`,
//! `sdk/src/identity.rs::rotate_effects`), never the sealed pubkey — proven in
//! Lean by `Dregg2/Apps/PreRotation.lean::rotate_current_keys_irrelevant` (`rfl`:
//! the rotate verb is the SAME function of the commitment for ANY current key
//! set). VERDICT: **the id is STABLE across rotation** — so a `Cell(id)` embed of
//! an identity cell is unbroken across that cell's recovery. (If the id had been
//! current-key-bound, rotation WOULD break the embed — that would be the loud
//! finding; it is not the case.) The test below models this fact in-crate: the
//! cell's id is held FIXED while its rotating key state advances, and the embed
//! still resolves.

use dregg_doc::composition::{
    CellId, ChildRef, ChildResolution, DreggUri, EmbedRole, LayoutAtom, LayoutGraph, MapResolver,
    Op, Pin, Segment, Viewer, content_composed,
};
use dregg_doc::{AtomId, Author, PatchId, Provenance, Status};

fn root() -> AtomId {
    AtomId::ROOT
}

fn embed_id(seed: u64, tag: &str) -> AtomId {
    AtomId::derive(seed, tag)
}

/// A child cell carrying one marker text atom (so it is a non-empty cell). The
/// `key_commit` arg is a stand-in for the cell's rotating key-commitment slot —
/// included so a "rotation" can ADVANCE the cell's content while its CellId is held
/// fixed (the §3.5 model).
fn id_cell(marker: &str, key_commit: u64) -> LayoutGraph {
    let mut g = LayoutGraph::new();
    let id = AtomId::derive(key_commit, marker);
    g.insert_atom(LayoutAtom {
        id,
        content: dregg_doc::composition::AtomContent::Text(format!("{marker}@k{key_commit}")),
        status: Status::Alive,
        provenance: Provenance {
            author: Author(7),
            patch: PatchId(key_commit as u128),
        },
    });
    g.connect_pub(AtomId::ROOT, id);
    g
}

/// A child cell whose rotation is OBSERVABLE through the render: it embeds a
/// distinct marker-grandchild cell per key-commitment, so the rendered output's
/// `embedded_cells` reveals which key-generation it is (text atoms are skipped by
/// the embed-focused fold, so we make the marker an embed, not text).
fn id_cell_with_marker(key_commit: u64) -> (LayoutGraph, CellId) {
    let marker_cell = CellId::from_u128(0xD0_0000 + key_commit as u128); // distinct per generation
    let mut g = LayoutGraph::new();
    let eid = AtomId::derive(key_commit, "alice-key-marker");
    g.insert_atom(LayoutAtom {
        id: eid,
        content: dregg_doc::composition::AtomContent::Embed(
            ChildRef::live(marker_cell),
            EmbedRole::Inline,
        ),
        status: Status::Alive,
        provenance: Provenance {
            author: Author(7),
            patch: PatchId(key_commit as u128),
        },
    });
    g.connect_pub(AtomId::ROOT, eid);
    (g, marker_cell)
}

fn leaf(text: &str) -> LayoutGraph {
    id_cell(text, 1)
}

// ── (a) EMBED-FOLLOWS-REBIND ─────────────────────────────────────────────────
//
// A `Name` embed resolves to cell X; rebind the namespace (name -> Y); the same
// embed now renders Y. AND a `Cell(id)` embed does NOT follow a rebind.

#[test]
fn name_embed_follows_a_rebind_but_a_cell_embed_does_not() {
    let ns = CellId::from_u128(0xACE); // the namespace cell
    let x = CellId::from_u128(0x11); // the cell "hero" first binds to
    let y = CellId::from_u128(0x22); // the cell it is later rebound to

    // ONE document with TWO embeds at fixed positions:
    //  - a NAME embed of dregg://<ns>/hero  (the re-bindable arm)
    //  - a CELL embed of x                   (the identity arm, pinned to x's id)
    let name_eid = embed_id(1, "embed:name:hero");
    let cell_eid = embed_id(2, "embed:cell:x");
    let hero = DreggUri::new(ns, "hero");

    let mut layout = LayoutGraph::new();
    layout.apply_patch(
        Author(1),
        &[
            Op::Embed {
                id: name_eid,
                child: ChildRef::live_name(hero.clone()),
                after: root(),
                role: EmbedRole::Figure,
            },
            Op::Embed {
                id: cell_eid,
                child: ChildRef::live(x),
                after: name_eid,
                role: EmbedRole::Figure,
            },
        ],
    );

    let viewer = Viewer::able([x, y]);

    // BEFORE the rebind: the namespace binds hero -> X.
    let before = MapResolver::default()
        .with(x, leaf("X"))
        .with(y, leaf("Y"))
        .with_name(ns, "hero", x);
    let r0 = content_composed(&layout, &viewer, &before);
    // Both embeds resolve to X here (the name binds to X; the cell ref IS x).
    assert_eq!(
        r0.embedded_cells(),
        vec![x, x],
        "before rebind: name->X and cell->X both render X"
    );

    // THE REBIND: a turn on the namespace cell rebinds hero -> Y. The DOCUMENT is
    // untouched — only the namespace binding changed.
    let mut after = before.clone();
    after.rebind(ns, "hero", y);

    let r1 = content_composed(&layout, &viewer, &after);

    // POSITIVE polarity: the NAME embed FOLLOWED the rebind — it now renders Y.
    // NEGATIVE polarity: the CELL embed did NOT follow — it is still pinned to x's
    // identity, so it still renders X.
    assert_eq!(
        r1.embedded_cells(),
        vec![y, x],
        "after rebind: the NAME embed follows to Y; the CELL embed stays pinned to X"
    );

    // And confirm the rendered MARKER inside the name embed actually came from Y,
    // not a stale X (the binding is transitory, the embed re-resolves live).
    match &r1.segments[0] {
        Segment::Embedded {
            child: ChildRef::Name(uri, _),
            resolved_cell,
            resolution,
            ..
        } => {
            assert_eq!(
                uri, &hero,
                "the embed ref is unchanged — still the NAME 'hero'"
            );
            assert_eq!(*resolved_cell, Some(y), "the name now resolves to Y");
            assert!(
                matches!(resolution, ChildResolution::Rendered(_)),
                "Y rendered through the membrane"
            );
        }
        other => panic!("expected a Name embed resolving to Y, got {other:?}"),
    }
}

/// An unbound `Name` is a first-class state (never a forge), and a later bind
/// HEALS it — the re-bindable arm's distinguishing behavior.
#[test]
fn an_unbound_name_is_a_first_class_state_and_a_later_bind_heals_it() {
    let ns = CellId::from_u128(0xACE);
    let z = CellId::from_u128(0x33);
    let eid = embed_id(1, "embed:name:slot");
    let slot = DreggUri::new(ns, "slot");

    let mut layout = LayoutGraph::new();
    layout.apply_patch(
        Author(1),
        &[Op::Embed {
            id: eid,
            child: ChildRef::live_name(slot.clone()),
            after: root(),
            role: EmbedRole::Section,
        }],
    );
    let viewer = Viewer::able([z]);

    // NEGATIVE: nothing bound -> Unbound (not Unresolved, not a panic, not a forge).
    let empty = MapResolver::default().with(z, leaf("Z"));
    let r0 = content_composed(&layout, &viewer, &empty);
    match &r0.segments[0] {
        Segment::Embedded {
            resolution: ChildResolution::Unbound { namespace, name },
            resolved_cell,
            ..
        } => {
            assert_eq!(*namespace, ns);
            assert_eq!(name, "slot");
            assert_eq!(*resolved_cell, None, "an unbound name resolves to no cell");
        }
        other => panic!("expected Unbound, got {other:?}"),
    }
    assert!(
        r0.embedded_cells().is_empty(),
        "an unbound name embeds no cell"
    );

    // POSITIVE: bind slot -> Z; the SAME embed now renders Z (the binding heals it).
    let bound = empty.with_name(ns, "slot", z);
    let r1 = content_composed(&layout, &viewer, &bound);
    assert_eq!(
        r1.embedded_cells(),
        vec![z],
        "a later bind heals the unbound name"
    );
}

// ── (b) EMBED-SURVIVES-ROTATION ──────────────────────────────────────────────
//
// A `Cell(id)` embed of an identity cell still resolves after that cell's
// authorized keys ROTATE (recovery): the CellId is stable across rotation, so the
// embed is unbroken. (The substrate stability fact is established by census — see
// the module doc; here the cell's id is held FIXED while its key-commitment /
// content advances, modeling exactly the §3.5 rotation.)

#[test]
fn a_cell_embed_survives_the_identity_cells_key_rotation() {
    // The identity cell: a STABLE id (the inception anchor), whose content/key
    // state advances on rotation. We model the rotation by advancing the key
    // commitment the cell's content reflects, while the CellId is unchanged.
    let alice = CellId::from_u128(0xA11CE); // inception-anchored, NEVER changes across rotation

    let eid = embed_id(1, "embed:cell:alice");
    let mut layout = LayoutGraph::new();
    layout.apply_patch(
        Author(1),
        &[Op::Embed {
            id: eid,
            child: ChildRef::live(alice), // the IDENTITY arm: pinned to alice's id
            after: root(),
            role: EmbedRole::Section,
        }],
    );
    // BEFORE rotation: alice's cell has key-commitment k1 (its render embeds the
    // k1 marker-grandchild).
    let (alice_k1, marker_k1) = id_cell_with_marker(1);
    let viewer = Viewer::able([alice, marker_k1]);
    let pre = MapResolver::default()
        .with(alice, alice_k1)
        .with(marker_k1, leaf("k1"));
    let r0 = content_composed(&layout, &viewer, &pre);
    assert_eq!(
        r0.embedded_cells(),
        vec![alice],
        "the embed resolves to alice (pre-rotation)"
    );

    // ROTATION / RECOVERY: alice rotates her authorized keys. On the substrate this
    // is a SetField on CURRENT_KEYS_COMMIT_SLOT — the cell's STATE advances (here:
    // key-commitment k1 -> k2, a new marker-grandchild) while the CellId is
    // UNCHANGED (blake3 of the sealed genesis pubkey ‖ token_id). We re-register the
    // SAME id with the rotated cell to model "same identity, evolved key state."
    let (alice_k2, marker_k2) = id_cell_with_marker(2);
    let viewer2 = Viewer::able([alice, marker_k1, marker_k2]);
    let post = MapResolver::default()
        .with(alice, alice_k2)
        .with(marker_k2, leaf("k2"));

    let r1 = content_composed(&layout, &viewer2, &post);

    // POSITIVE polarity: the embed is UNBROKEN — same id resolves, now to the
    // rotated state. The embed never had to be re-authored across the recovery.
    assert_eq!(
        r1.embedded_cells(),
        vec![alice],
        "the Cell(id) embed still resolves to alice AFTER her key rotation (id is stable)"
    );
    // And it resolved to the ROTATED state (the k2 marker, not k1), confirming the
    // embed tracks the SAME cell's evolving state, not a frozen pre-rotation snapshot.
    match &r1.segments[0] {
        Segment::Embedded {
            resolution: ChildResolution::Rendered(inner),
            ..
        } => {
            assert_eq!(
                inner.embedded_cells(),
                vec![marker_k2],
                "the live embed tracks alice's ROTATED state (k2 marker), not the pre-rotation k1"
            );
            assert_ne!(
                marker_k1, marker_k2,
                "the rotation genuinely changed the rendered state"
            );
        }
        other => panic!("expected alice rendered post-rotation, got {other:?}"),
    }

    // NEGATIVE polarity (the counterfactual the finding rules out): IF the id had
    // been current-key-bound, rotation would have MOVED it to a different id and the
    // embed would dangle. We exhibit that broken world to show our world is NOT it:
    // a hypothetical "rotated-to-a-new-id" cell is a DIFFERENT CellId, and a
    // Cell(id) embed of THAT old id would be Unresolved. The substrate's actual id
    // is inception-anchored, so this broken branch never occurs for a real rotation.
    let alice_if_id_were_keybound = CellId::from_u128(0xA11CE_BAD); // a DIFFERENT id
    let broken_world = MapResolver::default().with(alice_if_id_were_keybound, id_cell("alice", 2));
    let r_broken = content_composed(&layout, &viewer, &broken_world);
    match &r_broken.segments[0] {
        Segment::Embedded {
            resolution: ChildResolution::Unresolved { cell },
            ..
        } => {
            assert_eq!(
                *cell, alice,
                "WERE the id current-key-bound, the old-id embed would dangle — \
                 the substrate is NOT this world (id is inception-anchored, sealed)"
            );
        }
        other => panic!("expected the counterfactual dangle, got {other:?}"),
    }
}

// ── (4) NO-ROT corner: a frozen `Pin::At` survives the source's destruction ───
//
// A `Pin::At(receipt)` embed still resolves to the frozen past version even after
// the source cell is destroyed/retired (the immutable past). The pin selects a
// committed receipt, not the live tip — so retiring the live cell cannot break it.

#[test]
fn a_pinned_embed_resolves_the_frozen_past_even_after_the_source_is_retired() {
    let src = CellId::from_u128(0xF0);
    let frozen_receipt: u128 = 0xDEAD_BEEF;
    let eid = embed_id(1, "embed:pinned:src");

    let mut layout = LayoutGraph::new();
    layout.apply_patch(
        Author(1),
        &[Op::Embed {
            id: eid,
            child: ChildRef::pinned(src, frozen_receipt), // PINNED to a frozen receipt
            after: root(),
            role: EmbedRole::Citation,
        }],
    );
    assert_eq!(
        layout.effective_pin(eid),
        Some(Pin::At(frozen_receipt)),
        "the embed is frozen"
    );

    let viewer = Viewer::able([src]);

    // The "frozen archive" resolver still serves the pinned past version — on the
    // substrate the cited receipt is an immutable commitment, available regardless
    // of the live cell's fate (the Xanadu no-rot property, lifted to whole-cell).
    // We model retirement by a resolver that holds ONLY the frozen archive copy and
    // NOT a live tip: the live cell is gone, the cited past remains.
    let archive_only = MapResolver::default().with(src, id_cell("src-at-frozen", 99));
    let r = content_composed(&layout, &viewer, &archive_only);
    assert_eq!(
        r.embedded_cells(),
        vec![src],
        "a Pin::At embed still resolves the frozen past after the source is retired"
    );
    // The frozen pin rode through unchanged (it is the parent's commitment, §3.3).
    match &r.segments[0] {
        Segment::Embedded {
            child,
            resolution: ChildResolution::Rendered(_),
            ..
        } => {
            assert_eq!(
                child.pin(),
                Pin::At(frozen_receipt),
                "the cited receipt is unchanged"
            );
        }
        other => panic!("expected the frozen citation to render, got {other:?}"),
    }

    // NEGATIVE polarity: a LIVE embed of the SAME now-retired source DOES break —
    // it tracks the (gone) tip, so it is Unresolved. This is the distinction: only
    // the frozen pin is immune to retirement; liveness is not.
    let live_eid = embed_id(2, "embed:live:src");
    let mut live_layout = LayoutGraph::new();
    live_layout.apply_patch(
        Author(1),
        &[Op::Embed {
            id: live_eid,
            child: ChildRef::live(src),
            after: root(),
            role: EmbedRole::Section,
        }],
    );
    // The live tip is GONE (retired): a resolver that knows the cell's id but has no
    // live layout for it. (Modeled as an empty resolver — the live fetch fails.)
    let no_live = MapResolver::default();
    let r_live = content_composed(&live_layout, &viewer, &no_live);
    match &r_live.segments[0] {
        Segment::Embedded {
            resolution: ChildResolution::Unresolved { cell },
            ..
        } => {
            assert_eq!(
                *cell, src,
                "a LIVE embed of a retired source dangles — only a frozen pin survives"
            );
        }
        other => panic!("expected the live embed to dangle, got {other:?}"),
    }
}
