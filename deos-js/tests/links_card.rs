//! THE WHAT-LINKS-HERE CARD, PROVEN BY RUNNING — the cockpit's two-way-link panel reborn as a
//! deos-js card, whose view is GENERATED from the focused cell's verified backlinks (the real
//! `Backlinks` witness-graph), projected per-viewer (the link fog-of-war), and EDITABLE FROM
//! WITHIN.
//!
//! The chain proven here:
//!   (a) OPEN → the panel's view-tree carries the question + the focus's dregg:// identity, a
//!       live-bound visible-count row, a visible-of-total row, and one cited backlink row per
//!       observer the viewer is cleared to see.
//!   (b) FOG-OF-WAR → an incomparable (Signature) viewer sees STRICTLY FEWER backlinks than a
//!       root (None) viewer; the god's-eye total is the SAME, only the projection differs.
//!   (c) EDIT FROM WITHIN → `edit_view` relabels the header on the panel's OWN view-source →
//!       the view changes, the edit a RECEIPTED PATCH attributed by BLAME.

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::card_editor::{ViewPatch, ViewTree};
use deos_js::links_card::LINK_COUNT_SLOT;
use deos_js::LinksCard;
use dregg_cell::AuthRequired;
use dregg_cell::{Credential, Requirement};
use dregg_doc::Author;
use dregg_types::CellId;

/// A bare substance cell for the panel card.
fn substance(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let noop = Affordance {
        name: "noop".into(),
        required: Requirement::AtLeast(Credential::Signature),
        apply: Box::new(|_m, _a| vec![(0usize, pack_u64(0))]),
    };
    Applet::mint(pk, [0u8; 32], &[], vec![noop], AuthRequired::Signature)
}

/// A ring of three cells — enough for a witness-graph where each cell has exactly one backlink
/// (its predecessor in the ring).
fn ring() -> [CellId; 3] {
    [
        CellId::from_bytes([0x11; 32]),
        CellId::from_bytes([0x22; 32]),
        CellId::from_bytes([0x33; 32]),
    ]
}

fn links_card(viewer: AuthRequired) -> LinksCard {
    let cells = ring();
    LinksCard::open(
        substance(0x10),
        cells[1], // the focus
        &cells,
        viewer,
        Author(5),
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ Requirement::AtLeast(Credential::Signature),
    )
}

// ── (a) OPEN — the view is GENERATED from the focus's verified backlinks. ──
#[test]
fn open_generates_a_panel_from_the_focused_cells_real_backlinks() {
    let card = links_card(AuthRequired::None);
    let tree = card.view_tree().expect("the generated panel view parses");
    let blob: String = tree
        .walk()
        .iter()
        .filter_map(|n| n.label())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(blob.contains("What Links Here"), "the question is named");
    assert!(
        blob.contains("dregg://"),
        "the focus has a dregg:// identity"
    );
    assert!(
        has_bind_for_slot(&tree, LINK_COUNT_SLOT),
        "the panel carries a live-bound visible-count row"
    );
    // A root (None) viewer clears the gated focus lineage → sees backlinks.
    assert!(
        !card.is_empty(),
        "the root viewer sees the focus's backlinks"
    );
    assert!(
        blob.contains("transcludes dregg://"),
        "a backlink row is a cited two-way link"
    );
    assert!(
        blob.contains("receipt"),
        "the backlink carries its cited receipt"
    );
    assert!(
        blob.contains("commitment"),
        "the backlink carries its content commitment"
    );
}

// ── (b) FOG-OF-WAR — an incomparable viewer sees fewer than the god's-eye. ──
#[test]
fn a_fogged_viewer_sees_fewer_backlinks_than_the_godseye() {
    let root = links_card(AuthRequired::None);
    let fogged = links_card(AuthRequired::Signature);

    assert!(
        !root.is_empty(),
        "the root viewer sees the focus's backlinks"
    );
    assert!(
        fogged.is_empty(),
        "the Signature viewer (incomparable to the Proof lineage) fogs the gated backlinks"
    );
    assert!(
        fogged.backlinks().len() < root.backlinks().len(),
        "the fogged viewer sees STRICTLY fewer backlinks (the fog-of-war)"
    );
    assert_eq!(
        root.total(),
        fogged.total(),
        "the god's-eye docuverse is the same; only the per-viewer projection differs"
    );
    assert!(
        fogged.fogged_count() >= 1,
        "the incomparable viewer has >=1 fogged backlink"
    );
}

// ── publish_count advances the bound visible-count via a real verified turn. ──
#[test]
fn publish_count_advances_the_bound_visible_count_via_a_real_turn() {
    let mut card = links_card(AuthRequired::None);
    assert_eq!(card.live_count(), 0, "the bound count starts at 0");
    let receipt = card.publish_count().expect("publish the visible count");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "a real TurnReceipt committed"
    );
    assert_eq!(
        card.live_count(),
        card.backlinks().len() as u64,
        "the bound count now reflects the visible backlinks (the live ledger the bind re-reads)"
    );
}

// ── (c) EDIT FROM WITHIN — reshape the panel's OWN view, accountably. ──
#[test]
fn editing_the_panel_view_from_within_is_a_receipted_patch_with_blame() {
    let mut card = links_card(AuthRequired::None);
    let source_before = card.view_source();

    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "What Links Here".into(),
            to: "Two-Way Links".into(),
        })
        .expect("the authorized relabel reshape is admitted");
    assert_ne!(card.view_source(), source_before, "the view-source changed");
    assert!(
        edit.tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Two-Way Links")),
        "the re-folded view carries the new header"
    );
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the structural edit left a real provenance receipt"
    );
    assert!(
        card.view_blame().iter().any(|l| l.author == Author(5)),
        "the reshape is blamed on its author"
    );
}

// ── an unfocusable cell (not in the ring) has an honest empty readout. ──
#[test]
fn a_cell_outside_the_ring_has_an_honest_empty_readout() {
    let cells = ring();
    let stranger = CellId::from_bytes([0x99; 32]);
    let card = LinksCard::open(
        substance(0x20),
        stranger,
        &cells,
        AuthRequired::None,
        Author(5),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    assert!(
        card.is_empty(),
        "a cell nobody transcludes has no backlinks"
    );
    assert_eq!(card.total(), 0, "the god's-eye map is also empty for it");
    let blob: String = card
        .view_tree()
        .unwrap()
        .walk()
        .iter()
        .filter_map(|n| n.label())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        blob.contains("no backlinks"),
        "an empty readout renders an honest line"
    );
}

fn has_bind_for_slot(tree: &ViewTree, slot: usize) -> bool {
    tree.walk()
        .iter()
        .any(|n| matches!(n, ViewTree::Bind { props } if props.slot == slot))
}
