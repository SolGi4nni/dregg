//! THE REFLECTIVE-INSPECTOR CARD, PROVEN BY RUNNING — the cockpit's inspector reborn as a
//! deos-js card, whose view is GENERATED from a focused cell's moldable faces, fires real
//! verified turns, and is EDITABLE FROM WITHIN (each reshape a receipted patch with blame).
//!
//! The chain proven here:
//!   (a) FOCUS → the inspector card's view-tree is generated from the focused cell's faces:
//!       a RawFields section (a live `Bind` row per scalar state slot, labeled `Text` for the
//!       structural substances) + an Affordances section (a `Button` per cap-gated affordance).
//!   (b) FIRE → firing an affordance from the inspector commits a REAL cap-gated verified turn
//!       on the live World; the bound field advances (the `Bind` row the renderer re-reads).
//!   (c) EDIT FROM WITHIN → `edit_view` relabels a face / appends a row on the inspector card's
//!       OWN view-source → the view changes, the edit a RECEIPTED PATCH attributed by BLAME.

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::card_editor::{ViewPatch, ViewTree};
use deos_js::InspectorCard;
use dregg_cell::AuthRequired;
use dregg_doc::Author;

/// A focused cell: slot 0 holds a counter (seeded to 1 so the RawFields face surfaces it as a
/// revealed state slot → a LIVE bind row), with an `inc` affordance (Signature-gated, held).
fn counter_card(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let inc = Affordance {
        name: "inc".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    Applet::mint(
        pk,
        [0u8; 32],
        &[(0usize, pack_u64(1))],
        vec![inc],
        AuthRequired::Signature,
    )
}

/// Focus an inspector card on a counter cell, authorized to reshape itself (held=None admits
/// edit_authority=Signature).
fn focused_inspector() -> InspectorCard {
    InspectorCard::focus(
        counter_card(0xAB),
        Author(42),
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ AuthRequired::Signature,
    )
}

// ── (a) FOCUS — the view is GENERATED from the focused cell's faces. ──────────────────
#[test]
fn focus_generates_a_view_from_the_cells_raw_fields_and_affordances() {
    let card = focused_inspector();
    let tree = card.view_tree().expect("the generated view parses");

    // The Affordances face: a button for the focused cell's `inc` affordance (cap-gated,
    // held → visible → a fireable button in the inspector view).
    assert!(
        tree.has_button_for("inc"),
        "the inspector view carries a button for the focused cell's `inc` affordance"
    );

    // The RawFields face: a LIVE bind row for the scalar state slot 0 (the counter), bound so
    // a turn that writes slot 0 updates the displayed row.
    assert!(
        has_bind_for_slot(&tree, 0),
        "the inspector view carries a live-bound row for the focused cell's state slot 0"
    );

    // The faces' section labels are rendered as text (relabelable from within — see (c)).
    // The default face uses warm, jargon-free section titles (the consumer-delight pass):
    // the RawFields section is "What this holds", the Affordances section "What you can do".
    assert!(
        tree.walk()
            .iter()
            .any(|n| n.label() == Some("What this holds")),
        "the RawFields section is labeled"
    );
    assert!(
        tree.walk()
            .iter()
            .any(|n| n.label() == Some("What you can do")),
        "the Affordances section is labeled"
    );
}

// ── (b) FIRE — an affordance from the inspector advances the bound field. ─────────────
#[test]
fn firing_an_affordance_from_the_inspector_advances_the_bound_field() {
    let mut card = focused_inspector();
    assert_eq!(card.get_u64(0), 1, "the counter starts at its seed (1)");

    let receipt = card
        .fire("inc", 1)
        .expect("the `inc` affordance fires a verified turn");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "a real TurnReceipt committed on the live World"
    );
    assert_eq!(
        card.get_u64(0),
        2,
        "the bound slot-0 row advanced 1 -> 2 (the live ledger the bind re-reads)"
    );
    assert_eq!(
        card.card().receipt_count(),
        1,
        "exactly one verified turn committed"
    );
}

// ── (c) EDIT FROM WITHIN — the keystone: reshape the inspector's OWN view. ────────────
#[test]
fn editing_the_inspector_view_from_within_is_a_receipted_patch_with_blame() {
    let mut card = focused_inspector();
    let source_before = card.view_source();
    let blame_before = card.view_blame().len();

    // RELABEL a face from within: "What this holds" → "Substance".
    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "What this holds".into(),
            to: "Substance".into(),
        })
        .expect("the authorized relabel reshape is admitted");

    // The view CHANGED (the source differs; the re-folded tree carries the new label).
    assert_ne!(
        card.view_source(),
        source_before,
        "the inspector's view-source changed (it reshaped from within)"
    );
    assert!(
        edit.tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Substance")),
        "the re-folded view-tree carries the new face label"
    );
    assert!(
        !edit
            .tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("What this holds")),
        "the old label is gone"
    );

    // The reshape is a RECEIPTED PATCH — a provenance turn landed on the card's chain.
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the structural view-edit left a real provenance receipt"
    );

    // BLAME attributes the reshape to its author.
    assert!(
        card.view_blame().iter().any(|l| l.author == Author(42)),
        "the view reshape is blamed on its author (the accountable patch)"
    );

    // ADD a new row from within: append a button (a new fireable affordance row).
    let edit2 = card
        .edit_view(ViewPatch::AddButton {
            label: "inc ×5".into(),
            turn: "inc".into(),
            arg: 5,
        })
        .expect("the authorized add-button reshape is admitted");
    assert!(
        edit2.tree.has_button_for("inc"),
        "the inspector view now carries the appended button"
    );
    assert!(
        card.view_blame().len() > blame_before,
        "the reshapes added view-source lines (patches, not a recompile)"
    );
    assert_eq!(
        card.card().receipt_count(),
        2,
        "two reshapes → two provenance receipts on the card's chain"
    );
}

// ── the cap tooth — an unauthorized reshape is refused in-band (no patch, no receipt). ──
#[test]
fn an_unauthorized_reshape_is_refused_in_band() {
    // held=Signature does NOT satisfy edit_authority=Proof → the authoring tooth refuses.
    let mut card = InspectorCard::focus(
        counter_card(0xCD),
        Author(7),
        /*held=*/ AuthRequired::Signature,
        /*edit_authority=*/ AuthRequired::Proof,
    );
    let before = card.view_source();
    let err = card.edit_view(ViewPatch::AddText {
        text: "sneaky".into(),
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
        card.card().receipt_count(),
        0,
        "no receipt on an unauthorized reshape"
    );
}

/// Does the tree contain a `Bind` node reading `slot`?
fn has_bind_for_slot(tree: &ViewTree, slot: usize) -> bool {
    tree.walk()
        .iter()
        .any(|n| matches!(n, ViewTree::Bind { props } if props.slot == slot))
}
