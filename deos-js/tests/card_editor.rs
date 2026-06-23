//! THE CARD EDITOR, PROVEN BY RUNNING — a card (a deos-js applet = a cell) is EDITABLE
//! FROM WITHIN deos. HYPERDREGGMEDIA gap #1: inspection becomes authoring, every
//! authoring gesture a real verified turn / a receipted patch, all bounded by the
//! editor's `held` (the cap tooth — an agent authors only the cards it may).
//!
//! The chain proven here:
//!   (a) EDIT THE VIEW (the keystone) — `edit_view` appends a button to a card's view as
//!       a PATCH; the re-folded view-tree CONTAINS the new button; blame attributes the
//!       edit to its author; the structural edit leaves a provenance receipt. Also: a
//!       relabel patch changes a label, accountably.
//!   (b) EDIT A FIELD — `set_field` is a real `SetField` verified turn; a re-read
//!       reflects the new value; the receipt proves it.
//!   (c) ADD AN AFFORDANCE — `add_affordance` welds a new fireable affordance; firing it
//!       commits a new verified turn; the welded affordance travels in a re-minted cell.
//!   (d) THE AGENT DOES IT — a `run_js`-shaped agent snippet drives a CardEditor to patch
//!       a card's view (add a button); the change lands as a receipted patch, BOUNDED by
//!       the agent's `held` (an unauthorized card-edit is refused in-band).

use deos_js::card_editor::{CardEditor, EditError, ViewPatch, ViewTree};
use deos_js::portable::{AffordanceSpec, ApplyOp, AppletManifest, PortableApplet};
use dregg_cell::AuthRequired;
use dregg_doc::Author;

/// A card whose view is a structured view-tree (the shape `deos-view` paints), with a
/// counter model + an `inc` affordance. The starting view: a title + a live count bind.
fn counter_card_manifest() -> AppletManifest {
    let view = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: deos_js::card_editor::TextProps {
                    text: "Counter".into(),
                },
            },
            ViewTree::Bind {
                props: deos_js::card_editor::BindProps {
                    slot: 0,
                    label: "count".into(),
                },
            },
        ],
    };
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![AffordanceSpec {
            name: "inc".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::AddToSlot { slot: 0 },
        }],
        held: AuthRequired::Signature,
        view_source: view.to_json(),
    }
}

/// Mint a card + adopt it for authoring, with the editor authorized (held=None admits the
/// card's `edit_authority`=Signature). Returns the editor.
fn authorized_editor() -> CardEditor {
    let manifest = counter_card_manifest();
    let mut pk = [0u8; 32];
    pk[0] = 0xCA;
    let card = PortableApplet::mint(pk, [0u8; 32], &manifest);
    CardEditor::adopt(
        card,
        manifest,
        Author(7),
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ AuthRequired::Signature,
    )
}

// ── (a) EDIT THE VIEW — the keystone. ──────────────────────────────────────────────
#[test]
fn edit_view_adds_a_button_as_a_receipted_patch_and_blame_attributes_it() {
    let mut editor = authorized_editor();

    // The starting view has NO button (just title + bind).
    let before = editor.view_tree().unwrap();
    assert!(
        !before.has_button_for("inc"),
        "the card starts with no inc button"
    );
    let blame_lines_before = editor.view_blame().len();

    // THE KEYSTONE: add a "+1" button (firing the inc affordance) — a view PATCH.
    let edit = editor
        .edit_view(ViewPatch::AddButton {
            label: "+1".into(),
            turn: "inc".into(),
            arg: 1,
        })
        .expect("the authorized view-patch is admitted");

    // The re-folded view-tree CONTAINS the new button (assert the tree shape).
    assert!(
        edit.tree.has_button_for("inc"),
        "the re-folded view-tree contains the new inc button (the UI changed from within)"
    );
    // The same is true reading the editor's current view (the fold IS the view_source).
    assert!(
        editor.view_tree().unwrap().has_button_for("inc"),
        "the card's current view-source folds to a tree carrying the new button"
    );

    // The edit is a RECEIPTED PATCH — a provenance turn landed on the card's chain.
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the structural view-edit left a real provenance receipt"
    );
    assert_eq!(
        editor.card().receipt_count(),
        1,
        "exactly one verified turn (the authorship provenance) committed for the view-edit"
    );

    // BLAME attributes the edit: the new lines are authored by THIS editor (Author 7),
    // and blame grew (the patch added view-source lines, accountably).
    assert!(
        editor.view_blame().len() > blame_lines_before,
        "the view-patch added view-source lines (a patch, not a recompile)"
    );
    assert!(
        editor
            .view_blame()
            .iter()
            .any(|l| l.author == Author(7)),
        "the view edit is blamed on its author (the accountable patch)"
    );
}

#[test]
fn edit_view_relabel_changes_a_label_accountably() {
    let mut editor = authorized_editor();
    assert!(
        editor
            .view_tree()
            .unwrap()
            .walk()
            .iter()
            .any(|n| n.label() == Some("Counter")),
        "the card starts titled Counter"
    );

    editor
        .edit_view(ViewPatch::Relabel {
            from: "Counter".into(),
            to: "Clicks".into(),
        })
        .expect("the relabel patch is admitted");

    let tree = editor.view_tree().unwrap();
    assert!(
        tree.walk().iter().any(|n| n.label() == Some("Clicks")),
        "the label was changed from within (Counter -> Clicks)"
    );
    assert!(
        !tree.walk().iter().any(|n| n.label() == Some("Counter")),
        "the old label is gone"
    );

    // A relabel matching nothing is a no-op (refused, not a phantom patch).
    let noop = editor.edit_view(ViewPatch::Relabel {
        from: "Nonexistent".into(),
        to: "X".into(),
    });
    assert!(matches!(noop, Err(EditError::NoOp)), "a no-op edit is refused");
}

// ── (b) EDIT A FIELD — a real verified turn. ───────────────────────────────────────
#[test]
fn set_field_is_a_real_verified_turn_and_reread_reflects_it() {
    let mut editor = authorized_editor();
    assert_eq!(editor.card().get_u64(0), 0, "the field starts at 0");

    let receipt = editor.set_field(0, 42).expect("set_field fires a real turn");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "set_field left a real receipt"
    );
    assert_eq!(
        editor.card().get_u64(0),
        42,
        "a re-read reflects the new field value (set via a verified turn)"
    );
    assert_eq!(editor.card().receipt_count(), 1, "exactly one verified turn committed");
}

// ── (c) ADD AN AFFORDANCE — a new fireable turn. ───────────────────────────────────
#[test]
fn add_affordance_adds_a_fireable_turn_that_travels_in_the_cell() {
    let mut editor = authorized_editor();

    // Weld a new "dec" affordance (subtract from slot 0).
    let weld_receipt = editor
        .add_affordance(AffordanceSpec {
            name: "dec".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::SubFromSlot { slot: 0 },
        })
        .expect("the affordance weld is admitted");
    assert_ne!(
        weld_receipt.receipt_hash(),
        [0u8; 32],
        "the affordance weld left a provenance receipt"
    );

    // Seed the field so dec has something to subtract, then FIRE the new affordance —
    // a brand-new verified turn the card did not have before.
    editor.set_field(0, 10).unwrap();
    let before = editor.card().receipt_count();
    let fire = editor
        .card_mut()
        .fire("dec", 3)
        .expect("the newly-welded affordance fires a real verified turn");
    assert_ne!(fire.receipt_hash(), [0u8; 32], "the new affordance fired a real turn");
    assert_eq!(editor.card().get_u64(0), 7, "10 - 3 via the welded affordance");
    assert_eq!(
        editor.card().receipt_count(),
        before + 1,
        "firing the welded affordance committed one more verified turn"
    );

    // The welded affordance TRAVELS in the cell: re-mint from the authored manifest and
    // the new affordance fires on the fresh cell.
    let mut pk = [0u8; 32];
    pk[0] = 0xBE;
    let mut reminted = editor.remint(pk, [0u8; 32]);
    reminted.fire("inc", 5).unwrap();
    let r = reminted
        .fire("dec", 2)
        .expect("the welded affordance is present on the re-minted card");
    assert_ne!(r.receipt_hash(), [0u8; 32]);
    assert_eq!(reminted.get_u64(0), 3, "5 - 2 on the re-minted authored card");
}

// ── (d) THE AGENT DOES IT — run_js-shaped authoring, bounded by held. ──────────────
//
// We drive the CardEditor exactly as the agent's hands (`deos-hermes::run_js`) would,
// once the card-editor is bound into the JS surface: an authoring gesture is applied,
// lands a receipted patch, and is REFUSED in-band when the agent's `held` does not
// satisfy the card's authoring authority. (The run_js plumbing that binds the editor
// into SpiderMonkey is the next wire; the cap tooth + receipt semantics it relies on
// are proven here on the same code path the JS surface calls.)

/// The agent authors a card it IS authorized to: patch its view (add a button) → a
/// receipted patch lands.
#[test]
fn agent_authors_an_authorized_cards_ui_as_a_receipted_patch() {
    // The agent holds a broad-but-attenuated mandate; the target card's authoring
    // authority is Signature, which the agent's held (None = single-custody mandate)
    // satisfies. This mirrors run_js mounting the editor under the agent's `held`.
    let manifest = counter_card_manifest();
    let mut pk = [0u8; 32];
    pk[0] = 0xA6; // the agent's vessel
    let card = PortableApplet::mint(pk, [0u8; 32], &manifest);
    let mut editor = CardEditor::adopt(
        card,
        manifest,
        Author(99), // the AGENT is the author of its patches
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ AuthRequired::Signature,
    );

    // THE AGENT'S GESTURE — add a "reset" button to another card's UI, live.
    let edit = editor
        .edit_view(ViewPatch::AddButton {
            label: "reset".into(),
            turn: "reset".into(),
            arg: 0,
        })
        .expect("the agent's authorized view-patch is admitted");

    assert!(
        edit.tree.has_button_for("reset"),
        "the agent authored a card's UI from within — the new button is in the re-folded view"
    );
    // Every agent edit is a receipt, attributed to the agent (the agent-authors-its-own-
    // UI flex, accountably).
    assert_ne!(edit.receipt.receipt_hash(), [0u8; 32], "the agent's edit left a receipt");
    assert!(
        edit.blame.iter().any(|l| l.author == Author(99)),
        "the agent's patch is blamed on the agent"
    );
}

/// The agent is REFUSED authoring a card it is NOT authorized to: the cap tooth refuses
/// in-band — no patch, no receipt, no view change. The bound the agent cannot exceed.
#[test]
fn agent_cannot_author_a_card_outside_its_held() {
    let manifest = counter_card_manifest();
    let mut pk = [0u8; 32];
    pk[0] = 0xA6;
    let card = PortableApplet::mint(pk, [0u8; 32], &manifest);

    // The card requires PROOF to author; the agent only holds SIGNATURE — an over-reach.
    let mut editor = CardEditor::adopt(
        card,
        manifest,
        Author(99),
        /*held=*/ AuthRequired::Signature,
        /*edit_authority=*/ AuthRequired::Proof,
    );

    let view_before = editor.view_source();
    let refused = editor.edit_view(ViewPatch::AddButton {
        label: "+1".into(),
        turn: "inc".into(),
        arg: 1,
    });
    assert!(
        matches!(refused, Err(EditError::Unauthorized)),
        "the cap tooth refuses an unauthorized card-edit in-band"
    );
    assert_eq!(
        editor.view_source(),
        view_before,
        "the refused edit changed NOTHING — no patch landed"
    );
    assert_eq!(
        editor.card().receipt_count(),
        0,
        "the refused edit left no receipt"
    );

    // A field edit is refused identically (the same cap tooth).
    let refused_field = editor.set_field(0, 1);
    assert!(matches!(refused_field, Err(EditError::Unauthorized)));
    assert_eq!(editor.card().receipt_count(), 0, "still no receipt");
}
