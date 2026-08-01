//! THE DYNAMICS-FEED CARD, PROVEN BY RUNNING — the cockpit's dynamics feed reborn as a
//! deos-js card, whose view is GENERATED from a live stream of recent turns/receipts, APPENDS
//! a row (with a live-bound count) as a new turn is observed, and is EDITABLE FROM WITHIN.
//!
//! The chain proven here:
//!   (a) OPEN → the feed card's view-tree carries a header, a live `Bind` count, and a
//!       "(no turns observed yet)" placeholder row.
//!   (b) OBSERVE → observing a new turn appends a `@h<height> · <kind> · <author>` row,
//!       advances the bound count via a REAL verified turn (the live ledger the bind re-reads),
//!       and the rows are most-recent-LAST.
//!   (c) EDIT FROM WITHIN → `edit_view` relabels the header / appends a row on the card's OWN
//!       view-source → the view changes, the edit a RECEIPTED PATCH attributed by BLAME.

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::card_editor::{ViewPatch, ViewTree};
use deos_js::dynamics_card::FEED_LEN_SLOT;
use deos_js::{DynamicsCard, FeedEntry};
use dregg_cell::AuthRequired;
use dregg_cell::{Credential, Requirement};
use dregg_doc::Author;

/// A bare substance cell for the feed card (one no-op affordance; the card registers its own
/// internal field-bump affordances). Held=None admits the edit_authority=Signature.
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

fn feed_card() -> DynamicsCard {
    DynamicsCard::open(
        substance(0xD1),
        Author(7),
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ Requirement::AtLeast(Credential::Signature),
    )
}

fn entry(height: u64, kind: &str, author_seed: u8) -> FeedEntry {
    let mut a = [0u8; 32];
    a[0] = author_seed;
    FeedEntry::new(height, kind, &a)
}

// ── (a) OPEN — the view is GENERATED with a header, a bound count, and a placeholder. ──
#[test]
fn open_generates_a_feed_view_with_header_bound_count_and_placeholder() {
    let card = feed_card();
    let tree = card.view_tree().expect("the generated feed view parses");
    assert!(
        tree.walk().iter().any(|n| n.label() == Some("Dynamics")),
        "the feed has a header"
    );
    assert!(
        has_bind_for_slot(&tree, FEED_LEN_SLOT),
        "the feed carries a live-bound entry-count row"
    );
    assert!(
        tree.walk()
            .iter()
            .any(|n| n.label() == Some("(no turns observed yet)")),
        "an empty feed renders an honest placeholder, not a blank"
    );
    assert_eq!(card.live_len(), 0, "no turns observed yet");
}

// ── (b) OBSERVE — a new turn APPENDS a row + advances the bound count via a real turn. ──
#[test]
fn observing_a_turn_appends_a_row_and_advances_the_bound_count() {
    let mut card = feed_card();

    let r1 = card
        .observe(entry(1, "turn committed", 0xAA))
        .expect("observe a committed turn");
    assert_ne!(
        r1.receipt_hash(),
        [0u8; 32],
        "the append left a real TurnReceipt"
    );
    assert_eq!(
        card.live_len(),
        1,
        "the bound count advanced 0 -> 1 (the live ledger)"
    );
    assert_eq!(card.entries().len(), 1, "one entry in the stream");

    let r2 = card
        .observe(entry(2, "balance flowed", 0xBB))
        .expect("observe a second turn");
    assert_ne!(
        r2.receipt_hash(),
        [0u8; 32],
        "the second append left a receipt"
    );
    assert_eq!(card.live_len(), 2, "the bound count advanced 1 -> 2");

    // The rows are present, most-recent-LAST, each carrying the (height, kind, author) triple.
    let tree = card.view_tree().expect("re-folded feed view parses");
    let labels: Vec<&str> = tree.walk().iter().filter_map(|n| n.label()).collect();
    let blob = labels.join("\n");
    assert!(
        blob.contains("@h1 · turn committed"),
        "the first turn row landed: {blob}"
    );
    assert!(
        blob.contains("@h2 · balance flowed"),
        "the second turn row landed"
    );
    // Most-recent-LAST: the @h2 row appears after the @h1 row in the flattened order.
    let i1 = labels.iter().position(|l| l.starts_with("@h1")).unwrap();
    let i2 = labels.iter().position(|l| l.starts_with("@h2")).unwrap();
    assert!(
        i2 > i1,
        "the newest entry is the bottom row (most-recent-LAST)"
    );

    assert_eq!(
        card.card().receipt_count(),
        2,
        "two observes -> two verified turns"
    );
}

// ── (c) EDIT FROM WITHIN — reshape the feed card's OWN view, accountably. ──
#[test]
fn editing_the_feed_view_from_within_is_a_receipted_patch_with_blame() {
    let mut card = feed_card();
    let source_before = card.view_source();

    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "Dynamics".into(),
            to: "Live Feed".into(),
        })
        .expect("the authorized relabel reshape is admitted");
    assert_ne!(card.view_source(), source_before, "the view-source changed");
    assert!(
        edit.tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Live Feed")),
        "the re-folded view carries the new header"
    );
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the structural edit left a real provenance receipt"
    );
    assert!(
        card.view_blame().iter().any(|l| l.author == Author(7)),
        "the reshape is blamed on its author"
    );
}

// ── the cap tooth — an unauthorized observe/reshape is refused in-band. ──
#[test]
fn an_unauthorized_card_refuses_observe_and_reshape_in_band() {
    // held=Signature does NOT satisfy edit_authority=Proof → the cap tooth refuses.
    let mut pk = [0u8; 32];
    pk[0] = 0xEE;
    let card_cell = Applet::mint(pk, [0u8; 32], &[], vec![], AuthRequired::Signature);
    let mut card = DynamicsCard::open(
        card_cell,
        Author(1),
        AuthRequired::Signature,
        Requirement::AtLeast(Credential::Proof),
    );
    let before = card.view_source();
    assert!(
        matches!(
            card.observe(entry(1, "turn committed", 0x01)),
            Err(deos_js::card_editor::EditError::Unauthorized)
        ),
        "an unauthorized observe is refused"
    );
    assert_eq!(card.view_source(), before, "nothing changed on the refusal");
    assert_eq!(
        card.card().receipt_count(),
        0,
        "no receipt on a refused observe"
    );
}

fn has_bind_for_slot(tree: &ViewTree, slot: usize) -> bool {
    tree.walk()
        .iter()
        .any(|n| matches!(n, ViewTree::Bind { props } if props.slot == slot))
}
