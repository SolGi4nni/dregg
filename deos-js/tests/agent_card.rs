//! THE AGENT-ACTIVITY CARD, PROVEN BY RUNNING — the cockpit's ADOS agent-activity surface
//! reborn as a deos-js card, whose view is GENERATED from an agent cell's held mandate +
//! recent cap-gated turns, grows as a fresh turn is observed (a live-bound step count), and is
//! EDITABLE FROM WITHIN.
//!
//! The chain proven here:
//!   (a) OPEN → the card's view-tree carries the HELD MANDATE (a row per cap edge read off the
//!       live c-list), a live-bound step-count row, and an empty Cap-Gated-Turns placeholder.
//!   (b) OBSERVE → observing a committed turn prepends a `@h<height> · <kind> · receipt <hash>`
//!       row (most-recent-FIRST) and advances the bound step count via a REAL verified turn.
//!   (c) EDIT FROM WITHIN → `edit_view` relabels a section on the card's OWN view-source → the
//!       view changes, the edit a RECEIPTED PATCH attributed by BLAME.

use deos_js::agent_card::AGENT_NONCE_SLOT;
use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::card_editor::{ViewPatch, ViewTree};
use deos_js::{AgentAction, AgentCard};
use dregg_cell::AuthRequired;
use dregg_cell::Credential;
use dregg_cell::Requirement;
use dregg_doc::Author;
use dregg_types::CellId;

/// A substance cell that HOLDS a mandate: a capability reaching a peer cell, granted onto the
/// card cell's own c-list so `read_mandate` surfaces it. Held=None admits edit_authority=sig.
fn agent_card() -> (AgentCard, CellId) {
    let mut pk = [0u8; 32];
    pk[0] = 0xA9;
    let noop = Affordance {
        name: "noop".into(),
        required: Requirement::AtLeast(Credential::Signature),
        apply: Box::new(|_m, _a| vec![(0usize, pack_u64(0))]),
    };
    let mut card_cell = Applet::mint(pk, [0u8; 32], &[], vec![noop], AuthRequired::Signature);
    let agent = card_cell.cell();
    let peer = CellId::from_bytes([0x33; 32]);
    // Grant the agent a capability reaching the peer (its mandate edge), with an expiry so the
    // row exercises the expiry annotation.
    card_cell.with_cell_mut(|cell| {
        cell.capabilities
            .grant_with_expiry(peer, AuthRequired::Signature, 100);
    });
    let ledger_snapshot = card_cell.ledger();
    let card = AgentCard::open(
        // A fresh substance applet to drive (so the mandate read is off the seeded ledger).
        // We re-mint an identical cell as the card's substance.
        {
            let noop2 = Affordance {
                name: "noop".into(),
                required: Requirement::AtLeast(Credential::Signature),
                apply: Box::new(|_m, _a| vec![(0usize, pack_u64(0))]),
            };
            Applet::mint(pk, [0u8; 32], &[], vec![noop2], AuthRequired::Signature)
        },
        agent,
        ledger_snapshot,
        Author(9),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    (card, peer)
}

fn action(height: u64, kind: &str, receipt_seed: u8) -> AgentAction {
    let mut r = [0u8; 32];
    r[0] = receipt_seed;
    AgentAction::new(height, kind, &r)
}

// ── (a) OPEN — the view is GENERATED from the agent's mandate + an empty action stream. ──
#[test]
fn open_generates_a_view_from_the_held_mandate_and_a_bound_step_count() {
    let (card, peer) = agent_card();
    let tree = card.view_tree().expect("the generated agent view parses");

    assert!(
        tree.walk()
            .iter()
            .any(|n| n.label() == Some("Held Mandate")),
        "the HELD MANDATE section is labeled"
    );
    // The mandate row names the peer it reaches (read off the live c-list).
    let peer_short = deos_reflect_short(peer);
    let blob: String = tree
        .walk()
        .iter()
        .filter_map(|n| n.label())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        blob.contains(&format!("→ {peer_short}")),
        "the mandate row names the peer cell it reaches: {blob}"
    );
    assert!(
        blob.contains("expires@h100"),
        "the expiry is annotated on the row"
    );
    assert_eq!(card.reach(), 1, "the mandate reaches one peer");

    assert!(
        has_bind_for_slot(&tree, AGENT_NONCE_SLOT),
        "the card carries a live-bound step-count row"
    );
    assert!(
        blob.contains("(no committed turns observed yet)"),
        "an empty action stream renders an honest placeholder"
    );
    assert_eq!(card.live_steps(), 0, "no steps observed yet");
}

// ── (b) OBSERVE — a committed turn prepends a row + advances the bound step count. ──
#[test]
fn observing_a_turn_prepends_a_row_and_advances_the_bound_step_count() {
    let (mut card, _peer) = agent_card();

    let r1 = card
        .observe(action(1, "set field[0]", 0xAA))
        .expect("observe a committed turn");
    assert_ne!(
        r1.receipt_hash(),
        [0u8; 32],
        "the observe left a real TurnReceipt"
    );
    assert_eq!(card.live_steps(), 1, "the bound step count advanced 0 -> 1");

    let r2 = card
        .observe(action(2, "granted cap", 0xBB))
        .expect("observe a second turn");
    assert_ne!(
        r2.receipt_hash(),
        [0u8; 32],
        "the second observe left a receipt"
    );
    assert_eq!(card.live_steps(), 2, "the bound step count advanced 1 -> 2");

    // Most-recent-FIRST: the @h2 action is the first action in the stream.
    assert_eq!(card.actions().len(), 2, "two actions in the stream");
    assert_eq!(
        card.actions()[0].height,
        2,
        "the newest action is first (most-recent-FIRST)"
    );

    let tree = card.view_tree().expect("re-folded agent view parses");
    let blob: String = tree
        .walk()
        .iter()
        .filter_map(|n| n.label())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        blob.contains("@h2 · granted cap · receipt"),
        "the newest turn row carries its receipt"
    );
    assert!(
        blob.contains("@h1 · set field[0] · receipt"),
        "the older turn row is present"
    );

    assert_eq!(
        card.card().receipt_count(),
        2,
        "two observes -> two verified turns"
    );
}

// ── (c) EDIT FROM WITHIN — reshape the card's OWN view, accountably. ──
#[test]
fn editing_the_agent_view_from_within_is_a_receipted_patch_with_blame() {
    let (mut card, _peer) = agent_card();
    let source_before = card.view_source();

    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "Cap-Gated Turns".into(),
            to: "Receipted Actions".into(),
        })
        .expect("the authorized relabel reshape is admitted");
    assert_ne!(card.view_source(), source_before, "the view-source changed");
    assert!(
        edit.tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Receipted Actions")),
        "the re-folded view carries the new section label"
    );
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the structural edit left a real provenance receipt"
    );
    assert!(
        card.view_blame().iter().any(|l| l.author == Author(9)),
        "the reshape is blamed on its author"
    );
}

// ── a confined agent (no mandate) shows its boundary honestly. ──
#[test]
fn a_confined_agent_shows_an_empty_mandate_honestly() {
    let mut pk = [0u8; 32];
    pk[0] = 0x44;
    let card_cell = Applet::mint(pk, [0u8; 32], &[], vec![], AuthRequired::Signature);
    let agent = card_cell.cell();
    let card = AgentCard::open(
        card_cell,
        agent,
        // A fresh empty ledger view (the agent holds no cap).
        Applet::mint([0x55; 32], [0u8; 32], &[], vec![], AuthRequired::None).ledger(),
        Author(2),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    assert_eq!(card.reach(), 0, "a confined agent reaches no peer");
    let blob: String = card
        .view_tree()
        .unwrap()
        .walk()
        .iter()
        .filter_map(|n| n.label())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        blob.contains("confined to itself"),
        "the empty mandate is shown honestly, not as a blank"
    );
}

fn deos_reflect_short(c: CellId) -> String {
    deos_reflect::short_hex(c.as_bytes())
}

fn has_bind_for_slot(tree: &ViewTree, slot: usize) -> bool {
    tree.walk()
        .iter()
        .any(|n| matches!(n, ViewTree::Bind { props } if props.slot == slot))
}
