//! STEP 1 of the `<dregg-*>` web substrate — the in-wasm `render_html()` binding + the real
//! `collective-choice` poll as an in-tab `PollWorld`.
//!
//! Two proofs, both on the HOST target (the executor's `Instant` clock works here, so the FULL
//! verified-turn path runs end-to-end):
//!
//! (a) `CardWorld::render_html()` produces the SAME HTML the server bake produces for the
//!     counter card (`deos_view::render_html` over the counter view-tree), and REPAINTS after a
//!     fire — the bound `count` span carries the new committed value.
//!
//! (b) `PollWorld` casts a REAL one-vote-per-ballot verified turn: the tally increments, the
//!     light-client recompute matches the executor's stored monotone board, a double vote from
//!     one ballot is refused (nullifier depth), the ballot's `WriteOnce(VOTE)` refuses a second
//!     changing write at the EXECUTOR depth, and the polis quorum `AffineLe` gates resolution.

#![cfg(not(target_arch = "wasm32"))]

use dregg_wasm::bindings_card::{CardWorld, PollWorld};

/// The EXACT counter-card view-tree the server bake renders (byte-for-byte the SpiderMonkey
/// engine's `deos.ui.vstack(text, bind, button)` shape). `CardWorld::render_html()` must
/// produce the IDENTICAL HTML `deos_view::render_html` produces over this tree.
const COUNTER_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Counter applet" } },
    { "kind": "bind", "props": { "slot": 0, "label": "count: " } },
    { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
  ]
}"#;

fn server_bake(count: u64) -> String {
    let tree = deos_view::parse_view_tree(COUNTER_CARD_JSON).expect("parse counter tree");
    deos_view::render_html(&tree, &[count])
}

/// (a) `render_html()` is byte-identical to the server bake, and repaints after a fire.
#[test]
fn card_render_html_matches_server_bake_and_repaints() {
    let mut card = CardWorld::new(0, 0).expect("mint the counter card");

    // Frame 0: the in-wasm render equals the server bake at the committed value 0.
    let html0 = card.render_html();
    assert_eq!(
        html0,
        server_bake(0),
        "render_html() at count 0 must equal the server bake"
    );
    // It is genuinely the rendered card, not an error fragment.
    assert!(html0.contains("Counter applet"), "title painted");
    assert!(
        html0.contains("data-slot=\"0\""),
        "the bound slot carries data-slot"
    );
    assert!(
        html0.contains("count: 0"),
        "the bound span paints the committed count 0"
    );

    // THE FIRE → a real verified turn; the bound value moves to 1.
    let after = card
        .fire("inc", 1)
        .expect("the +1 fire commits a verified turn");
    assert_eq!(after, 1, "the fire returned the re-read bound value 1");

    // REPAINT: render_html now equals the server bake at 1 (the span re-painted).
    let html1 = card.render_html();
    assert_eq!(
        html1,
        server_bake(1),
        "render_html() after the fire must equal the server bake at count 1"
    );
    assert!(
        html1.contains("count: 1"),
        "the bound span repainted to the committed count 1"
    );
    assert_ne!(html0, html1, "the fire changed the rendered HTML");
}

/// The other worlds also render in-wasm (the substrate is uniform).
#[test]
fn every_world_renders_a_nonempty_card() {
    use dregg_wasm::bindings_card::{InspectorWorld, KvStoreWorld, TallyWorld};
    let insp = InspectorWorld::new(vec![]).expect("inspector");
    assert!(insp.render_html().contains("deos-"), "inspector renders");
    let tally = TallyWorld::new(vec![]).expect("tally");
    assert!(
        tally.render_html().contains("deos-table"),
        "tally renders a table"
    );
    let kv = KvStoreWorld::new(vec![]).expect("kvstore");
    assert!(
        kv.render_html().contains("deos-table"),
        "kvstore renders a table"
    );
}

fn counts(json: &str) -> Vec<u64> {
    serde_json::from_str(json).expect("tally JSON array")
}

fn refused(json: &str) -> bool {
    let v: serde_json::Value = serde_json::from_str(json).expect("json");
    v.get("refused").and_then(|b| b.as_bool()).unwrap_or(false)
}

/// (b) A real one-vote-per-ballot verified poll: cast → receipt, tally increments, light client
/// matches, double vote refused (nullifier + WriteOnce), quorum gates resolution.
#[test]
fn poll_casts_real_ballots_light_client_matches_double_vote_refused() {
    // 2 options, quorum M = 2.
    let mut poll = PollWorld::new(2, 2).expect("open the poll");
    assert_eq!(poll.option_count(), 2);
    let receipts_before = poll.receipt_count();

    // Voter 0 casts option 0 — a real cap-gated verified turn (ballot WriteOnce + tally bump).
    let t0 = poll.cast_as(0, 0).expect("voter 0's cast commits");
    assert_eq!(t0, 1, "option 0's tally is 1 after the first cast");
    assert!(
        poll.receipt_count() > receipts_before,
        "the cast left real receipts (ballot mint + WriteOnce turn + tally turn)"
    );
    assert_eq!(counts(&poll.tally()), vec![1, 0]);
    // The executor's stored monotone board equals the light-client recompute.
    assert_eq!(counts(&poll.light_client_tally()), vec![1, 0]);
    assert!(
        poll.verified(),
        "light client agrees with the executor board"
    );

    // Voter 1 casts option 0 — the board grows one verified vote.
    let t1 = poll.cast_as(1, 0).expect("voter 1's cast commits");
    assert_eq!(t1, 2);
    assert_eq!(counts(&poll.tally()), vec![2, 0]);
    assert_eq!(counts(&poll.light_client_tally()), vec![2, 0]);
    assert!(poll.verified());

    // DOUBLE VOTE from voter 0's already-consumed ballot → refused (the nullifier depth).
    let dv = poll.try_double_vote(0, 1);
    assert!(refused(&dv), "a double vote must be refused: {dv}");
    // The board did not move.
    assert_eq!(
        counts(&poll.tally()),
        vec![2, 0],
        "board unchanged after refused double vote"
    );

    // The ballot's WriteOnce(VOTE) refuses a second CHANGING write at the EXECUTOR depth.
    let wo = poll.try_ballot_write_once(0);
    assert!(
        refused(&wo),
        "WriteOnce(VOTE) must refuse a second changing ballot write at the executor: {wo}"
    );
    assert_eq!(
        counts(&poll.tally()),
        vec![2, 0],
        "board unchanged after refused overwrite"
    );
    assert!(poll.verified(), "board still light-client-consistent");

    // QUORUM: Σ TALLY = 2 == M = 2 → the decision-turn commits.
    let res = poll.try_resolve();
    let rv: serde_json::Value = serde_json::from_str(&res).unwrap();
    assert_eq!(
        rv["resolved"],
        serde_json::json!(true),
        "at quorum, resolve commits: {res}"
    );
    assert_eq!(rv["winner"], serde_json::json!(0), "option 0 is the winner");
    assert_eq!(rv["winner_tally"], serde_json::json!(2));
}

/// The quorum `AffineLe` REFUSES the decision-turn below threshold (M = 3, one vote cast).
#[test]
fn poll_quorum_affine_le_refuses_below_threshold() {
    let mut poll = PollWorld::new(3, 3).expect("open the poll");
    poll.cast_as(0, 1).expect("one cast commits");
    assert_eq!(counts(&poll.tally()), vec![0, 1, 0]);

    // Σ TALLY = 1 < M = 3 → the AffineLe gate refuses RESOLVED := 1.
    let res = poll.try_resolve();
    let rv: serde_json::Value = serde_json::from_str(&res).unwrap();
    assert_eq!(
        rv["resolved"],
        serde_json::json!(false),
        "below quorum the decision-turn must be refused: {res}"
    );
}

/// `fire("cast", opt)` auto-advances to a fresh voter each time — each cast is its own ballot.
#[test]
fn poll_fire_cast_uses_a_fresh_ballot_each_time() {
    let mut poll = PollWorld::new(2, 1).expect("open the poll");
    poll.fire("cast", 0).expect("cast 1");
    poll.fire("cast", 1).expect("cast 2");
    poll.fire("cast", 0).expect("cast 3");
    assert_eq!(counts(&poll.tally()), vec![2, 1]);
    assert_eq!(counts(&poll.light_client_tally()), vec![2, 1]);
    assert!(poll.verified());
    // render_html paints the live board.
    let html = poll.render_html();
    assert!(html.contains("deos-table"), "poll renders a tally table");
    // The label + the live bind are sibling spans; the option-0 tally slot paints "2".
    assert!(html.contains("option 0: "), "option 0's label is painted");
    assert!(
        html.contains(&format!("data-slot=\"{}\"", 8)) && html.contains(">2</span>"),
        "option 0's live tally (2) is painted from its Monotonic slot: {html}"
    );
}
