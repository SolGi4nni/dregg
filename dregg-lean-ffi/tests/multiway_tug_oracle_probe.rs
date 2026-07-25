//! MULTIWAY-TUG RULES ORACLE probe + PROVENANCE canary (the SPEC-twin class).
//!
//! Proves the `@[export] dregg_multiway_tug_rules` symbol (over the PROVEN
//! `Dregg2.Games.MultiwayTug`) is LINKED into the archive this build actually links, and that the
//! game's legality, escrow split, row control, tallies and ROUND WINNER are COMPUTED BY THE LEAN
//! SOURCE.
//!
//! Run:  cargo test -p dregg-lean-ffi --features lean-lib --test multiway_tug_oracle_probe -- --nocapture
//!   or: DREGG_REQUIRE_LEAN=1 cargo test -p dregg-lean-ffi --features lean-lib --test multiway_tug_oracle_probe
//!
//! ── WHY THIS EXISTS ──────────────────────────────────────────────────────────────────────────
//! `dregg-multiway-tug/src/reference.rs` is a SPEC-TWIN: ~1000 lines of Rust that re-decide what
//! `MultiwayTug.lean` proves. The twin-deletion sweep (`docs/TWIN-DELETION-MAP-2026-07-23.md`) hunted
//! twins of Lean **AIR**, so a twin of a Lean **SPEC** was structurally invisible to it and this one
//! survived — the same blind spot that filed automatafl "not a twin" until `a1e4abb1dc`.
//!
//! ── THE PROVENANCE CANARY (this is the part that makes a pass mean something) ────────────────
//! A test that merely shows "some object answered" is worth little; this one is designed to show
//! WHICH. `winner_of_as_reference_rs_has_it` below is the deleted-twin algorithm TRANSCRIBED
//! VERBATIM into this test file. It is `roundWinner` truncated to its two absolute-threshold
//! branches: no charm tie-break, no row tie-break. So on any sub-threshold round the two objects
//! DISAGREE — the Rust says "no winner", the model ADJUDICATES a seat (`undecidedState_adjudicates`,
//! the §7B fix that took the game's draw rate from 66.1% to 5.1%).
//!
//! `adjudicated_winner_is_not_the_deleted_twins_answer` asserts BOTH halves on the same input: the
//! twin returns `None`, the oracle returns a seat. A pass is therefore evidence about PROVENANCE, not
//! merely liveness — no configuration of the deleted twin can produce the answer this test observes.
//!
//! ── THE REALITY-GATE CANARY ──────────────────────────────────────────────────────────────────
//! To prove the answer goes THROUGH the Lean source: edit
//! `metatheory/Dregg2/Games/MultiwayTug.lean` and delete `roundWinner`'s charm tie-break branch
//! (`else if charmScore s .p2 < charmScore s .p1 then some .p1`), rebuild — and
//! `adjudicated_winner_is_not_the_deleted_twins_answer` FLIPS RED, because the oracle now agrees with
//! the truncated twin. Revert and it greens. A behavior change in the linked archive caused only by a
//! Lean-source edit is the proof the oracle is the source, not a parallel copy.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::{multiway_tug_rules, multiway_tug_rules_available};

/// A `GState` wire (see `Dregg2.Games.MultiwayTugFFI`'s header): fifteen tokens —
/// `removed deck hand₁ hand₂ secret₁ secret₂ disc₁ disc₂ placed₁ placed₂ USED₁ USED₂ PEND SEAT turns`.
/// A card zone is its rows' digits (multiplicity = repetition), `-` when empty.
struct State {
    removed: &'static str,
    deck: &'static str,
    hand: [&'static str; 2],
    secret: [&'static str; 2],
    discard: [&'static str; 2],
    placed: [&'static str; 2],
    used: [&'static str; 2],
    pend: &'static str,
    seat: u8,
    turns: u64,
}

/// `blankState`: empty everywhere, nobody has acted, no offer on the table, p1 to move.
const BLANK: State = State {
    removed: "-",
    deck: "-",
    hand: ["-", "-"],
    secret: ["-", "-"],
    discard: ["-", "-"],
    placed: ["-", "-"],
    used: ["0000", "0000"],
    pend: "0",
    seat: 0,
    turns: 0,
};

impl State {
    fn wire(&self) -> String {
        format!(
            "{} {} {} {} {} {} {} {} {} {} {} {} {} {} {}",
            self.removed,
            self.deck,
            self.hand[0],
            self.hand[1],
            self.secret[0],
            self.secret[1],
            self.discard[0],
            self.discard[1],
            self.placed[0],
            self.placed[1],
            self.used[0],
            self.used[1],
            self.pend,
            self.seat,
            self.turns
        )
    }
}

/// Ask the oracle, requiring a `"1 …"` success reply and returning its payload.
fn ask(wire: &str) -> String {
    let out =
        multiway_tug_rules(wire).unwrap_or_else(|e| panic!("oracle call failed on {wire:?}: {e}"));
    match out.strip_prefix("1 ") {
        Some(payload) => payload.to_owned(),
        None => panic!("oracle REFUSED (fail-closed) or answered malformed: {out:?} for {wire:?}"),
    }
}

/// Ask the oracle, requiring the fail-closed refusal `"0"`.
fn refused(wire: &str) -> bool {
    multiway_tug_rules(wire)
        .map(|out| out == "0")
        .unwrap_or(false)
}

/// ⚑ THE DELETED TWIN'S WIN RULE, transcribed verbatim from
/// `dregg-multiway-tug/src/reference.rs::winner_of`. Kept here — and ONLY here — so the divergence
/// from the model's `roundWinner` is machine-checked rather than asserted in prose. It returns the
/// winning seat index, or `None` for "no winner".
fn winner_of_as_reference_rs_has_it(charm: [u64; 2], controlled: [u64; 2]) -> Option<usize> {
    if charm[0] >= 11 && charm[0] >= charm[1] {
        return Some(0);
    }
    if charm[1] >= 11 {
        return Some(1);
    }
    if controlled[0] >= 4 && controlled[0] >= controlled[1] {
        return Some(0);
    }
    if controlled[1] >= 4 {
        return Some(1);
    }
    None
}

/// THE FIRST TEST ASSERTS THE ORACLE IS THERE. It does NOT skip when the export is absent: a
/// green-when-absent probe is exactly the pattern this repo has repeatedly been bitten by, and the
/// whole point of this file is that an absent oracle is a DEGRADE (the crate would fall back on the
/// drifted twin), not a quieter pass.
#[test]
fn oracle_is_linked_and_callable() {
    assert!(
        multiway_tug_rules_available(),
        "dregg_multiway_tug_rules is NOT in the linked archive — the multiway-tug rules have no \
         proven answer source in this build. Rebuild the archive (the splice picks up \
         metatheory/.lake/build/ir/Dregg2/Games/MultiwayTugFFI.c); do not treat this as a skip."
    );
    // And it really answers: the influence table is the model's `charm`, not a Rust constant.
    assert_eq!(ask("charm"), "7 2 2 2 3 3 4 5");
    assert_eq!(ask("turns"), "12");
}

/// `demo`'s own `#guard`s, reached over the wire: P1's Gift of rows `3 3 5` is legal, the cutter
/// cannot answer their own cut, the other seat can, and while the offer stands nothing else is.
#[test]
fn the_offer_interlock_and_the_anti_self_deal_tooth() {
    let demo = State {
        hand: ["033566", "012456"],
        ..BLANK
    };
    assert_eq!(ask(&format!("legal {} 0 2 3 3 5", demo.wire())), "1");
    // A card not in hand is illegal (row 4 is not in P1's hand).
    assert_eq!(ask(&format!("legal {} 0 0 4", demo.wire())), "0");
    // Executing the cut puts the offer in escrow and passes the seat to P2.
    let cut = ask(&format!("act {} 0 2 3 3 5", demo.wire()));
    assert_eq!(
        cut, "- - 066 012456 - - - - - - 0010 0000 1 0 3 3 5 1 1",
        "the cut must leave the three favors in escrow, the gift flag set, and P2 to answer"
    );
    let cut_wire = cut;
    // ⚑ The proposer can NEVER answer their own cut; the other seat can.
    assert_eq!(ask(&format!("legalresp {cut_wire} 0 0 0")), "0");
    assert_eq!(ask(&format!("legalresp {cut_wire} 1 0 0")), "1");
    // THE INTERLOCK: while the offer stands, no ACTION is legal for either seat.
    assert_eq!(ask(&format!("legal {cut_wire} 1 0 1")), "0");
    assert_eq!(ask(&format!("legal {cut_wire} 0 0 3")), "0");
    // A shape-mismatched answer (a competition pick against a gift offer) is refused.
    assert_eq!(ask(&format!("legalresp {cut_wire} 1 1 0")), "0");
    // A response with nothing on the table is refused.
    assert_eq!(ask(&format!("legalresp {} 0 0 0", demo.wire())), "0");
    // `kinds`: all four open for the seat to move before the cut; NONE during it, and only the
    // non-proposer's response.
    assert_eq!(ask(&format!("kinds {} 0", demo.wire())), "1 1 1 1 0");
    assert_eq!(ask(&format!("kinds {cut_wire} 0")), "0 0 0 0 0");
    assert_eq!(ask(&format!("kinds {cut_wire} 1")), "0 0 0 0 1");
}

/// The escrow split (`takerShare` / `cutterShare`): the taker takes ONE of a gift's three and the
/// cutter keeps the other two; on a competition the taker takes a PAIR. A pick off the end REFUSES.
#[test]
fn the_escrow_split_is_the_models_table() {
    assert_eq!(ask("split 1 0 6 0 2 0 0"), "6 02");
    assert_eq!(ask("split 1 0 6 0 2 0 1"), "0 26");
    assert_eq!(ask("split 1 0 6 0 2 0 2"), "2 06");
    assert_eq!(ask("split 2 0 6 5 1 0 1 0"), "56 01");
    assert_eq!(ask("split 2 0 6 5 1 0 1 1"), "01 56");
    assert!(refused("split 1 0 6 0 2 0 3"));
    assert!(refused("split 2 0 6 5 1 0 1 2"));
}

/// The Secret IS scored (`secret_is_scored`): a card sitting in the secret pile counts toward its
/// row's tally and can therefore CONTROL that row.
#[test]
fn the_secret_is_scored() {
    let s = State {
        secret: ["4", "-"],
        ..BLANK
    };
    assert_eq!(ask(&format!("count {} 0 4", s.wire())), "1");
    assert_eq!(ask(&format!("control {}", s.wire())), "7 0 0 0 0 1 0 0");
    // Control goes to whoever placed MORE; an exact tie leaves the row UNCONTROLLED.
    let tie = State {
        placed: ["4", "4"],
        ..BLANK
    };
    assert_eq!(ask(&format!("control {}", tie.wire())), "7 0 0 0 0 0 0 0");
}

/// A THRESHOLD win, where the oracle and the deleted twin AGREE — so the divergence pinned in the
/// next test is confined to the adjudication tail and is not a wholesale disagreement.
#[test]
fn a_threshold_win_is_where_the_two_objects_agree() {
    // `winState`: p1 holds rows 3,5,6 for 3+4+5 = 12 charm on 3 rows.
    let win = State {
        placed: ["356", "-"],
        ..BLANK
    };
    assert_eq!(ask(&format!("score {}", win.wire())), "12 3 0 0");
    assert_eq!(ask(&format!("won {} 0", win.wire())), "1");
    assert_eq!(ask(&format!("winner {}", win.wire())), "1");
    // The twin agrees here: 12 >= 11 clears the absolute threshold.
    assert_eq!(winner_of_as_reference_rs_has_it([12, 0], [3, 0]), Some(0));

    // A genuine dead heat is a draw for BOTH objects.
    assert_eq!(ask(&format!("winner {}", BLANK.wire())), "0");
    assert_eq!(winner_of_as_reference_rs_has_it([0, 0], [0, 0]), None);
}

/// ⚑⚑ THE PROVENANCE TEST. On a sub-threshold round the model ADJUDICATES and the deleted twin
/// throws the round away. Both halves are asserted on the SAME input, so a pass cannot be explained
/// by the twin having answered.
#[test]
fn adjudicated_winner_is_not_the_deleted_twins_answer() {
    // `undecidedState` (the model's own witness): p1 holds rows 5,6 (charm 9, two rows), p2 holds
    // row 3 (charm 3, one row). NEITHER seat clears a threshold.
    let undecided = State {
        placed: ["56", "3"],
        ..BLANK
    };
    assert_eq!(ask(&format!("score {}", undecided.wire())), "9 2 3 1");
    // `undecidedState_not_Won`: the absolute win predicate is FALSE for both seats ...
    assert_eq!(ask(&format!("won {} 0", undecided.wire())), "0");
    assert_eq!(ask(&format!("won {} 1", undecided.wire())), "0");
    // ... and the DELETED TWIN therefore answers "no winner".
    assert_eq!(
        winner_of_as_reference_rs_has_it([9, 3], [2, 1]),
        None,
        "the transcribed twin must be the truncated rule, or this test is not a provenance test"
    );
    // ⚑ ... but the round HAS a winner (`undecidedState_adjudicates`). Only `roundWinner` can say
    // this. `won` = 0/0 beside `winner` = p1 is the signature of the model's adjudication tail.
    assert_eq!(
        ask(&format!("winner {}", undecided.wire())),
        "1",
        "the oracle must adjudicate this round to p1 — if it says 0 the answer came from a \
         threshold-only rule, i.e. NOT from the proven roundWinner"
    );

    // ⚑ THE DEEPEST BRANCH: the charm TIES 5-5 and the ROW COUNT decides, for p2. p1 holds row 6
    // (charm 5, one row); p2 holds rows 0 and 4 (charm 2+3 = 5, two rows). The twin has neither
    // tie-break, so no input can make it produce this answer.
    let row_tie = State {
        placed: ["6", "04"],
        ..BLANK
    };
    assert_eq!(ask(&format!("score {}", row_tie.wire())), "5 1 5 2");
    assert_eq!(ask(&format!("won {} 0", row_tie.wire())), "0");
    assert_eq!(ask(&format!("won {} 1", row_tie.wire())), "0");
    assert_eq!(winner_of_as_reference_rs_has_it([5, 5], [1, 2]), None);
    assert_eq!(
        ask(&format!("winner {}", row_tie.wire())),
        "2",
        "the row-count tie-break must hand this round to p2 — the twin's rule cannot reach it"
    );
}

/// Conservation over a cut and its answer: `totalCards` is invariant (`conservation_move`).
#[test]
fn a_cut_and_its_answer_conserve_the_deck() {
    let demo = State {
        hand: ["033566", "012456"],
        ..BLANK
    };
    let before = ask(&format!("total {}", demo.wire()));
    let cut = ask(&format!("act {} 0 2 3 3 5", demo.wire()));
    assert_eq!(ask(&format!("total {cut}")), before);
    let answered = ask(&format!("respond {cut} 1 0 0"));
    assert_eq!(ask(&format!("total {answered}")), before);
    // The answer really did place the cards and clear the table (`respond_closes_pending`).
    assert!(
        answered.ends_with(" 0 1 2"),
        "after the answer the table must be clear, the responder to move, two turns stamped: {answered}"
    );
}

/// Fail-closed: a malformed wire REFUSES rather than answering for a position nobody sent.
#[test]
fn malformed_wires_fail_closed() {
    assert!(refused(""));
    assert!(refused("bogus"));
    assert!(refused("winner"));
    assert!(refused("winner - - - -"));
    // A card digit outside the seven rows, and a non-digit card.
    assert!(refused("winner - - 7 - - - - - - - 0000 0000 0 0 0"));
    assert!(refused("winner - - x - - - - - - - 0000 0000 0 0 0"));
    // A used-flag field that is not four bits, and a seat that is not a seat.
    assert!(refused("winner - - - - - - - - - - 0002 0000 0 0 0"));
    assert!(refused("winner - - - - - - - - - - 0000 0000 0 2 0"));
    // A trailing token where the grammar ends, and a truncated action.
    assert!(refused(&format!("winner {} 7", BLANK.wire())));
    assert!(refused(&format!("legal {} 0 2 3 3", BLANK.wire())));
}
