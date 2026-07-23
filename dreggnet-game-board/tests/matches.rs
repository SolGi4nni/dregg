//! FAST: a PLAYED match of each game lowers to the foldable leaves the fold consumes — and
//! the game's own teeth bite at lowering (a fabricated / replayed card has no leaf; a board
//! transition that is not the automaton step has no honest D1 witness). No proving here.

use dregg_automatafl::reference::{ATT, AUTO, Board, VAC, automaton_step, stock_two_player};
use dregg_circuit::field::BabyBear;
use dregg_multiway_tug::hidden_hand::{HandTree, card_leaf};
use dreggnet_game_board::{AutomataflMatch, MatchError, TugMatch, TugWin};

fn hand() -> Vec<(u64, u64)> {
    vec![
        (0, 1001),
        (1, 1002),
        (3, 1003),
        (7, 1004),
        (12, 1005),
        (18, 1006),
    ]
}

/// The driven 5x5 board (the same demo the automatafl crate's own prove/fold gate uses):
/// attractor two north of the automaton.
fn demo_board() -> Board {
    let n = 5usize;
    let mut cells = vec![VAC; n * n];
    cells[4 * n + 2] = ATT;
    cells[2 * n + 2] = AUTO;
    Board {
        n,
        cells,
        auto: (2, 2),
        col_rule: true,
    }
}

/// A PLAYED tug match lowers to one membership leaf per play — public inputs `[blinded_leaf,
/// hand_root]`, the CARD IDS ABSENT — plus the terminal win leaf binding `[charm, winner]`.
/// This is the hand-never-revealed property, at the leaf boundary.
#[test]
fn a_played_tug_match_lowers_to_hand_hiding_membership_leaves() {
    let m = TugMatch {
        hand: hand(),
        plays: vec![0, 3, 12],
        win: Some(TugWin {
            charm: 13,
            winner: 1,
        }),
    };
    let leaves = m.leaves().expect("the played match lowers");
    assert_eq!(leaves.len(), 4, "3 plays + the terminal win turn");

    // Each play's leaf proves membership under the CURRENT remaining-hand root.
    let mut tree = HandTree::commit(m.hand.clone());
    for (i, &card) in m.plays.iter().enumerate() {
        let nonce = tree.opening(card).expect("dealt").1;
        let root = leaves[i].public_inputs[1];
        assert_eq!(
            leaves[i].public_inputs,
            vec![card_leaf(card, nonce), root],
            "PIs are [blinded_leaf, hand_root]"
        );
        assert!(
            !leaves[i].public_inputs.contains(&BabyBear::from_u64(card)),
            "the played card id is NOT in the leaf's public inputs — the hand is hidden"
        );
        tree = tree.without(card);
    }
    // Successive plays prove under DIFFERENT roots (the hand shrinks) — no replay is possible.
    assert_ne!(
        leaves[0].public_inputs[1], leaves[1].public_inputs[1],
        "each play proves against the updated remaining-hand root"
    );
    // The free board leaf carries [charm, winner] as a public output — but that literal is NOT
    // welded to any cell (the mannequin: it reads back what the caller passed). The REAL win
    // path welds the output to the cell's state prefix: `win_leaf_bound` publishes
    // `[old8 ‖ new8 ‖ charm ‖ winner]`, so the SAME win over a DIFFERENT cell prefix is a
    // DIFFERENT public-input vector — a win cannot be replayed across cells. (The full
    // real-cell fold + light-client accept is `dregg-multiway-tug/tests/fold_real_cell.rs`; the
    // board adopts it via `prove_tug_win_over_cell`.)
    use dregg_multiway_tug::fold::{fixture_wire_commit8, win_leaf_bound};
    let new8: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(700 + i as u32));
    let cell_a: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(i as u32));

    let welded = win_leaf_bound(cell_a, new8, 13, 1);
    assert_eq!(
        &welded.public_inputs[16..18],
        &[BabyBear::from_u64(13), BabyBear::from_u64(1)],
        "the welded win leaf binds [charm, winner] as its app output"
    );
    assert_eq!(
        &welded.public_inputs[0..8],
        &cell_a,
        "PI[0..8] is the cell's old8 state prefix — the win is bound to a transition"
    );
    let over_fixture = win_leaf_bound(fixture_wire_commit8(), new8, 13, 1);
    assert_ne!(
        welded.public_inputs, over_fixture.public_inputs,
        "the SAME win over the pk[0]=7 fixture cell is a DIFFERENT welded public-input vector — \
         the win is welded to the real cell, not a free literal"
    );
}

/// The hidden-hand tooth bites at lowering: a card never dealt, and a card played twice, have
/// NO membership leaf — the match does not lower, so it can never be folded or submitted.
#[test]
fn a_fabricated_or_replayed_card_has_no_leaf() {
    let fabricated = TugMatch {
        hand: hand(),
        plays: vec![0, 20], // 20 was never dealt
        win: None,
    };
    assert!(matches!(
        fabricated.leaves().err(),
        Some(MatchError::NotInHand(20))
    ));

    let double = TugMatch {
        hand: hand(),
        plays: vec![0, 0], // the same card twice
        win: None,
    };
    assert!(
        matches!(double.leaves().err(), Some(MatchError::NotInHand(0))),
        "a played card is no longer under the remaining-hand root"
    );

    assert!(matches!(
        TugMatch {
            hand: hand(),
            plays: vec![],
            win: None
        }
        .leaves()
        .err(),
        Some(MatchError::Empty)
    ));
}

/// A PLAYED automatafl match lowers to one committed D1 leaf per turn, each proving
/// `boards[i+1] == automaton_step(boards[i])`; the boards themselves are never in the proof's
/// public inputs as *moves* — only the transition is attested.
#[test]
fn a_played_automatafl_match_lowers_to_d1_leaves() {
    let m = AutomataflMatch {
        start: demo_board(),
        turns: 2,
    };
    let boards = m.boards();
    assert_eq!(boards.len(), 3, "start + 2 stepped boards");
    assert_eq!(
        boards[1],
        automaton_step(&boards[0]),
        "the played boards ARE the automaton's steps"
    );
    assert_ne!(boards[1], boards[0], "the automaton actually moved");

    let leaves = m.leaves().expect("the played match lowers to D1 leaves");
    assert_eq!(leaves.len(), 2, "one D1 leaf per turn");
    for l in &leaves {
        assert!(l.num_rows > 0);
        assert!(
            !l.program.descriptor.constraints.is_empty(),
            "the D1 AIR carries real constraints"
        );
    }

    assert!(matches!(
        AutomataflMatch {
            start: demo_board(),
            turns: 0
        }
        .leaves()
        .err(),
        Some(MatchError::Empty)
    ));
}

/// **THE STEP CUTOVER, at leaf-construction resolution.** The deployed n=11 stock-game match
/// lowers each D1 leaf through the PROVEN Lean descriptor `automataflStepDescN 11`: every leaf
/// carries a `descriptor_state_leaf` source whose trace SATISFIES the descriptor (checked by the
/// `leaves()` fail-closed canary) and whose 36 public inputs are the packed-felt Lean form — NOT
/// the 32-PI Merkle form of the hand-authored Rust AIR. The SLOW recursion fold + light-client
/// accept over these leaves is the `end_to_end.rs` `#[ignore]` gate.
#[test]
fn n11_stock_match_lowers_through_the_lean_descriptor() {
    let m = AutomataflMatch {
        start: stock_two_player(),
        turns: 3,
    };
    let leaves = m
        .leaves()
        .expect("the n=11 stock match lowers to D1 leaves");
    assert_eq!(leaves.len(), 3, "one D1 leaf per turn");
    for (i, l) in leaves.iter().enumerate() {
        let src = l.descriptor_state_leaf.as_ref().unwrap_or_else(|| {
            panic!("turn {i}: the n=11 leaf must carry the Lean descriptor source")
        });
        assert_eq!(
            src.descriptor.name, "dregg-automatafl-step-d1-n11",
            "turn {i}: proven through the Lean-emitted n=11 step descriptor"
        );
        assert_eq!(src.descriptor.public_input_count, 36);
        assert_eq!(
            l.public_inputs.len(),
            36,
            "turn {i}: the leaf publishes the 36-PI packed-felt form the fold commits over"
        );
        assert!(
            src.base_trace
                .iter()
                .all(|row| row.len() == src.descriptor.trace_width),
            "turn {i}: every base-trace row is exactly the descriptor width (678)"
        );
    }
}

/// The n=5 TEST board size has NO emitted Lean descriptor (only n=2, n=11 are pinned), so its
/// leaves correctly FALL BACK to the Rust AIR (blocked-not-faked: no descriptor source, 32 PIs).
#[test]
fn n5_match_falls_back_to_rust_air_no_descriptor() {
    let leaves = AutomataflMatch {
        start: demo_board(),
        turns: 1,
    }
    .leaves()
    .expect("n=5 lowers via the Rust AIR fallback");
    assert!(
        leaves[0].descriptor_state_leaf.is_none(),
        "n=5 has no Lean descriptor; the leaf must fall back (no descriptor source)"
    );
    assert_eq!(
        leaves[0].public_inputs.len(),
        32,
        "the Rust-AIR fallback keeps the 32-PI Merkle form (old8‖new8‖board_old_root8‖board_new_root8)"
    );
}
