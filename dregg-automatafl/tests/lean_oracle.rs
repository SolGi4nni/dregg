//! **THE ACCEPTANCE BATTERY: the game oracle IS the proven Lean, and it is actually CALLED.**
//!
//! Every assertion here goes through `@[export] dregg_automatafl_rules`
//! (`Dregg2.Games.AutomataflFFI.rulesFFI` over `Dregg2.Games.AutomataflRules`) via
//! [`dregg_automatafl::rules`]. There is no Rust game oracle left to answer instead —
//! `src/reference.rs` is deleted — so a green run here means the linked Lean archive answered.
//!
//! ## Why the first test is a hard failure and not a `return`
//!
//! The pattern this replaces failed GREEN: a `#[cfg(...)]`-gated or `if !available() { return }` test
//! passes on a runner whose archive lacks the export, so the very gate it exists to check is silently
//! absent. The first test below therefore ASSERTS availability. If it fails, the archive is thin —
//! run `./scripts/bootstrap.sh` or `./scripts/fetch-lean-seed.sh`, and build with
//! `DREGG_REQUIRE_LEAN=1` so the absence is a build failure rather than a test surprise.
//!
//! ## What the last four tests pin
//!
//! They are the inputs on which the DELETED Rust oracle gave a different answer — the conformance
//! audit's own witnesses (`docs/reference/AUTOMATAFL-RULES-CONFORMANCE-AUDIT.md`). Each is a
//! divergence from the Creator-Approved ruleset that `reference.rs` inherited from
//! `~/dev/automatafl/logic`, and each now reads the ruleset's answer. They cannot pass against a
//! transcription of that experiment, which is exactly what makes them evidence about WHICH object
//! answered.

use dregg_automatafl::board::{ATT, AUTO, Board, Coord, Move, REP, VAC};
use dregg_automatafl::rules;

/// `mkBoard`: an `n × n` board with `placed` written over vacuum and the automaton at `auto`.
fn mk(n: usize, placed: &[(Coord, u8)], auto: Coord) -> Board {
    let mut cells = vec![VAC; n * n];
    for &(c, p) in placed {
        cells[(c.1 as usize) * n + (c.0 as usize)] = p;
    }
    cells[(auto.1 as usize) * n + (auto.0 as usize)] = AUTO;
    Board {
        n,
        cells,
        auto,
        col_rule: true,
    }
}

fn mv(frm: Coord, to: Coord) -> Move {
    Move { who: 0, frm, to }
}

/// **THE GATE.** The verified game oracle must be LINKED AND CALLABLE. Not `available()` ⇒ this
/// crate has no answer source at all (there is no Rust twin), so every other test below is
/// meaningless and this one says so instead of skipping.
#[test]
fn the_lean_game_oracle_is_linked_and_answers() {
    assert!(
        rules::available(),
        "the Lean game oracle (`@[export] dregg_automatafl_rules`) is NOT in the linked archive. \
         `dregg-automatafl` has no other answer source — `src/reference.rs` was deleted because it \
         carried a non-canonical experiment's bugs. Rebuild the archive \
         (`./scripts/bootstrap.sh` / `./scripts/fetch-lean-seed.sh`) and build with \
         DREGG_REQUIRE_LEAN=1 so this cannot degrade quietly."
    );
    // And it really round-trips: the stock board comes back as the 11×11 two-player opening.
    let b = rules::stock_two_player().expect("the oracle answers `stock`");
    assert_eq!(b.n, 11, "the stock two-player board is 11×11");
    assert_eq!(b.auto, (5, 5), "the automaton opens dead centre");
    assert_eq!(b.cell_at((5, 5)), AUTO);
    // The four corners are repulsors (they are also the four goal squares — the stock opening
    // OCCUPIES every goal).
    for c in [(0, 0), (10, 0), (0, 10), (10, 10)] {
        assert_eq!(b.cell_at(c), REP, "the stock corner {c:?} holds a repulsor");
    }
    // The `y = 1` rank: attractors at x ∈ {3,7}, repulsors at x ∈ {4,5,6}.
    for x in [3, 7] {
        assert_eq!(b.cell_at((x, 1)), ATT);
    }
    for x in [4, 5, 6] {
        assert_eq!(b.cell_at((x, 1)), REP);
    }
}

/// A malformed wire FAILS CLOSED — the Lean answers `"0"` (refuse), and the typed layer turns that
/// into an `Err` rather than a board.
#[test]
fn a_malformed_wire_fails_closed() {
    assert_eq!(
        dregg_lean_ffi::automatafl_rules("bogus verb").expect("the export is callable"),
        "0",
        "an unknown verb is REFUSED, not guessed"
    );
    assert_eq!(
        dregg_lean_ffi::automatafl_rules("mid 5 000 0 0 1 0 0").expect("the export is callable"),
        "0",
        "a board whose cell string does not match its size is REFUSED"
    );
}

/// The stock two-player GOAL ASSIGNMENT comes from the ruleset (`stockGoals2`): seat 0 owns the two
/// `y = 0` corners, seat 1 the two `y = 10` corners — "two corners in the same row".
///
/// The python prototype gets this WRONG (`DEFAULT_GOALS[2]` repeats `(10,0)` and gives seat 1 a
/// COLUMN); the README is the authority and the Lean follows it.
#[test]
fn the_goal_assignment_is_two_corners_per_seat_in_one_row() {
    let gs = rules::stock_goals2(11).expect("the oracle answers `goals`");
    assert_eq!(gs.len(), 4);
    let seat0: Vec<Coord> = gs
        .iter()
        .filter(|(_, w)| *w == 0)
        .map(|(c, _)| *c)
        .collect();
    let seat1: Vec<Coord> = gs
        .iter()
        .filter(|(_, w)| *w == 1)
        .map(|(c, _)| *c)
        .collect();
    assert_eq!(seat0, vec![(0, 0), (10, 0)], "seat 0 owns the y = 0 row");
    assert_eq!(seat1, vec![(0, 10), (10, 10)], "seat 1 owns the y = 10 row");
}

/// ⚑ **THE 2-CYCLE.** Two pieces naming each other's squares BOTH STAY PUT (`PHILOSOPHY.md`:
/// *"2-cycles (A→B, B→A): **Always** stay in place"*; `AutomataflRules.twoCyc`).
///
/// The deleted `reference.rs::resolve_mid` — transcribed from `~/dev/automatafl/logic` — performed
/// the SWAP here. That is audit divergence 3.5a, and it was live inside the witness oracle the
/// descriptors were checked against; `resolve_witness.rs` carried a comment documenting the
/// disagreement rather than fixing it. This test cannot pass against that transcription.
#[test]
fn a_two_cycle_keeps_both_pieces_put() {
    let b = mk(5, &[((0, 0), ATT), ((0, 1), REP)], (4, 4));
    let mid = rules::resolve_mid(&b, &[], &[mv((0, 0), (0, 1)), mv((0, 1), (0, 0))])
        .expect("the oracle answers `mid`");
    assert_eq!(mid.cell_at((0, 0)), ATT, "the attractor did not move");
    assert_eq!(mid.cell_at((0, 1)), REP, "the repulsor did not move");
    assert_eq!(mid.cells, b.cells, "the board is unchanged");
}

/// ⚑ **THE INCLUSIVE PATH CHECK.** A move onto a square held by a piece nobody moves FAILS, and the
/// mover is replaced at its origin (`model.py::CanMove` scans `range(min, max+1)`;
/// `AutomataflRules.blockedB`).
///
/// The deleted `reference.rs::occluded` scanned the STRICT INTERIOR only, so the mover landed on the
/// occupant and DESTROYED it — audit divergence 3.2, the worst one, and one of the three that
/// destroy pieces.
#[test]
fn a_move_onto_an_occupied_square_fails_and_destroys_nothing() {
    let b = mk(5, &[((0, 0), ATT), ((0, 3), REP)], (4, 4));
    let mid = rules::resolve_mid(&b, &[], &[mv((0, 0), (0, 3))]).expect("the oracle answers `mid`");
    assert_eq!(
        mid.cell_at((0, 0)),
        ATT,
        "the mover is replaced at its origin"
    );
    assert_eq!(mid.cell_at((0, 3)), REP, "the stationary occupant SURVIVES");
    assert_eq!(
        mid.cells, b.cells,
        "nothing moved and nothing was destroyed"
    );
    // The same move on an EMPTY file does execute — the block above is the occupancy, not a
    // blanket refusal.
    let clear = mk(5, &[((0, 0), ATT)], (4, 4));
    let moved =
        rules::resolve_mid(&clear, &[], &[mv((0, 0), (0, 3))]).expect("the oracle answers `mid`");
    assert_eq!(moved.cell_at((0, 3)), ATT);
    assert_eq!(moved.cell_at((0, 0)), VAC);
}

/// ⚑ **RULING (D): the automaton's square is banned as a move SOURCE ONLY.** Naming it as a
/// DESTINATION is legal to PROPOSE (`model.py::ev_Move` rejects only `POS_CANT_MOVE_THAT` on the
/// source) and then fails to execute by the path check above.
///
/// The deleted `reference.rs::move_valid` banned BOTH endpoints — `logic/src/game.rs`'s reading, not
/// the README's.
#[test]
fn the_automaton_is_banned_as_a_source_only() {
    let b = mk(5, &[((0, 2), ATT)], (2, 2));
    assert!(
        rules::move_legal(&b, &[], &mv((0, 2), (2, 2))).expect("the oracle answers `legal`"),
        "naming the automaton's square as a DESTINATION is legal to propose (ruling D)"
    );
    assert!(
        !rules::move_legal(&b, &[], &mv((2, 2), (0, 2))).expect("the oracle answers `legal`"),
        "moving the automaton ITSELF is illegal"
    );
    // And the proposed move fails to execute: the automaton occupies its square, so the attractor
    // stays where it is.
    let mid = rules::resolve_mid(&b, &[], &[mv((0, 2), (2, 2))]).expect("the oracle answers `mid`");
    assert_eq!(mid.cells, b.cells, "the move fails to execute");
    // A MARKED coordinate is illegal at either endpoint, for everyone (the conflict re-entry rule).
    assert!(
        !rules::move_legal(&b, &[(0, 2)], &mv((0, 2), (0, 4))).expect("the oracle answers `legal`"),
        "a marked SOURCE is illegal"
    );
    assert!(
        !rules::move_legal(&b, &[(0, 4)], &mv((0, 2), (0, 4))).expect("the oracle answers `legal`"),
        "a marked DESTINATION is illegal"
    );
}

/// ⚑ **THE WIN FIRES ON ENTRY, not on occupancy** (`AutomataflRules.winOnEntry`; audit §6). The
/// automaton must have MOVED into a declared goal on this turn.
///
/// The deleted Rust `win_owner` scanned the post-board for "is the automaton standing on a goal",
/// which fires forever once it arrives and fires for a position it never entered.
#[test]
fn the_win_fires_on_entry_and_not_on_occupancy() {
    let goals = rules::stock_goals2(5).expect("the oracle answers `goals`");
    assert!(goals.contains(&((0, 0), 0)), "seat 0 owns (0,0) at size 5");

    // ── A REAL ENTRY WINS. The automaton sits at (1,0); a repulsor two squares to its `+x` shoves
    // it along `−x` (`fromRepulsor`, priority 20, the `−x` ray having room: dist 2 to the wall),
    // and (0,0) is vacuum — so the step ENTERS seat 0's corner.
    let approach = mk(5, &[((3, 0), REP)], (1, 0));
    let (after, win) = rules::turn(&approach, &[], &[], &goals).expect("the oracle answers `turn`");
    assert_eq!(
        after.auto,
        (0, 0),
        "the automaton is shoved into the corner"
    );
    assert_eq!(win, Some(0), "entering seat 0's corner wins for seat 0");

    // ── SITTING ON IT IS NOT A WIN. Same corner, automaton already there, nothing pulling: it holds,
    // so it did not ENTER, so nobody wins — however long it stands there.
    let sitting = mk(5, &[], (0, 0));
    let (after, win) = rules::turn(&sitting, &[], &[], &goals).expect("the oracle answers `turn`");
    assert_eq!(
        after.auto,
        (0, 0),
        "it holds (nothing pulls on an empty board)"
    );
    assert_eq!(
        win, None,
        "SITTING on a goal is not a win — the ruleset fires on ENTRY"
    );

    // ── AND THE GOAL TABLE IS WHAT DECIDES. The same entry with NO goals declared wins nothing.
    let (after, win) = rules::turn(&approach, &[], &[], &[]).expect("the oracle answers `turn`");
    assert_eq!(after.auto, (0, 0));
    assert_eq!(win, None, "no declared goal, no win");
}

/// The LEGAL TARGET SET the surface paints is the ruleset's (`moveLegalB` over the board), and it is
/// exactly the rook line — no diagonals, not the source itself.
#[test]
fn the_legal_target_set_is_the_rook_line() {
    let b = mk(5, &[((0, 0), ATT)], (4, 4));
    let ts = rules::legal_targets(&b, &[], 0, (0, 0)).expect("the oracle answers `targets`");
    assert_eq!(ts.len(), 8, "four along the rank, four down the file");
    for t in [
        (1, 0),
        (2, 0),
        (3, 0),
        (4, 0),
        (0, 1),
        (0, 2),
        (0, 3),
        (0, 4),
    ] {
        assert!(ts.contains(&t), "{t:?} is on (0,0)'s rook line");
    }
    for t in [(1, 1), (2, 3), (0, 0)] {
        assert!(!ts.contains(&t), "{t:?} is not a legal target");
    }
    // From the automaton's own square nothing is legal at all.
    assert!(
        rules::legal_targets(&b, &[], 0, (4, 4))
            .expect("the oracle answers `targets`")
            .is_empty(),
        "the automaton is never a move SOURCE"
    );
}

/// A FORK (one source, two destinations) is a CONFLICT on that source, and the round does not
/// resolve: `roundStep` marks the coordinate and the seats re-enter.
#[test]
fn a_fork_conflicts_and_re_enters_instead_of_resolving() {
    let b = mk(5, &[((0, 0), ATT)], (4, 4));
    let ms = [
        Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        },
        Move {
            who: 1,
            frm: (0, 0),
            to: (3, 0),
        },
    ];
    assert_eq!(
        rules::clash(&b, &[], &ms).expect("the oracle answers `clash`"),
        vec![(0, 0)],
        "the contested SOURCE is the conflicted coordinate"
    );
    assert!(
        !rules::round_is_clean(&b, &ms).expect("the oracle answers"),
        "a fork is not a clean round — the fold must refuse it"
    );
    match rules::round(&b, &[], &[], &[], &[0, 1], &ms).expect("the oracle answers `round`") {
        rules::RoundOutcome::Again {
            marks,
            locked,
            waiting,
        } => {
            assert_eq!(marks, vec![(0, 0)], "the contested square is MARKED");
            assert!(locked.is_empty(), "both moves named it, so neither locks");
            assert_eq!(waiting, vec![0, 1], "both seats re-enter");
        }
        other => panic!("a fork must come back `Again`, got {other:?}"),
    }
    // A clean single move DOES resolve.
    match rules::round(&b, &[], &[], &[], &[0], &[ms[0]]).expect("the oracle answers `round`") {
        rules::RoundOutcome::Resolved { board, win } => {
            assert_eq!(board.cell_at((0, 3)), ATT, "the move executed");
            assert_eq!(win, None);
        }
        other => panic!("a clean round must RESOLVE, got {other:?}"),
    }
}
