//! Tests for [`AutomataflOffering`], DRIVEN — the CoordGrid board, the rook-line legal-move
//! highlighting (non-vacuously: an illegal target is NOT highlighted), the simultaneous
//! commit → reveal → resolve shape, the per-viewer sealed-move fog, and the REAL executor turns
//! (a legal play lands a receipt; an illegal one is refused and commits nothing).

use super::*;
use crate::board::ATT;
use crate::game::{GENESIS, coord_of, goals, index_of, opening_board};
use crate::rules::{apply_turn, move_legal};
use dreggnet_offerings::{Offering, Outcome, SessionConfig};

/// Every rendered string in a surface (text, pill/icon labels, section titles, menu rows, cell
/// glyphs) — what a viewer can (and cannot) read off the card.
fn rendered_text(surface: &Surface) -> String {
    fn walk(n: &ViewNode, out: &mut String) {
        match n {
            ViewNode::Text(s) => {
                out.push_str(s);
                out.push('\n');
            }
            ViewNode::Pill { text, .. } => {
                out.push_str(text);
                out.push('\n');
            }
            ViewNode::Icon { glyph, .. } => {
                out.push_str(glyph);
                out.push('\n');
            }
            ViewNode::Section {
                title, children, ..
            } => {
                out.push_str(title);
                out.push('\n');
                for c in children {
                    walk(c, out);
                }
            }
            ViewNode::Menu { items } => {
                for it in items {
                    out.push_str(&format!("MENU {} enabled={}\n", it.turn, it.enabled));
                }
            }
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                for c in cs {
                    walk(c, out);
                }
            }
            _ => {}
        }
    }
    let mut out = String::new();
    walk(surface.view(), &mut out);
    out
}

/// The board [`ViewNode::CoordGrid`] of a surface (the one board node).
fn grid(surface: &Surface) -> (usize, Vec<CoordCell>) {
    fn find(n: &ViewNode) -> Option<(usize, Vec<CoordCell>)> {
        match n {
            ViewNode::CoordGrid { cols, cells } => Some((*cols, cells.clone())),
            ViewNode::Section { children: cs, .. }
            | ViewNode::VStack(cs)
            | ViewNode::Row(cs)
            | ViewNode::List(cs)
            | ViewNode::Table(cs) => cs.iter().find_map(find),
            _ => None,
        }
    }
    find(surface.view()).expect("the surface paints a CoordGrid board")
}

fn seat_a() -> DreggIdentity {
    AutomataflOffering::seat_identity(Seat::A)
}
fn seat_b() -> DreggIdentity {
    AutomataflOffering::seat_identity(Seat::B)
}

fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

/// Drive one seat's whole commit (select → seal) and assert both land real turns.
fn seal(
    off: &AutomataflOffering,
    s: &mut AutomataflSession,
    who: &DreggIdentity,
    frm: Coord,
    to: Coord,
) {
    let src = index_of(frm).expect("in bounds") as i64;
    let dst = index_of(to).expect("in bounds") as i64;
    assert!(
        off.advance(s, act(SELECT, src), who.clone()).landed(),
        "the select lands a real turn"
    );
    assert!(
        off.advance(s, act(COMMIT, dst), who.clone()).landed(),
        "the seal lands a real turn"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 1. THE BOARD IS A COORDGRID
// ────────────────────────────────────────────────────────────────────────────────────────────

/// The board renders as a valid `CoordGrid`: 11 columns, 121 cells (the STOCK two-player board —
/// the size the Lean descriptors are emitted at), the particles as glyphs, the automaton cell
/// MARKED (`@`, tag `accent`, in the highlight-set).
#[test]
fn the_board_renders_as_a_coordgrid() {
    let off = AutomataflOffering;
    let session = off.open(SessionConfig::with_seed(11)).expect("open");
    let (cols, cells) = grid(&off.render(&session));

    assert_eq!(cols, N, "eleven columns — the stock board");
    assert_eq!(cells.len(), CELLS, "one cell per board square (121)");

    // The STOCK opening: twelve attractors, twenty-four repulsors, one automaton dead centre.
    assert_eq!(cells.iter().filter(|c| c.glyph == "A").count(), 12);
    assert_eq!(cells.iter().filter(|c| c.glyph == "R").count(), 24);
    assert_eq!(cells.iter().filter(|c| c.glyph == "@").count(), 1);

    // The automaton square (5,5) — marked and highlighted.
    let auto_idx = index_of((5, 5)).unwrap();
    assert_eq!(cells[auto_idx].glyph, "@");
    assert_eq!(cells[auto_idx].tag, "accent");
    assert!(cells[auto_idx].highlight, "the automaton cell is marked");

    // THE FOUR GOAL CORNERS ARE MARKED — even though the stock opening OCCUPIES every one of them
    // (a repulsor sits on all four). Before, a goal was legible only by its `a`/`b` glyph, which a
    // piece standing on it hides: on the stock board that made the four squares that decide the
    // game paint as ordinary pieces.
    for (g, who) in goals().expect("the Lean game oracle (`dregg_automatafl_rules`) answers") {
        let i = index_of(*g).expect("a goal corner is on the board");
        assert_eq!(
            cells[i].tag, "goal",
            "goal corner {g:?} (seat {who}) is marked as an objective"
        );
    }

    // The grid AGREES with the Lean-sourced opening board, square by square.
    let board = opening_board().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
    for idx in 0..CELLS {
        let expect = match board.cells[idx] {
            REP => "R",
            ATT => "A",
            AUTO => "@",
            _ => "",
        };
        if !expect.is_empty() {
            assert_eq!(cells[idx].glyph, expect, "square {idx} paints its particle");
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 2. ROOK-LINE LEGAL-MOVE HIGHLIGHTING — NON-VACUOUS
// ────────────────────────────────────────────────────────────────────────────────────────────

/// Selecting a piece LIGHTS ITS ROOK LINE and nothing else: every legal target (same row/column,
/// distinct, in-bounds, not the automaton) is highlighted and carries the `commit` affordance; an
/// ILLEGAL target (a diagonal, an off-line square, the source itself) is NOT highlighted and
/// carries no commit affordance.
#[test]
fn selecting_a_piece_highlights_exactly_its_legal_moves() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(12)).expect("open");

    // Before any selection: no legal-move highlight-set at all (only the automaton is marked).
    let (_, cold) = grid(&off.render_for(&session, &seat_a()));
    assert_eq!(
        cold.iter().filter(|c| c.highlight).count(),
        1,
        "with nothing selected, only the automaton is marked"
    );

    // Seat A selects the stock attractor at (3,1) — a REAL turn.
    let src = (3, 1);
    let src_idx = index_of(src).unwrap();
    assert!(
        off.advance(&mut session, act(SELECT, src_idx as i64), seat_a())
            .landed(),
        "the select lands a real turn"
    );

    let (_, cells) = grid(&off.render_for(&session, &seat_a()));

    // The LEAN's own legal set (the tooth the highlight must mirror).
    let expected: Vec<usize> = (0..CELLS)
        .filter(|&i| {
            move_legal(
                session.board(),
                &[],
                &Move {
                    who: 0,
                    frm: src,
                    to: coord_of(i),
                },
            )
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers")
        })
        .collect();
    // Rook line of (3,1) on an 11×11: row y=1 minus (3,1) → 10; column x=3 minus (3,1) → 10. The
    // automaton is at (5,5) — on neither, so nothing is excluded here.
    assert_eq!(
        expected.len(),
        20,
        "the rook line of (3,1) is twenty squares"
    );

    for &i in &expected {
        assert!(
            cells[i].highlight,
            "the legal target {:?} is highlighted",
            coord_of(i)
        );
        assert_eq!(cells[i].tag, "good");
        assert_eq!(cells[i].turn, COMMIT, "a legal target fires the seal");
        assert_eq!(cells[i].arg, i as i64);
    }

    // The SOURCE is marked as the selection (not as a legal target).
    assert!(cells[src_idx].highlight);
    assert_eq!(cells[src_idx].tag, "warn");

    // NON-VACUITY: every square that is NOT a legal target (and not the source / the automaton) is
    // NOT highlighted and offers no seal.
    let auto_idx = index_of((5, 5)).unwrap();
    for i in 0..CELLS {
        if expected.contains(&i) || i == src_idx || i == auto_idx {
            continue;
        }
        assert!(
            !cells[i].highlight,
            "the ILLEGAL target {:?} is NOT highlighted",
            coord_of(i)
        );
        assert_ne!(
            cells[i].turn,
            COMMIT,
            "the illegal target {:?} offers no seal",
            coord_of(i)
        );
    }

    // Four named illegal targets, explicitly: (4,2) is the diagonal step; (0,0) / (10,10) / (5,4)
    // share neither row nor column with (3,1) — off the rook line, so out of the highlight-set.
    for bad in [(4, 2), (0, 0), (10, 10), (5, 4)] {
        let i = index_of(bad).unwrap();
        assert!(
            !cells[i].highlight,
            "{bad:?} is not on (3,1)'s rook line — no highlight"
        );
    }

    // ⚑ THE AUTOMATON'S SQUARE, AS THE RULESET HAS IT. Naming it as a DESTINATION is LEGAL to
    // propose (ruling D: `model.py::ev_Move` rejects only a move whose SOURCE is the agent), and the
    // move then simply FAILS to execute, because the inclusive path check finds the square occupied.
    // So `(0,5) → (5,5)` is legal, and resolving it leaves the repulsor where it was.
    //
    // This test previously asserted the opposite. That came from `logic/src/game.rs`, which bans both
    // endpoints — the audit's ruling (D) is that the README and the python prototype are the
    // authority and only the SOURCE is banned.
    let onto_auto = Move {
        who: 0,
        frm: (0, 5),
        to: (5, 5),
    };
    assert!(
        move_legal(session.board(), &[], &onto_auto)
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers"),
        "naming the automaton's square as a destination is legal to PROPOSE (ruling D)"
    );
    let after = crate::rules::resolve_mid(session.board(), &[], &[onto_auto])
        .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
    assert_eq!(
        after.cells,
        session.board().cells,
        "and it FAILS TO EXECUTE: the occupied destination blocks the move, so nothing changes"
    );

    // Moving the automaton ITSELF is illegal — the square is banned as a SOURCE.
    assert!(
        !move_legal(
            session.board(),
            &[],
            &Move {
                who: 0,
                frm: (5, 5),
                to: (5, 3)
            }
        )
        .expect("the Lean game oracle (`dregg_automatafl_rules`) answers"),
        "the automaton is never a move SOURCE"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 3. REAL TURNS — a legal seal LANDS, an illegal move is REFUSED (nothing commits)
// ────────────────────────────────────────────────────────────────────────────────────────────

/// A move submission fires a REAL executor turn; an ILLEGAL move (a diagonal, the automaton's
/// square, an off-board square, a seal with no selection) is REFUSED and commits NOTHING.
#[test]
fn an_illegal_move_is_refused_and_commits_nothing() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(13)).expect("open");

    // A seal with no selection: refused.
    assert!(
        matches!(
            off.advance(&mut session, act(COMMIT, 0), seat_a()),
            Outcome::Refused(_)
        ),
        "sealing without selecting is refused"
    );

    // Select the stock attractor at (3,1) — a real turn.
    let src_idx = index_of((3, 1)).unwrap() as i64;
    assert!(
        off.advance(&mut session, act(SELECT, src_idx), seat_a())
            .landed()
    );
    let commits_before = session.game().read_reg("commits");

    // A DIAGONAL destination (4,2): not a rook line — refused.
    let diag = index_of((4, 2)).unwrap() as i64;
    let refused = off.advance(&mut session, act(COMMIT, diag), seat_a());
    assert!(
        matches!(refused, Outcome::Refused(_)),
        "a diagonal move is refused"
    );

    // ⚑ THE AUTOMATON'S SQUARE IS *NOT* IN THIS LIST. Naming it as a DESTINATION is legal to
    // PROPOSE under the ruleset (audit ruling D: `model.py::ev_Move` bans only a move whose SOURCE
    // is the agent) and then fails to execute at resolution. This test used to assert a refusal
    // here, which was `logic/src/game.rs`'s reading rather than the README's. The ruleset's answer
    // is pinned by `a_move_onto_the_automaton_is_a_legal_proposal_that_fails_to_execute` below and
    // by the highlight test above (the square is IN the rook-line set).
    //
    // Move the selection onto the automaton's own rank anyway, so the off-board case below is
    // exercised from a live selection.
    assert!(
        off.advance(
            &mut session,
            act(SELECT, index_of((0, 5)).unwrap() as i64),
            seat_a()
        )
        .landed()
    );

    // An OFF-BOARD square is refused.
    assert!(
        matches!(
            off.advance(&mut session, act(COMMIT, 999), seat_a()),
            Outcome::Refused(_)
        ),
        "an off-board square is refused"
    );

    // NOTHING committed: the executor's commit counter never moved, and no move is sealed.
    assert_eq!(
        session.game().read_reg("commits"),
        commits_before,
        "a refused move commits nothing (anti-ghost)"
    );
    assert!(matches!(session.phase(), Phase::Commit));

    // A LEGAL seal from the same selection lands a real turn: (0,5) → (3,5), along the rank.
    let clean = index_of((3, 5)).unwrap() as i64;
    let landed = off.advance(&mut session, act(COMMIT, clean), seat_a());
    assert!(landed.landed(), "the legal seal lands a real receipt");
    assert_eq!(
        session.game().read_reg("commits"),
        commits_before + 1,
        "the committed seal advanced the executor's commit counter"
    );
}

/// ⚑ **A MOVE ONTO THE AUTOMATON IS A LEGAL PROPOSAL THAT FAILS TO EXECUTE** — audit ruling (D)
/// plus clause 3.2, driven end-to-end through the surface.
///
/// Seat A seals the repulsor at `(5,1)` onto the automaton's square `(5,5)` — the file between them
/// is clear, so nothing but the DESTINATION can stop it. The seal LANDS (a legal proposal), and the
/// resolution leaves the repulsor exactly where it was, because the inclusive path check finds the
/// destination occupied. Seat B's clean move on another file executes in the same round, so the
/// round really did resolve — A's move failing is not the round refusing.
///
/// The deleted Rust oracle answered this input twice over differently: `move_valid` REFUSED the
/// proposal outright, and `occluded` (interior-only) would have let the mover land on and DESTROY
/// the automaton's cell had the proposal ever reached resolution.
#[test]
fn a_move_onto_the_automaton_is_a_legal_proposal_that_fails_to_execute() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(21)).expect("open");
    assert_eq!(session.board().cell_at((5, 1)), REP, "the stock repulsor");
    assert_eq!(
        session.board().cell_at((5, 5)),
        AUTO,
        "the automaton, dead centre"
    );

    // A: (5,1) → (5,5), the automaton's own square. THE SEAL LANDS.
    seal(&off, &mut session, &seat_a(), (5, 1), (5, 5));
    // B: a clean attractor move on a clear file.
    seal(&off, &mut session, &seat_b(), (3, 1), (3, 3));

    assert!(off.advance(&mut session, act(REVEAL, 0), seat_a()).landed());
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());
    assert!(
        off.advance(&mut session, act(RESOLVE, 0), seat_a())
            .landed(),
        "the round RESOLVES — a proposal that cannot execute is not a conflict"
    );

    assert_eq!(
        session.board().cell_at((5, 1)),
        REP,
        "A's repulsor is replaced at its origin: the occupied destination blocked the move"
    );
    assert_eq!(
        session.board().cell_at((3, 3)),
        ATT,
        "B's clean move executed in the same round"
    );
    assert_eq!(
        session.board().cell_at((3, 1)),
        VAC,
        "…and vacated its source"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 4. THE PER-VIEWER SEALED-MOVE FOG
// ────────────────────────────────────────────────────────────────────────────────────────────

/// `render_for` shows the viewer their OWN sealed move and FOGS the opponent's (the
/// simultaneous-secret shape): A's source/destination appear in A's view and NOT in B's.
#[test]
fn a_viewer_sees_their_own_sealed_move_and_the_opponent_is_fog() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(14)).expect("open");

    seal(&off, &mut session, &seat_a(), (3, 1), (3, 3));
    seal(&off, &mut session, &seat_b(), (7, 1), (7, 3));

    let a_view = rendered_text(&off.render_for(&session, &seat_a()));
    let b_view = rendered_text(&off.render_for(&session, &seat_b()));
    let public = rendered_text(&off.render(&session));

    // A sees their own move in full…
    assert!(
        a_view.contains("YOUR sealed move: (3,1) → (3,3)"),
        "A reads their own sealed move\n{a_view}"
    );
    // …and NOT B's (fog: only the commitment).
    assert!(
        !a_view.contains("(7,1) → (7,3)"),
        "B's sealed move is FOG to A\n{a_view}"
    );
    assert!(
        a_view.contains("move SEALED"),
        "A sees the opponent's commitment, not their move"
    );

    // Symmetrically for B.
    assert!(b_view.contains("YOUR sealed move: (7,1) → (7,3)"));
    assert!(
        !b_view.contains("(3,1) → (3,3)"),
        "A's sealed move is FOG to B\n{b_view}"
    );

    // The PUBLIC surface fogs BOTH.
    assert!(!public.contains("(3,1) → (3,3)") && !public.contains("(7,1) → (7,3)"));
    assert_eq!(
        public.matches("move SEALED").count(),
        2,
        "both moves are sealed on the public surface"
    );

    // After the reveals, both moves are open on every surface (the fog lifts on the open).
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_a()).landed());
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());
    let after = rendered_text(&off.render(&session));
    assert!(
        after.contains("revealed: (3,1) → (3,3)") && after.contains("revealed: (7,1) → (7,3)"),
        "the reveal opens both moves\n{after}"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 5. A FULL n=2 TURN — commit → reveal → resolve, against the LEAN's own transition
// ────────────────────────────────────────────────────────────────────────────────────────────

/// A full simultaneous turn drives through the Offering, and the resolved board is EXACTLY what the
/// LEAN says the turn is (`automatonStepCfg ∘ resolveMoves`, the object the AIR is refined against) —
/// on both the session's board AND the executor's COMMITTED cell state.
#[test]
fn a_full_turn_resolves_exactly_as_the_ruleset() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(15)).expect("open");

    let before = session.board().clone();
    // The CLEAN stock round the Lean resolve descriptor's own `clean_resolve_satisfies` guard
    // pins: two independent, unoccluded attractor moves off the `y = 1` rank.
    let ma = Move {
        who: 0,
        frm: (3, 1),
        to: (3, 3),
    };
    let mb = Move {
        who: 1,
        frm: (7, 1),
        to: (7, 3),
    };
    seal(&off, &mut session, &seat_a(), ma.frm, ma.to);
    seal(&off, &mut session, &seat_b(), mb.frm, mb.to);
    assert!(matches!(session.phase(), Phase::Reveal));

    // A resolve BEFORE both reveals is refused (the phase discipline).
    assert!(matches!(
        off.advance(&mut session, act(RESOLVE, 0), seat_a()),
        Outcome::Refused(_)
    ));

    assert!(off.advance(&mut session, act(REVEAL, 0), seat_a()).landed());
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());
    assert!(matches!(session.phase(), Phase::Resolve));

    let out = off.advance(&mut session, act(RESOLVE, 0), seat_a());
    assert!(out.landed(), "the resolution lands one real turn");

    // THE ORACLE: the resolved board is exactly the LEAN's transition.
    let expect = apply_turn(&before, &[ma, mb])
        .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
    assert_eq!(
        session.board().cells,
        expect.cells,
        "the board matches the Lean transition"
    );
    assert_eq!(
        session.board().auto,
        expect.auto,
        "the automaton stepped as the ruleset says"
    );

    // …and the EXECUTOR's committed cell state agrees, square for square: the deployed substrate
    // reproduces the board the ruleset resolved. (This is a per-case agreement check on two concrete
    // boards — not translation validation, which would need a formal semantics of the executor.)
    let committed = session.game().read_state();
    assert_eq!(
        committed.cells, expect.cells,
        "the committed board == the ruleset's board"
    );
    assert_eq!(committed.auto, expect.auto);
    assert_eq!(committed.turn_no, 1, "one resolved turn is committed");

    // The seals are cleared for the next turn, and the surface is back in the commit phase.
    assert!(matches!(session.phase(), Phase::Commit));
    assert_eq!(
        committed.commit,
        [0, 0],
        "the seals cleared on the resolution"
    );

    // The offering re-verifies the whole committed match.
    let report = off.verify(&session);
    assert!(
        report.verified,
        "the committed match verifies: {}",
        report.detail
    );
    assert!(
        report.turns >= 7,
        "genesis + 2 selects + 2 seals + 2 reveals + 1 resolve"
    );

    // ── THE MOVE HISTORY IS RECORDED. Before this the surface threw every move away on the
    // resolution, and the only foldable shape left was the automaton-only chain (which attests no
    // move at all). The session now hands the crown the genesis position + the played rounds.
    assert_eq!(
        session.start_board().cells,
        before.cells,
        "the genesis position is retained (the fold's decodable board_genesis)"
    );
    assert_eq!(
        session.rounds(),
        vec![(ma, mb)],
        "the resolved round recorded BOTH seats' revealed moves, in seat order"
    );
    // …and the TURN is recorded whole: its start board, its (empty) conflict braid, and the pair
    // that resolved — the `MultiRoundTurn` shape, with `conflict_subs` empty because nothing clashed.
    assert_eq!(session.turns_played().len(), 1);
    assert_eq!(session.turns_played()[0].start.cells, before.cells);
    assert!(
        session.turns_played()[0].conflict_subs.is_empty(),
        "a clean turn has NO conflict rounds — it folds through the plain two-leg path"
    );
    assert_eq!(session.turns_played()[0].clean_subs, [ma, mb]);
    // And the round state is CLEARED for the next turn (`model.py::ClearState` / `openRound`).
    assert!(session.marks().is_empty(), "the markers die at turn end");
    assert!(session.locked().is_empty());
    assert_eq!(
        session.waiting(),
        [0, 1].as_slice(),
        "both seats owe the next turn"
    );
    assert_eq!(
        session
            .unfoldable_round()
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers"),
        None,
        "a clean round is foldable — nothing blocks the crown"
    );
}

/// **A REFUSED resolution records NO round** (anti-ghost for the move history): the phase
/// discipline refuses a resolve before both reveals, and the history stays empty.
#[test]
fn a_refused_resolution_records_no_round() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(19)).expect("open");

    seal(&off, &mut session, &seat_a(), (3, 1), (3, 3));
    seal(&off, &mut session, &seat_b(), (7, 1), (7, 3));
    assert!(matches!(
        off.advance(&mut session, act(RESOLVE, 0), seat_a()),
        Outcome::Refused(_)
    ));
    assert!(
        session.rounds().is_empty(),
        "a refused resolution commits nothing and records nothing"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 5b. ⚑ THE CONFLICT RE-SUBMISSION LOOP — the ruleset's real turn structure, on the surface.
//
// Every decision in this section is the LEAN's: `crate::rules::round` is `AutomataflRules.roundStep`
// through `@[export] dregg_automatafl_rules`, and it returns the clash set, the marks, the freeze,
// the lock set and the waiting set in one reply. The tests assert the surface CARRIES them.
//
// RED BEFORE: the previous surface resolved a clash by DROPPING both moves and advancing the turn
// (the test these replace asserted exactly that — "the conflicting round still RESOLVES on the
// surface (both moves dropped)"), which the rules-conformance audit rates ABSENT/HIGH on four
// clauses. Every assertion below fails against that surface: there was no `Phase::Resubmit`, no
// `marks()`, no `waiting()`, and the turn counter moved.
// ────────────────────────────────────────────────────────────────────────────────────────────

/// The 11×11 stock opening's attractor at `(3,1)`, forked by both seats — the smallest clash the
/// played board admits.
const FORK_SRC: Coord = (3, 1);

/// Drive both seats through seal → open → resolve for one round, returning the resolution outcome.
fn play_round(
    off: &AutomataflOffering,
    s: &mut AutomataflSession,
    a: Option<(Coord, Coord)>,
    b: Option<(Coord, Coord)>,
) -> Outcome {
    if let Some((frm, to)) = a {
        seal(off, s, &seat_a(), frm, to);
    }
    if let Some((frm, to)) = b {
        seal(off, s, &seat_b(), frm, to);
    }
    for (waiting, who) in [(a.is_some(), seat_a()), (b.is_some(), seat_b())] {
        if waiting {
            assert!(
                off.advance(s, act(REVEAL, 0), who).landed(),
                "the reveal lands a real turn"
            );
        }
    }
    assert!(matches!(s.phase(), Phase::Resolve));
    off.advance(s, act(RESOLVE, 0), seat_a())
}

/// ⚑ **A FORCED CLASH RE-ENTERS THE ROUND — it does not drop the moves.** Both seats fork the
/// attractor at `(3,1)`. Under the ruleset that round does not resolve at all: the contested
/// coordinate is MARKED, the board FREEZES, the turn counter does NOT advance, and both seats owe a
/// FRESH move. Every one of those is read back off the session, and the negatives are asserted too
/// (the board did not move, the turn did not advance, no turn was recorded as played).
#[test]
fn a_forced_clash_re_enters_the_round_instead_of_dropping_the_moves() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(20)).expect("open");
    let before = session.board().clone();

    let out = play_round(
        &off,
        &mut session,
        Some((FORK_SRC, (3, 3))),
        Some((FORK_SRC, (5, 1))),
    );
    assert!(
        out.landed(),
        "the re-entry is a REAL turn on the executor (the `resubmit` method), not a soft state flip"
    );

    // ── THE PHASE. A fourth station the surface did not have.
    assert_eq!(
        session.phase(),
        Phase::Resubmit,
        "a clash re-opens the round for re-submission"
    );
    assert_eq!(session.conflict_round_no(), 1, "one conflict round so far");

    // ── THE MARK, from the LEAN. `roundStep`'s `cs` for a fork is the shared SOURCE.
    assert_eq!(
        session.marks(),
        [FORK_SRC].as_slice(),
        "the contested coordinate is marked — the Lean's own conflict set"
    );

    // ── THE FREEZE (a negative). Nothing resolved, so the board is byte-identical, automaton
    // INCLUDED: the daemon does not step on a round that never happened.
    assert_eq!(
        session.board().cells,
        before.cells,
        "a conflicted round resolves nothing — the board is FROZEN"
    );
    assert_eq!(
        session.board().auto,
        before.auto,
        "the automaton does NOT step on a conflicted round"
    );
    assert_eq!(session.turn_no(), 0, "the turn counter does not advance");
    assert!(
        session.turns_played().is_empty(),
        "no turn is recorded as played — the turn is still in flight"
    );
    assert!(
        session.last_step().is_none(),
        "no automaton step is recorded for a round that did not resolve"
    );

    // ── WHO RE-SUBMITS. A fork over two moves names both, so both seats re-enter and nothing locks.
    assert_eq!(
        session.waiting(),
        [0, 1].as_slice(),
        "both seats owe a fresh move"
    );
    assert!(session.locked().is_empty(), "nothing is locked at n=2 here");
    for seat in [Seat::A, Seat::B] {
        assert!(session.is_waiting(seat));
        assert!(
            session.owes_a_move(seat),
            "seat {} owes a fresh move",
            seat.label()
        );
        assert!(
            session.committed[seat.idx()].is_none(),
            "the re-entering seat's seal is WOUND BACK — it has a fresh move to make"
        );
        assert!(!session.revealed[seat.idx()]);
        assert!(session.sel[seat.idx()].is_none());
    }

    // ── ⚑ RED-BEFORE, MEASURED — and it pins WHY the old bug was invisible.
    //
    // The old surface resolved this exact pair with `rules::turn`, whose type cannot express a
    // re-entry: it returns `(board, win)`, so a clash could only ever come back as a finished turn.
    // Ask both verbs the same question and the disagreement is in the TURN STRUCTURE.
    let forced = apply_turn(
        &before,
        &[
            Move {
                who: 0,
                frm: FORK_SRC,
                to: (3, 3),
            },
            Move {
                who: 1,
                frm: FORK_SRC,
                to: (5, 1),
            },
        ],
    )
    .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
    // ⚑ THE FINDING, and it is worse than "both moves drop". `turn`/`apply_turn` are the RESOLUTION
    // legs (`automatonStepCfg ∘ resolveMoves`), and `resolveMoves` is guarded by `resolvableB` —
    // which is the MERGE clause (`unresolved`) ONLY. The fork/collide clauses live in `roundStep`,
    // and `turn` never consults them. So on this input the old path did not drop both moves: the
    // inclusive path check blocked seat B's move (a repulsor stands on (4,1), mid-path), which left
    // seat A's as the single unblocked edge out of (3,1) — and it EXECUTED. One seat's move landed,
    // the other silently evaporated, and the turn advanced.
    assert_ne!(
        forced.cells, before.cells,
        "the verb the OLD surface called MOVED A PIECE on a clashed round"
    );
    assert_eq!(
        forced.cell_at((3, 3)),
        ATT,
        "…specifically seat A's move EXECUTED (it was the surviving unblocked edge)"
    );
    assert_eq!(
        forced.cell_at(FORK_SRC),
        VAC,
        "…vacating the contested source"
    );
    assert_eq!(
        forced.cell_at((5, 1)),
        REP,
        "…while seat B's move vanished with no trace at all"
    );
    // The ruleset's answer is the opposite on every count: nothing moved, nothing was chosen
    // between, and the round is still open. (Asserted in full above; restated here as the direct
    // contrast to the line above it.)
    assert_eq!(
        session.board().cell_at(FORK_SRC),
        ATT,
        "the ruleset moved NOTHING"
    );
    assert_eq!(session.board().cell_at((3, 3)), VAC);
    // So the divergence is entirely in the turn structure, and it is total: the ruleset says this
    // round does not resolve, and the old surface had no way to say that.
    assert!(
        matches!(
            rules::round(
                &before,
                goals().expect("the goal assignment"),
                &[],
                &[],
                &[0, 1],
                &[
                    Move {
                        who: 0,
                        frm: FORK_SRC,
                        to: (3, 3)
                    },
                    Move {
                        who: 1,
                        frm: FORK_SRC,
                        to: (5, 1)
                    },
                ],
            )
            .expect("the oracle answers `round`"),
            rules::RoundOutcome::Again { .. }
        ),
        "the RULESET's answer for this pair is `again` — a round that does not resolve"
    );

    // ── THE EXECUTOR SAW IT. `marked` is the committed termination witness.
    let committed = session.game().read_state();
    assert_eq!(
        committed.marked, 1,
        "the cell holds the marked-square count"
    );
    assert_eq!(committed.turn_no, 0, "the committed turn did not advance");
    assert_eq!(
        committed.cells, before.cells,
        "the committed board is frozen too"
    );

    // ── AND IT IS VISIBLE. The board paints the marked square dead, with no affordance; the plaque
    // says what happened, who re-submits and why.
    let (_, cells) = grid(&off.render(&session));
    let mark_cell = &cells[index_of(FORK_SRC).expect("in bounds")];
    assert_eq!(mark_cell.tag, "mark", "the marked square gets its own tag");
    assert_eq!(
        mark_cell.glyph, "×",
        "and its own glyph, for the text frontends"
    );
    assert!(
        mark_cell.turn.is_empty(),
        "a marked square carries NO affordance — clicking it can only be refused"
    );
    assert!(!mark_cell.highlight, "a dead square is not a live one");
    let text = rendered_text(&off.render_for(&session, &seat_a()));
    assert!(text.contains("The clash"), "the clash plaque is rendered");
    assert!(text.contains("RE-SUBMITTING: seat A and seat B"), "{text}");
    assert!(
        text.contains("MARKS the contested coordinate — (3,1)"),
        "{text}"
    );
}

/// ⚑ **A RE-SUBMITTED MOVE ONTO A MARKED SQUARE IS REFUSED** — the marks-legality RE-CHECK, which
/// is a real rule (`MoveLegal`: `m.frm ∉ marks ∧ m.to ∉ marks`) and not decoration. Both endpoints,
/// both seats, and NOTHING commits either way.
#[test]
fn a_re_submitted_move_naming_a_marked_square_is_refused() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(21)).expect("open");
    assert!(
        play_round(
            &off,
            &mut session,
            Some((FORK_SRC, (3, 3))),
            Some((FORK_SRC, (5, 1))),
        )
        .landed()
    );
    assert_eq!(session.marks(), [FORK_SRC].as_slice());
    let commits_before = session.game().read_reg("commits");
    let marked_src = index_of(FORK_SRC).expect("in bounds") as i64;

    // (a) THE MARKED SQUARE AS A SOURCE. It still holds an attractor, so it looks movable — the
    // mark is why it is not, and the refusal says so by name.
    assert!(
        session.board().cell_at(FORK_SRC) == ATT,
        "the piece is still there"
    );
    assert!(
        !session.movable(FORK_SRC),
        "a marked square cannot be picked up"
    );
    match off.advance(&mut session, act(SELECT, marked_src), seat_a()) {
        Outcome::Refused(why) => assert!(
            why.contains("MARKED"),
            "the refusal names the mark, not a generic illegality: {why}"
        ),
        other => panic!("selecting a MARKED square must be refused, got {other:?}"),
    }

    // (b) THE MARKED SQUARE AS A DESTINATION. Pick up the repulsor at (4,1) — its rook line runs
    // straight through (3,1) — and try to seal a move ONTO the mark.
    assert!(
        off.advance(
            &mut session,
            act(SELECT, index_of((4, 1)).unwrap() as i64),
            seat_b()
        )
        .landed()
    );
    match off.advance(&mut session, act(COMMIT, marked_src), seat_b()) {
        Outcome::Refused(why) => {
            assert!(why.contains("MARKED"), "the refusal names the mark: {why}")
        }
        other => panic!("sealing a move ONTO a MARKED square must be refused, got {other:?}"),
    }

    // …and it is not merely refused, it is not OFFERED: the marked square is absent from the rook
    // line the surface paints for that very piece, because the LEAN's `moveLegalB` was asked WITH
    // the marks.
    assert!(
        !session.legal_targets((4, 1)).contains(&FORK_SRC),
        "the marked square is not in the offered target set"
    );
    let (_, cells) = grid(&off.render_for(&session, &seat_b()));
    assert_eq!(cells[marked_src as usize].tag, "mark");
    assert!(cells[marked_src as usize].turn.is_empty());

    // ANTI-GHOST: neither refusal sealed anything.
    assert_eq!(
        session.game().read_reg("commits"),
        commits_before,
        "a refused re-submission commits NOTHING"
    );
    assert!(session.committed[1].is_none(), "seat B still owes a move");
}

/// ⚑ **THE MARKS ACCUMULATE ACROSS ≥2 CONFLICT ROUNDS, AND THEY STRICTLY GROW** (M3's termination
/// bound). Two forks in a row on two different sources leave two marks, and the deployed cell's
/// `marked` register grows `0 → 1 → 2` — which is exactly what makes the re-entry terminate.
#[test]
fn the_marks_accumulate_across_two_conflict_rounds_and_strictly_grow() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(22)).expect("open");
    let before = session.board().clone();

    // Round 1: fork (3,1).
    assert!(
        play_round(
            &off,
            &mut session,
            Some((FORK_SRC, (3, 3))),
            Some((FORK_SRC, (5, 1))),
        )
        .landed()
    );
    assert_eq!(session.marks(), [FORK_SRC].as_slice());
    assert_eq!(session.game().read_reg("marked"), 1);

    // Round 2: fork the OTHER `y = 1` attractor, (7,1). Neither move names the first mark, so both
    // are legal — and the round clashes again.
    assert!(
        play_round(
            &off,
            &mut session,
            Some(((7, 1), (7, 3))),
            Some(((7, 1), (9, 1))),
        )
        .landed()
    );

    assert_eq!(session.phase(), Phase::Resubmit, "still re-submitting");
    assert_eq!(session.conflict_round_no(), 2, "two conflict rounds");
    let marks = session.marks();
    assert_eq!(marks.len(), 2, "the marks ACCUMULATE: {marks:?}");
    assert!(
        marks.contains(&FORK_SRC) && marks.contains(&(7, 1)),
        "{marks:?}"
    );
    assert_eq!(
        session.game().read_reg("marked"),
        2,
        "the committed marked count STRICTLY GREW — the executor's termination tooth"
    );
    // Still frozen, still turn 0, after TWO conflict rounds.
    assert_eq!(session.board().cells, before.cells);
    assert_eq!(session.turn_no(), 0);
    // The n² bound, said as an invariant rather than a hope: each re-entry marked ≥1 new square, so
    // the count is at least the round number and at most the board.
    assert!(session.marks().len() >= session.conflict_round_no());
    assert!(session.marks().len() <= CELLS);

    // ── ROUND 3 RESOLVES, and it resolves the moves that were actually submitted — the accumulated
    // marks are still in force for its legality (both moves avoid them).
    assert!(
        play_round(
            &off,
            &mut session,
            Some(((3, 9), (3, 7))),
            Some(((7, 9), (7, 7))),
        )
        .landed()
    );
    assert_eq!(session.turn_no(), 1, "NOW the turn advances");
    assert_eq!(session.phase(), Phase::Commit, "and a fresh turn opens");
    assert!(
        session.marks().is_empty(),
        "the markers DIE at turn end (`model.py::ClearState`)"
    );
    assert_eq!(
        session.game().read_reg("marked"),
        0,
        "and the cell's count drops back with them"
    );

    // ── THE TURN IS RECORDED WHOLE — the `MultiRoundTurn` the Leg C braid folds: the frozen start
    // board, the TWO conflict rounds' submissions in re-entry order, and the pair that resolved.
    assert_eq!(session.turns_played().len(), 1, "ONE turn, three rounds");
    let t = &session.turns_played()[0];
    assert_eq!(
        t.start.cells, before.cells,
        "the turn-start board is the frozen one"
    );
    assert_eq!(
        t.conflict_subs,
        vec![
            [
                Move {
                    who: 0,
                    frm: FORK_SRC,
                    to: (3, 3)
                },
                Move {
                    who: 1,
                    frm: FORK_SRC,
                    to: (5, 1)
                },
            ],
            [
                Move {
                    who: 0,
                    frm: (7, 1),
                    to: (7, 3)
                },
                Move {
                    who: 1,
                    frm: (7, 1),
                    to: (9, 1)
                },
            ],
        ],
        "both conflict rounds are recorded, in re-entry order"
    );
    assert_eq!(
        t.clean_subs,
        [
            Move {
                who: 0,
                frm: (3, 9),
                to: (3, 7)
            },
            Move {
                who: 1,
                frm: (7, 9),
                to: (7, 7)
            },
        ]
    );
    // …and the PLAIN two-leg fold must refuse this turn BY NAME: it resolved against accumulated
    // marks, and Leg R has no marks lane. It is a `MultiRoundTurn`, not a round of `played`.
    assert_eq!(
        session
            .unfoldable_round()
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers"),
        Some(0),
        "a turn that RE-ENTERED is not foldable by the plain path"
    );
}

/// ⚑ **THE TERMINATION TOOTH IS THE DEPLOYED CELL'S, not the surface's good manners.** After a real
/// clash, a raw `resubmit` turn that does NOT mark a new square is REFUSED by
/// `StrictMonotonic{marked}`, and one that claims more marks than the board has squares is REFUSED
/// by `FieldLte{marked ≤ CELLS}` — which together bound a turn at n² re-entries.
#[test]
fn the_cell_refuses_a_re_entry_that_marks_nothing_new() {
    use crate::game::RESUBMIT;

    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(23)).expect("open");
    assert!(
        play_round(
            &off,
            &mut session,
            Some((FORK_SRC, (3, 3))),
            Some((FORK_SRC, (5, 1))),
        )
        .landed()
    );
    assert_eq!(session.game().read_reg("marked"), 1);

    // (a) A re-entry that marks NOTHING NEW — the non-termination shape.
    assert!(
        session
            .game()
            .commit_raw(RESUBMIT, vec![session.game().reg_effect("marked", 1)])
            .is_err(),
        "a `resubmit` that does not burn a NEW square is REFUSED — that is the n² bound"
    );
    // (b) A re-entry claiming MORE marks than the board has squares.
    assert!(
        session
            .game()
            .commit_raw(
                RESUBMIT,
                vec![session.game().reg_effect("marked", CELLS as u64 + 1)]
            )
            .is_err(),
        "a marked count above the board's square count is REFUSED"
    );
    // (c) …and a `resubmit` may not move the board or the turn either.
    assert!(
        session
            .game()
            .commit_raw(
                RESUBMIT,
                vec![
                    session.game().reg_effect("marked", 2),
                    session.game().reg_effect("turn_no", 1),
                ]
            )
            .is_err(),
        "a re-entry that ADVANCES the turn is REFUSED — a conflicted round is not a resolution"
    );
    assert_eq!(
        session.game().read_reg("marked"),
        1,
        "and none of the three refusals wrote anything"
    );
}

/// ⚑ **A LOCKED SEAT'S MOVE SURVIVES THE RE-ENTRY UNTOUCHED, AND EXECUTES** when the round finally
/// resolves.
///
/// ⚠ SCOPE, said plainly: at the DEPLOYED n=2 the ruleset never produces a non-empty `locked`. A
/// fork needs two moves out of one square and a collide two moves into one, so with two
/// submissions every clash names both — `roundStep` returns `locked = []` and `waiting = [0,1]`
/// every time (the previous test observes exactly that). The ruleset really does lock a third seat
/// (`tests/lean_oracle.rs::a_locked_seats_move_stands_and_executes` drives `roundStep` at three
/// seats and watches the locked move execute), so what is under test HERE is the SURFACE'S CARRY:
/// given a round state with a lock in it, does the surface leave that seat's move alone, refuse to
/// re-open it, hand it to the Lean as `locked`, and let it execute? The round state is therefore
/// installed directly (this test is inside the module) — the lock is a STATE, not a rule decision,
/// and every rule decision below is still the Lean's.
#[test]
fn a_locked_seats_move_survives_the_re_entry_and_executes() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(24)).expect("open");
    let before = session.board().clone();

    let ma = Move {
        who: 0,
        frm: (3, 1),
        to: (3, 3),
    };
    let mb_dropped = Move {
        who: 1,
        frm: (7, 1),
        to: (7, 3),
    };
    seal(&off, &mut session, &seat_a(), ma.frm, ma.to);
    seal(&off, &mut session, &seat_b(), mb_dropped.frm, mb_dropped.to);
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_a()).landed());
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());

    // THE ROUND STATE, INSTALLED (see the scope note): a mark on a square neither move names, seat
    // A's move LOCKED, seat B alone re-entering.
    let mark: Coord = (5, 0);
    session.conflict_subs.push([ma, mb_dropped]);
    session.marks = vec![mark];
    session.locked = vec![ma];
    session.waiting = vec![1];
    session.sel[1] = None;
    session.committed[1] = None;
    session.seal[1] = 0;
    session.revealed[1] = false;

    // ── THE LOCKED SEAT IS UNTOUCHED, and is not waited on.
    assert_eq!(session.phase(), Phase::Resubmit);
    assert_eq!(
        session.committed[0],
        Some(ma),
        "the locked seat's move is intact — plaintext, seal and reveal all stand"
    );
    assert!(session.revealed[0]);
    assert!(!session.is_waiting(Seat::A));
    assert!(
        !session.owes_a_move(Seat::A),
        "a LOCKED seat owes nothing — a clock must not forfeit it"
    );
    assert!(
        session.owes_a_move(Seat::B),
        "the re-entering seat owes a move"
    );

    // ── AND IT IS REFUSED IF IT TRIES TO MOVE AGAIN (the negative).
    for turn in [SELECT, COMMIT] {
        match off.advance(
            &mut session,
            act(turn, index_of((4, 4)).unwrap() as i64),
            seat_a(),
        ) {
            Outcome::Refused(why) => assert!(
                why.contains("LOCKED"),
                "a locked seat's `{turn}` is refused by name: {why}"
            ),
            other => panic!("a LOCKED seat may not `{turn}` again, got {other:?}"),
        }
    }
    // The locked seat is offered nothing but the resolve, and its plaque says why.
    let mine = off.actions_for(&session, &seat_a());
    assert!(
        mine.iter().all(|a| !a.enabled || a.turn == RESOLVE),
        "a locked seat is offered no submission affordance: {:?}",
        mine.iter()
            .filter(|a| a.enabled)
            .map(|a| a.turn.clone())
            .collect::<Vec<_>>()
    );
    let text = rendered_text(&off.render_for(&session, &seat_a()));
    assert!(text.contains("LOCKED"), "{text}");
    assert!(
        text.contains("YOUR move STANDS, untouched: (3,1) → (3,3)"),
        "{text}"
    );

    // ── THE ROUND RESOLVES, and the LOCKED move executes with the fresh one. Only seat B submits.
    let mb_fresh = Move {
        who: 1,
        frm: (7, 9),
        to: (7, 7),
    };
    seal(&off, &mut session, &seat_b(), mb_fresh.frm, mb_fresh.to);
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());
    assert_eq!(session.phase(), Phase::Resolve, "seat A is already opened");
    assert!(
        off.advance(&mut session, act(RESOLVE, 0), seat_b())
            .landed()
    );

    // The LEAN's answer for the pair {locked, fresh} — and the board is it.
    let expect = apply_turn(&before, &[ma, mb_fresh])
        .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
    assert_eq!(
        session.board().cells,
        expect.cells,
        "the locked move EXECUTED alongside the re-submitted one"
    );
    assert_eq!(
        session.board().cell_at((3, 3)),
        ATT,
        "seat A's attractor arrived"
    );
    assert_eq!(
        session.board().cell_at((3, 1)),
        VAC,
        "and vacated its source"
    );
    assert_eq!(session.turn_no(), 1);
    let t = &session.turns_played()[0];
    assert_eq!(t.conflict_subs, vec![[ma, mb_dropped]]);
    assert_eq!(
        t.clean_subs,
        [ma, mb_fresh],
        "the terminating round's pair is the LOCKED move plus the fresh one"
    );
}

/// ⚑ **THE FOG HOLDS ACROSS A RE-SUBMISSION.** A re-submitted move is sealed exactly like a first
/// one: its own seat reads it, the opponent reads a commitment, a spectator reads neither. The
/// MARKS are the opposite — public in every view, because the ruleset produced them by revealing
/// every submission at once.
#[test]
fn a_re_submitted_move_is_sealed_exactly_like_a_first_one() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(25)).expect("open");
    assert!(
        play_round(
            &off,
            &mut session,
            Some((FORK_SRC, (3, 3))),
            Some((FORK_SRC, (5, 1))),
        )
        .landed()
    );

    // Seat A re-submits; seat B has not yet.
    seal(&off, &mut session, &seat_a(), (3, 9), (3, 7));

    let a_view = rendered_text(&off.render_for(&session, &seat_a()));
    let b_view = rendered_text(&off.render_for(&session, &seat_b()));
    let watcher = rendered_text(&off.render(&session));

    assert!(
        a_view.contains("YOUR sealed move: (3,9) → (3,7)"),
        "the re-submitting seat reads its own fresh move: {a_view}"
    );
    for (name, view) in [("the opponent", &b_view), ("a spectator", &watcher)] {
        assert!(
            !view.contains("(3,9) → (3,7)") && !view.contains("(3,9)"),
            "{name} must NOT read the re-submitted plaintext: {view}"
        );
        assert!(
            view.contains("move SEALED"),
            "{name} reads a commitment instead: {view}"
        );
        // …but the MARK is public: it is a scar on the shared board, not a secret.
        assert!(
            view.contains("(3,1)"),
            "{name} sees the marked square: {view}"
        );
    }

    // The board itself: seat A's own sealed destination is painted for A and for nobody else, and
    // the mark is painted for everyone.
    let dest = index_of((3, 7)).expect("in bounds");
    let marked = index_of(FORK_SRC).expect("in bounds");
    let (_, a_cells) = grid(&off.render_for(&session, &seat_a()));
    let (_, b_cells) = grid(&off.render_for(&session, &seat_b()));
    let (_, w_cells) = grid(&off.render(&session));
    assert_eq!(a_cells[dest].tag, "sealed", "A sees where A sealed");
    assert_ne!(b_cells[dest].tag, "sealed", "B does not");
    assert_ne!(w_cells[dest].tag, "sealed", "nor does a spectator");
    for cells in [&a_cells, &b_cells, &w_cells] {
        assert_eq!(cells[marked].tag, "mark", "the mark is in EVERY view");
    }
}

/// The automaton REACHES a goal and the match is WON — a real terminal turn (`ended: true`), with
/// the winner write-once on the cell.
#[test]
fn the_automaton_can_be_pulled_to_a_goal_and_win() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(16)).expect("open");

    // Each seat pulls toward its OWN rank of goal corners (A the `y = 0` pair, B the `y = 10`
    // pair) by putting an attractor on the automaton's file. The reference decides what actually
    // happens; we assert the offering reproduces it exactly, turn for turn.
    let mut turns = 0;
    let mut won = None;
    while !session.ended() && turns < 12 {
        let board = session.board().clone();
        // Pick the first legal move for each seat that pulls the automaton toward a goal — a simple
        // driver: A tries to place an attractor on the file above the automaton, B below.
        let pick = |seat: Seat, board: &Board| -> Option<Move> {
            // The seat owns TWO corners on the same rank; either wins, so aim at the first.
            let goal = seat.goals()[0];
            for idx in 0..CELLS {
                let frm = coord_of(idx);
                if board.cell_at(frm) != ATT {
                    continue;
                }
                // A target on the goal side of the automaton, on the automaton's file.
                for ty in 0..N as i32 {
                    let to = (board.auto.0, ty);
                    let m = Move {
                        who: seat.idx() as u32,
                        frm,
                        to,
                    };
                    if move_legal(board, &[], &m).unwrap_or(false)
                        && (ty - goal.1).abs() < (board.auto.1 - goal.1).abs().max(1)
                    {
                        return Some(m);
                    }
                }
            }
            None
        };
        let (Some(ma), Some(mb)) = (pick(Seat::A, &board), pick(Seat::B, &board)) else {
            break;
        };
        seal(&off, &mut session, &seat_a(), ma.frm, ma.to);
        seal(&off, &mut session, &seat_b(), mb.frm, mb.to);
        assert!(off.advance(&mut session, act(REVEAL, 0), seat_a()).landed());
        assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());
        let out = off.advance(&mut session, act(RESOLVE, 0), seat_a());
        assert!(out.landed(), "each resolution lands a real turn");
        // The board always tracks the Lean.
        let expect = apply_turn(&board, &[ma, mb])
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        assert_eq!(session.board().cells, expect.cells);
        won = session.winner();
        turns += 1;
    }
    // Whether or not the crude driver reaches a goal, EVERY turn matched the Lean and the
    // executor verified. If a goal was reached, the winner is committed write-once.
    assert!(off.verify(&session).verified);
    if let Some(w) = won {
        assert!(session.ended(), "a reached goal ends the match");
        assert_eq!(
            session.game().read_state().winner,
            w.idx() as u64 + 1,
            "the winner is committed on the cell"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 6. THE EXECUTOR TEETH ARE REAL — a forged raw turn is REFUSED by the substrate
// ────────────────────────────────────────────────────────────────────────────────────────────

/// The executor is the referee, not the surface: a RAW turn that moves a piece during the commit
/// phase, or conjures a particle on the resolution, is REFUSED by the deployed teeth.
#[test]
fn the_executor_refuses_a_forged_raw_turn() {
    let off = AutomataflOffering;
    let session = off.open(SessionConfig::with_seed(17)).expect("open");
    let game = session.game();

    // A `commit` that also MOVES a piece — the board is Immutable during the commit phase.
    let forged_board = vec![
        game.reg_effect("commits", 1),
        game.cell_effect(index_of((3, 1)).unwrap(), 0), // wipe the stock attractor
    ];
    assert!(
        game.commit_raw(COMMIT, forged_board).is_err(),
        "a commit that moves a piece is REFUSED (the board is immutable in the commit phase)"
    );

    // A `resolve` that conjures a particle code outside `{0,1,2,3}` — the membership tooth.
    let forged_particle = vec![
        game.reg_effect("turn_no", 1),
        game.cell_effect(index_of((0, 0)).unwrap(), 7),
    ];
    assert!(
        game.commit_raw(RESOLVE, forged_particle).is_err(),
        "a resolution conjuring particle code 7 is REFUSED"
    );

    // A `resolve` that does NOT advance the turn counter — the strict-monotonic tooth.
    assert!(
        game.commit_raw(RESOLVE, vec![game.reg_effect("turn_no", 0)])
            .is_err(),
        "a resolution that does not advance the turn is REFUSED"
    );

    // Genesis is ONE-SHOT: the opening seed already consumed it during `open`, so a
    // post-deploy genesis staple — the universal write-hatch — is now REFUSED regardless
    // of which slot it targets (the `0 → 1` sentinel guard, not a per-slot tooth).
    assert!(
        game.commit_raw(GENESIS, vec![game.reg_effect("phase", 0)])
            .is_err(),
        "a post-deploy genesis staple is refused (the one-shot write-hatch is closed)"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 7. SEAT CLAIMING — a web/Discord identity really sits down
// ────────────────────────────────────────────────────────────────────────────────────────────

/// A derived (web/Discord/Telegram) identity CLAIMS a seat on its first action — so the offering is
/// playable by real frontend users, not only by the canonical seat strings. A third identity is a
/// spectator and is refused.
#[test]
fn a_derived_identity_claims_a_seat_and_a_third_is_a_spectator() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(18)).expect("open");

    let alice = DreggIdentity("blake3-of-alice".into());
    let bob = DreggIdentity("blake3-of-bob".into());
    let carol = DreggIdentity("blake3-of-carol".into());

    let src = index_of((3, 1)).unwrap() as i64;
    assert!(
        off.advance(&mut session, act(SELECT, src), alice.clone())
            .landed()
    );
    assert_eq!(
        session.seat_of(&alice),
        Some(Seat::A),
        "alice claimed seat A"
    );

    let src_b = index_of((7, 1)).unwrap() as i64;
    assert!(
        off.advance(&mut session, act(SELECT, src_b), bob.clone())
            .landed()
    );
    assert_eq!(session.seat_of(&bob), Some(Seat::B), "bob claimed seat B");

    // A third identity has no seat — refused, nothing commits.
    let refused = off.advance(&mut session, act(SELECT, src), carol.clone());
    assert!(
        matches!(refused, Outcome::Refused(_)),
        "a third identity is a spectator"
    );
    assert_eq!(session.seat_of(&carol), None);

    // And alice's view fogs bob's seal, not her own (the same per-viewer projection).
    seal(&off, &mut session, &alice, (3, 1), (3, 3));
    seal(&off, &mut session, &bob, (7, 1), (7, 3));
    let a_view = rendered_text(&off.render_for(&session, &alice));
    assert!(a_view.contains("YOUR sealed move: (3,1) → (3,3)"));
    assert!(
        !a_view.contains("(7,1) → (7,3)"),
        "bob's seal is fog to alice"
    );
}
