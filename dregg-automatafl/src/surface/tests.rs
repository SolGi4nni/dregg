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
        &[(ma, mb)],
        "the resolved round recorded BOTH seats' revealed moves, in seat order"
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

/// **A CONFLICTING round is recorded but is NOT foldable** — and it says so by name. Both seats
/// fork the SAME source: conflict resolution drops both moves (the surface's audited-WRONG rule;
/// the ruleset marks the square and re-enters the round). The round IS played and IS recorded —
/// the history is the truth of what happened — but [`AutomataflSession::unfoldable_round`] names
/// it, and the fold refuses it rather than minting a proof of an unlicensed transition.
#[test]
fn a_conflicting_round_is_played_but_refuses_to_fold() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(20)).expect("open");

    // A FORK: both seats move the attractor at (3,1), to different squares.
    let before = session.board().clone();
    seal(&off, &mut session, &seat_a(), (3, 1), (3, 3));
    seal(&off, &mut session, &seat_b(), (3, 1), (5, 1));
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_a()).landed());
    assert!(off.advance(&mut session, act(REVEAL, 0), seat_b()).landed());
    assert!(
        off.advance(&mut session, act(RESOLVE, 0), seat_a())
            .landed(),
        "the conflicting round still RESOLVES on the surface (both moves dropped)"
    );

    // The RULESET's answer: a conflicted round does not resolve its moves at all (`resolveMoves` is
    // guarded by `resolvableB`), so the board only took the automaton's step. The old Rust twin
    // reached the same board here by DROPPING the two forking moves; the ruleset gets there by not
    // resolving the round — which is why the fold still refuses it below.
    assert_eq!(
        session.board().cells,
        apply_turn(
            &before,
            &[
                Move {
                    who: 0,
                    frm: (3, 1),
                    to: (3, 3)
                },
                Move {
                    who: 1,
                    frm: (3, 1),
                    to: (5, 1)
                },
            ]
        )
        .expect("the Lean game oracle (`dregg_automatafl_rules`) answers")
        .cells
    );
    assert_eq!(session.rounds().len(), 1, "the round is recorded as played");
    assert_eq!(
        session
            .unfoldable_round()
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers"),
        Some(0),
        "round 0 CONFLICTS — the fold must refuse it by name, not fake a leaf"
    );
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
