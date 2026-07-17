//! Tests for [`AutomataflOffering`], DRIVEN — the CoordGrid board, the rook-line legal-move
//! highlighting (non-vacuously: an illegal target is NOT highlighted), the simultaneous
//! commit → reveal → resolve shape, the per-viewer sealed-move fog, and the REAL executor turns
//! (a legal play lands a receipt; an illegal one is refused and commits nothing).

use super::*;
use crate::game::{GENESIS, coord_of, index_of, opening_board};
use crate::reference::{ATT, apply_turn};
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

/// The board renders as a valid `CoordGrid`: 5 columns, 25 cells, the particles as glyphs, the
/// automaton cell MARKED (`@`, tag `accent`, in the highlight-set).
#[test]
fn the_board_renders_as_a_coordgrid() {
    let off = AutomataflOffering;
    let session = off.open(SessionConfig::with_seed(11)).expect("open");
    let (cols, cells) = grid(&off.render(&session));

    assert_eq!(cols, N, "five columns");
    assert_eq!(cells.len(), CELLS, "one cell per board square");

    // The opening: four attractors, two repulsors, one automaton, the rest vacuum/goal squares.
    assert_eq!(cells.iter().filter(|c| c.glyph == "A").count(), 4);
    assert_eq!(cells.iter().filter(|c| c.glyph == "R").count(), 2);
    assert_eq!(cells.iter().filter(|c| c.glyph == "@").count(), 1);

    // The automaton square (2,2) — marked and highlighted.
    let auto_idx = index_of((2, 2)).unwrap();
    assert_eq!(cells[auto_idx].glyph, "@");
    assert_eq!(cells[auto_idx].tag, "accent");
    assert!(cells[auto_idx].highlight, "the automaton cell is marked");

    // The grid AGREES with the reference board, square by square.
    let board = opening_board();
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

    // Seat A selects the attractor at (1,1) — a REAL turn.
    let src = (1, 1);
    let src_idx = index_of(src).unwrap();
    assert!(
        off.advance(&mut session, act(SELECT, src_idx as i64), seat_a())
            .landed(),
        "the select lands a real turn"
    );

    let (_, cells) = grid(&off.render_for(&session, &seat_a()));

    // The reference's own legal set (the tooth the highlight must mirror).
    let expected: Vec<usize> = (0..CELLS)
        .filter(|&i| {
            move_valid(
                session.board(),
                &Move {
                    who: 0,
                    frm: src,
                    to: coord_of(i),
                },
            )
        })
        .collect();
    // Rook line of (1,1) on a 5×5: row y=1 minus (1,1) → 4; column x=1 minus (1,1) → 4. The
    // automaton is at (2,2) — not on this line, so nothing is excluded here.
    assert_eq!(expected.len(), 8, "the rook line of (1,1) is eight squares");

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
    let auto_idx = index_of((2, 2)).unwrap();
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

    // Four named illegal targets, explicitly: (3,3) is the diagonal; (2,3) / (4,4) / (0,0) share
    // neither row nor column with (1,1) — off the rook line, so out of the highlight-set.
    for bad in [(2, 3), (3, 3), (0, 0), (4, 4)] {
        let i = index_of(bad).unwrap();
        assert!(
            !cells[i].highlight,
            "{bad:?} is not on (1,1)'s rook line — no highlight"
        );
    }

    // The automaton square is never a legal target — even on a rook line through it.
    assert!(
        !move_valid(
            session.board(),
            &Move {
                who: 0,
                frm: (0, 2),
                to: (2, 2)
            }
        ),
        "the automaton's square is never a move target"
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

    // Select (1,1) — a real turn.
    let src_idx = index_of((1, 1)).unwrap() as i64;
    assert!(
        off.advance(&mut session, act(SELECT, src_idx), seat_a())
            .landed()
    );
    let commits_before = session.game().read_reg("commits");

    // A DIAGONAL destination (3,3): not a rook line — refused.
    let diag = index_of((3, 3)).unwrap() as i64;
    let refused = off.advance(&mut session, act(COMMIT, diag), seat_a());
    assert!(
        matches!(refused, Outcome::Refused(_)),
        "a diagonal move is refused"
    );

    // The AUTOMATON's square (2,2) — on (1,1)'s… no: (2,2) is off (1,1)'s line anyway. Use a
    // source on the automaton's row: select the repulsor at (0,2), then seal onto (2,2).
    assert!(
        off.advance(
            &mut session,
            act(SELECT, index_of((0, 2)).unwrap() as i64),
            seat_a()
        )
        .landed()
    );
    let onto_auto = index_of((2, 2)).unwrap() as i64;
    assert!(
        matches!(
            off.advance(&mut session, act(COMMIT, onto_auto), seat_a()),
            Outcome::Refused(_)
        ),
        "a move onto the automaton is refused"
    );

    // An OFF-BOARD square is refused.
    assert!(
        matches!(
            off.advance(&mut session, act(COMMIT, 99), seat_a()),
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

    // A LEGAL seal from the same selection lands a real turn: (0,2) → (0,4), straight up the file.
    let clean = index_of((0, 4)).unwrap() as i64;
    let landed = off.advance(&mut session, act(COMMIT, clean), seat_a());
    assert!(landed.landed(), "the legal seal lands a real receipt");
    assert_eq!(
        session.game().read_reg("commits"),
        commits_before + 1,
        "the committed seal advanced the executor's commit counter"
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

    seal(&off, &mut session, &seat_a(), (1, 1), (1, 4));
    seal(&off, &mut session, &seat_b(), (3, 3), (3, 0));

    let a_view = rendered_text(&off.render_for(&session, &seat_a()));
    let b_view = rendered_text(&off.render_for(&session, &seat_b()));
    let public = rendered_text(&off.render(&session));

    // A sees their own move in full…
    assert!(
        a_view.contains("YOUR sealed move: (1,1) → (1,4)"),
        "A reads their own sealed move\n{a_view}"
    );
    // …and NOT B's (fog: only the commitment).
    assert!(
        !a_view.contains("(3,3) → (3,0)"),
        "B's sealed move is FOG to A\n{a_view}"
    );
    assert!(
        a_view.contains("move SEALED"),
        "A sees the opponent's commitment, not their move"
    );

    // Symmetrically for B.
    assert!(b_view.contains("YOUR sealed move: (3,3) → (3,0)"));
    assert!(
        !b_view.contains("(1,1) → (1,4)"),
        "A's sealed move is FOG to B\n{b_view}"
    );

    // The PUBLIC surface fogs BOTH.
    assert!(!public.contains("(1,1) → (1,4)") && !public.contains("(3,3) → (3,0)"));
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
        after.contains("revealed: (1,1) → (1,4)") && after.contains("revealed: (3,3) → (3,0)"),
        "the reveal opens both moves\n{after}"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────
// 5. A FULL n=2 TURN — commit → reveal → resolve, against the reference `apply_turn`
// ────────────────────────────────────────────────────────────────────────────────────────────

/// A full simultaneous turn drives through the Offering, and the resolved board is EXACTLY
/// `apply_turn(old, [move_a, move_b])` — the reference oracle the AIR pins — on both the session's
/// board AND the executor's COMMITTED cell state.
#[test]
fn a_full_turn_resolves_exactly_as_the_reference() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(15)).expect("open");

    let before = session.board().clone();
    let ma = Move {
        who: 0,
        frm: (1, 1),
        to: (1, 4),
    };
    let mb = Move {
        who: 1,
        frm: (3, 3),
        to: (3, 0),
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

    // THE ORACLE: the resolved board is exactly the reference transition.
    let expect = apply_turn(&before, &[ma, mb]);
    assert_eq!(
        session.board().cells,
        expect.cells,
        "the board matches the reference apply_turn"
    );
    assert_eq!(
        session.board().auto,
        expect.auto,
        "the automaton stepped as the reference says"
    );

    // …and the EXECUTOR's committed cell state agrees, square for square (translation validation).
    let committed = session.game().read_state();
    assert_eq!(
        committed.cells, expect.cells,
        "the committed board == the reference"
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
}

/// The automaton REACHES a goal and the match is WON — a real terminal turn (`ended: true`), with
/// the winner write-once on the cell.
#[test]
fn the_automaton_can_be_pulled_to_a_goal_and_win() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(16)).expect("open");

    // Both seats pull the SAME lever — A moves the attractor at (1,1) onto the centre file north of
    // the automaton, B moves the attractor at (3,3) out of the way. The reference decides what
    // happens; we assert the offering reproduces it exactly, and drive to a decided match.
    let mut turns = 0;
    let mut won = None;
    while !session.ended() && turns < 12 {
        let board = session.board().clone();
        // Pick the first legal move for each seat that pulls the automaton toward a goal — a simple
        // driver: A tries to place an attractor on the file above the automaton, B below.
        let pick = |seat: Seat, board: &Board| -> Option<Move> {
            let goal = seat.goal();
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
                    if move_valid(board, &m)
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
        // The board always tracks the reference.
        let expect = apply_turn(&board, &[ma, mb]);
        assert_eq!(session.board().cells, expect.cells);
        won = session.winner();
        turns += 1;
    }
    // Whether or not the crude driver reaches a goal, EVERY turn matched the reference and the
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
        game.cell_effect(index_of((1, 1)).unwrap(), 0), // wipe the attractor
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

    let src = index_of((1, 1)).unwrap() as i64;
    assert!(
        off.advance(&mut session, act(SELECT, src), alice.clone())
            .landed()
    );
    assert_eq!(
        session.seat_of(&alice),
        Some(Seat::A),
        "alice claimed seat A"
    );

    let src_b = index_of((3, 3)).unwrap() as i64;
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
    seal(&off, &mut session, &alice, (1, 1), (1, 4));
    seal(&off, &mut session, &bob, (3, 3), (3, 0));
    let a_view = rendered_text(&off.render_for(&session, &alice));
    assert!(a_view.contains("YOUR sealed move: (1,1) → (1,4)"));
    assert!(
        !a_view.contains("(3,3) → (3,0)"),
        "bob's seal is fog to alice"
    );
}
