//! # ⚑ THE PLAY EXPERIENCE, DRIVEN — is this a game worth sitting down to?
//!
//! Every other test in this crate asks whether automatafl is CORRECT. This one asks whether it is
//! PLAYABLE: it drives real turns through the offering and reads the PROSE projection
//! ([`deos_view::text::render_text`] — what a Telegram / Discord / WeChat player is actually served,
//! and the projection a web-only feature silently fails), then pins the facts the surface's teaching
//! depends on.
//!
//! Run with `--nocapture` to read a match out loud; that is as much the point of this file as the
//! assertions are. Three findings are load-bearing, and measured here rather than remembered:
//!
//! 1. **The opening offers a seat 720 legal moves and 20 that move the automaton at all** — a board
//!    that highlights legality alone is offering a set that is 97% noise. This is why the surface
//!    paints the automaton's four SIGHTLINES.
//! 2. **Nothing off the automaton's rank and file can change what it does.** The surface tells the
//!    player exactly that, so it is checked from both sides — here on the moves that DO matter, and
//!    in `surface::tests::a_move_off_every_sightline_cannot_change_the_read` on the whole
//!    off-sightline set.
//! 3. **The ruleset resolves a ONE-SEAT round.** `roundStep` with `waiting = [0]` and a single
//!    submission resolves cleanly and walks the automaton — which is the entire rules-side cost of a
//!    solo puzzle mode.

use deos_view::text::render_text;
use deos_view::{CoordCell, ViewNode};
use dregg_automatafl::board::{ATT, Board, Coord, Move, REP};
use dregg_automatafl::game::{CELLS, COMMIT, RESOLVE, REVEAL, SELECT, coord_of, goals, index_of};
use dregg_automatafl::rules;
use dregg_automatafl::surface::{AutomataflOffering, AutomataflSession, Seat};
use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig, Surface};

fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}
fn seat_a() -> DreggIdentity {
    AutomataflOffering::seat_identity(Seat::A)
}
fn seat_b() -> DreggIdentity {
    AutomataflOffering::seat_identity(Seat::B)
}

fn seal(
    off: &AutomataflOffering,
    s: &mut AutomataflSession,
    who: &DreggIdentity,
    frm: Coord,
    to: Coord,
) -> bool {
    let src = index_of(frm).expect("in bounds") as i64;
    let dst = index_of(to).expect("in bounds") as i64;
    off.advance(s, act(SELECT, src), who.clone()).landed()
        && off.advance(s, act(COMMIT, dst), who.clone()).landed()
}

/// The board grid of a surface.
fn grid(surface: &Surface) -> Vec<CoordCell> {
    fn find(n: &ViewNode) -> Option<Vec<CoordCell>> {
        match n {
            ViewNode::CoordGrid { cells, .. } => Some(cells.clone()),
            ViewNode::Section { children: cs, .. } | ViewNode::VStack(cs) | ViewNode::Row(cs) => {
                cs.iter().find_map(find)
            }
            _ => None,
        }
    }
    find(surface.view()).expect("the surface paints a board")
}

/// The prose a viewer is served — printed AND returned.
fn read_out_loud(
    off: &AutomataflOffering,
    s: &AutomataflSession,
    label: &str,
    who: Option<&DreggIdentity>,
) -> String {
    let surface = match who {
        Some(w) => off.render_for(s, w),
        None => off.render(s),
    };
    let text = render_text(surface.view());
    println!("\n╔══════ {label} ══════");
    for line in text.lines() {
        println!("║ {line}");
    }
    println!("╚═══════════════════════════════════");
    text
}

/// Every legal move on `b` for seat `who` — asked of the LEAN, never enumerated by a Rust rule.
fn all_legal(b: &Board, who: u32) -> Vec<Move> {
    let mut out = Vec::new();
    for i in 0..CELLS {
        let frm = coord_of(i);
        let p = b.cell_at(frm);
        if p != REP && p != ATT {
            continue;
        }
        for to in rules::legal_targets(b, &[], who, frm).unwrap_or_default() {
            out.push(Move { who, frm, to });
        }
    }
    out
}

/// Where the automaton ends up if `ms` is the whole round.
fn auto_after(b: &Board, ms: &[Move]) -> Coord {
    rules::apply_turn(b, ms).expect("the Lean answers").auto
}

/// ⚑ **THE FIRST-TURN AGENCY CENSUS** — how much of the opening's offered choice is real?
///
/// **720 legal moves, 20 that move the automaton.** A player choosing off the legal-move highlight
/// alone has a 1-in-36 chance of doing anything at all, and the surface used to give them nothing
/// else to go on. This is the measurement the sightline painting exists to answer.
#[test]
fn the_opening_offers_720_moves_and_20_that_matter() {
    let off = AutomataflOffering;
    let session = off.open(SessionConfig::with_seed(1)).expect("open");
    let board = session.board().clone();

    let base = rules::sense(&board).expect("the oracle senses the opening");
    println!(
        "opening: automaton {:?}, offset {:?} — it HOLDS, boxed by four repulsors at distance 4",
        board.auto, base.offset
    );
    assert_eq!(base.offset, (0, 0), "the stock opening is perfectly boxed");

    // The sightline squares the surface PAINTS, read back off the rendered board.
    let cells = grid(&off.render(&session));
    let painted: Vec<Coord> = (0..CELLS)
        .filter(|i| cells[*i].glyph == "─" || cells[*i].glyph == "│")
        .map(coord_of)
        .collect();

    let legal = all_legal(&board, 0);
    let idle = auto_after(&board, &[]);
    let effective: Vec<Move> = legal
        .iter()
        .copied()
        .filter(|m| auto_after(&board, std::slice::from_ref(m)) != idle)
        .collect();

    println!(
        "seat A: {} legal moves · {} move the automaton ({:.1}% of the offered set) · {} painted \
         sightline squares",
        legal.len(),
        effective.len(),
        100.0 * effective.len() as f64 / legal.len() as f64,
        painted.len()
    );
    for m in effective.iter().take(6) {
        println!(
            "  ({},{}) → ({},{})  ⇒ automaton {:?} → {:?}",
            m.frm.0,
            m.frm.1,
            m.to.0,
            m.to.1,
            board.auto,
            auto_after(&board, std::slice::from_ref(m))
        );
    }

    assert_eq!(legal.len(), 720, "the opening's offered set");
    assert_eq!(effective.len(), 20, "and the part of it that does anything");
    assert!(
        !painted.is_empty(),
        "the surface paints the arms — that is the whole answer to the ratio above"
    );
    // The teaching claim from the weak side: every move that matters touches the automaton's own
    // rank or file. (The strong side — that nothing OFF the arms can matter — is
    // `surface::tests::a_move_off_every_sightline_cannot_change_the_read`.)
    for m in &effective {
        let on_axis = |c: Coord| c != board.auto && (c.0 == board.auto.0 || c.1 == board.auto.1);
        assert!(
            on_axis(m.frm) || on_axis(m.to),
            "({},{}) → ({},{}) moved the automaton from off its rank and file entirely",
            m.frm.0,
            m.frm.1,
            m.to.0,
            m.to.1
        );
    }
}

/// ⚑ **THE FIRST SCREEN ANSWERS THE FOUR QUESTIONS** a stranger arrives with: who am I, what do I
/// do, what does the automaton answer to, and what happens if nobody ever reaches a corner.
#[test]
fn the_first_screen_answers_a_strangers_four_questions() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(2)).expect("open");
    let text = read_out_loud(&off, &session, "TURN 0 · seat A", Some(&seat_a()));

    assert!(text.contains("You hold seat A"), "WHO AM I");
    assert!(text.contains("YOUR MOVE."), "WHAT DO I DO");
    assert!(
        text.contains("WHAT IT CAN SEE") && text.contains("a repulsor 4 squares to its left"),
        "WHAT DOES THE AUTOMATON ANSWER TO — in the LEAN's own ray distances"
    );
    assert!(
        text.contains('─') && text.contains('│'),
        "and the arms reach the PROSE board, not only the styled one"
    );
    assert!(
        text.contains("ON THE CLOCK") && text.contains("adjudicated"),
        "WHAT IF NOBODY WINS — the adjudication used to be invisible until turn 64"
    );

    // Picking a piece up does not displace any of it.
    assert!(
        off.advance(
            &mut session,
            act(SELECT, index_of((1, 4)).unwrap() as i64),
            seat_a()
        )
        .landed()
    );
    let picked = read_out_loud(
        &off,
        &session,
        "TURN 0 · seat A, attractor (1,4) picked up",
        Some(&seat_a()),
    );
    assert!(picked.contains("WHAT IT CAN SEE"));
}

/// ⚑ **A REAL MATCH, READ OUT LOUD** — two greedy seats, and the two things that actually happen at
/// this table: they reach for the SAME shared piece, and the automaton answers a board neither of
/// them controls alone. Every screen is printed; the assertions pin that the intent → consequence
/// loop is present and that it stays inside its own seat.
#[test]
fn a_played_match_shows_intent_then_consequence() {
    let off = AutomataflOffering;
    let mut session = off.open(SessionConfig::with_seed(3)).expect("open");

    // Each seat takes the move that — if it were the only one to land — drags the automaton nearest
    // one of its OWN corners. Two seats reasoning alike over SHARED pieces is how a clash gets made.
    let plan = |b: &Board, seat: Seat| -> Option<Move> {
        let gs = seat.goals();
        let d = |c: Coord| {
            gs.iter()
                .map(|g| (g.0 - c.0).abs() + (g.1 - c.1).abs())
                .min()
                .unwrap_or(0)
        };
        let mut best: Option<(i32, Move)> = None;
        for m in all_legal(b, seat.idx() as u32) {
            let score = d(auto_after(b, std::slice::from_ref(&m)));
            if best.as_ref().map(|(s, _)| score < *s).unwrap_or(true) {
                best = Some((score, m));
            }
        }
        best.map(|(_, m)| m)
    };

    let mut saw_forecast = false;
    let mut saw_clash = false;
    for round in 0..6 {
        if session.ended() {
            break;
        }
        let board = session.board().clone();
        // Only the seats the ruleset is WAITING on owe a move — a locked seat's move stands.
        let owed: Vec<Seat> = [Seat::A, Seat::B]
            .into_iter()
            .filter(|s| session.is_waiting(*s))
            .collect();
        let mut ok = true;
        for s in &owed {
            let Some(m) = plan(&board, *s) else {
                ok = false;
                break;
            };
            println!(
                "\n### round {round}: seat {} plays ({},{}) → ({},{})",
                s.label(),
                m.frm.0,
                m.frm.1,
                m.to.0,
                m.to.1
            );
            let who = if *s == Seat::A { seat_a() } else { seat_b() };
            if !seal(&off, &mut session, &who, m.frm, m.to) {
                ok = false;
                break;
            }
            if *s == Seat::A {
                let a_view = read_out_loud(
                    &off,
                    &session,
                    &format!("round {round} · seat A has SEALED — its OWN view"),
                    Some(&seat_a()),
                );
                saw_forecast |= a_view.contains("Your move alone would")
                    || a_view.contains("IF YOURS IS THE ONLY MOVE")
                    || a_view.contains("CAREFUL");
                let b_view = read_out_loud(
                    &off,
                    &session,
                    &format!("round {round} · seat B's view of the SAME instant"),
                    Some(&seat_b()),
                );
                assert!(
                    !b_view.contains("Your move alone would"),
                    "the forecast is A's alone — it is derived from A's sealed move"
                );
            }
        }
        if !ok {
            println!("(the greedy driver ran out of plans)");
            break;
        }
        for who in [seat_a(), seat_b()] {
            off.advance(&mut session, act(REVEAL, 0), who);
        }
        assert!(
            off.advance(&mut session, act(RESOLVE, 0), seat_a())
                .landed(),
            "every resolution is a real executor turn"
        );
        let after = read_out_loud(
            &off,
            &session,
            &format!("after round {round} · seat A"),
            Some(&seat_a()),
        );
        saw_clash |= after.contains("WHAT COLLIDED");
    }

    let end = read_out_loud(&off, &session, "the table as it stands", Some(&seat_a()));
    println!(
        "\nturn_no={} ended={} winner={:?} automaton={:?} standing={:?}",
        session.turn_no(),
        session.ended(),
        session.winner().map(|w| w.label()),
        session.board().auto,
        session.contest()
    );
    assert!(
        off.verify(&session).verified,
        "the committed match verifies"
    );
    assert!(
        saw_forecast,
        "a sealing seat is told what its own move would do"
    );
    assert!(
        saw_clash,
        "two seats reasoning alike over shared pieces clash, and the plaque names the collision"
    );
    assert!(end.contains("ON THE CLOCK"), "the stakes stay on screen");
}

/// ⚑ **PUZZLE-MODE FEASIBILITY, MEASURED ON THE RULES SIDE.** `roundStep` accepts `waiting = [0]`
/// with a single submission: it resolves cleanly (a lone seat cannot clash with itself), the
/// automaton steps, and `winOnEntry` still fires. So a solo "walk the automaton to your own corner"
/// mode needs NO new Lean verb and no new cell tooth — the remaining cost is the surface's two-seat
/// assumptions, and this test is the evidence for that estimate.
#[test]
fn the_ruleset_resolves_a_one_seat_round() {
    let off = AutomataflOffering;
    let session = off.open(SessionConfig::with_seed(6)).expect("open");
    let mut board = session.board().clone();
    let gs = goals().expect("goals");
    let corners = Seat::A.goals();
    let dist = |b: &Board| {
        corners
            .iter()
            .map(|g| (g.0 - b.auto.0).abs() + (g.1 - b.auto.1).abs())
            .min()
            .unwrap_or(0)
    };

    let start = dist(&board);
    let mut resolved = 0usize;
    for _ in 0..6 {
        let mut best: Option<(i32, Move)> = None;
        for m in all_legal(&board, 0) {
            let after = rules::apply_turn(&board, std::slice::from_ref(&m)).expect("turn");
            let score = dist(&after);
            if best.as_ref().map(|(s, _)| score < *s).unwrap_or(true) {
                best = Some((score, m));
            }
        }
        let Some((_, m)) = best else { break };
        match rules::round(&board, gs, &[], &[], &[0], std::slice::from_ref(&m))
            .expect("the Lean answers a ONE-SEAT round")
        {
            rules::RoundOutcome::Resolved { board: next, win } => {
                println!(
                    "solo ({},{})→({},{}): automaton {:?} → {:?} · {} from seat A's corner · win \
                     {win:?}",
                    m.frm.0,
                    m.frm.1,
                    m.to.0,
                    m.to.1,
                    board.auto,
                    next.auto,
                    dist(&next)
                );
                board = next;
                resolved += 1;
                if win.is_some() {
                    break;
                }
            }
            rules::RoundOutcome::Again { marks, .. } => {
                panic!("a lone seat clashed with itself, marking {marks:?}")
            }
        }
    }
    assert_eq!(resolved, 6, "every one-seat round resolved");
    assert!(
        dist(&board) < start,
        "and a solo player can genuinely walk the automaton ({start} → {})",
        dist(&board)
    );
}
