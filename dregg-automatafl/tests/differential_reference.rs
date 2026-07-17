//! **The DIFFERENTIAL test vs the real automatafl reference engine.**
//!
//! The dregg reference oracle ([`dregg_automatafl::reference`]) is the AIR's
//! refinement target — the off-circuit `apply_turn` the in-circuit AIR re-checks.
//! This battery drives the ACTUAL automatafl engine (`~/dev/automatafl/logic`, the
//! `automatafl-logic` crate) move-for-move on the REAL 11×11 two-player board and
//! asserts the two engines agree: same opening, same board rewrite, same Automaton
//! step, same win. It is a genuine differential (two independent implementations),
//! not a self-comparison against a re-implementation.
//!
//! SCOPE: two-player only (`m = 2`), `use_column_rule = true`, and the modes the
//! dregg single-round resolution mirrors: [`MergeResolutionMode::DetectAndConflict`]
//! (fork/collision are dropped, exactly the dregg `conflict_resolve`) +
//! [`CycleBehaviorMode::RotatePieces`] (irrelevant at m=2 — only 2-cycles arise, and
//! those always stay). No SCC / merge-mode / >2-player surface is exercised.

use automatafl_logic as o1;

use dregg_automatafl::reference::{
    self as dref, Board as DBoard, GOAL_CORNERS_2P, Move as DMove, N11, apply_turn, automaton_step,
};

// ---------------------------------------------------------------------------
// A tiny deterministic PRNG (SplitMix64) — no external `rand` dependency, so the
// battery is fully hermetic and reproducible.
// ---------------------------------------------------------------------------
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_add(0x9E37_79B9_7F4A_7C15))
    }
    fn next_u64(&mut self) -> u64 {
        // SplitMix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

// ---------------------------------------------------------------------------
// Conversions between the automatafl world and the dregg reference world.
// ---------------------------------------------------------------------------
fn particle_code(p: o1::Particle) -> u8 {
    match p {
        o1::Particle::Vacuum => dref::VAC,
        o1::Particle::Repulsor => dref::REP,
        o1::Particle::Attractor => dref::ATT,
        o1::Particle::Automaton => dref::AUTO,
    }
}

/// Snapshot an automatafl board as the equivalent dregg reference [`DBoard`].
fn to_dregg(board: &o1::Board) -> DBoard {
    let n = board.size.x as usize;
    assert_eq!(n, board.size.y as usize, "square board");
    let mut cells = vec![dref::VAC; n * n];
    for y in 0..n {
        for x in 0..n {
            // automatafl indexes particles[[y, x]] (row-major, y is the row).
            cells[y * n + x] = particle_code(board.particles[[y, x]].what);
        }
    }
    DBoard {
        n,
        cells,
        auto: (
            board.automaton_location.x as i32,
            board.automaton_location.y as i32,
        ),
        col_rule: true,
    }
}

/// Set the standard two-player goals on an automatafl `Game` (mirrors [`GOAL_CORNERS_2P`]).
/// Pushes into the public `goals` field so we never have to name the `SmallVec` type
/// (smallvec is only a transitive dependency here).
fn set_goals(game: &mut o1::Game) {
    game.goals.clear();
    for &((x, y), who) in GOAL_CORNERS_2P.iter() {
        game.goals.push((
            o1::Coord {
                x: x as u8,
                y: y as u8,
            },
            o1::Pid(who as u8),
        ));
    }
}

fn new_stock_game() -> o1::Game {
    let mut g = o1::Game::new(
        o1::Board::stock_two_player(),
        2,
        true,
        o1::MergeResolutionMode::DetectAndConflict,
        o1::CycleBehaviorMode::RotatePieces,
    );
    set_goals(&mut g);
    g
}

// ---------------------------------------------------------------------------
// Random LEGAL two-player move generation, played against the LIVE automatafl board.
// A legal move (per automatafl `propose_move`): both endpoints in-bounds, neither the
// Automaton, source != destination, rook-aligned. The source need not carry a
// piece (vacuum-source flow-through is legal automatafl).
// ---------------------------------------------------------------------------
fn random_legal_move(rng: &mut Rng, board: &o1::Board, who: u8) -> o1::Move {
    let n = board.size.x as usize;
    loop {
        let fx = rng.below(n);
        let fy = rng.below(n);
        let from = o1::Coord {
            x: fx as u8,
            y: fy as u8,
        };
        if board.is_automaton(from) {
            continue;
        }
        // Pick an axis and a distinct in-bounds destination along it.
        let horizontal = rng.next_u64() & 1 == 0;
        let to = if horizontal {
            let mut tx = rng.below(n);
            if tx == fx {
                tx = (tx + 1) % n;
            }
            o1::Coord {
                x: tx as u8,
                y: fy as u8,
            }
        } else {
            let mut ty = rng.below(n);
            if ty == fy {
                ty = (ty + 1) % n;
            }
            o1::Coord {
                x: fx as u8,
                y: ty as u8,
            }
        };
        if board.is_automaton(to) {
            continue;
        }
        // from != to guaranteed by the axis fix-up above.
        return o1::Move {
            who: o1::Pid(who),
            from,
            to,
        };
    }
}

fn to_dmove(m: &o1::Move) -> DMove {
    DMove {
        who: m.who.0 as u32,
        frm: (m.from.x as i32, m.from.y as i32),
        to: (m.to.x as i32, m.to.y as i32),
    }
}

/// Would the dregg oracle keep BOTH moves (no fork / no destination-collision)?
/// The non-conflict subset is where the interactive automatafl conflict pause and the
/// dregg single-round drop coincide, so a full board-for-board comparison is valid.
fn non_conflicting(old: &DBoard, a: &DMove, b: &DMove) -> bool {
    let valid: Vec<DMove> = [*a, *b]
        .into_iter()
        .filter(|m| dref::move_valid(old, m))
        .collect();
    valid.len() == 2 && dref::conflict_resolve(old, &valid).len() == 2
}

fn grid(b: &DBoard) -> String {
    let mut s = String::new();
    for y in 0..b.n {
        for x in 0..b.n {
            let c = b.cells[y * b.n + x];
            s.push(match c {
                0 => '.',
                1 => 'r',
                2 => 'a',
                3 => 'D',
                _ => '?',
            });
        }
        s.push('\n');
    }
    s
}

fn dump_divergence(
    seed: u64,
    turn: usize,
    old: &DBoard,
    a: &DMove,
    b: &DMove,
    o1_next: &DBoard,
    dregg_next: &DBoard,
) -> ! {
    let diffs: Vec<usize> = (0..old.cells.len())
        .filter(|&i| o1_next.cells[i] != dregg_next.cells[i])
        .collect();
    panic!(
        "DIVERGENCE seed {seed} turn {turn}\n\
         move A = {a:?}\n move B = {b:?}\n auto_before = {:?}\n\
         --- OLD ---\n{}\n--- automatafl NEXT (auto {:?}) ---\n{}\n--- dregg NEXT (auto {:?}) ---\n{}\n\
         differing indices = {diffs:?}",
        old.auto,
        grid(old),
        o1_next.auto,
        grid(o1_next),
        dregg_next.auto,
        grid(dregg_next),
    );
}

#[allow(dead_code)]
fn boards_agree(o1_board: &o1::Board, dboard: &DBoard, ctx: &str) {
    let converted = to_dregg(o1_board);
    assert_eq!(
        converted.cells, dboard.cells,
        "{ctx}: board cells diverge\n automatafl={:?}\n dregg ={:?}",
        converted.cells, dboard.cells
    );
    assert_eq!(
        converted.auto, dboard.auto,
        "{ctx}: automaton location diverges"
    );
}

// ===========================================================================
// (1) The stock opening agrees, byte for byte.
// ===========================================================================
#[test]
fn stock_opening_matches_automatafl() {
    let o1_board = o1::Board::stock_two_player();
    let dregg = dref::stock_two_player();
    assert_eq!(dregg.n, N11);
    assert_eq!(dregg.auto, (5, 5));
    boards_agree(&o1_board, &dregg, "stock opening");
}

// ===========================================================================
// (2) Full-turn differential across many random legal two-player turns, played as
//     real multi-turn games on the live 11×11 board. Board rewrite AND the
//     Automaton step AND the win check must agree every turn.
// ===========================================================================
#[test]
fn full_turn_differential_11x11_two_player() {
    const GAMES: u64 = 120;
    const MAX_TURNS: usize = 40;
    let mut total_turns = 0usize;
    let mut chain_or_step = 0usize; // turns where the automaton moved or a chain formed

    for seed in 0..GAMES {
        let mut rng = Rng::new(0xA0F1 ^ (seed.wrapping_mul(0x100000001B3)));
        let mut game = new_stock_game();

        for _turn in 0..MAX_TURNS {
            if game.winner.is_some() {
                break;
            }
            // The dregg `old` is the current live automatafl board.
            let old = to_dregg(&game.board);

            // Draw a non-conflicting legal move pair (regenerate on conflict; the
            // conflicting case is checked separately in `conflict_detection_*`).
            let mut a;
            let mut b;
            let mut tries = 0;
            loop {
                a = random_legal_move(&mut rng, &game.board, 0);
                b = random_legal_move(&mut rng, &game.board, 1);
                let (da, db) = (to_dmove(&a), to_dmove(&b));
                if non_conflicting(&old, &da, &db) {
                    break;
                }
                tries += 1;
                if tries > 64 {
                    break; // give up this turn; extremely unlikely
                }
            }
            let (da, db) = (to_dmove(&a), to_dmove(&b));
            if !non_conflicting(&old, &da, &db) {
                continue;
            }

            // The dregg reference transition.
            let auto_before = old.auto;
            let dregg_next = apply_turn(&old, &[da, db]);
            if dregg_next.auto != auto_before {
                chain_or_step += 1;
            }

            // Drive the SAME two moves through the automatafl engine.
            let f0 = game.propose_move(a);
            assert!(
                matches!(f0, o1::ProposeFeedback::Accepted),
                "automatafl rejected legal move A: {f0:?}"
            );
            let f1 = game.propose_move(b);
            assert!(
                matches!(f1, o1::ProposeFeedback::AcceptedAndReady),
                "automatafl did not become ready after move B: {f1:?}"
            );
            match game.try_complete_round() {
                o1::CompleteRoundFeedback::CompletedMoves(_) => {}
                other => panic!(
                    "expected CompletedMoves for a non-conflicting pair, got {other:?}\n a={a:?} b={b:?}"
                ),
            }

            // Board + automaton must agree move-for-move.
            let converted = to_dregg(&game.board);
            if converted.cells != dregg_next.cells || converted.auto != dregg_next.auto {
                dump_divergence(seed, _turn, &old, &da, &db, &converted, &dregg_next);
            }

            // Win check must agree.
            let dregg_winner = dref::win_owner(&dregg_next, &GOAL_CORNERS_2P);
            let o1_winner = game.winner.map(|p| p.0 as u32);
            assert_eq!(
                dregg_winner, o1_winner,
                "seed {seed} turn {_turn}: win verdict diverges (dregg {dregg_winner:?} vs o1 {o1_winner:?})"
            );

            total_turns += 1;
        }
    }

    // The battery must actually EXERCISE the engine, including automaton motion.
    assert!(
        total_turns > 1000,
        "differential ran too few turns ({total_turns}) to be meaningful"
    );
    assert!(
        chain_or_step > 0,
        "no turn ever moved the automaton — the step path was never exercised"
    );
    eprintln!(
        "differential: {total_turns} full two-player turns agreed across {GAMES} games; \
         automaton moved on {chain_or_step} turns"
    );
}

// ===========================================================================
// (3) Automaton-step differential in isolation: for many random boards, the dregg
//     `automaton_step` and the automatafl `automaton_move` land the daemon on the same
//     square. This isolates the raycast/priority logic from move resolution.
// ===========================================================================
#[test]
fn automaton_step_differential() {
    let mut rng = Rng::new(0x5713);
    let n = N11;
    let mut moved = 0usize;

    for _ in 0..4000 {
        // Sprinkle a handful of repulsors/attractors and an automaton on a fresh board.
        let mut o1_board = o1::Board::stock_two_player();
        // Clear it to vacuum first, then place fresh.
        for y in 0..n {
            for x in 0..n {
                o1_board.place(
                    o1::Coord {
                        x: x as u8,
                        y: y as u8,
                    },
                    o1::Particle::Vacuum,
                );
            }
        }
        let ax = rng.below(n);
        let ay = rng.below(n);
        o1_board.place(
            o1::Coord {
                x: ax as u8,
                y: ay as u8,
            },
            o1::Particle::Automaton,
        );

        let k = 1 + rng.below(6);
        for _ in 0..k {
            let x = rng.below(n);
            let y = rng.below(n);
            let c = o1::Coord {
                x: x as u8,
                y: y as u8,
            };
            if o1_board.is_automaton(c) {
                continue;
            }
            let p = if rng.next_u64() & 1 == 0 {
                o1::Particle::Repulsor
            } else {
                o1::Particle::Attractor
            };
            o1_board.place(c, p);
        }

        // automatafl: where would the automaton move? (use_column_rule = true)
        let mut game = o1::Game::new(
            o1_board.clone(),
            2,
            true,
            o1::MergeResolutionMode::DetectAndConflict,
            o1::CycleBehaviorMode::RotatePieces,
        );
        let o1_target = game.automaton_move();
        game.update_automaton();

        // dregg: the step.
        let dboard = to_dregg(&o1_board);
        let dstepped = automaton_step(&dboard);

        assert_eq!(
            dstepped.auto,
            (o1_target.x as i32, o1_target.y as i32),
            "automaton target diverges\n board={dboard:?}"
        );
        // And the whole board (o1 applied the move) agrees.
        boards_agree(&game.board, &dstepped, "automaton-step board");

        if dstepped.auto != dboard.auto {
            moved += 1;
        }
    }
    assert!(
        moved > 50,
        "automaton hardly ever moved ({moved}); weak coverage"
    );
    eprintln!("automaton-step differential: 4000 boards agreed; automaton moved on {moved}");
}

// ===========================================================================
// (4) Conflict DETECTION agrees. Where the two engines' post-conflict flow differs
//     (automatafl pauses the round to re-collect; dregg drops-and-continues in one
//     round), what MUST still coincide is *which* moves are conflicted. We feed
//     deliberately-conflicting pairs and check the automatafl conflicted set equals the
//     dregg dropped set.
// ===========================================================================
#[test]
fn conflict_detection_matches_automatafl() {
    // Source fork: one piece, two distinct destinations.
    {
        let mut game = new_stock_game();
        // (0,1) holds a vacuum in the stock board? Pick a known piece: (3,1) is an
        // attractor in the stock opening. Two players target it to different squares.
        let src = o1::Coord { x: 3, y: 1 };
        assert!(
            !game.board.is_vacuum(src),
            "picked a real piece as fork source"
        );
        let a = o1::Move {
            who: o1::Pid(0),
            from: src,
            to: o1::Coord { x: 3, y: 2 },
        };
        let b = o1::Move {
            who: o1::Pid(1),
            from: src,
            to: o1::Coord { x: 5, y: 1 },
        };
        assert!(matches!(
            game.propose_move(a),
            o1::ProposeFeedback::Accepted
        ));
        assert!(matches!(
            game.propose_move(b),
            o1::ProposeFeedback::AcceptedAndReady
        ));
        let o1_conflicted = match game.try_complete_round() {
            o1::CompleteRoundFeedback::Conflict(s) => s.conflicted_moves,
            other => panic!("expected a source-fork Conflict, got {other:?}"),
        };
        // dregg: which moves does conflict_resolve DROP?
        let old = {
            // Re-derive `old` from a fresh stock game (propose_move did not mutate the board).
            to_dregg(&o1::Board::stock_two_player())
        };
        let (da, db) = (to_dmove(&a), to_dmove(&b));
        let valid: Vec<DMove> = [da, db]
            .into_iter()
            .filter(|m| dref::move_valid(&old, m))
            .collect();
        let kept = dref::conflict_resolve(&old, &valid);
        assert!(kept.is_empty(), "dregg must drop both forked moves");
        assert_eq!(
            o1_conflicted.len(),
            2,
            "automatafl must flag both forked moves as conflicted"
        );
    }

    // Destination collision: two distinct non-vacuum sources onto one empty square.
    {
        let mut game = new_stock_game();
        // (3,1) attractor and (4,1) repulsor both drive to the empty (3,3)/(4,3)... pick a
        // common empty destination reachable by a rook move from each on its own axis.
        // (3,1)->(3,3) [down column 3]; (7,1) attractor ->(7,3) is different dest.
        // Use a shared destination: (3,1)->(3,5) and (0,5)? (0,5) is a repulsor; row 5.
        // Simplest shared dest on a shared column/row: (3,1)->(3,4) and (3,6)->(3,4)?
        // (3,6) is vacuum in stock. Use two real pieces sharing a destination:
        // attractor (3,1) down to (3,4); attractor (0,4) right to (3,4).
        let a_src = o1::Coord { x: 3, y: 1 };
        let b_src = o1::Coord { x: 0, y: 4 };
        let dest = o1::Coord { x: 3, y: 4 };
        assert!(!game.board.is_vacuum(a_src) && !game.board.is_vacuum(b_src));
        assert!(game.board.is_vacuum(dest));
        let a = o1::Move {
            who: o1::Pid(0),
            from: a_src,
            to: dest,
        };
        let b = o1::Move {
            who: o1::Pid(1),
            from: b_src,
            to: dest,
        };
        assert!(matches!(
            game.propose_move(a),
            o1::ProposeFeedback::Accepted
        ));
        assert!(matches!(
            game.propose_move(b),
            o1::ProposeFeedback::AcceptedAndReady
        ));
        let o1_conflicted = match game.try_complete_round() {
            o1::CompleteRoundFeedback::Conflict(s) => s.conflicted_moves,
            other => panic!("expected a destination-collision Conflict, got {other:?}"),
        };
        let old = to_dregg(&o1::Board::stock_two_player());
        let (da, db) = (to_dmove(&a), to_dmove(&b));
        let valid: Vec<DMove> = [da, db]
            .into_iter()
            .filter(|m| dref::move_valid(&old, m))
            .collect();
        let kept = dref::conflict_resolve(&old, &valid);
        assert!(kept.is_empty(), "dregg must drop both colliding moves");
        assert_eq!(
            o1_conflicted.len(),
            2,
            "automatafl must flag both colliding moves as conflicted"
        );
    }
}

// ===========================================================================
// (5) Win condition: a move that pulls the automaton into a goal corner wins for
//     that corner's owner, agreeing with automatafl.
// ===========================================================================
#[test]
fn win_condition_matches_automatafl() {
    // Engineer a board where the automaton is one step from a seat-1 corner (10,10)
    // and an attractor beyond it drags it in. We start from a cleared board.
    let n = N11;
    let mut o1_board = o1::Board::stock_two_player();
    for y in 0..n {
        for x in 0..n {
            o1_board.place(
                o1::Coord {
                    x: x as u8,
                    y: y as u8,
                },
                o1::Particle::Vacuum,
            );
        }
    }
    // Automaton at (10,9); attractor at (10,7) two north => step north to (10,8)?
    // We want it to reach the corner (10,10). Place automaton at (10,9), attractor at
    // nothing north (edge). Instead: automaton at (8,10), attractor at (10,10)'s side.
    // Cleanest: automaton at (10,8), attractor at (10,10) is the goal corner itself —
    // but the automaton cannot land ON an attractor. So the corner must be VACUUM and
    // the attractor must sit beyond the corner — impossible past an edge corner.
    //
    // Use a ROW approach to the corner (10,10): automaton at (8,10), attractor at
    // (10,10)? same problem. So drive the automaton toward the corner along a column
    // with the attractor on the far interior side is impossible past the edge.
    //
    // Therefore reach the corner by a single-step where the corner is the attractor
    // TARGET direction with empty space: put the automaton at (9,10) and an attractor
    // at... none beyond. Not possible. Instead approach (0,0) (seat 0) from (2,0) with
    // an attractor at (0,0)? Also on the corner. The automaton can only ENTER a corner
    // that is vacuum, pulled by an attractor further along the SAME axis — but a corner
    // has no cell beyond it. So a corner is entered from the PERPENDICULAR direction:
    // e.g. entering (0,0) moving south (y-) with an attractor south is off-board.
    //
    // The reachable geometry: the automaton enters corner (cx,cy) by moving along one
    // axis toward an attractor on the OTHER side of the corner along the SAME line —
    // which for a corner means the attractor is on the board edge line through the
    // corner. Example: corner (10,10). Move the automaton EAST along row y=10 toward an
    // attractor — but (10,10) is the last cell; nothing east. Move NORTH along col x=10
    // toward an attractor north of the corner — nothing north.
    //
    // So a corner is only enterable from a piece PUSHING (repulsor) behind it. Put a
    // repulsor south of the automaton on column 10 so it flees north into (10,10):
    // automaton at (10,9), repulsor at (10,7) (dist 2 south), empty north (dist>1 to OOB).
    o1_board.place(o1::Coord { x: 10, y: 9 }, o1::Particle::Automaton);
    o1_board.place(o1::Coord { x: 10, y: 7 }, o1::Particle::Repulsor);

    let dboard = to_dregg(&o1_board);
    // The automaton should flee north to (10,10) — the seat-1 corner.
    let dstepped = automaton_step(&dboard);
    assert_eq!(
        dstepped.auto,
        (10, 10),
        "automaton should flee into the corner"
    );

    let mut game = o1::Game::new(
        o1_board.clone(),
        2,
        true,
        o1::MergeResolutionMode::DetectAndConflict,
        o1::CycleBehaviorMode::RotatePieces,
    );
    set_goals(&mut game);
    game.update_automaton();
    // Emulate the automatafl post-step goal scan.
    let o1_win = game
        .goals
        .iter()
        .copied()
        .find(|(c, _)| *c == game.board.automaton_location)
        .map(|(_, p)| p.0 as u32);

    let dregg_win = dref::win_owner(&dstepped, &GOAL_CORNERS_2P);
    assert_eq!(dregg_win, Some(1), "seat 1 owns corner (10,10)");
    assert_eq!(dregg_win, o1_win, "win verdict must agree with automatafl");
}
