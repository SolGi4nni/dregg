//! The reference automatafl transition — the WITNESS ORACLE and the refinement
//! target. Ported faithfully from the committed Lean contract
//! `metatheory/Dregg2/Games/Automatafl.lean` (`applyTurn` and its fragments),
//! which itself mirrors the automatafl reference engine `~/dev/automatafl/logic`.
//!
//! Particle codes match the Lean/DSL board felt encoding:
//! `0 = vacuum, 1 = repulsor, 2 = attractor, 3 = automaton`.
//!
//! The AIR (`crate::air`) re-checks `new == apply_turn(old, moves)` in-circuit;
//! this module computes `new` off-circuit (translation validation) and drives the
//! witness generator. The `#[cfg(test)]` `#guard` battery pins byte-for-byte
//! agreement with the Lean `#guard`s (§8 of `Automatafl.lean`).

pub const VAC: u8 = 0;
pub const REP: u8 = 1;
pub const ATT: u8 = 2;
pub const AUTO: u8 = 3;

pub type Coord = (i32, i32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Board {
    pub n: usize,
    /// `cells[y*n + x]` in `{0,1,2,3}`. The automaton cell also holds `AUTO`.
    pub cells: Vec<u8>,
    pub auto: Coord,
    pub col_rule: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Move {
    pub who: u32,
    pub frm: Coord,
    pub to: Coord,
}

/// Cardinal directions, `(dx, dy)`.
pub const XP: Coord = (1, 0);
pub const XN: Coord = (-1, 0);
pub const YP: Coord = (0, 1);
pub const YN: Coord = (0, -1);
pub const DIRS: [Coord; 4] = [XP, XN, YP, YN];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Raycast {
    pub what: u8,
    pub dist: usize,
}

/// The Automaton's per-axis decision (`evaluate_axis`). Field layout mirrors the
/// Lean `Decision`; `variant` codes `0 = None, 1 = TowardAttractor,
/// 2 = FromRepulsor, 3 = UnbalancedPair` (== the priority order / 10).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decision {
    pub variant: u8,
    pub pos: bool,
    pub att_dist: usize,
    pub rep_dist: usize,
}

impl Decision {
    pub const NONE: Decision = Decision {
        variant: 0,
        pos: false,
        att_dist: 0,
        rep_dist: 0,
    };

    pub fn priority(&self) -> usize {
        match self.variant {
            3 => 30,
            2 => 20,
            1 => 10,
            _ => 0,
        }
    }

    /// The one-step offset this decision induces along `base` (`Decision.delta`).
    pub fn delta(&self, base: Coord) -> Coord {
        if self.variant == 0 {
            (0, 0)
        } else if self.pos {
            base
        } else {
            (-base.0, -base.1)
        }
    }
}

impl Board {
    pub fn cell_at(&self, c: Coord) -> u8 {
        let (x, y) = c;
        if x >= 0 && (x as usize) < self.n && y >= 0 && (y as usize) < self.n {
            self.cells[(y as usize) * self.n + (x as usize)]
        } else {
            VAC
        }
    }

    pub fn in_bounds(&self, c: Coord) -> bool {
        let (x, y) = c;
        x >= 0 && (x as usize) < self.n && y >= 0 && (y as usize) < self.n
    }

    pub fn idx(&self, c: Coord) -> usize {
        (c.1 as usize) * self.n + (c.0 as usize)
    }

    /// `Board::raycast` (fuel = n+1, seeded dist 0). Returns the first non-vacuum
    /// particle and the terminating step index, or vacuum + the OOB step index.
    pub fn raycast(&self, from: Coord, dir: Coord) -> Raycast {
        let mut x = from.0;
        let mut y = from.1;
        let mut dist = 0usize;
        let fuel = self.n + 1;
        for _ in 0..fuel {
            x += dir.0;
            y += dir.1;
            if x >= 0 && (x as usize) < self.n && y >= 0 && (y as usize) < self.n {
                let p = self.cells[(y as usize) * self.n + (x as usize)];
                if p == VAC {
                    dist += 1;
                    continue;
                } else {
                    return Raycast {
                        what: p,
                        dist: dist + 1,
                    };
                }
            } else {
                return Raycast {
                    what: VAC,
                    dist: dist + 1,
                };
            }
        }
        // Unreachable with fuel = n+1; mirror Lean's fuel-0 fallback.
        Raycast { what: VAC, dist }
    }
}

/// `evaluate_axis` — the faithful priority match with `dist > 1` guards.
pub fn evaluate_axis(pos: Raycast, neg: Raycast) -> Decision {
    let (pw, nw) = (pos.what, neg.what);
    let (pd, nd) = (pos.dist, neg.dist);
    match (pw, nw) {
        (ATT, REP) if pd > 1 => Decision {
            variant: 3,
            pos: true,
            att_dist: pd,
            rep_dist: nd,
        },
        (REP, ATT) if nd > 1 => Decision {
            variant: 3,
            pos: false,
            att_dist: nd,
            rep_dist: pd,
        },
        (REP, REP) if pd != nd => Decision {
            variant: 2,
            pos: pd > nd,
            att_dist: 0,
            rep_dist: pd.min(nd),
        },
        (REP, VAC) if nd > 1 => Decision {
            variant: 2,
            pos: false,
            att_dist: 0,
            rep_dist: pd,
        },
        (VAC, REP) if pd > 1 => Decision {
            variant: 2,
            pos: true,
            att_dist: 0,
            rep_dist: nd,
        },
        (ATT, ATT) if pd != nd && pd.min(nd) > 1 => Decision {
            variant: 1,
            pos: pd < nd,
            att_dist: pd.min(nd),
            rep_dist: 0,
        },
        (ATT, VAC) if pd > 1 => Decision {
            variant: 1,
            pos: true,
            att_dist: pd,
            rep_dist: 0,
        },
        (VAC, ATT) if nd > 1 => Decision {
            variant: 1,
            pos: false,
            att_dist: nd,
            rep_dist: 0,
        },
        _ => Decision::NONE,
    }
}

/// A single monotone integer capturing `decision_cmp` exactly: priority dominates,
/// then the reversed-distance tiebreak (`chose_smaller_distance`: smaller distance
/// ranks greater). `att` is the primary tiebreak key for UnbalancedPair/
/// TowardAttractor, `rep` the secondary (and the sole key for FromRepulsor). With
/// distances `< n <= COORD_CAP`, the coefficients keep priority > att-key > rep-key.
pub const SCORE_PRI: i64 = 100_000;
pub const SCORE_ATT: i64 = 100;

pub fn decision_score(d: &Decision) -> i64 {
    // The Decision field conventions already zero the irrelevant tiebreak key
    // (FromRepulsor: att=0; TowardAttractor: rep=0; None: both 0), so the single
    // formula `variant*PRI - att*ATT - rep` reproduces decision_cmp exactly:
    // priority (variant) dominates; within a variant the reversed-distance tiebreak
    // (smaller distance ranks greater) is `-att*ATT - rep`.
    d.variant as i64 * SCORE_PRI - d.att_dist as i64 * SCORE_ATT - d.rep_dist as i64
}

/// `choose_offset(xDec, yDec, col)` via the monotone scores (== `decision_cmp`).
pub fn choose_offset(x: &Decision, y: &Decision, col: bool) -> Coord {
    let sx = decision_score(x);
    let sy = decision_score(y);
    if sx > sy {
        x.delta(XP)
    } else if sy > sx {
        y.delta(YP)
    } else if col {
        y.delta(YP)
    } else {
        (0, 0)
    }
}

/// The four raycasts + both axis decisions + the chosen offset.
pub struct AutomatonSense {
    pub rays: [Raycast; 4], // xp, xn, yp, yn
    pub x_dec: Decision,
    pub y_dec: Decision,
    pub offset: Coord,
}

pub fn automaton_sense(b: &Board) -> AutomatonSense {
    let xp = b.raycast(b.auto, XP);
    let xn = b.raycast(b.auto, XN);
    let yp = b.raycast(b.auto, YP);
    let yn = b.raycast(b.auto, YN);
    let x_dec = evaluate_axis(xp, xn);
    let y_dec = evaluate_axis(yp, yn);
    let offset = choose_offset(&x_dec, &y_dec, b.col_rule);
    AutomatonSense {
        rays: [xp, xn, yp, yn],
        x_dec,
        y_dec,
        offset,
    }
}

/// `automaton_step`: move onto the one-step target iff in bounds, a genuine move,
/// and vacuum; else unchanged.
pub fn automaton_step(b: &Board) -> Board {
    let s = automaton_sense(b);
    let (ox, oy) = s.offset;
    let tx = b.auto.0 + ox;
    let ty = b.auto.1 + oy;
    let target = (tx, ty);
    let moves = b.in_bounds(target) && (ox != 0 || oy != 0) && b.cell_at(target) == VAC;
    if moves {
        let mut nb = b.clone();
        let old_i = b.idx(b.auto);
        let new_i = b.idx(target);
        nb.cells[old_i] = VAC;
        nb.cells[new_i] = AUTO;
        nb.auto = target;
        nb
    } else {
        b.clone()
    }
}

/// `MoveValid` — distinct, rook-aligned, both endpoints in-bounds, neither the
/// automaton. (`isConflict` is always false in the resolved model.)
pub fn move_valid(b: &Board, m: &Move) -> bool {
    m.frm != m.to
        && (m.frm.0 == m.to.0 || m.frm.1 == m.to.1)
        && b.in_bounds(m.frm)
        && b.in_bounds(m.to)
        && m.frm != b.auto
        && m.to != b.auto
}

/// Interior coordinates strictly between two axis-aligned endpoints (exclusive).
pub fn interior(frm: Coord, to: Coord) -> Vec<Coord> {
    let mut out = Vec::new();
    if frm.0 == to.0 {
        let lo = frm.1.min(to.1);
        let hi = frm.1.max(to.1);
        for y in (lo + 1)..hi {
            out.push((frm.0, y));
        }
    } else {
        let lo = frm.0.min(to.0);
        let hi = frm.0.max(to.0);
        for x in (lo + 1)..hi {
            out.push((x, frm.1));
        }
    }
    out
}

fn has_two_distinct<T: PartialEq + Copy>(l: &[T]) -> bool {
    l.iter().any(|a| l.iter().any(|c| a != c))
}

fn frm_conflict(ms: &[Move], m: &Move) -> bool {
    let dests: Vec<Coord> = ms
        .iter()
        .filter(|m2| m2.frm == m.frm)
        .map(|m2| m2.to)
        .collect();
    has_two_distinct(&dests)
}

fn to_conflict(b: &Board, ms: &[Move], m: &Move) -> bool {
    let srcs: Vec<Coord> = ms
        .iter()
        .filter(|m2| m2.to == m.to && b.cell_at(m2.frm) != VAC)
        .map(|m2| m2.frm)
        .collect();
    has_two_distinct(&srcs)
}

/// `conflictResolve`: drop moves touching a conflicted source or destination.
pub fn conflict_resolve(b: &Board, ms: &[Move]) -> Vec<Move> {
    ms.iter()
        .filter(|m| !frm_conflict(ms, m) && !to_conflict(b, ms, m))
        .copied()
        .collect()
}

fn occluded(b: &Board, srcs: &[Coord], m: &Move) -> bool {
    interior(m.frm, m.to)
        .iter()
        .any(|&c| b.cell_at(c) != VAC && !srcs.contains(&c))
}

fn next_of(b: &Board, moved: &[Move], srcs: &[Coord], c: Coord) -> Option<Coord> {
    moved
        .iter()
        .find(|m| m.frm == c && !occluded(b, srcs, m))
        .map(|m| m.to)
}

fn follow_chain(
    next_c: &dyn Fn(Coord) -> Option<Coord>,
    piece_srcs: &[Coord],
    start: Coord,
    visited: &mut Vec<Coord>,
    fuel: usize,
) -> Coord {
    if fuel == 0 {
        return start;
    }
    match next_c(start) {
        None => start,
        Some(nxt) => {
            if visited.contains(&nxt) {
                start
            } else if piece_srcs.contains(&nxt) {
                nxt
            } else {
                match next_c(nxt) {
                    None => nxt,
                    Some(_) => {
                        visited.push(start);
                        follow_chain(next_c, piece_srcs, nxt, visited, fuel - 1)
                    }
                }
            }
        }
    }
}

/// `applyMoves` (faithful subset): occlusion + chain-follow + rewrite.
pub fn apply_moves(b: &Board, moves: &[Move]) -> Board {
    let srcs: Vec<Coord> = moves.iter().map(|m| m.frm).collect();
    // A source counts as a MOVING piece only if it carries a particle AND its move
    // is not occluded. This mirrors the automatafl `apply_moves`, which inserts a source
    // into `initial_piece_coords` only inside `if !is_occluded` (all sources are
    // marked passable first, so `occluded` here matches). An OCCLUDED move's source
    // is therefore NOT journeyed and NOT cleared — it stays put as a static occupant,
    // and another piece's chain may flow onto and overwrite it. (Including occluded
    // sources here would spawn a spurious stationary journey that blocks the incoming
    // piece — a divergence from automatafl the 11×11 differential surfaces.)
    let mut piece_srcs: Vec<Coord> = Vec::new();
    for m in moves {
        if b.cell_at(m.frm) != VAC && !occluded(b, &srcs, m) && !piece_srcs.contains(&m.frm) {
            piece_srcs.push(m.frm);
        }
    }
    let fuel = moves.len() + 1;
    let next_c = |c: Coord| next_of(b, moves, &srcs, c);

    struct Journey {
        dest: Coord,
        particle: u8,
    }
    let journeys: Vec<Journey> = piece_srcs
        .iter()
        .map(|&s| {
            let mut visited = Vec::new();
            let dest = follow_chain(&next_c, &piece_srcs, s, &mut visited, fuel);
            Journey {
                dest,
                particle: b.cell_at(s),
            }
        })
        .collect();

    let mut nb = b.clone();
    for i in 0..(b.n * b.n) {
        let c = ((i % b.n) as i32, (i / b.n) as i32);
        // find? : first journey landing on c
        if let Some(j) = journeys.iter().find(|j| j.dest == c) {
            nb.cells[i] = j.particle;
        } else if piece_srcs.contains(&c) {
            nb.cells[i] = VAC;
        } else {
            nb.cells[i] = b.cell_at(c);
        }
    }
    nb
}

/// The chain-follow endpoint of the piece starting at `src` under the (already
/// conflict-resolved) `moves` — the journey destination `apply_moves` computes.
/// `None` if `src` carries no piece (vacuum source).
pub fn chain_endpoint(b: &Board, moves: &[Move], src: Coord) -> Option<Coord> {
    let all_srcs: Vec<Coord> = moves.iter().map(|m| m.frm).collect();
    // Occlusion-aware moving-piece set — coherent with `apply_moves`: an occluded
    // move's source is a static occupant, not a journeyed piece.
    let mut piece_srcs: Vec<Coord> = Vec::new();
    for m in moves {
        if b.cell_at(m.frm) != VAC && !occluded(b, &all_srcs, m) && !piece_srcs.contains(&m.frm) {
            piece_srcs.push(m.frm);
        }
    }
    if !piece_srcs.contains(&src) {
        return None;
    }
    let fuel = moves.len() + 1;
    let next_c = |c: Coord| next_of(b, moves, &all_srcs, c);
    let mut visited = Vec::new();
    Some(follow_chain(&next_c, &piece_srcs, src, &mut visited, fuel))
}

/// The move-resolved intermediate board `mid` — validity-filter → conflict-resolve →
/// apply-all, STOPPING BEFORE the automaton step. This is the exact C.5 fold-leg split:
/// `apply_turn = automaton_step ∘ resolve_mid`. Leg R proves `old → mid` (this function),
/// Leg A proves `mid → new` (`automaton_step`), and the composed refinement is exactly
/// this equation.
pub fn resolve_mid(b: &Board, ms: &[Move]) -> Board {
    let valid: Vec<Move> = ms.iter().filter(|m| move_valid(b, m)).copied().collect();
    let resolved = conflict_resolve(b, &valid);
    apply_moves(b, &resolved)
}

/// **THE PURE TRANSITION** (`applyTurn`): validity-filter → conflict-resolve →
/// apply-all → automaton step. Factored as `automaton_step ∘ resolve_mid` — the two
/// composed fold legs (Leg R then Leg A).
pub fn apply_turn(b: &Board, ms: &[Move]) -> Board {
    automaton_step(&resolve_mid(b, ms))
}

// ============================================================================
// The REAL 11×11 two-player game: the stock opening, the goal corners, the win
// check. Faithful to the automatafl reference `~/dev/automatafl/logic`
// (`board.rs::stock_two_player`, `game.rs::try_complete_round`'s goal check) and
// the README ruleset. TWO-PLAYER ONLY (m=2). The transition itself is the same
// `apply_turn` above — it is fully parameterized by `Board::n`, so nothing about
// the resolution changes; only the board size and the win layer are new here.
// ============================================================================

/// The real board edge for the deployed two-player game.
pub const N11: usize = 11;

/// **The stock two-player opening (11×11).** A byte-for-byte transcription of the
/// automatafl `Board::stock_two_player` grid (`~/dev/automatafl/logic/src/board.rs`):
/// a repulsor/attractor ring around the flanks, four attractor pairs and repulsor
/// pairs, and the Automaton dead centre at `(5,5)`. Rows are `y = 0..11` from the
/// top of the `arr2` literal (automatafl indexes `particles[[y, x]]`, matching our
/// `cells[y*n + x]`).
pub fn stock_two_player() -> Board {
    // `.` vacuum, `r` repulsor, `a` attractor, `d` automaton — the exact automatafl grid.
    const GRID: [&[u8; N11]; N11] = [
        b"rroorrroorr", // y = 0
        b"oooarrraooo", // y = 1
        b"ooooooooooo", // y = 2
        b"ooooooooooo", // y = 3
        b"aaoooooooaa", // y = 4
        b"rrooodooorr", // y = 5
        b"aaoooooooaa", // y = 6
        b"ooooooooooo", // y = 7
        b"ooooooooooo", // y = 8
        b"oooarrraooo", // y = 9
        b"rroorrroorr", // y = 10
    ];
    let mut cells = vec![VAC; N11 * N11];
    let mut auto = (0, 0);
    for (y, row) in GRID.iter().enumerate() {
        for (x, &ch) in row.iter().enumerate() {
            let p = match ch {
                b'o' => VAC,
                b'r' => REP,
                b'a' => ATT,
                b'd' => {
                    auto = (x as i32, y as i32);
                    AUTO
                }
                other => panic!("bad opening glyph {other:?}"),
            };
            cells[y * N11 + x] = p;
        }
    }
    debug_assert_eq!(auto, (5, 5), "the stock automaton sits dead centre");
    Board {
        n: N11,
        cells,
        auto,
        col_rule: true,
    }
}

/// The four goal corners of the stock two-player game, each tagged with its owning
/// seat (`0` or `1`). Per the README two-player rule, "each player picks two
/// corners that are in the same row": seat 0 owns the two `y = 0` corners, seat 1
/// owns the two `y = 10` corners. When the Automaton steps into a corner, that
/// corner's owner wins (`Game::try_complete_round`).
pub const GOAL_CORNERS_2P: [(Coord, u32); 4] = [
    ((0, 0), 0),
    ((N11 as i32 - 1, 0), 0),
    ((0, N11 as i32 - 1), 1),
    ((N11 as i32 - 1, N11 as i32 - 1), 1),
];

/// **The win check.** The seat whose goal corner the Automaton currently occupies,
/// or `None`. Mirrors the automatafl `try_complete_round` goal scan
/// (`goals.iter().find(|(c, _)| c == automaton_location)`), evaluated on the
/// post-`apply_turn` board.
pub fn win_owner(b: &Board, goals: &[(Coord, u32)]) -> Option<u32> {
    goals
        .iter()
        .find(|(c, _)| *c == b.auto)
        .map(|(_, who)| *who)
}

// ============================================================================
// #guard battery — byte-for-byte agreement with Automatafl.lean §8.
// ============================================================================
#[cfg(test)]
mod guards {
    use super::*;

    /// `mkBoard size placed auto` — the Lean witness builder.
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

    #[test]
    fn lean_demoboard_guards() {
        // Automaton at (2,2); attractor at (2,4). Daemon steps north to (2,3).
        let demo = mk(5, &[((2, 4), ATT)], (2, 2));
        let stepped = automaton_step(&demo);
        assert_eq!(stepped.auto, (2, 3));
        assert_eq!(stepped.cell_at((2, 3)), AUTO);
        assert_eq!(stepped.cell_at((2, 2)), VAC);
        assert_eq!(stepped.cell_at((2, 4)), ATT);
    }

    #[test]
    fn lean_repboard_guard() {
        // Repulsor one south at (2,1), empty north — flees north to (2,3).
        let rep = mk(5, &[((2, 1), REP)], (2, 2));
        assert_eq!(automaton_step(&rep).auto, (2, 3));
    }

    #[test]
    fn lean_move_guards() {
        // Move attractor (0,0)->(0,3) on empty 5x5, automaton parked at (4,4).
        let mb = mk(5, &[((0, 0), ATT)], (4, 4));
        let m = Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        };
        assert!(move_valid(&mb, &m));
        let after = apply_moves(&mb, &[m]);
        assert_eq!(after.cell_at((0, 3)), ATT);
        assert_eq!(after.cell_at((0, 0)), VAC);
        // Full turn: daemon in corner doesn't move.
        let turn = apply_turn(&mb, &[m]);
        assert_eq!(turn.cell_at((0, 3)), ATT);

        // Validity teeth (both polarities).
        assert!(!move_valid(
            &mb,
            &Move {
                who: 0,
                frm: (0, 0),
                to: (0, 0)
            }
        )); // from==to
        assert!(!move_valid(
            &mb,
            &Move {
                who: 0,
                frm: (0, 0),
                to: (1, 3)
            }
        )); // not rook
        assert!(!move_valid(
            &mb,
            &Move {
                who: 0,
                frm: (4, 4),
                to: (4, 0)
            }
        )); // src is auto
        assert!(!move_valid(
            &mb,
            &Move {
                who: 0,
                frm: (0, 0),
                to: (0, 9)
            }
        )); // dest OOB
    }

    #[test]
    fn lean_fork_conflict_guard() {
        // Two distinct destinations from one source: fork -> both dropped, piece stays.
        let mb = mk(5, &[((0, 0), ATT)], (4, 4));
        let a = Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        };
        let b = Move {
            who: 1,
            frm: (0, 0),
            to: (3, 0),
        };
        assert!(conflict_resolve(&mb, &[a, b]).is_empty());
        let after = apply_moves(&mb, &conflict_resolve(&mb, &[a, b]));
        assert_eq!(after.cell_at((0, 0)), ATT);
    }
}
