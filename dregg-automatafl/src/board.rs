//! The automatafl board as DATA, and the wire that carries it to Lean.
//!
//! This module holds no game rules. It is the state shape (`Board` / `Move` / `Coord` / the particle
//! codes), the pure indexing every consumer needs (`cell_at` / `in_bounds` / `idx`), and the
//! MARSHALLER for `@[export] dregg_automatafl_rules` (`Dregg2.Games.AutomataflFFI`). Every question
//! with a rules answer — what a round resolves to, whether a move is legal, which coordinates clash,
//! who won — is asked of the Lean through [`crate::rules`], never answered here.
//!
//! ## What used to be here
//!
//! `src/reference.rs` — a hand transcription of `~/dev/automatafl/logic/src/game.rs`, one of two
//! non-canonical Rust experiments — computed all of it in Rust and was consulted as the "witness
//! oracle" by the generators that fill the Lean-emitted descriptors. The four-way conformance audit
//! (`docs/reference/AUTOMATAFL-RULES-CONFORMANCE-AUDIT.md`) found that lineage divergent from the
//! Creator-Approved ruleset on nine clauses, and two of them were live in that file:
//!
//! * a **2-cycle** (A→B, B→A) SWAPPED the two pieces, where the ruleset keeps both PUT — so on that
//!   input the oracle and the descriptor it was checking disagreed *by construction*, which
//!   `resolve_witness.rs` documented instead of fixing;
//! * `occluded` scanned only the STRICT INTERIOR of a move, so a mover landed on and DESTROYED a
//!   stationary piece standing on its destination, where the ruleset's inclusive path check blocks
//!   the move and replaces the mover at its origin.
//!
//! The particle codes below (`0 = vacuum, 1 = repulsor, 2 = attractor, 3 = automaton`) are the
//! canonical Lean encoding (`Emit.AutomataflCommit.particleCode`), shared by the AIR and the wire.

/// Vacuum — the only pass-through particle.
pub const VAC: u8 = 0;
/// Repulsor.
pub const REP: u8 = 1;
/// Attractor.
pub const ATT: u8 = 2;
/// The Automaton. It also occupies a cell, so it occludes and can be raycast from.
pub const AUTO: u8 = 3;

/// The real board edge of the deployed two-player game — and the size the Lean descriptors are
/// emitted at.
pub const N11: usize = 11;

/// A board coordinate, `(x, y)`. Signed because a caller can NAME an off-board square; the Lean
/// answers `illegal` for it (see [`Board::wire_coord`]).
pub type Coord = (i32, i32);

/// A board position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Board {
    /// The board edge; the grid is `n × n`.
    pub n: usize,
    /// `cells[y*n + x]` in `{0,1,2,3}`. The automaton's cell also holds [`AUTO`].
    pub cells: Vec<u8>,
    /// The automaton's coordinate.
    pub auto: Coord,
    /// The equal-priority tie-break: the column rule (prefer the Y axis) when set, freeze when
    /// clear. Maps onto `AutomataflRules.TieBreak` — see [`Board::tie_token`].
    pub col_rule: bool,
}

/// A revealed move: `who` moved a piece from `frm` to `to`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Move {
    /// The seat that submitted it.
    pub who: u32,
    /// The source square.
    pub frm: Coord,
    /// The destination square.
    pub to: Coord,
}

/// Cardinal directions, `(dx, dy)` — the ray order the Lean `sense` verb reports in.
pub const XP: Coord = (1, 0);
/// `-x`.
pub const XN: Coord = (-1, 0);
/// `+y`.
pub const YP: Coord = (0, 1);
/// `-y`.
pub const YN: Coord = (0, -1);
/// `[XP, XN, YP, YN]`.
pub const DIRS: [Coord; 4] = [XP, XN, YP, YN];

/// One raycast result, as the Lean reported it: the first non-vacuum particle hit (or vacuum at the
/// wall) and the step index at which the scan stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Raycast {
    /// The particle code hit, or [`VAC`] for the wall.
    pub what: u8,
    /// The step index the scan terminated at.
    pub dist: usize,
}

/// One axis decision, as the Lean reported it. `variant` is the priority over ten
/// (`0 = none, 1 = towardAttractor, 2 = fromRepulsor, 3 = unbalancedPair`); the distance fields the
/// variant does not carry read `0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decision {
    /// `0 none · 1 towardAttractor · 2 fromRepulsor · 3 unbalancedPair`.
    pub variant: u8,
    /// The decision points along the axis-POSITIVE direction.
    pub pos: bool,
    /// The attractor distance the decision was taken on (`0` if the variant carries none).
    pub att_dist: usize,
    /// The repulsor distance the decision was taken on (`0` if the variant carries none).
    pub rep_dist: usize,
}

impl Decision {
    /// The all-zero `none` decision.
    pub const NONE: Decision = Decision {
        variant: 0,
        pos: false,
        att_dist: 0,
        rep_dist: 0,
    };

    /// The priority number (`Decision.priority`): `variant × 10`.
    pub fn priority(&self) -> usize {
        (self.variant as usize) * 10
    }
}

/// The automaton's whole decision on a board, as the Lean `sense` verb reported it: the four
/// raycasts (in [`DIRS`] order), the two axis decisions, and the chosen one-step offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AutomatonSense {
    /// `[xp, xn, yp, yn]`.
    pub rays: [Raycast; 4],
    /// The X-axis decision.
    pub x_dec: Decision,
    /// The Y-axis decision.
    pub y_dec: Decision,
    /// The chosen offset — one of the five cardinal offsets including `(0,0)`
    /// (`AutomataflRules.chooseOffsetCfg_mem`).
    pub offset: Coord,
}

impl Board {
    /// The particle at a cell; vacuum outside the board (`Board.cellAt`).
    pub fn cell_at(&self, c: Coord) -> u8 {
        if self.in_bounds(c) {
            self.cells[(c.1 as usize) * self.n + (c.0 as usize)]
        } else {
            VAC
        }
    }

    /// Is the coordinate on the board?
    pub fn in_bounds(&self, c: Coord) -> bool {
        let (x, y) = c;
        x >= 0 && (x as usize) < self.n && y >= 0 && (y as usize) < self.n
    }

    /// The row-major index of an in-bounds coordinate.
    pub fn idx(&self, c: Coord) -> usize {
        (c.1 as usize) * self.n + (c.0 as usize)
    }

    /// The tie-break token this board's `col_rule` denotes: `0` = `TieBreak.column` (prefer Y, the
    /// deployed default), `2` = `TieBreak.freeze` (no move on an equal-priority tie). These are the
    /// two behaviours the flag ever meant; `TieBreak.row` is a third setting no deployed board
    /// selects, so nothing in this crate can ask for it.
    pub fn tie_token(&self) -> &'static str {
        if self.col_rule { "0" } else { "2" }
    }

    /// **Is this board a well-formed POSITION?** — the cell vector has exactly `n²` entries, every
    /// code is in the alphabet `{0,1,2,3}`, and the automaton is in bounds and standing on its own
    /// code. A DATA-SHAPE check, not a game rule: it says the value can be encoded faithfully, and
    /// nothing about whether the position is reachable. Called before every wire encode so a corrupt
    /// board fails CLOSED here instead of being silently re-coded into a legal-looking one.
    pub fn validate(&self) -> Result<(), String> {
        if self.cells.len() != self.n * self.n {
            return Err(format!(
                "board carries {} cells for size {}",
                self.cells.len(),
                self.n
            ));
        }
        for (i, &code) in self.cells.iter().enumerate() {
            if code > AUTO {
                return Err(format!(
                    "board cell {i} holds {code}, outside the particle alphabet {{0,1,2,3}}"
                ));
            }
        }
        if !self.in_bounds(self.auto) {
            return Err(format!("the automaton at {:?} is off the board", self.auto));
        }
        if self.cell_at(self.auto) != AUTO {
            return Err(format!(
                "the automaton at {:?} does not carry its own code (cell = {})",
                self.auto,
                self.cell_at(self.auto)
            ));
        }
        Ok(())
    }

    /// The five-token board wire: `size cells autoX autoY colRule`, cells row-major (`y*n + x`) as
    /// digits in `{0,1,2,3}`, `-` for the empty board. Encode only what [`Board::validate`] admits —
    /// the `& 3` below is then the identity, never a silent re-coding.
    pub fn to_wire(&self) -> String {
        let mut s = String::with_capacity(self.cells.len() + 24);
        s.push_str(&self.n.to_string());
        s.push(' ');
        if self.cells.is_empty() {
            s.push('-');
        } else {
            for c in &self.cells {
                s.push(char::from(b'0' + (c & 3)));
            }
        }
        s.push(' ');
        s.push_str(&self.auto.0.to_string());
        s.push(' ');
        s.push_str(&self.auto.1.to_string());
        s.push(' ');
        s.push_str(if self.col_rule { "1" } else { "0" });
        s
    }

    /// A coordinate as two wire tokens. Signed: a negative component decodes on the Lean side to a
    /// sentinel that is out of bounds at every size, which every verb reads as illegal.
    pub fn wire_coord(c: Coord) -> String {
        format!("{} {}", c.0, c.1)
    }

    /// Read a board back off `toks`, returning it and the unconsumed tail.
    pub fn from_wire<'a, 'b>(toks: &'a [&'b str]) -> Result<(Board, &'a [&'b str]), String> {
        if toks.len() < 5 {
            return Err(format!("board wire needs 5 tokens, got {}", toks.len()));
        }
        let n: usize = toks[0]
            .parse()
            .map_err(|e| format!("board size {:?}: {e}", toks[0]))?;
        let cells: Vec<u8> = if toks[1] == "-" {
            Vec::new()
        } else {
            toks[1]
                .bytes()
                .map(|b| {
                    if b.is_ascii_digit() && b - b'0' < 4 {
                        Ok(b - b'0')
                    } else {
                        Err(format!("cell digit {:?} outside {{0,1,2,3}}", b as char))
                    }
                })
                .collect::<Result<_, _>>()?
        };
        if cells.len() != n * n {
            return Err(format!(
                "board wire carries {} cells for size {n}",
                cells.len()
            ));
        }
        let ax: i32 = toks[2]
            .parse()
            .map_err(|e| format!("auto x {:?}: {e}", toks[2]))?;
        let ay: i32 = toks[3]
            .parse()
            .map_err(|e| format!("auto y {:?}: {e}", toks[3]))?;
        let col = toks[4] != "0";
        Ok((
            Board {
                n,
                cells,
                auto: (ax, ay),
                col_rule: col,
            },
            &toks[5..],
        ))
    }
}

/// A length-prefixed coordinate list: `k` then `k × [x y]`.
pub fn coords_wire(cs: &[Coord]) -> String {
    let mut s = cs.len().to_string();
    for c in cs {
        s.push(' ');
        s.push_str(&Board::wire_coord(*c));
    }
    s
}

/// A length-prefixed move list: `k` then `k × [who fromX fromY toX toY]`.
pub fn moves_wire(ms: &[Move]) -> String {
    let mut s = ms.len().to_string();
    for m in ms {
        s.push(' ');
        s.push_str(&m.who.to_string());
        s.push(' ');
        s.push_str(&Board::wire_coord(m.frm));
        s.push(' ');
        s.push_str(&Board::wire_coord(m.to));
    }
    s
}

/// A length-prefixed goal assignment: `k` then `k × [x y seat]`.
pub fn goals_wire(g: &[(Coord, u32)]) -> String {
    let mut s = g.len().to_string();
    for (c, seat) in g {
        s.push(' ');
        s.push_str(&Board::wire_coord(*c));
        s.push(' ');
        s.push_str(&seat.to_string());
    }
    s
}

/// A length-prefixed seat list: `k` then `k × [pid]`.
pub fn pids_wire(ps: &[u32]) -> String {
    let mut s = ps.len().to_string();
    for p in ps {
        s.push(' ');
        s.push_str(&p.to_string());
    }
    s
}

/// Read a length-prefixed coordinate list off `toks`, returning it and the unconsumed tail.
pub fn coords_from_wire<'a, 'b>(
    toks: &'a [&'b str],
) -> Result<(Vec<Coord>, &'a [&'b str]), String> {
    let (k, mut rest) = match toks.split_first() {
        Some((kt, rest)) => (
            kt.parse::<usize>()
                .map_err(|e| format!("coord count {kt:?}: {e}"))?,
            rest,
        ),
        None => return Err("coord list wire is empty".into()),
    };
    let mut out = Vec::with_capacity(k);
    for _ in 0..k {
        if rest.len() < 2 {
            return Err("coord list wire is truncated".into());
        }
        let x: i32 = rest[0]
            .parse()
            .map_err(|e| format!("coord x {:?}: {e}", rest[0]))?;
        let y: i32 = rest[1]
            .parse()
            .map_err(|e| format!("coord y {:?}: {e}", rest[1]))?;
        out.push((x, y));
        rest = &rest[2..];
    }
    Ok((out, rest))
}

/// Read a length-prefixed move list off `toks`, returning it and the unconsumed tail.
pub fn moves_from_wire<'a, 'b>(toks: &'a [&'b str]) -> Result<(Vec<Move>, &'a [&'b str]), String> {
    let (k, mut rest) = match toks.split_first() {
        Some((kt, rest)) => (
            kt.parse::<usize>()
                .map_err(|e| format!("move count {kt:?}: {e}"))?,
            rest,
        ),
        None => return Err("move list wire is empty".into()),
    };
    let mut out = Vec::with_capacity(k);
    for _ in 0..k {
        if rest.len() < 5 {
            return Err("move list wire is truncated".into());
        }
        let num = |t: &str| -> Result<i32, String> {
            t.parse::<i32>()
                .map_err(|e| format!("move field {t:?}: {e}"))
        };
        out.push(Move {
            who: rest[0]
                .parse()
                .map_err(|e| format!("move seat {:?}: {e}", rest[0]))?,
            frm: (num(rest[1])?, num(rest[2])?),
            to: (num(rest[3])?, num(rest[4])?),
        });
        rest = &rest[5..];
    }
    Ok((out, rest))
}

/// Read a length-prefixed seat list off `toks`, returning it and the unconsumed tail.
pub fn pids_from_wire<'a, 'b>(toks: &'a [&'b str]) -> Result<(Vec<u32>, &'a [&'b str]), String> {
    let (k, mut rest) = match toks.split_first() {
        Some((kt, rest)) => (
            kt.parse::<usize>()
                .map_err(|e| format!("seat count {kt:?}: {e}"))?,
            rest,
        ),
        None => return Err("seat list wire is empty".into()),
    };
    let mut out = Vec::with_capacity(k);
    for _ in 0..k {
        match rest.split_first() {
            Some((t, tail)) => {
                out.push(t.parse().map_err(|e| format!("seat {t:?}: {e}"))?);
                rest = tail;
            }
            None => return Err("seat list wire is truncated".into()),
        }
    }
    Ok((out, rest))
}
