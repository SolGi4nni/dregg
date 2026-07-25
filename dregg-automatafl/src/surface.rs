//! # The **Offering** — automatafl playable on every dreggnet frontend.
//!
//! [`AutomataflOffering`] hosts an n=2 automatafl match as a [`dreggnet_offerings::Offering`]: the
//! same `open`/`actions`/`advance`/`verify`/`render`/`render_for`/`price` shape every frontend
//! (web / Discord / Telegram / WeChat) already drives. It is the coordinate-grid sibling of
//! `dregg-multiway-tug`'s `TugOffering`: where the tug paints a hidden HAND, automatafl paints a
//! hidden MOVE on a shared BOARD.
//!
//! **The board is the STOCK 11×11 two-player game**, and every resolved round's two revealed moves
//! are RECORDED ([`AutomataflSession::rounds`], [`AutomataflSession::start_board`]) — so a finished
//! match hands the crown the exact object the two-leg fold attests
//! (`AutomataflMatch::played(start, rounds)`: Leg R the players' adjudicated moves, Leg A the
//! automaton's step, board-window chained). CLEAN rounds only: a round the seats CLASHED on is
//! still played and still recorded, but [`AutomataflSession::unfoldable_round`] names it and the
//! fold refuses it — the surface resolves a clash by DROPPING moves, which is not the rule the
//! ruleset states (mark the square, re-enter the round), so attesting it would be a proof of a
//! transition nobody licensed.
//!
//! **The board is a [`deos_view::ViewNode::CoordGrid`]** — one [`deos_view::CoordCell`] per square,
//! the particle as the glyph (`·` vacuum, `R` repulsor, `A` attractor, `@` automaton), the
//! automaton cell marked, and each affordance-bearing square carrying the `{turn, arg}` a click
//! fires. Selecting one of your pieces LIGHTS ITS ROOK LINE: every legal target of that source
//! (same row or column, in-bounds, and never the automaton as a SOURCE — exactly what the LEAN
//! `AutomataflRules.moveLegalB` admits, asked of it) is painted in the highlight-set; an illegal
//! target (a diagonal, the source itself) is NOT.
//!
//! **The simultaneous-move shape, rendered.** Automatafl's turn is not alternating: both players
//! move at once. So the surface runs COMMIT → REVEAL → RESOLVE:
//! 1. **commit** — each seat selects a source and seals a destination. The executor stores only the
//!    COMMITMENT (a blake3 seal over the move + a per-turn nonce), never the plaintext;
//! 2. **reveal** — each seat opens its seal (the plaintext lands on the cell, checked against the
//!    commitment it opens);
//! 3. **resolve** — ONE real turn asks the LEAN for `roundStep`'s clean-round arm
//!    ([`crate::rules::turn`]): illegal moves filtered, the conflict set checked, the moves resolved,
//!    the automaton takes its step, and the win is checked ON ENTRY.
//!
//! [`Offering::render_for`] paints the table AS A VIEWER SEES IT: the viewer's own committed move is
//! shown in full (they know what they sealed), while the opponent's is FOG — a sealed commitment, no
//! source, no destination — until the reveal. So seat A's move appears in A's view and not in B's.
//!
//! **Every advance is a REAL turn.** `select` / `commit` / `reveal` / `resolve` each commit the whole
//! witnessed state to a deployed [`crate::game::AutomataflGame`] world-cell under the matching
//! method; the executor's teeth (board immutable during the commit phase, strictly-monotone
//! commit/reveal counters, particle-code membership + a write-once winner on the resolution) admit a
//! legal turn and REFUSE an illegal one — [`Outcome::Landed`] with a genuine `TurnReceipt`, or
//! [`Outcome::Refused`] with nothing committed (anti-ghost).
//!
//! HONEST SCOPE: the seal HIDES the move by non-reveal on this trusted host (the commitment is what
//! the cell holds; the plaintext lives in the session until the reveal) — the *in-proof* sealed move
//! (the commitment opened inside the AIR, folded as a custom leaf) is the named next lane, exactly
//! as the tug's in-proof hidden hand is. The board TRANSITION is already proven in-circuit by the
//! PROVEN Lean descriptors ([`crate::witness`] / [`crate::resolve_witness`],
//! `new == applyTurn(old, moves)`); this surface asks the same LEAN SPEC the descriptors
//! pin.

use deos_view::{CoordCell, MenuItem, PillCase, ViewNode};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::board::{ATT, AUTO, Board, Coord, Decision, Move, REP, VAC};
use crate::game::{
    AutomataflGame, CELLS, COMMIT, MatchState, N, RESOLVE, REVEAL, SELECT, coord_of, goal_owner_at,
    goals, goals_of, index_of, opening_board,
};
use crate::rules;

/// The default match seed when a [`SessionConfig`] pins none.
const DEFAULT_SEED: u64 = 0xA07F;

/// A match runs at most this many resolved turns before it is called a draw (the surface's own
/// clock — the executor is happy to keep going).
const MAX_TURNS: u64 = 64;

/// A seat at the table (automatafl is n=2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seat {
    /// Seat A — the two `y = 0` goal corners (see [`Seat::goals`]).
    A,
    /// Seat B — the two `y = 10` goal corners.
    B,
}

impl Seat {
    /// The seat's index (`0` / `1`).
    pub fn idx(self) -> usize {
        match self {
            Seat::A => 0,
            Seat::B => 1,
        }
    }

    /// The other seat.
    pub fn other(self) -> Seat {
        match self {
            Seat::A => Seat::B,
            Seat::B => Seat::A,
        }
    }

    /// The seat's TWO goal corners — the automaton arriving on either wins the match for them
    /// (the stock two-player rule: each player owns the two corners in one row). Sourced from the
    /// LEAN `stockGoals2` via [`goals_of`].
    ///
    /// Empty only if the game oracle cannot answer, which no live session can reach: a session
    /// exists only because [`opening_board`] already got an answer out of it
    /// (`AutomataflOffering::open`). Painting NO corners is the honest degrade — it never paints a
    /// transcribed guess.
    pub fn goals(self) -> Vec<Coord> {
        goals_of(self.idx() as u32).unwrap_or_default()
    }

    /// The seat that owns goal corner `c`, if any (the Lean-sourced goal table).
    pub fn owner_of_goal(c: Coord) -> Option<Seat> {
        goal_owner_at(c).ok().flatten().map(Seat::from_idx)
    }

    /// The seat an index / owner tag (`0`/`1`) names.
    pub fn from_idx(who: u32) -> Seat {
        if who == 0 { Seat::A } else { Seat::B }
    }

    /// The seat's label.
    pub fn label(self) -> &'static str {
        match self {
            Seat::A => "A",
            Seat::B => "B",
        }
    }
}

/// The turn phase — the simultaneous-move shape, as a state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Both seats are sealing a move (select → commit).
    Commit,
    /// Both moves are sealed; each seat opens its commitment.
    Reveal,
    /// Both moves are open; the resolution is one real turn away.
    Resolve,
    /// The match is decided (a goal reached, or the clock ran out).
    Over,
}

/// **What the automaton DID on the last resolution, and why.**
///
/// The daemon's step is the whole mechanic and it used to happen INVISIBLY: the board simply
/// differed between two renders and the reader was left to diff it by eye. Recorded on a LANDED
/// resolution only (a refused one restores the previous record — anti-ghost) and read back by
/// [`AutomataflSession::last_step`].
#[derive(Clone, Debug)]
pub struct AutoStep {
    /// The resolved-turn number this step belongs to (the turn that had just fired).
    pub turn_no: u64,
    /// Where the automaton stood BEFORE the step — i.e. after the players' moves landed
    /// ([`resolve_mid`]), which is the board it actually senses.
    pub from: Coord,
    /// Where it stood after. Equal to `from` when it held.
    pub to: Coord,
    /// The plain-language reading of the pull that decided it.
    pub why: String,
}

/// The on-screen word for a one-step offset. The board is painted row-major with `y = 0` at the
/// TOP (seat A's goal row), so `+y` is DOWN the screen.
fn dir_word(off: Coord) -> &'static str {
    match off {
        (dx, _) if dx > 0 => "right",
        (dx, _) if dx < 0 => "left",
        (_, dy) if dy > 0 => "down",
        (_, dy) if dy < 0 => "up",
        _ => "nowhere",
    }
}

/// `1 square` / `3 squares`.
fn squares(d: usize) -> String {
    if d == 1 {
        "1 square".to_string()
    } else {
        format!("{d} squares")
    }
}

/// **Read one axis's [`Decision`] as a sentence** — WHY that axis pulls the way it does. The variant
/// codes and the distances are the ones the LEAN reported (`1 = towardAttractor, 2 = fromRepulsor,
/// 3 = unbalancedPair`, and the raycast distances the decision was actually taken on), so this is the
/// spec's own reason rendered into English, not a plausible-sounding gloss.
fn decision_why(d: &Decision, axis_x: bool) -> String {
    let (dir, back) = match (axis_x, d.pos) {
        (true, true) => ("right", "left"),
        (true, false) => ("left", "right"),
        (false, true) => ("down", "up"),
        (false, false) => ("up", "down"),
    };
    match d.variant {
        // UnbalancedPair: an attractor ahead and a repulsor behind, both pushing the same way.
        3 => format!(
            "an attractor {} to its {dir} and a repulsor {} to its {back} — both send it {dir}",
            squares(d.att_dist),
            squares(d.rep_dist),
        ),
        // FromRepulsor: the repulsor it is running from is BEHIND it.
        2 => format!(
            "shoved {dir}, away from a repulsor {} to its {back}",
            squares(d.rep_dist.max(1)),
        ),
        // TowardAttractor: the attractor it is going to is AHEAD of it.
        1 => format!(
            "pulled {dir}, toward an attractor {} to its {dir}",
            squares(d.att_dist.max(1)),
        ),
        _ => "nothing pulls it on this axis".to_string(),
    }
}

/// **The automaton's READ of a board** — where it would step next and why, as
/// `(destination, reason)`. `destination == board.auto` means it holds.
///
/// This is PUBLIC information: it is a pure function of the board every viewer already sees, so it
/// is safe on a spectator's surface and leaks nothing about a sealed move.
fn sense_reading(b: &Board) -> (Coord, String) {
    let s = match rules::sense(b) {
        Ok(s) => s,
        // The oracle is the only thing that knows; say so rather than guess. Unreachable in a live
        // session (see `Seat::goals`).
        Err(_) => {
            return (
                b.auto,
                "the game oracle did not answer, so the automaton's read is unknown".to_string(),
            );
        }
    };
    let (ox, oy) = s.offset;
    let target = (b.auto.0 + ox, b.auto.1 + oy);
    let moves = (ox != 0 || oy != 0) && b.in_bounds(target) && b.cell_at(target) == VAC;
    if !moves {
        let why = if ox == 0 && oy == 0 {
            "the two axes pull equally hard, so it holds".to_string()
        } else if !b.in_bounds(target) {
            format!(
                "it leans {} but that is off the board, so it holds",
                dir_word(s.offset)
            )
        } else {
            format!(
                "it leans {} but a piece is standing there, so it holds",
                dir_word(s.offset)
            )
        };
        return (b.auto, why);
    }
    let axis_x = ox != 0;
    let dec = if axis_x { s.x_dec } else { s.y_dec };
    (target, decision_why(&dec, axis_x))
}

/// **The automatafl Offering** — hosts one n=2 match with a per-viewer sealed-move surface.
/// Stateless; the live match lives in [`AutomataflSession`].
pub struct AutomataflOffering;

impl AutomataflOffering {
    /// The canonical seat identity (what a frontend that already knows its seats passes to
    /// [`Offering::render_for`] / [`Offering::advance`]).
    pub fn seat_identity(seat: Seat) -> DreggIdentity {
        match seat {
            Seat::A => DreggIdentity("automatafl:seat-A".to_string()),
            Seat::B => DreggIdentity("automatafl:seat-B".to_string()),
        }
    }
}

/// A live automatafl match: the deployed executor game, the board the Lean oracle is asked about, the
/// two seats, and each seat's SEALED move (the plaintext the opponent cannot see).
pub struct AutomataflSession {
    /// The deployed executor game — every advance commits this state as ONE real verified turn.
    game: AutomataflGame,
    /// The live board; every resolution is computed by the Lean ([`crate::rules::turn`]).
    board: Board,
    /// **The GENESIS position** — the board the match opened on, kept so the played match can be
    /// folded (`AutomataflMatch::played(start, rounds)`); the fold's first leaf declares this as
    /// its IN window and the root exposes it as the decodable `board_genesis`.
    start: Board,
    /// **THE MOVE HISTORY** — every RESOLVED round's two revealed moves, in order. Without this
    /// the surface threw every move away and the only foldable shape left was the automaton-only
    /// chain, which attests K independent automaton steps and NO MOVE AT ALL. With it, a played
    /// match folds through the TWO-LEG (Leg R resolve, Leg A step) chain that actually attests the
    /// players' moves. Pushed on a LANDED resolution only (a refused resolution commits nothing
    /// and records nothing — anti-ghost).
    rounds: Vec<(Move, Move)>,
    /// The seat holders. A seat is CLAIMED by the first identity that acts from it (so a web /
    /// Discord / Telegram user — whose identity is a derived key, not a fixed string — really
    /// sits down). The canonical [`AutomataflOffering::seat_identity`] claims work the same way.
    seats: [Option<DreggIdentity>; 2],
    /// Each seat's selected source square (the highlight anchor).
    sel: [Option<Coord>; 2],
    /// Each seat's SEALED move — the plaintext, held here (fog to the opponent) until the reveal.
    committed: [Option<Move>; 2],
    /// The commitment the executor holds for each seat (`0` = unsealed).
    seal: [u64; 2],
    /// Whether each seat has opened its seal.
    revealed: [bool; 2],
    /// The resolved-turn counter.
    turn_no: u64,
    /// Total sealed commitments / opened seals across the match (the strictly-monotone counters).
    commits: u64,
    reveals: u64,
    /// **The automaton's last step** — what the daemon did on the most recent LANDED resolution,
    /// and the pull that decided it. `None` until the first resolution.
    last_step: Option<AutoStep>,
    /// The winner, once the automaton reaches a goal square.
    winner: Option<Seat>,
    /// Whether the match is over (a winner, or the clock).
    ended: bool,
    /// The match seed (the per-turn commitment nonce is derived from it).
    seed: u64,
    /// The number of committed turns (genesis + every landed advance) — the verify count.
    turns: usize,
}

impl AutomataflSession {
    /// The current phase.
    pub fn phase(&self) -> Phase {
        if self.ended {
            Phase::Over
        } else if self.committed[0].is_none() || self.committed[1].is_none() {
            Phase::Commit
        } else if !self.revealed[0] || !self.revealed[1] {
            Phase::Reveal
        } else {
            Phase::Resolve
        }
    }

    /// Whether the match has ended.
    pub fn ended(&self) -> bool {
        self.ended
    }

    /// The winner, if the automaton has reached a goal.
    pub fn winner(&self) -> Option<Seat> {
        self.winner
    }

    /// The resolved-turn counter.
    pub fn turn_no(&self) -> u64 {
        self.turn_no
    }

    /// **What the automaton did on the last resolution** — the daemon's step and the pull that
    /// decided it. `None` before the first resolution.
    pub fn last_step(&self) -> Option<&AutoStep> {
        self.last_step.as_ref()
    }

    /// **Where the automaton would go if the board did not change** — `(destination, reason)`;
    /// `destination == board().auto` means it would hold. A pure function of the PUBLIC board.
    pub fn automaton_read(&self) -> (Coord, String) {
        sense_reading(&self.board)
    }

    /// The fewest steps the automaton could possibly need to reach `seat`'s nearest goal corner
    /// (Manhattan — it moves one orthogonal square per resolution). `0` = it is standing on one.
    pub fn goal_distance(&self, seat: Seat) -> i32 {
        seat.goals()
            .iter()
            .map(|g| (g.0 - self.board.auto.0).abs() + (g.1 - self.board.auto.1).abs())
            .min()
            .unwrap_or(0)
    }

    /// The reference board (the committed position).
    pub fn board(&self) -> &Board {
        &self.board
    }

    /// **The genesis position** — the board this match opened on (the fold's `board_genesis`).
    pub fn start_board(&self) -> &Board {
        &self.start
    }

    /// **The recorded move history** — each resolved round's `(seat A move, seat B move)`, in
    /// order. This is the object `AutomataflMatch::played(start, rounds)` folds.
    pub fn rounds(&self) -> &[(Move, Move)] {
        &self.rounds
    }

    /// The index of the first recorded round that is NOT clean (a fork on a shared source or a
    /// clash on a shared destination), or `None` when every round folds.
    ///
    /// A conflicting round is refused by the fold ([`round_is_clean`]): the surface resolved it by
    /// DROPPING the clashing moves, which is the audited-WRONG rule — the ruleset marks the
    /// contested square and re-enters the round. Surfacing the index here lets a frontend say
    /// WHICH round blocks the crown instead of reporting an opaque prover failure.
    pub fn unfoldable_round(&self) -> Result<Option<usize>, String> {
        let mut b = self.start.clone();
        for (i, (ma, mb)) in self.rounds.iter().enumerate() {
            if !rules::round_is_clean(&b, &[*ma, *mb])? {
                return Ok(Some(i));
            }
            b = rules::apply_turn(&b, &[*ma, *mb])?;
        }
        Ok(None)
    }

    /// The deployed executor game (read the COMMITTED state off the cell).
    pub fn game(&self) -> &AutomataflGame {
        &self.game
    }

    /// The seat a CANONICAL identity names ([`AutomataflOffering::seat_identity`]), if any.
    fn canonical(who: &DreggIdentity) -> Option<Seat> {
        for seat in [Seat::A, Seat::B] {
            if *who == AutomataflOffering::seat_identity(seat) {
                return Some(seat);
            }
        }
        None
    }

    /// The seat `who` holds: the seat they have claimed, or — if they present a canonical seat
    /// identity for a seat nobody has taken — that seat (so a frontend can render for a seat before
    /// its holder has moved). `None` = a spectator (both sealed moves are fog to them).
    pub fn seat_of(&self, who: &DreggIdentity) -> Option<Seat> {
        for seat in [Seat::A, Seat::B] {
            if self.seats[seat.idx()].as_ref() == Some(who) {
                return Some(seat);
            }
        }
        Self::canonical(who).filter(|s| self.seats[s.idx()].is_none())
    }

    /// **Seat `who` explicitly** (a frontend that already knows who sits where). `false` if the seat
    /// is taken by someone else.
    pub fn sit(&mut self, seat: Seat, who: DreggIdentity) -> bool {
        match &self.seats[seat.idx()] {
            Some(held) if *held != who => false,
            _ => {
                self.seats[seat.idx()] = Some(who);
                true
            }
        }
    }

    /// The seat `who` holds, CLAIMING one if they hold none: their canonical seat if they present
    /// one and it is free, else the first free seat (A, then B). `None` when both seats are taken by
    /// other identities (a spectator).
    /// **The seat a not-yet-seated viewer would claim on their first accepted move** — the
    /// read-only half of [`claim_seat`](Self::claim_seat), which is the mutating one. `None` once
    /// both seats are held (that viewer is a spectator). Rendering never reserves a seat.
    pub fn claimable_seat(&self) -> Option<Seat> {
        [Seat::A, Seat::B]
            .into_iter()
            .find(|seat| self.seats[seat.idx()].is_none())
    }

    /// **Whether `seat` still owes a move in the CURRENT phase.** The whole simultaneous-move
    /// wound in one predicate: in `Phase::Reveal` the seat that already opened owes nothing while
    /// the one that never opened owes the reveal, so a host with a clock can tell WHICH seat
    /// walked away instead of guessing or blaming both. Pure — reads the phase and that seat's own
    /// commit/reveal flags, nothing else.
    pub fn owes_a_move(&self, seat: Seat) -> bool {
        if self.ended {
            return false;
        }
        let i = seat.idx();
        match self.phase() {
            Phase::Commit => self.committed[i].is_none(),
            Phase::Reveal => !self.revealed[i],
            // Either seat may fire the resolution, so both owe it: a table left sitting in
            // `Resolve` was abandoned by both, and recording that as a double abandonment is
            // honest where blaming one of them would be arbitrary.
            Phase::Resolve => true,
            Phase::Over => false,
        }
    }

    fn claim_seat(&mut self, who: &DreggIdentity) -> Option<Seat> {
        for seat in [Seat::A, Seat::B] {
            if self.seats[seat.idx()].as_ref() == Some(who) {
                return Some(seat);
            }
        }
        if let Some(s) = Self::canonical(who) {
            if self.seats[s.idx()].is_none() {
                self.seats[s.idx()] = Some(who.clone());
                return Some(s);
            }
        }
        for seat in [Seat::A, Seat::B] {
            if self.seats[seat.idx()].is_none() {
                self.seats[seat.idx()] = Some(who.clone());
                return Some(seat);
            }
        }
        None
    }

    /// The per-turn, per-seat commitment nonce (deterministic in the match seed — a real blind, so
    /// the seal does not leak the move by brute-forcing the tiny move space).
    fn nonce(&self, seat: Seat) -> u64 {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-automatafl/seal-nonce");
        h.update(&self.seed.to_le_bytes());
        h.update(&self.turn_no.to_le_bytes());
        h.update(&[seat.idx() as u8]);
        u64::from_le_bytes(h.finalize().as_bytes()[..8].try_into().unwrap()) >> 1
    }

    /// The COMMITMENT a seat's move seals to — `blake3(turn ‖ seat ‖ from ‖ to ‖ nonce)`, truncated
    /// into the field. The executor holds this; the plaintext stays in the session until the reveal.
    fn seal_of(&self, seat: Seat, mv: &Move) -> u64 {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-automatafl/seal");
        h.update(&self.turn_no.to_le_bytes());
        h.update(&[seat.idx() as u8]);
        h.update(&(index_of(mv.frm).unwrap_or(0) as u64).to_le_bytes());
        h.update(&(index_of(mv.to).unwrap_or(0) as u64).to_le_bytes());
        h.update(&self.nonce(seat).to_le_bytes());
        // `>> 1` keeps it comfortably inside the field's u64 range.
        (u64::from_le_bytes(h.finalize().as_bytes()[..8].try_into().unwrap()) >> 1).max(1)
    }

    /// The full witnessed state the next turn commits.
    fn state(&self) -> MatchState {
        let phase = match self.phase() {
            Phase::Commit => 0,
            Phase::Reveal | Phase::Resolve => 1,
            Phase::Over => 2,
        };
        let idx1 = |c: Option<Coord>| c.and_then(index_of).map(|i| i as u64 + 1).unwrap_or(0);
        let revealed_frm = |s: Seat| {
            if self.revealed[s.idx()] {
                idx1(self.committed[s.idx()].map(|m| m.frm))
            } else {
                0
            }
        };
        let revealed_to = |s: Seat| {
            if self.revealed[s.idx()] {
                idx1(self.committed[s.idx()].map(|m| m.to))
            } else {
                0
            }
        };
        MatchState {
            turn_no: self.turn_no,
            phase,
            winner: self.winner.map(|s| s.idx() as u64 + 1).unwrap_or(0),
            commits: self.commits,
            reveals: self.reveals,
            commit: self.seal,
            sel: [idx1(self.sel[0]), idx1(self.sel[1])],
            frm: [revealed_frm(Seat::A), revealed_frm(Seat::B)],
            to: [revealed_to(Seat::A), revealed_to(Seat::B)],
            auto: self.board.auto,
            cells: self.board.cells.clone(),
        }
    }

    /// The LEGAL TARGETS of `src` — the set the LEAN admits (`AutomataflRules.moveLegalB` over the
    /// board: same row or column, distinct, in-bounds, and never the automaton as a SOURCE). The
    /// highlight-set the board paints.
    ///
    /// ⚑ Naming the automaton's square as a DESTINATION is legal to propose and then FAILS to execute
    /// (ruling D + the inclusive path check), so it is in this set. The old Rust `move_valid` banned
    /// it, which is `logic/src/game.rs`'s reading rather than the README's.
    ///
    /// Empty when the oracle cannot answer — no affordance is offered for a move nobody can
    /// adjudicate, and `advance` re-asks before it commits anything.
    pub fn legal_targets(&self, src: Coord) -> Vec<Coord> {
        rules::legal_targets(&self.board, &[], 0, src).unwrap_or_default()
    }

    /// Whether `src` is a square a seat may move: a real (non-vacuum) particle that is not the
    /// automaton. (Automatafl's pieces are SHARED — either seat may push any piece; that is what
    /// makes the simultaneous conflict resolution the heart of the game.)
    pub fn movable(&self, src: Coord) -> bool {
        let p = self.board.cell_at(src);
        p != VAC && p != AUTO
    }

    /// The glyph a particle paints in the board grid.
    fn glyph(p: u8) -> &'static str {
        match p {
            REP => "R",
            ATT => "A",
            AUTO => "@",
            _ => "·",
        }
    }

    /// **The board as a [`ViewNode::CoordGrid`]** — one cell per square, painted for `viewer`.
    ///
    /// * the automaton square is marked (`@`, tag `accent`, in the highlight-set);
    /// * the viewer's SELECTED source is tagged `warn` and highlighted;
    /// * every LEGAL target of that source is tagged `good` and highlighted, and carries the
    ///   `{turn: "commit", arg: index}` affordance a click fires (the rook-line highlighting);
    /// * a movable piece carries `{turn: "select", arg: index}` while the viewer has not sealed;
    /// * once the VIEWER has sealed, the stale rook line is dropped and their own move is painted
    ///   instead: the source `warn`, the destination `sealed`. Per-viewer, out of the viewer's own
    ///   slot only — a spectator and the opponent see neither square marked;
    /// * everything else is inert (empty `turn`) and NOT highlighted — a diagonal square, the
    ///   source itself, an out-of-line square: no highlight, no affordance.
    ///
    /// With NO viewer (the public surface a catalog frontend paints) the grid stays PLAYABLE: the
    /// selections are public state anyway (the executor holds `a_sel` / `b_sel` in the clear — the
    /// SECRET is the sealed DESTINATION, not which piece you are eyeing), so the public board lights
    /// the union of both live selections and offers the same affordances. `advance` resolves a
    /// `commit` against the ACTOR's own selection, so the affordance means the same thing to both.
    fn board_grid(&self, viewer: Option<Seat>) -> ViewNode {
        let selections: Vec<Coord> = match viewer {
            Some(s) => self.sel[s.idx()].into_iter().collect(),
            None => self.sel.iter().flatten().copied().collect(),
        };
        // **THE VIEWER'S OWN SEALED MOVE, ON THE BOARD.** Strictly per-viewer: read ONLY out of
        // `viewer`'s OWN slot, so a spectator (`None`) and the opponent get nothing here — the fog
        // is untouched. Once a seat HAS sealed, its rook-line highlight is stale (there is no
        // affordance left on those squares) and painting it lies about what is pending; the two
        // squares that matter are the piece it sealed and where it sealed it TO.
        let own_sealed: Option<Move> = viewer.and_then(|s| self.committed[s.idx()]);
        let mut targets: Vec<Coord> = Vec::new();
        if own_sealed.is_none() {
            for &src in &selections {
                for t in self.legal_targets(src) {
                    if !targets.contains(&t) {
                        targets.push(t);
                    }
                }
            }
        }
        // Can a click still seal? Per-viewer: only while THAT seat is unsealed. Publicly: while
        // either seat is unsealed.
        let sealed = match viewer {
            Some(s) => self.committed[s.idx()].is_some(),
            None => self.committed[0].is_some() && self.committed[1].is_some(),
        };
        let playable = !self.ended && matches!(self.phase(), Phase::Commit);

        let mut cells = Vec::with_capacity(CELLS);
        for idx in 0..CELLS {
            let c = coord_of(idx);
            let p = self.board.cell_at(c);
            let is_auto = c == self.board.auto;
            let is_selected = selections.contains(&c);
            let is_target = targets.contains(&c);

            let is_goal = Seat::owner_of_goal(c).is_some();

            let (tag, highlight) = if is_auto {
                ("accent", true)
            } else if own_sealed.map(|m| m.to) == Some(c) {
                // WHERE YOU SEALED IT TO — its own treatment, and only ever on its own seat's
                // surface.
                ("sealed", true)
            } else if own_sealed.map(|m| m.frm) == Some(c) {
                ("warn", true)
            } else if is_selected {
                ("warn", true)
            } else if is_target {
                ("good", true)
            } else if is_goal {
                // THE OBJECTIVE RING on an OCCUPIED goal corner. A vacant one is already legible by
                // its `a`/`b` glyph, but the stock opening starts with a repulsor on all four
                // corners — without this the four squares that decide the game would paint as
                // ordinary pieces, and a stranger could not see where the automaton must be driven.
                ("goal", false)
            } else if p == VAC {
                ("muted", false)
            } else {
                ("", false)
            };

            // The affordance: a legal target commits; a movable piece selects (while unsealed).
            let (turn, arg) = if playable && !sealed && is_target {
                (COMMIT.to_string(), idx as i64)
            } else if playable && !sealed && self.movable(c) {
                (SELECT.to_string(), idx as i64)
            } else {
                (String::new(), idx as i64)
            };

            // A VACANT goal corner paints its owner's lowercase letter (`a` / `b`) — the four
            // stock corners, two per seat. An OCCUPIED corner keeps its particle glyph and is
            // marked by the `goal` tag above.
            let mut glyph = Self::glyph(p).to_string();
            if p == VAC && is_goal {
                glyph = Seat::owner_of_goal(c)
                    .expect("is_goal")
                    .label()
                    .to_lowercase();
            }

            cells.push(CoordCell {
                glyph,
                tag: tag.to_string(),
                turn,
                arg,
                highlight,
            });
        }
        ViewNode::CoordGrid { cols: N, cells }
    }

    /// The seat's move line — REVEALED to its owner, FOG to everyone else until the open.
    fn move_line(&self, seat: Seat, viewer: Option<Seat>) -> ViewNode {
        let own = viewer == Some(seat);
        let title = format!(
            "Seat {} — {}",
            seat.label(),
            if own { "you" } else { "them" }
        );
        let body = match (self.committed[seat.idx()], self.revealed[seat.idx()]) {
            (None, _) => {
                let s = self.sel[seat.idx()];
                if own {
                    match s {
                        Some(c) => format!("selected ({},{}) — pick a destination", c.0, c.1),
                        None => "no move sealed — select one of your pieces".to_string(),
                    }
                } else {
                    "thinking… (no move sealed yet)".to_string()
                }
            }
            (Some(mv), false) if own => format!(
                "YOUR sealed move: ({},{}) → ({},{}) · seal {:x}… (the opponent sees only the seal)",
                mv.frm.0,
                mv.frm.1,
                mv.to.0,
                mv.to.1,
                self.seal[seat.idx()] >> 40
            ),
            (Some(_), false) => format!(
                "move SEALED · commitment {:x}… (hidden — revealed on the open)",
                self.seal[seat.idx()] >> 40
            ),
            (Some(mv), true) => format!(
                "revealed: ({},{}) → ({},{})",
                mv.frm.0, mv.frm.1, mv.to.0, mv.to.1
            ),
        };
        ViewNode::Section {
            title,
            tag: if own { "accent".into() } else { String::new() },
            children: vec![ViewNode::Text(body)],
        }
    }

    /// The action MENU — `reveal` / `resolve`, greyed (`enabled=false`) outside their phase (the
    /// tooth SHOWN, never hidden; the executor is still the referee on `advance`).
    fn action_menu(&self, viewer: Option<Seat>) -> ViewNode {
        let phase = self.phase();
        // Per-viewer: only while THIS seat is unopened. Publicly (the catalog surface): while EITHER
        // seat is unopened — the executor refuses a double reveal, so the control is honest.
        let can_reveal = matches!(phase, Phase::Reveal)
            && match viewer {
                Some(s) => !self.revealed[s.idx()],
                None => !self.revealed[0] || !self.revealed[1],
            };
        let items = vec![
            MenuItem {
                label: "Reveal your sealed move".to_string(),
                turn: REVEAL.to_string(),
                arg: 0,
                enabled: can_reveal,
            },
            MenuItem {
                label: "Resolve the turn (conflicts drop · the automaton steps)".to_string(),
                turn: RESOLVE.to_string(),
                arg: 0,
                enabled: matches!(phase, Phase::Resolve),
            },
        ];
        ViewNode::Menu { items }
    }

    /// **THE ONE SENTENCE that says what to do now.** The single largest legibility win on a
    /// simultaneous-move board: without it the reader has to infer the phase, then infer whether
    /// they are the one being waited on, then infer which control fires.
    ///
    /// Per-viewer, and it discloses NOTHING a viewer may not see: the only facts it reads about the
    /// OTHER seat are `has sealed` / `has opened`, both of which are already public (the executor
    /// holds the commitment and the reveal counters in the clear). Never the move.
    fn next_step_line(&self, viewer: Option<Seat>) -> String {
        if let Some(w) = self.winner {
            let mine = viewer == Some(w);
            return format!(
                "The match is over: the automaton reached seat {}'s goal corner. {}",
                w.label(),
                if viewer.is_none() {
                    format!("Seat {} wins.", w.label())
                } else if mine {
                    "You win.".to_string()
                } else {
                    "You lose.".to_string()
                }
            );
        }
        if self.ended {
            return "The match is over: the clock ran out with the automaton on nobody's corner — \
                    a draw."
                .to_string();
        }
        let Some(s) = viewer else {
            // The spectator's line — the same facts, in the third person.
            return match self.phase() {
                Phase::Commit => {
                    let waiting: Vec<&str> = [Seat::A, Seat::B]
                        .iter()
                        .filter(|s| self.committed[s.idx()].is_none())
                        .map(|s| s.label())
                        .collect();
                    format!(
                        "Both seats are sealing a move at the same time. Still to seal: {}.",
                        waiting.join(" and ")
                    )
                }
                Phase::Reveal => {
                    "Both moves are sealed. Each seat now opens its own seal.".to_string()
                }
                Phase::Resolve => {
                    "Both moves are open — the turn is one press from firing.".to_string()
                }
                Phase::Over => "The match is over.".to_string(),
            };
        };
        let i = s.idx();
        let other = s.other();
        match self.phase() {
            Phase::Commit if self.committed[i].is_some() => format!(
                "Sealed. Waiting for seat {} to seal — this page updates by itself, so there is \
                 nothing to reload.",
                other.label()
            ),
            Phase::Commit if self.sel[i].is_some() => {
                "Your piece is picked up. Click one of the GLOWING squares to seal a move there — \
                 the other seat cannot see where you sealed until you both open."
                    .to_string()
            }
            Phase::Commit => {
                "YOUR MOVE. Click any piece to pick it up; its rook line lights up, and clicking a \
                 lit square seals a move there. Both seats move at once, so nothing happens on the \
                 board until you have both sealed."
                    .to_string()
            }
            Phase::Reveal if !self.revealed[i] => {
                "Both moves are sealed. Press Reveal your sealed move to open yours.".to_string()
            }
            Phase::Reveal => format!(
                "You have opened. Waiting for seat {} to open theirs.",
                other.label()
            ),
            Phase::Resolve => "Both moves are open. Press Resolve the turn — conflicting moves \
                               drop, the survivors apply, and THEN the automaton takes its step."
                .to_string(),
            Phase::Over => "The match is over.".to_string(),
        }
    }

    /// **"Where the turn stands"** — the status plaque: which of the three phases is live, who you
    /// are at this table, whether each seat has sealed / opened, and the one sentence that says
    /// what to do now.
    fn standing(&self, viewer: Option<Seat>) -> ViewNode {
        let phase = self.phase();
        let phase_pill = |p: Phase, label: &str| ViewNode::Pill {
            text: label.to_string(),
            tag: if p == phase { "good" } else { "muted" }.to_string(),
            slot: None,
            cases: Vec::<PillCase>::new(),
        };
        // A seat's PUBLIC standing this turn (never its move): choosing → sealed → opened.
        let seat_pill = |s: Seat| {
            let i = s.idx();
            let (word, tag) = if self.revealed[i] {
                ("opened", "good")
            } else if self.committed[i].is_some() {
                ("sealed", "accent")
            } else {
                ("still choosing", "warn")
            };
            let whose = match viewer {
                Some(v) if v == s => " (you)",
                Some(_) => " (them)",
                None => "",
            };
            ViewNode::Pill {
                text: format!("seat {}{whose} · {word}", s.label()),
                tag: tag.to_string(),
                slot: None,
                cases: Vec::<PillCase>::new(),
            }
        };
        let who = match viewer {
            Some(s) => format!(
                "You hold seat {} — your goal corners are {}.",
                s.label(),
                Self::goal_text(s)
            ),
            None => "You are watching this table: BOTH sealed moves are fog to you, and every \
                     control is inert."
                .to_string(),
        };
        ViewNode::Section {
            title: "Where the turn stands".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Row(vec![
                    phase_pill(Phase::Commit, "1 · SEAL"),
                    phase_pill(Phase::Reveal, "2 · OPEN"),
                    phase_pill(Phase::Resolve, "3 · RESOLVE"),
                ]),
                ViewNode::Text(self.next_step_line(viewer)),
                ViewNode::Row(vec![seat_pill(Seat::A), seat_pill(Seat::B)]),
                ViewNode::Text(who),
            ],
        }
    }

    /// **"The automaton"** — the plaque for the piece that decides the match and that neither
    /// player owns. It answers the two questions the board alone cannot: what did it just do and
    /// WHY, and — since the read is a pure function of the public board — where it would go next
    /// if nobody moved. Both are public; nothing here is per-viewer.
    fn automaton_plaque(&self) -> ViewNode {
        let auto = self.board.auto;
        let mut kids = vec![ViewNode::Text(format!(
            "The automaton stands at ({},{}). Nobody moves it directly — it answers the attractors \
             and repulsors around it, one square per resolution, and whoever's corner it reaches \
             wins the match.",
            auto.0, auto.1
        ))];
        kids.push(ViewNode::Text(match &self.last_step {
            None => "It has not stepped yet — the first resolution is its first step.".to_string(),
            Some(s) if s.from == s.to => format!(
                "Last turn (turn {}) it HELD at ({},{}) — {}.",
                s.turn_no, s.from.0, s.from.1, s.why
            ),
            Some(s) => format!(
                "Last turn (turn {}) it stepped from ({},{}) onto ({},{}) — {}.",
                s.turn_no, s.from.0, s.from.1, s.to.0, s.to.1, s.why
            ),
        }));
        if !self.ended {
            let (target, why) = self.automaton_read();
            kids.push(ViewNode::Text(if target == auto {
                format!("If nothing moved it would HOLD — {why}.")
            } else {
                format!(
                    "If nothing moved it would step onto ({},{}) — {why}.",
                    target.0, target.1
                )
            }));
        }
        // HOW CLOSE IS IT TO ENDING THE MATCH. `1` means the very next resolution can decide it.
        let dist_pill = |s: Seat| {
            let d = self.goal_distance(s);
            let (word, tag) = match d {
                0 => ("ON a goal corner".to_string(), "bad"),
                1 => ("1 step from a goal".to_string(), "bad"),
                2..=3 => (format!("{d} steps from a goal"), "warn"),
                _ => (format!("{d} steps from a goal"), ""),
            };
            ViewNode::Pill {
                text: format!("seat {} · {word}", s.label()),
                tag: tag.to_string(),
                slot: None,
                cases: Vec::<PillCase>::new(),
            }
        };
        kids.push(ViewNode::Row(vec![dist_pill(Seat::A), dist_pill(Seat::B)]));
        ViewNode::Section {
            title: "The automaton".to_string(),
            tag: "accent".to_string(),
            children: kids,
        }
    }

    /// A seat's two goal corners, rendered (`(0,0)·(10,0)`).
    fn goal_text(seat: Seat) -> String {
        seat.goals()
            .iter()
            .map(|c| format!("({},{})", c.0, c.1))
            .collect::<Vec<_>>()
            .join("·")
    }

    /// The surface for `viewer` (`None` = a spectator: BOTH sealed moves are fog).
    fn surface_for(&self, viewer: Option<Seat>) -> Surface {
        let phase = self.phase();
        let headline = match (self.winner, self.ended) {
            (Some(w), _) => format!(
                "Automatafl — the automaton reached seat {}'s goal · WINNER: {}",
                w.label(),
                w.label()
            ),
            (None, true) => "Automatafl — the clock ran out (a draw)".to_string(),
            (None, false) => format!(
                "Automatafl — turn {} · phase: {}",
                self.turn_no,
                match phase {
                    Phase::Commit => "COMMIT (both seats seal a move)",
                    Phase::Reveal => "REVEAL (both moves sealed — open yours)",
                    Phase::Resolve => "RESOLVE (both open — fire the turn)",
                    Phase::Over => "over",
                }
            ),
        };
        let mut kids = vec![
            ViewNode::Text(headline),
            ViewNode::Row(vec![
                ViewNode::Pill {
                    text: format!("automaton ({},{})", self.board.auto.0, self.board.auto.1),
                    tag: "accent".to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
                ViewNode::Pill {
                    text: format!("goals A {}", Self::goal_text(Seat::A)),
                    tag: "good".to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
                ViewNode::Pill {
                    text: format!("goals B {}", Self::goal_text(Seat::B)),
                    tag: "good".to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
            ]),
            self.standing(viewer),
            ViewNode::Section {
                title: "The board".to_string(),
                tag: String::new(),
                children: vec![
                    ViewNode::Text(
                        "Attractors (A) are the round brass discs; repulsors (R) are the angular \
                         pale blades; the automaton (@) is the violet ring; the four brass corners \
                         are the goals (a/b). Click a piece to pick it up — its rook line lights \
                         up, and clicking a lit square seals a move there."
                            .to_string(),
                    ),
                    self.board_grid(viewer),
                ],
            },
            self.automaton_plaque(),
        ];
        kids.push(self.move_line(Seat::A, viewer));
        kids.push(self.move_line(Seat::B, viewer));
        kids.push(self.action_menu(viewer));
        Surface(ViewNode::VStack(kids))
    }
}

/// The reason an advance was refused (an honest executor-level / offering-level refusal — nothing
/// commits either way).
fn refuse(why: impl Into<String>) -> Outcome {
    Outcome::Refused(why.into())
}

impl Offering for AutomataflOffering {
    type Session = AutomataflSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(DEFAULT_SEED);
        let game =
            AutomataflGame::deploy(seed as u8).map_err(|e| OfferingError::Deploy(e.to_string()))?;
        let board = opening_board().map_err(OfferingError::Deploy)?;
        let session = AutomataflSession {
            game,
            start: board.clone(),
            board,
            rounds: Vec::new(),
            seats: [None, None],
            sel: [None, None],
            committed: [None, None],
            seal: [0, 0],
            revealed: [false, false],
            turn_no: 0,
            commits: 0,
            reveals: 0,
            last_step: None,
            winner: None,
            ended: false,
            seed,
            turns: 1, // the genesis turn
        };
        // Seed the opening position as the genesis turn (the `old` value every relational tooth
        // reads).
        session
            .game
            .seed(&session.state())
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        Ok(session)
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        if session.ended {
            return Vec::new();
        }
        let phase = session.phase();
        let mut out = Vec::new();
        if matches!(phase, Phase::Commit) {
            // ORDER MATTERS on a button-budgeted frontend. The Discord/Telegram renderers paint
            // the first ≤25 actions as buttons and silently drop the rest; at 11×11 the stock
            // opening has 36 movable pieces, so putting the SEAL targets after every select left
            // a Discord player able to select a piece and never able to seal it. The live
            // selection's targets therefore come FIRST (the affordance the phase is waiting on),
            // then the selects. The WEB board is unaffected either way: every square of the
            // `CoordGrid` is its own POST form, so the browser never reads this list.
            //
            // One `commit` affordance per legal target of EITHER seat's live selection (a seat's
            // own board grid shows only its own; the executor re-checks the seat on advance).
            let mut targets: Vec<usize> = Vec::new();
            for seat in [Seat::A, Seat::B] {
                if let Some(src) = session.sel[seat.idx()] {
                    for t in session.legal_targets(src) {
                        if let Some(i) = index_of(t) {
                            if !targets.contains(&i) {
                                targets.push(i);
                            }
                        }
                    }
                }
            }
            targets.sort_unstable();
            for idx in targets {
                let c = coord_of(idx);
                out.push(Action::new(
                    format!("Seal a move to ({},{})", c.0, c.1),
                    COMMIT,
                    idx as i64,
                    true,
                ));
            }
            // One `select` affordance per movable piece (the board grid paints the same
            // `{turn, arg}` per square).
            for idx in 0..CELLS {
                let c = coord_of(idx);
                if session.movable(c) {
                    out.push(Action::new(
                        format!("Select ({},{})", c.0, c.1),
                        SELECT,
                        idx as i64,
                        true,
                    ));
                }
            }
        }
        out.push(Action::new(
            "Reveal your sealed move",
            REVEAL,
            0,
            matches!(phase, Phase::Reveal),
        ));
        out.push(Action::new(
            "Resolve the turn",
            RESOLVE,
            0,
            matches!(phase, Phase::Resolve),
        ));
        out
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        if session.ended {
            return refuse("the match is already decided");
        }
        // A seat is claimed by the first identity that acts from it (so a web/Discord/Telegram user
        // really sits down); a third identity is a spectator and is refused.
        let Some(seat) = session.claim_seat(&actor) else {
            return refuse("both seats are taken — you are a spectator");
        };
        let i = seat.idx();

        match input.turn.as_str() {
            SELECT => {
                if !matches!(session.phase(), Phase::Commit) {
                    return refuse("the commit phase is closed this turn");
                }
                if session.committed[i].is_some() {
                    return refuse("your move is already sealed this turn");
                }
                let Some(idx) = usize::try_from(input.arg).ok().filter(|&i| i < CELLS) else {
                    return refuse(format!("square {} is off the board", input.arg));
                };
                let c = coord_of(idx);
                if !session.movable(c) {
                    return refuse(format!(
                        "({},{}) holds no movable piece (a vacuum square, or the automaton)",
                        c.0, c.1
                    ));
                }
                let prev = session.sel[i];
                session.sel[i] = Some(c);
                match session.game.commit_state(SELECT, &session.state()) {
                    Ok(receipt) => {
                        session.turns += 1;
                        Outcome::Landed {
                            receipt,
                            ended: false,
                        }
                    }
                    Err(e) => {
                        session.sel[i] = prev; // nothing committed — roll the surface back
                        refuse(e.to_string())
                    }
                }
            }

            COMMIT => {
                if !matches!(session.phase(), Phase::Commit) {
                    return refuse("the commit phase is closed this turn");
                }
                if session.committed[i].is_some() {
                    return refuse("your move is already sealed this turn");
                }
                let Some(frm) = session.sel[i] else {
                    return refuse("select one of your pieces first");
                };
                let Some(idx) = usize::try_from(input.arg).ok().filter(|&i| i < CELLS) else {
                    return refuse(format!("square {} is off the board", input.arg));
                };
                let to = coord_of(idx);
                let mv = Move {
                    who: i as u32,
                    frm,
                    to,
                };
                // THE LEGALITY TOOTH — the LEAN's `moveLegalB` (rook-line, distinct, in-bounds,
                // and the automaton is banned as a SOURCE). An illegal move commits NOTHING, and a
                // move nobody can adjudicate commits nothing either.
                match rules::move_legal(&session.board, &[], &mv) {
                    Ok(true) => {}
                    Ok(false) => {
                        return refuse(format!(
                            "illegal move ({},{}) → ({},{}): a move is a rook line to a distinct \
                             in-bounds square, and never moves the automaton itself",
                            frm.0, frm.1, to.0, to.1
                        ));
                    }
                    Err(why) => {
                        return refuse(format!(
                            "the game oracle could not adjudicate ({},{}) → ({},{}): {why}",
                            frm.0, frm.1, to.0, to.1
                        ));
                    }
                }
                let seal = session.seal_of(seat, &mv);
                session.committed[i] = Some(mv);
                session.seal[i] = seal;
                session.commits += 1;
                match session.game.commit_state(COMMIT, &session.state()) {
                    Ok(receipt) => {
                        session.turns += 1;
                        Outcome::Landed {
                            receipt,
                            ended: false,
                        }
                    }
                    Err(e) => {
                        session.committed[i] = None;
                        session.seal[i] = 0;
                        session.commits -= 1;
                        refuse(e.to_string())
                    }
                }
            }

            REVEAL => {
                if !matches!(session.phase(), Phase::Reveal) {
                    return refuse("both moves must be sealed before a reveal");
                }
                if session.revealed[i] {
                    return refuse("you already revealed this turn");
                }
                let mv = session.committed[i].expect("the reveal phase implies a sealed move");
                // The opened plaintext must be the one the seal binds (the commitment tooth).
                if session.seal_of(seat, &mv) != session.seal[i] {
                    return refuse("the revealed move does not open the sealed commitment");
                }
                session.revealed[i] = true;
                session.reveals += 1;
                match session.game.commit_state(REVEAL, &session.state()) {
                    Ok(receipt) => {
                        session.turns += 1;
                        Outcome::Landed {
                            receipt,
                            ended: false,
                        }
                    }
                    Err(e) => {
                        session.revealed[i] = false;
                        session.reveals -= 1;
                        refuse(e.to_string())
                    }
                }
            }

            RESOLVE => {
                if !matches!(session.phase(), Phase::Resolve) {
                    return refuse("both seats must reveal before the turn resolves");
                }
                let ma = session.committed[0].expect("sealed");
                let mb = session.committed[1].expect("sealed");
                // THE RESOLUTION AND THE WIN, BOTH FROM THE LEAN — `roundStep`'s clean-round arm:
                // legality filter → conflict check → resolve → the automaton's step → the win
                // checked ON ENTRY (`winOnEntry`: the automaton must have MOVED into a goal, not
                // merely be sitting on one). This is the object the AIR is refined against.
                let stock_goals = match goals() {
                    Ok(g) => g,
                    Err(why) => {
                        return refuse(format!("the goal assignment is unavailable: {why}"));
                    }
                };
                let (next, win) = match rules::turn(&session.board, &[], &[ma, mb], stock_goals) {
                    Ok(pair) => pair,
                    Err(why) => {
                        return refuse(format!(
                            "the game oracle could not resolve the turn: {why}"
                        ));
                    }
                };
                // THE DAEMON'S STEP, RECORDED. The turn is `automatonStepCfg ∘ resolveMoves`, so the
                // board the automaton actually senses is the MID board (the players' moves already
                // applied) — read it there, exactly once, and keep the reading for the surface. The
                // step used to leave no trace at all: the reader saw two boards and had to diff.
                let mid = match rules::resolve_mid(&session.board, &[], &[ma, mb]) {
                    Ok(m) => m,
                    Err(why) => {
                        return refuse(format!(
                            "the game oracle could not resolve the moves: {why}"
                        ));
                    }
                };
                let (auto_to, auto_why) = sense_reading(&mid);
                let step = AutoStep {
                    turn_no: session.turn_no,
                    from: mid.auto,
                    to: auto_to,
                    why: auto_why,
                };
                let winner = win.map(Seat::from_idx);

                let before = (
                    session.board.clone(),
                    session.sel,
                    session.committed,
                    session.seal,
                    session.revealed,
                    session.turn_no,
                    session.last_step.clone(),
                );
                session.last_step = Some(step);
                session.board = next;
                session.turn_no += 1;
                session.sel = [None, None];
                session.committed = [None, None];
                session.seal = [0, 0];
                session.revealed = [false, false];
                session.winner = winner;
                session.ended = winner.is_some() || session.turn_no >= MAX_TURNS;
                // RECORD THE ROUND — the two revealed moves, in seat order, appended only once
                // the executor accepts the resolution below (a refused resolution pops it).
                session.rounds.push((ma, mb));

                match session.game.commit_state(RESOLVE, &session.state()) {
                    Ok(receipt) => {
                        session.turns += 1;
                        Outcome::Landed {
                            receipt,
                            ended: session.ended,
                        }
                    }
                    Err(e) => {
                        // Nothing committed — restore the pre-resolution surface (anti-ghost),
                        // INCLUDING the move history: an unlanded round is not a played round.
                        session.board = before.0;
                        session.sel = before.1;
                        session.committed = before.2;
                        session.seal = before.3;
                        session.revealed = before.4;
                        session.turn_no = before.5;
                        session.last_step = before.6;
                        session.winner = None;
                        session.ended = false;
                        session.rounds.pop();
                        refuse(e.to_string())
                    }
                }
            }

            other => refuse(format!("unknown action method `{other}`")),
        }
    }

    /// Re-verify the committed match: the executor's COMMITTED board must be exactly the board the
    /// LEAN oracle resolved (the substrate reproduces the game the ruleset describes), every square must
    /// hold a real particle code, and there must be exactly one automaton, where the state says it is.
    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let committed = session.game.read_state();
        let turns = session.turns;
        if committed.cells != session.board.cells {
            return VerifyReport::broken(turns, "the committed board diverged from the ruleset");
        }
        if committed.auto != session.board.auto {
            return VerifyReport::broken(turns, "the committed automaton coordinate diverged");
        }
        if committed.cells.iter().any(|&p| p > AUTO) {
            return VerifyReport::broken(turns, "a committed square holds no real particle");
        }
        let autos = committed.cells.iter().filter(|&&p| p == AUTO).count();
        if autos != 1 {
            return VerifyReport::broken(turns, format!("{autos} automatons on the board"));
        }
        if index_of(committed.auto).map(|i| committed.cells[i]) != Some(AUTO) {
            return VerifyReport::broken(turns, "the automaton is not where the state says it is");
        }
        if committed.turn_no != session.turn_no {
            return VerifyReport::broken(turns, "the committed turn counter diverged");
        }
        VerifyReport::ok(turns)
    }

    /// The PUBLIC surface — BOTH sealed moves are fog (no viewer to reveal to).
    fn render(&self, session: &Self::Session) -> Surface {
        session.surface_for(None)
    }

    /// The per-VIEWER surface — the viewer's own sealed move is shown in full, the opponent's stays
    /// a commitment (the simultaneous-secret fog), and the viewer's selection lights its rook line.
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        session.surface_for(session.seat_of(viewer))
    }

    /// **The affordances THIS seat may fire right now** — the per-seat projection of
    /// [`actions`](Offering::actions).
    ///
    /// `actions` paints the anonymous union: every seat's live selection targets plus both phase
    /// buttons, enabled by PHASE alone. That is right for a viewer-blind render and wrong for a
    /// player, who should not be shown the reveal they already made lit up as if it were theirs to
    /// press.
    ///
    /// It is also the only oracle a host OUTSIDE this crate has for **which seat owes the next
    /// move** ([`AutomataflSession::owes_a_move`], threaded through the `Offering` boundary that
    /// erases the session type). `dreggnet-web`'s table clock asks it once per seat and forfeits
    /// the seat still being offered something after the deadline — which is how a match parked in
    /// `Phase::Reveal` because one seat walked away now ends instead of hanging forever.
    ///
    /// Every turn NAME `actions` emits is still emitted here, disabled rather than dropped, so a
    /// frontend validating a POST against this list still reaches the executor and gets ITS
    /// refusal. The executor remains the sole referee of what lands; `enabled` is decoration.
    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let mut all = self.actions(session);
        if all.is_empty() {
            return all;
        }
        // The seat this viewer holds — or, if they hold none and one is free, the seat they would
        // claim by acting. That is exactly the rule `advance`'s `claim_seat` applies, so the
        // affordances a first-time visitor is offered are the ones their first press would use.
        let Some(seat) = session.seat_of(viewer).or_else(|| session.claimable_seat()) else {
            // Both seats are held by other identities: a spectator. Everything is shown, inert.
            for action in &mut all {
                action.enabled = false;
            }
            return all;
        };
        let i = seat.idx();
        let phase = session.phase();
        for action in &mut all {
            let mine = match action.turn.as_str() {
                SELECT | COMMIT => matches!(phase, Phase::Commit) && session.committed[i].is_none(),
                REVEAL => matches!(phase, Phase::Reveal) && !session.revealed[i],
                RESOLVE => matches!(phase, Phase::Resolve),
                _ => false,
            };
            action.enabled = action.enabled && mine;
        }
        all
    }

    /// **Hidden information: YES.** `render_for` shows the viewer their own SEALED move before it
    /// is revealed — simultaneous secrecy is the game. Painting that into a shared surface hands
    /// the opponent the seal, so a frontend serves [`render`] (both moves fog) on any surface with
    /// more than one reader.
    fn hidden_information(&self) -> bool {
        true
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[cfg(test)]
mod tests;
