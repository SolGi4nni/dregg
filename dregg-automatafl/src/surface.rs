//! # The **Offering** — automatafl playable on every dreggnet frontend.
//!
//! [`AutomataflOffering`] hosts an n=2 automatafl match as a [`dreggnet_offerings::Offering`]: the
//! same `open`/`actions`/`advance`/`verify`/`render`/`render_for`/`price` shape every frontend
//! (web / Discord / Telegram / WeChat) already drives. It is the coordinate-grid sibling of
//! `dregg-multiway-tug`'s `TugOffering`: where the tug paints a hidden HAND, automatafl paints a
//! hidden MOVE on a shared BOARD.
//!
//! **The board is the STOCK 11×11 two-player game**, and every resolved TURN is recorded WHOLE
//! ([`PlayedTurn`] via [`AutomataflSession::turns_played`], with the genesis in
//! [`AutomataflSession::start_board`]) — its start board, every CONFLICT round's submissions, and
//! the pair that finally resolved. A clash-free match hands the crown the object the two-leg fold
//! attests (`AutomataflMatch::played(start, rounds)`: Leg R the players' adjudicated moves, Leg A
//! the automaton's step, board-window chained); a turn that RE-ENTERED is the object
//! `MultiRoundTurn` folds (the Leg C conflict braid ∘ the marks-aware Leg RM ∘ the marks-carrying
//! Leg A). [`AutomataflSession::unfoldable_round`] names which turns the plain path cannot attest.
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
//! move at once, and a turn is N ROUNDS, not one. So the surface runs
//! COMMIT → REVEAL → RESOLVE → (⚑ RE-SUBMIT → REVEAL → RESOLVE)*:
//! 1. **commit** — each seat selects a source and seals a destination. The executor stores only the
//!    COMMITMENT (a blake3 seal over the move + a per-turn nonce), never the plaintext;
//! 2. **reveal** — each seat opens its seal (the plaintext lands on the cell, checked against the
//!    commitment it opens);
//! 3. **resolve** — ONE real turn asks the LEAN for `AutomataflRules.roundStep` WHOLE
//!    ([`crate::rules::round`], one call per round) and gets back one of its two arms;
//! 4. **⚑ re-submit** — the `again` arm. The round CLASHED, so it does not resolve: the contested
//!    coordinate is MARKED, the board FREEZES, the moves that were not part of the clash are LOCKED,
//!    and exactly the seats the ruleset NAMED owe a fresh move — which is re-checked against the
//!    accumulated marks. The turn counter does not move. Every one of those five facts is the Lean's
//!    answer, carried; none of them is computed here.
//!
//! The marks, locks and pending moves die when a round finally comes back clean
//! (`model.py::ClearState`), and the re-entry TERMINATES because every re-entry must burn a NEW
//! square: the deployed cell pins `marked` strictly monotone and `≤ CELLS` on its own `resubmit`
//! case, so a turn re-enters at most n² times and a round that marks nothing is REFUSED.
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
    VerifyReport, refusal::refuse_world_error,
};

use crate::board::{ATT, AUTO, Board, Coord, Decision, Move, REP, VAC};
use crate::game::{
    AutomataflGame, CELLS, COMMIT, MatchState, N, RESOLVE, RESUBMIT, REVEAL, SELECT, coord_of,
    goal_owner_at, goals, goals_of, index_of, opening_board,
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
    /// ⚑ **THE CONFLICT ROUND.** The previous round CLASHED: the contested coordinate is MARKED,
    /// the board is FROZEN, and exactly the seats the ruleset NAMED
    /// ([`AutomataflSession::waiting`]) owe a FRESH move. A seat whose move was not part of the
    /// clash is [`AutomataflSession::locked`] and owes nothing.
    ///
    /// Mechanically this is `Commit` again — a seal, then an open — but it is a distinct phase
    /// because it means something different on a board: the turn has not advanced, the marks are
    /// permanent for the rest of the turn, and only some seats are being waited on.
    Resubmit,
    /// Both moves are sealed; each seat opens its commitment.
    Reveal,
    /// Both moves are open; the resolution is one real turn away.
    Resolve,
    /// The match is decided (a goal reached, or the clock ran out).
    Over,
}

impl Phase {
    /// Is a seat SEALING a move in this phase? (`Commit` and `Resubmit` are the same affordance —
    /// select a source, seal a destination — over different round states.)
    pub fn is_sealing(self) -> bool {
        matches!(self, Phase::Commit | Phase::Resubmit)
    }
}

/// **ONE PLAYED TURN, WHOLE** — the turn-start board, every CONFLICT round's submissions in
/// re-entry order, and the terminating CLEAN round's submissions.
///
/// This is exactly the shape `dreggnet_game_board::MultiRoundTurn` folds
/// (`start` / `conflict_subs` / `clean_subs`): the conflict braid lowers to one Leg C leaf per
/// entry on the 32-lane RoundState window, and `clean_subs` lowers to the marks-aware Leg RM +
/// the marks-carrying Leg A. `conflict_subs` empty ⇒ the turn was clean and folds through the
/// plain two-leg `AutomataflMatch::played` path.
///
/// ⚑ Recorded on a LANDED resolution only — a refused one restores the previous history
/// (anti-ghost), so an unlanded round is not a played round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlayedTurn {
    /// The turn-start board — FROZEN across the whole turn, every round of it.
    pub start: Board,
    /// Each conflict round's move set, in re-entry order (`[seat A's, seat B's]`). A locked seat's
    /// move appears again in the next round's entry, because that is what the round CONSIDERED.
    pub conflict_subs: Vec<[Move; 2]>,
    /// The terminating clean round's move set — the pair that actually resolved.
    pub clean_subs: [Move; 2],
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

/// ⚑ **ONE OF THE AUTOMATON'S FOUR SIGHTLINES** — the ray the LEAN cast along one axis direction
/// (`Board.raycast`, carried out of [`rules::sense`]), read as squares on the board.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sightline {
    /// The on-screen word for the direction (`left` / `right` / `up` / `down`).
    pub dir: &'static str,
    /// The unit step along it.
    pub step: Coord,
    /// How far the ray travelled before it stopped — the LEAN's `Raycast.dist`.
    pub dist: usize,
    /// What stopped it: [`REP`] / [`ATT`], or [`VAC`] when the ray ran off the board (the WALL —
    /// `raycastFuel` records vacuum plus the out-of-bounds step index).
    pub what: u8,
    /// The square it stopped on. OUT OF BOUNDS exactly when `what == VAC`.
    pub end: Coord,
}

impl Sightline {
    /// Where the ray points, as a phrase that reads after a distance (`4 squares to its left`,
    /// `4 squares above it`) — `dir` alone gives "4 squares to its up".
    fn whither(&self) -> &'static str {
        match self.dir {
            "left" => "to its left",
            "right" => "to its right",
            "up" => "above it",
            _ => "below it",
        }
    }

    /// What the ray found, in words.
    pub fn found(&self) -> String {
        match self.what {
            ATT => format!("an attractor {} {}", squares(self.dist), self.whither()),
            REP => format!("a repulsor {} {}", squares(self.dist), self.whither()),
            // A vacuum ray reached the boundary: nothing stopped it but the edge of the board.
            _ => format!("open board {} {}", squares(self.dist), self.whither()),
        }
    }

    /// Is the end of this ray a real PIECE (as opposed to the board's edge)? A wall-terminated ray
    /// stops one square OFF the board, so its `end` is not a square anybody can play.
    pub fn caps_a_piece(&self) -> bool {
        self.what == ATT || self.what == REP
    }
}

/// **THE FOUR SIGHTLINES** of `b`, in `left, right, up, down` order.
///
/// The rays come out of the LEAN (`senseOf`'s own `xp / xn / yp / yn` raycasts, in that wire order);
/// the only thing done here is turning the Lean's distance into the coordinate it designates.
fn sightlines_of(b: &Board) -> Option<[Sightline; 4]> {
    let s = rules::sense(b).ok()?;
    // `senseOf` emits xp, xn, yp, yn. `-y` is UP the screen (row-major, `y = 0` at the top).
    let spec: [(&'static str, Coord, usize); 4] = [
        ("left", (-1, 0), 1),
        ("right", (1, 0), 0),
        ("up", (0, -1), 3),
        ("down", (0, 1), 2),
    ];
    Some(spec.map(|(dir, step, i)| {
        let r = s.rays[i];
        Sightline {
            dir,
            step,
            dist: r.dist,
            what: r.what,
            end: (
                b.auto.0 + step.0 * r.dist as i32,
                b.auto.1 + step.1 * r.dist as i32,
            ),
        }
    }))
}

/// ⚑ **THE SQUARES THAT CAN CHANGE THE AUTOMATON'S MIND** — the union of the four sightline
/// SEGMENTS, from the automaton's neighbour out to and including the square the ray stopped on
/// (clipped to the board, since a wall-terminated ray stops one square off it).
///
/// It follows from the ruleset's own shape: `raycastFuel` steps outward and stops at the first
/// non-vacuum square, and `evaluateAxis` reads nothing but the two `Raycast` values on its axis — so
/// the automaton's whole decision is a function of these squares alone, and a move with neither
/// endpoint here leaves every ray identical.
///
/// ⚑ HONEST SCOPE OF THAT CLAIM. It is a reading of the Lean's definitions plus an EXHAUSTIVE
/// falsifier over the stock opening (`surface::tests::a_move_off_every_sightline_cannot_change_the_read`
/// checks every legal move that misses the arms, and requires the on-arm set to contain a mover so
/// the check cannot pass vacuously). It is NOT a machine-checked theorem quantified over all boards
/// — nothing in `AutomataflRules` states it — so it is a well-tested fact about the shipped surface's
/// hint, not part of the proof floor.
///
/// It is the answer to the single worst thing about the opening position: the stock board offers a
/// seat **720 legal moves, of which 20 move the automaton at all** — so a player choosing by the
/// legal-move highlight alone is choosing at random, from a set that is 97% noise.
fn sightline_squares(b: &Board, lines: &[Sightline; 4]) -> Vec<Coord> {
    let mut out = Vec::new();
    for l in lines {
        for k in 1..=l.dist {
            let c = (
                b.auto.0 + l.step.0 * k as i32,
                b.auto.1 + l.step.1 * k as i32,
            );
            if b.in_bounds(c) && !out.contains(&c) {
                out.push(c);
            }
        }
    }
    out
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
    /// The live board — `AutomataflRules.RoundState.board` while a turn is in flight (frozen: only a
    /// resolution writes it). Every resolution is computed by the Lean ([`crate::rules::round`]).
    board: Board,
    /// **The GENESIS position** — the board the match opened on, kept so the played match can be
    /// folded (`AutomataflMatch::played(start, rounds)`); the fold's first leaf declares this as
    /// its IN window and the root exposes it as the decodable `board_genesis`.
    start: Board,
    /// **THE TURN HISTORY** — every RESOLVED turn, whole: its start board, its conflict rounds'
    /// submissions and its terminating clean round's ([`PlayedTurn`]).
    ///
    /// Without this the surface threw every move away and the only foldable shape left was the
    /// automaton-only chain, which attests K independent automaton steps and NO MOVE AT ALL. With
    /// the clean pairs alone ([`Self::rounds`], derived from this) a clash-free match folds through
    /// the TWO-LEG (Leg R resolve, Leg A step) chain; with the CONFLICT rounds recorded too, a turn
    /// the seats clashed on is the `MultiRoundTurn` the Leg C braid folds. Pushed on a LANDED
    /// resolution only (a refused resolution commits nothing and records nothing — anti-ghost).
    turns_played: Vec<PlayedTurn>,
    /// **THE TURN-START BOARD** — `AutomataflRules.RoundState.board`, frozen for every round of the
    /// current turn. Equal to [`Self::board`] (nothing but a resolution writes the board); held
    /// separately so a recorded [`PlayedTurn`] carries the position its rounds were played against
    /// even after the resolution has moved on.
    turn_start: Board,
    /// ⚑ **THE ACCUMULATED CONFLICT MARKERS** — `RoundState.marks`, exactly as
    /// [`crate::rules::round`] returned them. A marked coordinate is illegal at EITHER endpoint for
    /// EVERYONE for the rest of the turn, and the marks are cleared when the turn resolves
    /// (`model.py::ClearState`). Never computed here: the Lean says which square was contested.
    marks: Vec<Coord>,
    /// **THE LOCKED MOVES** — `RoundState.locked`: the moves that were not part of the clash and
    /// therefore STAND, unchanged, into the next round. Their seats owe nothing.
    locked: Vec<Move>,
    /// **THE SEATS THAT OWE A FRESH MOVE** — `RoundState.waiting`. `[0, 1]` at turn start
    /// (`openRound`), and after a clash exactly the seats the ruleset NAMED.
    waiting: Vec<u32>,
    /// This turn's conflict rounds' submissions so far, in re-entry order — the `MultiRoundTurn`
    /// braid under construction. Cleared when the turn resolves.
    conflict_subs: Vec<[Move; 2]>,
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
    /// **The current phase**, read off the ROUND STATE the Lean handed back.
    ///
    /// Only the seats in [`Self::waiting`] are waited on: a LOCKED seat (one whose move survived a
    /// clash) has already sealed and opened, and the phase must not sit forever waiting for it to
    /// do so again. `Resubmit` rather than `Commit` exactly when this turn has already had a
    /// conflict round.
    pub fn phase(&self) -> Phase {
        if self.ended {
            return Phase::Over;
        }
        let owed = |f: &dyn Fn(usize) -> bool| self.waiting.iter().any(|w| f(*w as usize));
        if owed(&|i| self.committed[i].is_none()) {
            if self.conflict_subs.is_empty() {
                Phase::Commit
            } else {
                Phase::Resubmit
            }
        } else if owed(&|i| !self.revealed[i]) {
            Phase::Reveal
        } else {
            Phase::Resolve
        }
    }

    /// ⚑ **This turn's MARKED coordinates** — `AutomataflRules.RoundState.marks`, as the Lean's
    /// `round` verb returned them. A marked square is dead for the rest of the turn: illegal as a
    /// source AND as a destination, for EVERY seat. PUBLIC (both viewers see the same marks; a mark
    /// is not a secret, it is a scar on the board).
    pub fn marks(&self) -> &[Coord] {
        &self.marks
    }

    /// **The moves that STAND into the next round** — `RoundState.locked`. Their seats are not
    /// waited on and their moves are carried into the next round untouched.
    pub fn locked(&self) -> &[Move] {
        &self.locked
    }

    /// **The seats that owe a fresh move this round** — `RoundState.waiting`. `[0, 1]` on a first
    /// round; after a clash, exactly the seats the ruleset named.
    pub fn waiting(&self) -> &[u32] {
        &self.waiting
    }

    /// Whether `seat` owes a submission this round (it is in [`Self::waiting`]). A locked seat does
    /// not.
    pub fn is_waiting(&self, seat: Seat) -> bool {
        self.waiting.contains(&(seat.idx() as u32))
    }

    /// **How many CONFLICT rounds this turn has already had.** `0` on a first round; each re-entry
    /// marks at least one new square, so this is bounded by `N²` — the executor enforces exactly
    /// that (`marked` is `StrictMonotonic` and `FieldLte CELLS` on the `resubmit` case).
    pub fn conflict_round_no(&self) -> usize {
        self.conflict_subs.len()
    }

    /// **THE TURN HISTORY** — every resolved turn, whole ([`PlayedTurn`]): the shape
    /// `dreggnet_game_board::MultiRoundTurn` folds.
    pub fn turns_played(&self) -> &[PlayedTurn] {
        &self.turns_played
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

    /// **WHO IS AHEAD** — the ruleset's own reading of the live board ([`rules::Standing`]): each
    /// seat's `goalDistance` and the `adjudicateCapped` verdict those two numbers produce.
    ///
    /// ⚑ This is the game's ONLY running contest. `winOnEntry` is the ruleset's sole terminal
    /// condition and a match that never walks the automaton into a corner never ends — measured
    /// against this exact spec, *two competent seats draw 100% of the time*, freezing on the neutral
    /// mid-line in 8–11 turns (`AutomataflRules` §6B). The cap's adjudication is what destroys that
    /// free freeze, because parking is no longer as good as winning. It was decided at turn 64 and
    /// shown NOWHERE, so the player could not see the contest they were in until it was over.
    ///
    /// `None` when the oracle cannot answer — the plaque then says so rather than guessing.
    pub fn contest(&self) -> Option<rules::Standing> {
        rules::standing(&self.board, goals().ok()?).ok()
    }

    /// The fewest steps the automaton could possibly need to reach `seat`'s nearest goal corner —
    /// the LEAN's `goalDistance` (it moves one orthogonal square per resolution, so this is a floor
    /// on the turns left). `Some(0)` = it is standing on one; `None` = the seat owns no corner, or
    /// the oracle did not answer.
    ///
    /// ⚑ This was a Manhattan distance hand-written in Rust, painted beside a verdict taken from the
    /// Lean — two computations of one quantity, one of them unproven. It is now the number
    /// `adjudicateCapped` actually compares.
    pub fn goal_distance(&self, seat: Seat) -> Option<u32> {
        self.contest()?.dist[seat.idx()]
    }

    /// The reference board (the committed position).
    pub fn board(&self) -> &Board {
        &self.board
    }

    /// **The genesis position** — the board this match opened on (the fold's `board_genesis`).
    pub fn start_board(&self) -> &Board {
        &self.start
    }

    /// **The resolved turns' terminating moves** — each resolved turn's `(seat A move, seat B
    /// move)`, in order. This is the object `AutomataflMatch::played(start, rounds)` folds, and it
    /// is honest ONLY for a match with no conflict rounds: a turn that re-entered resolved against
    /// ACCUMULATED MARKS, and the plain two-leg fold has no marks lane to consume them with (that is
    /// Leg RM). Ask [`Self::unfoldable_round`] before folding this.
    pub fn rounds(&self) -> Vec<(Move, Move)> {
        self.turns_played
            .iter()
            .map(|t| (t.clean_subs[0], t.clean_subs[1]))
            .collect()
    }

    /// The index of the first recorded turn the PLAIN two-leg fold cannot attest, or `None` when
    /// every turn folds through `AutomataflMatch::played`.
    ///
    /// Two ways a turn fails that:
    ///
    /// 1. **it RE-ENTERED** — the turn had ≥1 conflict round, so its terminating round resolved
    ///    against accumulated MARKS. Folding it as a plain Leg R + Leg A round would attest a
    ///    transition in which the clash never happened. That turn is a `MultiRoundTurn`
    ///    (`conflict braid ∘ Leg RM ∘ Leg A`), not a round of `played`.
    /// 2. **its terminating round is not clean** — unreachable through this surface now that the
    ///    resolution is the ruleset's own `roundStep` (a clash RE-ENTERS instead of resolving), and
    ///    kept as a checked side condition: the answer comes from the LEAN
    ///    ([`rules::round_is_clean`]), so if it ever fires the fold is refused rather than fed a
    ///    round the rules never licensed.
    pub fn unfoldable_round(&self) -> Result<Option<usize>, String> {
        let mut b = self.start.clone();
        for (i, t) in self.turns_played.iter().enumerate() {
            if !t.conflict_subs.is_empty() {
                return Ok(Some(i));
            }
            let pair = [t.clean_subs[0], t.clean_subs[1]];
            if !rules::round_is_clean(&b, &pair)? {
                return Ok(Some(i));
            }
            b = rules::apply_turn(&b, &pair)?;
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
    /// walked away instead of guessing or blaming both. Pure — reads the phase, the round's
    /// `waiting` set and that seat's own commit/reveal flags, nothing else.
    ///
    /// ⚑ A seat the ruleset did NOT name for re-entry ([`Self::locked`]) owes nothing: its move
    /// stands. Forfeiting it on a clock would punish the seat that did not cause the clash.
    pub fn owes_a_move(&self, seat: Seat) -> bool {
        if self.ended {
            return false;
        }
        let i = seat.idx();
        if !self.is_waiting(seat) && !matches!(self.phase(), Phase::Resolve) {
            return false;
        }
        match self.phase() {
            Phase::Commit | Phase::Resubmit => self.committed[i].is_none(),
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
    ///
    /// The committed `phase` register keeps its three values (`0 = sealing, 1 = opened, 2 = over`):
    /// a re-submission IS a sealing phase, so it reads `0` — the thing that distinguishes a
    /// conflict round on the cell is `marked`, which the `resubmit` case pins strictly monotone.
    fn state(&self) -> MatchState {
        let phase = match self.phase() {
            Phase::Commit | Phase::Resubmit => 0,
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
            // THE TERMINATION WITNESS: how many squares this turn has marked. `StrictMonotonic` on
            // the `resubmit` case turns "the marks strictly grow" into a cell tooth, and
            // `FieldLte CELLS` caps the re-entries at n².
            marked: self.marks.len() as u64,
            cells: self.board.cells.clone(),
        }
    }

    /// The PROPOSABLE targets of `src` — the set the LEAN admits (`AutomataflRules.moveLegalB` over
    /// the board: same row or column, distinct, in-bounds, and never the automaton as a SOURCE).
    /// This is what [`Offering::advance`]'s legality tooth accepts, so it is exactly the set of
    /// destinations a seal can name without being refused.
    ///
    /// ⚑ Naming the automaton's square as a DESTINATION is legal to propose and then FAILS to execute
    /// (ruling D + the inclusive path check), so it is in this set. The old Rust `move_valid` banned
    /// it, which is `logic/src/game.rs`'s reading rather than the README's.
    ///
    /// ⚑ **THIS IS NOT THE LEGAL-MOVE HIGHLIGHT AND MUST NEVER BE PAINTED AS ONE.** `MoveLegal` has
    /// no occupancy clause, so this runs the whole rook line THROUGH every piece standing on it —
    /// ember selected the stock attractor at `(3,1)` on the live board and was shown a lit `(3,10)`,
    /// behind the attractor on `(3,9)`, plus all of row 1 behind three repulsors. Nine of the twenty
    /// squares could not have executed. [`Self::executable_targets`] is the set that would.
    ///
    /// ⚑ Asked WITH THIS TURN'S MARKS ([`Self::marks`]), so after a clash the offered rook line
    /// shrinks: a marked square is not a legal destination for anyone, and the re-check is the
    /// ruleset's own `moveLegalB`, not a Rust filter over the Lean's answer.
    ///
    /// Empty when the oracle cannot answer — no affordance is offered for a move nobody can
    /// adjudicate, and `advance` re-asks before it commits anything.
    pub fn legal_targets(&self, src: Coord) -> Vec<Coord> {
        rules::legal_targets(&self.board, &self.marks, 0, src).unwrap_or_default()
    }

    /// ⚑ **THE TARGETS THAT WOULD ACTUALLY EXECUTE** — `AutomataflFFI.liveTargetsOf`, the LEAN's own
    /// `moveLegalB && !blockedB` in one call. The legal-move dots on the board are this set, and
    /// only this set.
    ///
    /// Asked against the round's LOCKED moves, which is what a viewer is entitled to know (the
    /// ruleset published them when it marked the clash) and never an opponent's sealed move. That
    /// operand matters: a mover's SOURCE is passable while the round resolves, so a square behind a
    /// piece a locked move is already carrying away IS reachable — the Lean is told, and answers.
    ///
    /// ⚑ **BLOCKED IS NOT ILLEGAL.** The complement of this set inside [`Self::legal_targets`] is
    /// still proposable, and proposing it is a real play: seal a move behind a blocker, betting the
    /// other seat picks the blocker up, and the same destination becomes live. That is why the board
    /// paints a third state instead of hiding those squares — hiding them would be this crate
    /// narrowing the ruleset's own legality in Rust, which is precisely what the deleted twin did.
    ///
    /// Empty when the oracle cannot answer; the board then offers no dots rather than guessing.
    pub fn executable_targets(&self, src: Coord) -> Vec<Coord> {
        rules::executable_targets(&self.board, &self.marks, &self.locked, 0, src)
            .unwrap_or_default()
    }

    /// Whether `src` is a square a seat may move: a real (non-vacuum) particle that is not the
    /// automaton, and NOT a marked square. (Automatafl's pieces are SHARED — either seat may push
    /// any piece; that is what makes the simultaneous conflict resolution the heart of the game.)
    ///
    /// ⚑ The mark clause is a RULE, not decoration: `MoveLegal` requires `m.frm ∉ marks`, so a
    /// marked square cannot be picked up for the rest of the turn. Offering it as a selection would
    /// hand the player an affordance that can only end in a refusal.
    pub fn movable(&self, src: Coord) -> bool {
        let p = self.board.cell_at(src);
        p != VAC && p != AUTO && !self.marks.contains(&src)
    }

    /// Is `c` one of this turn's MARKED squares — dead at either endpoint, for everyone?
    pub fn is_marked(&self, c: Coord) -> bool {
        self.marks.contains(&c)
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
    /// * ⚑ a MARKED square (a coordinate a clash killed this turn) is tagged `mark`, carries the
    ///   `×` glyph, and has NO affordance at all — it outranks every other role because it is the
    ///   only one that says "you cannot use this square", and a player who cannot see it will keep
    ///   trying to. PUBLIC: the marks are the same in every viewer's board;
    /// * the automaton square is marked (`@`, tag `accent`, in the highlight-set);
    /// * the viewer's SELECTED source is tagged `warn` and highlighted;
    /// * ⚑ every target of that source that would EXECUTE ([`Self::executable_targets`]) is tagged
    ///   `good` and highlighted, and carries the `{turn: "commit", arg: index}` affordance a click
    ///   fires. **This used to be [`Self::legal_targets`], which is the PROPOSABLE set** — it has no
    ///   occupancy clause, so the rook line lit straight through every piece standing on it and the
    ///   player read a dot as "I can go there" for squares nothing could reach. On the stock opening
    ///   that was nine of twenty;
    /// * ⚑ a target that is proposable but BLOCKED right now is tagged `blocked`, is NOT highlighted,
    ///   and KEEPS its `commit` affordance. It is not illegal and the surface may not pretend it is:
    ///   the ruleset lets a seat name it and eat the refusal, and — because a mover's source is
    ///   passable — the same square goes live the moment somebody picks the blocker up. Sealing one
    ///   is a bet on the other seat, which is a real play in a simultaneous-move game;
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
        // The public board lights the union of the LIVE selections — a seat that is waiting and has
        // not yet sealed. A LOCKED seat's selection is stale (its move is already sealed and stands),
        // and painting its rook line publicly would offer affordances nobody can fire.
        let selections: Vec<Coord> = match viewer {
            Some(s) => self.sel[s.idx()].into_iter().collect(),
            None => self
                .waiting
                .iter()
                .filter(|w| self.committed[**w as usize].is_none())
                .filter_map(|w| self.sel[*w as usize])
                .collect(),
        };
        // **THE VIEWER'S OWN SEALED MOVE, ON THE BOARD.** Strictly per-viewer: read ONLY out of
        // `viewer`'s OWN slot, so a spectator (`None`) and the opponent get nothing here — the fog
        // is untouched. Once a seat HAS sealed, its rook-line highlight is stale (there is no
        // affordance left on those squares) and painting it lies about what is pending; the two
        // squares that matter are the piece it sealed and where it sealed it TO.
        let own_sealed: Option<Move> = viewer.and_then(|s| self.committed[s.idx()]);
        // ⚑ TWO SETS, BOTH THE LEAN'S. `targets` is what a seal may NAME (`moveLegalB`); `live` is
        // what would actually RUN (`moveLegalB && !blockedB`, one call). Nothing here scans a path or
        // decides what occludes what — the difference between the two lists IS the oracle's answer,
        // and the board paints them as two different things because they mean two different things.
        let mut targets: Vec<Coord> = Vec::new();
        let mut live: Vec<Coord> = Vec::new();
        if own_sealed.is_none() {
            for &src in &selections {
                for t in self.legal_targets(src) {
                    if !targets.contains(&t) {
                        targets.push(t);
                    }
                }
                for t in self.executable_targets(src) {
                    if !live.contains(&t) {
                        live.push(t);
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
        // A re-submission is the same affordance as a first submission, over a frozen board with
        // marks on it — so the grid is playable in `Resubmit` too, and a seat that is NOT waiting
        // (its move is locked) is offered nothing.
        let playable = !self.ended
            && self.phase().is_sealing()
            && match viewer {
                Some(s) => self.is_waiting(s),
                None => self
                    .waiting
                    .iter()
                    .any(|w| self.committed[*w as usize].is_none()),
            };
        // ⚑ THE AUTOMATON'S FOUR SIGHTLINES, ON THE BOARD. Public (a pure function of the visible
        // position), and drawn as a GLYPH rather than a tag so it survives the PROSE projection —
        // Discord and Telegram paint `coordgrid_text` and have no CSS to lean on, and the sightlines
        // are the one thing a first-time player most needs to see.
        let lines = sightlines_of(&self.board);
        let sight: Vec<Coord> = lines
            .as_ref()
            .map(|l| sightline_squares(&self.board, l))
            .unwrap_or_default();

        let mut cells = Vec::with_capacity(CELLS);
        for idx in 0..CELLS {
            let c = coord_of(idx);
            let p = self.board.cell_at(c);
            let is_auto = c == self.board.auto;
            let is_selected = selections.contains(&c);
            let is_target = targets.contains(&c);
            // The LEAN's composed answer: proposable AND unobstructed. Never `is_target && !live`
            // computed the other way round — the blocked set is the difference between two lists the
            // oracle handed back, not a Rust judgement about what is in the way.
            let is_live = live.contains(&c);

            let is_goal = Seat::owner_of_goal(c).is_some();

            let (tag, highlight) = if self.is_marked(c) {
                // ⚑ THE MARK OUTRANKS EVERYTHING. It is the only tag that means "unusable", and it
                // must survive a square that is also a goal corner, also the automaton's, also
                // where you sealed last round. Not highlighted: the highlight means "live".
                ("mark", false)
            } else if is_auto {
                ("accent", true)
            } else if own_sealed.map(|m| m.to) == Some(c) {
                // WHERE YOU SEALED IT TO — its own treatment, and only ever on its own seat's
                // surface.
                ("sealed", true)
            } else if own_sealed.map(|m| m.frm) == Some(c) {
                ("warn", true)
            } else if is_selected {
                ("warn", true)
            } else if is_live {
                ("good", true)
            } else if is_target {
                // ⚑ PROPOSABLE BUT BLOCKED — legal to name, and it would not run against the board
                // as it stands. Deliberately NOT highlighted: the highlight is the promise "this
                // move happens", and it was being made for squares behind a piece. The affordance
                // stays (below), because the ruleset licenses the proposal and the other seat can
                // clear the way; what changes is that the board stops calling it a legal move.
                ("blocked", false)
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

            // The affordance: a PROPOSABLE target commits (blocked ones included — `advance`'s
            // legality tooth is `moveLegalB`, so refusing the click here would be this crate
            // narrowing the ruleset in Rust); a movable piece selects (while unsealed).
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
            // ⚑ A MARKED square says so in its GLYPH as well as its tag, because the text
            // frontends (Discord / Telegram) paint the glyph literally and have no CSS to lean on.
            // The piece standing there is still there — the square is dead, not empty — so the
            // cross replaces the glyph and the plaque names the piece.
            if self.is_marked(c) {
                glyph = "×".to_string();
            } else if p == VAC && is_goal {
                glyph = Seat::owner_of_goal(c)
                    .expect("is_goal")
                    .label()
                    .to_lowercase();
            } else if p == VAC && sight.contains(&c) {
                // ⚑ AN EMPTY SQUARE THE AUTOMATON IS LOOKING THROUGH. The four sightlines are the
                // ONLY squares a move can use to change what the daemon does, and an unmarked
                // vacuum square is the one place there is room to say so — the pieces at the ends
                // keep their own `R`/`A` glyph (naming them is the plaque's job) and a goal corner
                // keeps its letter, because both of those outrank a hint.
                //
                // A square is on at most ONE line: the rank line needs `y == auto.y` and the file
                // line needs `x == auto.x`, and both at once IS the automaton's own square.
                glyph = if c.1 == self.board.auto.1 {
                    "─"
                } else {
                    "│"
                }
                .to_string();
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

    /// ⚑ **THE LINES THAT MAKE THE BOARD READABLE WITHOUT A MANUAL** — the glyph vocabulary, the
    /// axes, and (from [`deos_view::coordgrid_legend`], so it cannot drift from what the projection
    /// actually paints) what each bracket around a square means.
    ///
    /// This exists because the prose above the board describes the WEB board: brass discs, a violet
    /// ring, squares "drawn dimmed and outlined". On Discord / Telegram / WeChat there is no colour,
    /// no outline and no tooltip — the glyph and its brackets are the entire board — and this
    /// surface shipped without a single line telling a reader what either meant. The native
    /// Descent's own map legend is the pattern being mirrored (`native_descent::map_legend`).
    ///
    /// Every renderer gets these lines: on the web they are a caption under the board and read as
    /// one, and a caption that agrees with the text channels is the point.
    fn board_legend() -> Vec<ViewNode> {
        vec![
            ViewNode::Text(format!(
                "Columns are x (left to right), rows are y (top to bottom), both 0–{last} — the \
                 same (x,y) every button names.",
                last = N - 1
            )),
            ViewNode::Text(
                "A attractor · R repulsor · @ the automaton · a / b an EMPTY goal corner (whose \
                 seat's letter it is) · × a MARKED square, dead at both ends for the rest of the \
                 turn · ─ or │ an empty square the automaton is looking along (the only squares a \
                 move can change what it does) · · plain empty."
                    .to_string(),
            ),
            ViewNode::Text(deos_view::coordgrid_legend()),
        ]
    }

    /// ⚑ **WHAT YOUR OWN MOVE ALONE WOULD DO** — the sentence that turns a sealed move from a
    /// gamble into a PLAN.
    ///
    /// Asked of the LEAN (`turnOf` = `winOnEntry ∘ automatonStepCfg ∘ resolveMoves`, one call) over a
    /// board on which only the moves this viewer is ENTITLED to know have landed: their own sealed
    /// move, plus any LOCKED move (public — the ruleset published it when it marked the clash). It is
    /// therefore computed from `viewer`'s own slot and public state ONLY: the opponent's sealed move
    /// is not read, so nothing here narrows it and a spectator is never shown one at all.
    ///
    /// It is a COUNTERFACTUAL and it says so. The other seat is moving too — there is no pass in
    /// automatafl — so the real resolution can differ, and that gap is the game. Before this the
    /// surface explained the automaton's step beautifully in the PAST TENSE and said nothing at the
    /// moment of choice, which is the moment that decides anything.
    fn own_move_forecast(&self, seat: Seat, mv: &Move) -> Option<String> {
        let goals = goals().ok()?;
        let mut ms = self.locked.clone();
        ms.push(*mv);
        let (after, win) = rules::turn(&self.board, &self.marks, &ms, goals).ok()?;
        let mine = self.contest().and_then(|s| s.dist[seat.idx()]);
        let then = rules::standing(&after, goals)
            .ok()
            .and_then(|s| s.dist[seat.idx()]);
        let closer = match (mine, then) {
            (Some(a), Some(b)) if b < a => format!(" — {} NEARER your corner", a - b),
            (Some(a), Some(b)) if b > a => format!(" — {} further from your corner", b - a),
            _ => " — no nearer your corner".to_string(),
        };
        Some(match win {
            Some(w) if w == seat.idx() as u32 => {
                "⚑ IF YOURS IS THE ONLY MOVE THAT LANDS, THIS WINS THE MATCH — the automaton steps \
                 into your own corner. The other seat is sealing right now and can take that away."
                    .to_string()
            }
            Some(w) => format!(
                "⚑ CAREFUL: if yours is the only move that lands, this hands the match to SEAT {} \
                 — it walks the automaton into THEIR corner.",
                Seat::from_idx(w).label()
            ),
            None if after.auto == self.board.auto => "Your move alone would leave the automaton \
                                                     where it is. (The other seat is moving too, so \
                                                     the round can still shift it.)"
                .to_string(),
            None => format!(
                "Your move alone would send the automaton to ({},{}){closer}. The other seat is \
                 sealing at the same time, so the real answer can differ — that gap is the game.",
                after.auto.0, after.auto.1
            ),
        })
    }

    /// The seat's move line — REVEALED to its owner, FOG to everyone else until the open.
    ///
    /// ⚑ A LOCKED seat's line says so, and says it PUBLICLY: which seats are locked is not a
    /// secret (the ruleset named them out loud when it marked the square), and a seat that is not
    /// being waited on needs to know it is not holding the table up. The locked seat's MOVE is
    /// still fog to the opponent — it was revealed to the ruleset, not to the other player, and it
    /// stays sealed on their surface until the turn resolves.
    fn move_line(&self, seat: Seat, viewer: Option<Seat>) -> ViewNode {
        let own = viewer == Some(seat);
        let locked = !self.is_waiting(seat) && !self.marks.is_empty();
        // ⚑ THE SURFACE NOW SAYS WHICH SEAT IS YOURS — and, when neither is, says THAT.
        //
        // Both panels read `Seat A — them` / `Seat B — them` to a seatless viewer, so a reader
        // could not tell whether they were a player or a spectator
        // (`docs/reference/UX-QA-SWEEP-2026-07-26.md`, the automatafl section — "the best of the
        // four" surface, undone by this one word). "them" is only meaningful against a "you", and
        // with no viewer there is none: a free seat is `OPEN`, a held one `held by the other
        // player`, and the standing plaque above says which of the two you would take.
        let whose = match viewer {
            Some(_) if own => "YOURS".to_string(),
            Some(_) => "them".to_string(),
            // Exact about WHICH free seat is yours: `claimable_seat` takes A before B, so with both
            // seats open only A is the one your first move would take.
            None if self.claimable_seat() == Some(seat) => {
                "OPEN — the seat your first move would claim".to_string()
            }
            None if self.seats[seat.idx()].is_none() => "OPEN".to_string(),
            None => "held by another player".to_string(),
        };
        let title = format!(
            "Seat {} — {}{}",
            seat.label(),
            whose,
            if locked { " · LOCKED" } else { "" }
        );
        let body = match (self.committed[seat.idx()], self.revealed[seat.idx()]) {
            (None, _) => {
                let s = self.sel[seat.idx()];
                if own {
                    match s {
                        Some(c) => format!("selected ({},{}) — pick a destination", c.0, c.1),
                        None if self.marks.is_empty() => {
                            "no move sealed — select one of your pieces".to_string()
                        }
                        None => "you owe a FRESH move — select one of your pieces (the marked \
                                 squares are dead)"
                            .to_string(),
                    }
                } else {
                    "thinking… (no move sealed yet)".to_string()
                }
            }
            // ⚑ A LOCKED move is PUBLIC, and that is the RULESET, not a leak: the clash was found
            // by revealing every submission simultaneously, so a move that survived the clash was
            // revealed before it was locked. Hiding it again would invent a rule. What stays fog is
            // the RE-SUBMISSION — a fresh seal, sealed exactly like a first one.
            (Some(mv), true) if locked => format!(
                "{} move STANDS, untouched: ({},{}) → ({},{}) — {} not part of the clash, so {} do \
                 not re-submit, and it executes when the round finally resolves. (It was revealed \
                 with the clash, so both seats can see it.)",
                if own { "YOUR" } else { "their" },
                mv.frm.0,
                mv.frm.1,
                mv.to.0,
                mv.to.1,
                if own { "you were" } else { "they were" },
                if own { "you" } else { "they" },
            ),
            (Some(mv), false) if own => format!(
                "YOUR sealed move: ({},{}) → ({},{}) · seal {:x}… (the opponent sees only the seal){}",
                mv.frm.0,
                mv.frm.1,
                mv.to.0,
                mv.to.1,
                self.seal[seat.idx()] >> 40,
                match self.own_move_forecast(seat, &mv) {
                    Some(f) => format!("\n{f}"),
                    None => String::new(),
                }
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
        // ⚑ **A SPECTATOR'S PHASE CONTROLS ARE DIMMED.** Found by
        // `dreggnet-web/tests/catalog_flow_harness.rs`'s `fog` check and handed to this lane as a
        // named, self-retiring allowance: the board CELLS already go inert for a spectator
        // (`board_grid`'s `playable`), but this MENU was gated on the PHASE alone — so once both
        // seats were taken, a viewer holding NEITHER was still served an ENABLED `Reveal` /
        // `Resolve`. `advance` refuses them ("both seats are taken — you are a spectator"), which
        // makes them controls that can ONLY refuse: a lie the page tells before the substrate gets
        // a say.
        //
        // The gate is "no seat AND no seat to claim". A CLAIMANT keeps live controls, and correctly:
        // `claim_seat` seats them on their first accepted move, so their press really does fire. As
        // everywhere else, `enabled` is DECORATION — the executor stays the sole referee and a
        // crafted POST of a dimmed row still reaches it and still gets its refusal.
        let spectator = viewer.is_none() && self.claimable_seat().is_none();
        // Per-viewer: only while THIS seat is unopened. Publicly (the catalog surface): while EITHER
        // seat is unopened — the executor refuses a double reveal, so the control is honest.
        let can_reveal = !spectator
            && matches!(phase, Phase::Reveal)
            && match viewer {
                Some(s) => self.is_waiting(s) && !self.revealed[s.idx()],
                None => self.waiting.iter().any(|w| !self.revealed[*w as usize]),
            };
        let items = vec![
            MenuItem {
                label: "Reveal your sealed move".to_string(),
                turn: REVEAL.to_string(),
                arg: 0,
                enabled: can_reveal,
                wants_text: false,
            },
            MenuItem {
                // ⚑ The label used to promise "conflicts drop", which was the audited-WRONG rule
                // the surface actually implemented. It does not drop them any more: a clash MARKS
                // the square and RE-OPENS the round, and the button says which of the two can
                // happen.
                label: "Resolve the round (a clash MARKS the square and re-opens it · otherwise \
                        the moves apply and the automaton steps)"
                    .to_string(),
                turn: RESOLVE.to_string(),
                arg: 0,
                enabled: !spectator && matches!(phase, Phase::Resolve),
                wants_text: false,
            },
        ];
        ViewNode::Menu { items }
    }

    /// ⚑ **"The clash"** — the plaque that exists because a re-entry is invisible otherwise.
    ///
    /// A simultaneous-move board that suddenly asks one seat for another move, with two squares
    /// newly dead and the turn counter unmoved, is unreadable without being told: it looks like the
    /// game lost the move. So this says, in order, WHAT was contested, WHO owes a fresh move, WHO is
    /// locked, and HOW MANY squares the turn has burned.
    ///
    /// `None` when the turn has no marks (nothing has clashed) — the plaque appears exactly when
    /// there is something to explain. Entirely PUBLIC: every fact here (which squares are marked,
    /// which seats re-enter, which are locked) was produced by revealing every submission at once,
    /// so none of it is per-viewer.
    fn conflict_plaque(&self, viewer: Option<Seat>) -> Option<ViewNode> {
        if self.marks.is_empty() {
            return None;
        }
        // A marked square paints as a bare `×`, which loses WHICH piece is standing on it — so the
        // prose names it. (The piece is still there: the square is dead, not empty.)
        let squares = |cs: &[Coord]| {
            cs.iter()
                .map(|c| {
                    let what = match self.board.cell_at(*c) {
                        REP => ", where a repulsor stands",
                        ATT => ", where an attractor stands",
                        AUTO => ", the automaton's own square",
                        _ => ", an empty square",
                    };
                    format!("({},{}){what}", c.0, c.1)
                })
                .collect::<Vec<_>>()
                .join(" · ")
        };
        let round = self.conflict_round_no();
        let mut kids = vec![ViewNode::Text(format!(
            "The seats CONTESTED the same square, so this round did NOT resolve. The ruleset does \
             not throw the clashing moves away: it MARKS the contested coordinate — {} — and \
             re-opens the round. A marked square is dead for the rest of this turn: nobody may move \
             a piece off it, and nobody may move a piece onto it. The board is FROZEN until a round \
             comes back clean, and the turn counter has not moved.",
            squares(&self.marks)
        ))];
        // ⚑ **WHAT THE TWO SEATS ACTUALLY TRIED** — the collision itself, named.
        //
        // This is the one moment in the game where you get to see the other seat's intent, and it
        // was being thrown away: the plaque said a square had been contested and never said WHO
        // reached for what. `conflict_subs` already holds the pair the round considered (it is
        // recorded for the fold), so the drama costs nothing but the sentence.
        //
        // NOT a fog regression — it is the ruleset's own disclosure. `roundStep` detects a clash by
        // revealing every submission SIMULTANEOUSLY, so a move that took part in one was published
        // before it was marked; the surface already tells both seats a LOCKED move on exactly that
        // reasoning, and this applies it symmetrically when both seats clashed instead of one. What
        // stays sealed is the RE-SUBMISSION, which is a fresh seal like any first one.
        if let Some(subs) = self.conflict_subs.last() {
            let tried = |s: Seat| {
                let m = subs[s.idx()];
                format!(
                    "seat {} reached for ({},{}) and sent it to ({},{})",
                    s.label(),
                    m.frm.0,
                    m.frm.1,
                    m.to.0,
                    m.to.1
                )
            };
            let same_piece = subs[0].frm == subs[1].frm;
            let same_landing = subs[0].to == subs[1].to;
            kids.push(ViewNode::Text(format!(
                "WHAT COLLIDED: {}, and {}. {} (Those two moves are public now — the ruleset opened \
                 every submission at once to find the clash. What you seal NEXT is secret again.)",
                tried(Seat::A),
                tried(Seat::B),
                if same_piece {
                    "You both grabbed the SAME PIECE and pulled it two ways, so neither of you got \
                     it."
                } else if same_landing {
                    "Two different pieces were sent to the SAME SQUARE, and only one thing can \
                     stand there."
                } else {
                    "Their paths crossed on the marked square."
                },
            )));
        }
        let waiting_seats: Vec<Seat> = self.waiting.iter().map(|w| Seat::from_idx(*w)).collect();
        let locked_seats: Vec<Seat> = [Seat::A, Seat::B]
            .into_iter()
            .filter(|s| !self.is_waiting(*s))
            .collect();
        let names = |ss: &[Seat]| {
            ss.iter()
                .map(|s| format!("seat {}", s.label()))
                .collect::<Vec<_>>()
                .join(" and ")
        };
        kids.push(ViewNode::Text(format!(
            "RE-SUBMITTING: {}{}. {}",
            names(&waiting_seats),
            match viewer {
                Some(v) if waiting_seats.contains(&v) => " — that is YOU",
                Some(_) => "",
                None => "",
            },
            if locked_seats.is_empty() {
                "Nobody is locked this round: every submission named a contested square, so every \
                 seat owes a fresh move."
                    .to_string()
            } else {
                format!(
                    "LOCKED: {} — that move was not part of the clash, it stands untouched, and it \
                     executes when the round finally resolves.",
                    names(&locked_seats)
                )
            }
        )));
        // THE TERMINATION FACT, said out loud. Each re-entry marks at least one NEW square and the
        // board has finitely many, so the turn cannot re-enter forever — and it is the deployed
        // cell, not this sentence, that enforces it (`marked` is strictly monotone under
        // `resubmit`).
        kids.push(ViewNode::Text(format!(
            "This turn has re-opened {} time{} and burned {} of the board's {} squares. Every \
             re-entry has to burn a NEW one, so the round runs out of squares before it runs \
             forever — the executor refuses a re-entry that marks nothing.",
            round,
            if round == 1 { "" } else { "s" },
            self.marks.len(),
            CELLS,
        )));
        let pill = |text: String, tag: &str| ViewNode::Pill {
            text,
            tag: tag.to_string(),
            slot: None,
            cases: Vec::<PillCase>::new(),
        };
        let mut pills = vec![pill(format!("round {} · RE-SUBMIT", round + 1), "bad")];
        for c in &self.marks {
            pills.push(pill(format!("× ({},{}) dead", c.0, c.1), "bad"));
        }
        for s in [Seat::A, Seat::B] {
            pills.push(if self.is_waiting(s) {
                pill(format!("seat {} · re-submitting", s.label()), "warn")
            } else {
                pill(format!("seat {} · locked", s.label()), "muted")
            });
        }
        kids.push(ViewNode::Row(pills));
        Some(ViewNode::Section {
            title: "The clash — this round did not resolve".to_string(),
            tag: "bad".to_string(),
            children: kids,
        })
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
        // The seats still owed a submission this round — `waiting` minus whoever has already
        // sealed, which is the honest list on a re-entry (a LOCKED seat is not being waited on).
        let still_to_seal = |f: &dyn Fn(usize) -> bool| -> Vec<&'static str> {
            self.waiting
                .iter()
                .filter(|w| f(**w as usize))
                .map(|w| Seat::from_idx(*w).label())
                .collect()
        };
        let Some(s) = viewer else {
            // The spectator's line — the same facts, in the third person.
            return match self.phase() {
                Phase::Commit => format!(
                    "Both seats are sealing a move at the same time. Still to seal: {}.",
                    still_to_seal(&|i| self.committed[i].is_none()).join(" and ")
                ),
                Phase::Resubmit => format!(
                    "⚑ The round CLASHED and did not resolve: {} marked, the board frozen, and \
                     seat {} owe a FRESH move. Still to re-seal: {}.",
                    self.marks
                        .iter()
                        .map(|c| format!("({},{})", c.0, c.1))
                        .collect::<Vec<_>>()
                        .join(" · "),
                    self.waiting
                        .iter()
                        .map(|w| Seat::from_idx(*w).label())
                        .collect::<Vec<_>>()
                        .join(" and "),
                    still_to_seal(&|i| self.committed[i].is_none()).join(" and ")
                ),
                Phase::Reveal => {
                    "Both moves are sealed. Each seat now opens its own seal.".to_string()
                }
                Phase::Resolve => {
                    "Both moves are open — the round is one press from firing.".to_string()
                }
                Phase::Over => "The match is over.".to_string(),
            };
        };
        let i = s.idx();
        let other = s.other();
        // A seat that is not being waited on this round: its move is LOCKED and it presses nothing.
        if !self.is_waiting(s) && !matches!(self.phase(), Phase::Resolve | Phase::Over) {
            return format!(
                "Your move was NOT part of the clash, so it is LOCKED and stands exactly as you \
                 sealed it — you owe nothing this round. Seat {} is choosing a fresh move; when \
                 they seal and open, the round resolves and your move executes with theirs.",
                other.label()
            );
        }
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
                "YOUR MOVE. Click any piece to pick it up; the squares it can reach light up, and \
                 clicking a lit square seals a move there. Both seats move at once, so nothing \
                 happens on the board until you have both sealed."
                    .to_string()
            }
            Phase::Resubmit if self.committed[i].is_some() => format!(
                "Re-sealed. Waiting for seat {} to re-seal after the clash.",
                other.label()
            ),
            Phase::Resubmit => format!(
                "⚑ YOU CLASHED, so this round did not happen: the contested square{} {} now \
                 MARKED (the × squares) and dead for the rest of this turn, the board is frozen \
                 exactly as it was, and you owe a FRESH move. Pick a piece and seal again — you \
                 cannot use a marked square as a source or a destination.",
                if self.marks.len() == 1 {
                    " is"
                } else {
                    "s are"
                },
                self.marks
                    .iter()
                    .map(|c| format!("({},{})", c.0, c.1))
                    .collect::<Vec<_>>()
                    .join(" · "),
            ),
            Phase::Reveal if !self.revealed[i] => {
                "Both moves are sealed. Press Reveal your sealed move to open yours.".to_string()
            }
            Phase::Reveal => format!(
                "You have opened. Waiting for seat {} to open theirs.",
                other.label()
            ),
            Phase::Resolve => {
                "Both moves are open. Press Resolve the round — if you contested the \
                               same square it MARKS that square and re-opens the round; otherwise \
                               the moves apply and THEN the automaton takes its step."
                    .to_string()
            }
            Phase::Over => "The match is over.".to_string(),
        }
    }

    /// **"Where the turn stands"** — the status plaque: which of the three phases is live, who you
    /// are at this table, whether each seat has sealed / opened, and the one sentence that says
    /// what to do now.
    fn standing(&self, viewer: Option<Seat>) -> ViewNode {
        let phase = self.phase();
        // `Resubmit` IS the sealing station, so station 1 lights for it too — the round is back at
        // the start of the ladder, which is the whole point of the fourth pill below.
        let phase_pill = |p: Phase, label: &str| ViewNode::Pill {
            text: label.to_string(),
            tag: if p == phase || (p == Phase::Commit && phase == Phase::Resubmit) {
                "good"
            } else {
                "muted"
            }
            .to_string(),
            slot: None,
            cases: Vec::<PillCase>::new(),
        };
        // A seat's PUBLIC standing this turn (never its move): choosing → sealed → opened, or
        // LOCKED once a clash has taken it out of the waiting set.
        let seat_pill = |s: Seat| {
            let i = s.idx();
            let (word, tag) = if !self.marks.is_empty() && !self.is_waiting(s) {
                ("LOCKED · move stands", "muted")
            } else if self.revealed[i] {
                ("opened", "good")
            } else if self.committed[i].is_some() {
                ("sealed", "accent")
            } else if self.marks.is_empty() {
                ("still choosing", "warn")
            } else {
                ("RE-SUBMITTING", "bad")
            };
            let whose = match viewer {
                Some(v) if v == s => " (you)",
                Some(_) => " (them)",
                // A seatless viewer got a blank here, so both pills read `seat A · sealed` /
                // `seat B · sealed` and the reader still could not place themselves. The pill now
                // says which seat is free and which is the one they would take.
                None if self.claimable_seat() == Some(s) => " (YOURS on your first move)",
                None if self.seats[s.idx()].is_none() => " (open)",
                None => " (another player)",
            };
            ViewNode::Pill {
                text: format!("seat {}{whose} · {word}", s.label()),
                tag: tag.to_string(),
                slot: None,
                cases: Vec::<PillCase>::new(),
            }
        };
        // ⚑ "EVERY CONTROL IS INERT" WAS FALSE, AND PROVABLY SO. This branch told a seatless viewer
        // exactly that while `board_grid(None)` went on serving 121 cell buttons carrying no
        // `disabled` attribute — and the QA reader proved it from a before/after pair: pressing an
        // "inert" control changed their seat, their hand and the turn counter
        // (`docs/reference/UX-QA-SWEEP-2026-07-26.md`, finding 2).
        //
        // The claim is now split by the state that decides it. A CLAIMANT (a seat is free) is told
        // the truth: the board is live and their first landed press takes that seat. A SPECTATOR
        // (both seats held) keeps the honest version — and it is honest twice over there, because
        // the web spectator route additionally wraps the whole surface in a `disabled` fieldset
        // (`dreggnet_web::table_door::spectate_page`) and `table_seats::enforce` refuses a seatless
        // POST on a locked table outright.
        let who = match viewer {
            Some(s) => format!(
                "You hold seat {} — your goal corners are {}.",
                s.label(),
                Self::goal_text(s)
            ),
            None => match self.claimable_seat() {
                Some(seat) => format!(
                    "You hold no seat here YET, so both sealed moves are fog to you — but the board \
                     below is LIVE, not a picture. The first move you land CLAIMS seat {}, whose \
                     goal corners are {}. Pick up a piece and the squares it can reach will light.",
                    seat.label(),
                    Self::goal_text(seat),
                ),
                // ⚑ NOT "every control is inert" HERE EITHER, and for a subtler reason. With both
                // seats held there is nothing for this viewer to claim, but the board is the SHARED
                // one the seated players press (Discord posts exactly this surface as the channel
                // board), so its squares are still drawn as controls. "Inert" would be a claim about
                // the MARKUP that is false; the true statement is about the EXECUTOR, which refuses
                // an advance from an identity holding no seat ("both seats are taken — you are a
                // spectator") and commits nothing.
                None => "Both seats are held, so you are watching: BOTH sealed moves are fog to \
                         you. The board still draws its squares — it is the same board the two \
                         players press — but nothing you press can move it: the executor refuses a \
                         move from an identity holding no seat, and commits nothing."
                    .to_string(),
            },
        };
        // The ladder is SEAL → OPEN → RESOLVE, plus the fourth station the ruleset adds: a clash
        // sends the round back to the start of the ladder with the contested square burned. It is
        // shown always (greyed when the round is clean) so the possibility is legible BEFORE it
        // happens rather than appearing out of nowhere when it does.
        let mut ladder = vec![
            phase_pill(Phase::Commit, "1 · SEAL"),
            phase_pill(Phase::Reveal, "2 · OPEN"),
            phase_pill(Phase::Resolve, "3 · RESOLVE"),
        ];
        ladder.push(ViewNode::Pill {
            text: if self.marks.is_empty() {
                "↺ CLASH → RE-SUBMIT".to_string()
            } else {
                format!(
                    "↺ CLASH → RE-SUBMIT · round {} · {} marked",
                    self.conflict_round_no() + 1,
                    self.marks.len()
                )
            },
            tag: if self.marks.is_empty() {
                "muted"
            } else {
                "bad"
            }
            .to_string(),
            slot: None,
            cases: Vec::<PillCase>::new(),
        });
        ViewNode::Section {
            title: "Where the turn stands".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Row(ladder),
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
        // ⚑ **WHAT IT CAN SEE** — the four rays, and the rule that follows from them. Without this
        // the board is 121 squares of undifferentiated legality: the stock opening offers a seat 720
        // legal moves and exactly 20 of them move the automaton at all, so a player picking off the
        // rook-line highlight alone is picking from a set that is 97% noise. The four sightlines are
        // WHY, and they are cheap to say because the rays are the Lean's own.
        if !self.ended {
            if let Some(lines) = sightlines_of(&self.board) {
                let found = lines
                    .iter()
                    .map(Sightline::found)
                    .collect::<Vec<_>>()
                    .join(", ");
                let n = sightline_squares(&self.board, &lines).len();
                let caps = lines.iter().filter(|l| l.caps_a_piece()).count();
                kids.push(ViewNode::Text(format!(
                    "WHAT IT CAN SEE — one arm along each direction of its rank and file: {found}. \
                     Those are the whole of what it answers: each axis is a COMPARISON of the two \
                     distances on it, so nothing off the arms reaches the decision at all. The arms \
                     are drawn ─ and │ on the board and there are {n} squares on them, {caps} of \
                     which hold the pieces that cap the rays. A move that neither LEAVES nor LANDS \
                     ON one of those {n} squares cannot change what the automaton does, however \
                     legal it is. That is where the game actually is.",
                )));
            }
        }
        // HOW CLOSE IS IT TO ENDING THE MATCH, and — the part that was never shown — WHO IS AHEAD.
        //
        // ⚑ The distance pills alone are not a stake signal: while the automaton sits anywhere on
        // the neutral mid-line both seats read the SAME number, which is exactly the position two
        // competent seats freeze on (`AutomataflRules` §6B: 100% draws, in 8–11 turns). The verdict
        // is the ruleset's answer to that freeze, and it was computed once at turn 64 and shown
        // nowhere — so the contest the players were actually in was invisible for the whole match.
        let contest = self.contest();
        let dist_pill = |s: Seat| {
            let (word, tag) = match contest.and_then(|st| st.dist[s.idx()]) {
                Some(0) => ("ON a goal corner".to_string(), "bad"),
                Some(1) => ("1 step from a goal".to_string(), "bad"),
                Some(d @ 2..=3) => (format!("{d} steps from a goal"), "warn"),
                Some(d) => (format!("{d} steps from a goal"), ""),
                // `goalDistance = none`: the seat owns no corner. NOT the same as standing on one.
                None => ("owns no goal corner".to_string(), "muted"),
            };
            ViewNode::Pill {
                text: format!("seat {} · {word}", s.label()),
                tag: tag.to_string(),
                slot: None,
                cases: Vec::<PillCase>::new(),
            }
        };
        kids.push(ViewNode::Row(vec![dist_pill(Seat::A), dist_pill(Seat::B)]));
        if !self.ended {
            let left = MAX_TURNS.saturating_sub(self.turn_no);
            kids.push(ViewNode::Text(match contest {
                Some(st) => format!(
                    "ON THE CLOCK: {left} more resolution{} and the match is adjudicated where it \
                     stands — the seat whose own corner is strictly nearer takes it. {} So a \
                     position is not safe just because nobody has reached a corner.",
                    if left == 1 { "" } else { "s" },
                    match st.verdict {
                        Some(w) => format!(
                            "Right now it would go to SEAT {} — nearer its own corner on this \
                             board.",
                            Seat::from_idx(w).label()
                        ),
                        None =>
                            "Right now it is a DEAD HEAT: both seats are exactly as far from their \
                             own corners, so the adjudication draws. Parking here wins nobody the \
                             match."
                                .to_string(),
                    }
                ),
                None => format!(
                    "ON THE CLOCK: {left} more resolutions before the match is adjudicated where \
                     it stands. (The game oracle did not answer, so who is ahead is unknown.)"
                ),
            }));
        }
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
                "Automatafl — turn {}{} · phase: {}",
                self.turn_no,
                if self.marks.is_empty() {
                    String::new()
                } else {
                    format!(" · round {}", self.conflict_round_no() + 1)
                },
                match phase {
                    Phase::Commit => "COMMIT (both seats seal a move)",
                    Phase::Resubmit => "⚑ RE-SUBMIT (the round clashed — the square is marked)",
                    Phase::Reveal => "REVEAL (both moves sealed — open yours)",
                    Phase::Resolve => "RESOLVE (both open — fire the round)",
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
                children: {
                    // The RULE, and only the rule. What each glyph and bracket MEANS moved to
                    // `board_legend` below — it used to be said here, in words that only worked in
                    // pixels ("the round brass discs", "the angular pale blades", "drawn dimmed
                    // and outlined"), which is no help at all on a channel that paints one
                    // character per square. The web page's own richer piece prose still lives in
                    // `dreggnet_web::automatafl_web` and the guide.
                    let mut board = vec![
                        ViewNode::Text(format!(
                            "Pick up a piece and the squares it can actually REACH light up: a \
                             piece moves like a rook and stops at the first thing in its way, so \
                             the light stops there too. A square further along that line reads as \
                             BLOCKED — you may still seal a move to it, and it runs only if the \
                             other seat moves the piece that is in the way.{}",
                            if self.marks.is_empty() {
                                ""
                            } else {
                                " ⚑ A × square is MARKED: a clash burned it, and for the rest of \
                                 this turn nobody may move a piece off it or onto it."
                            }
                        )),
                        self.board_grid(viewer),
                    ];
                    board.extend(Self::board_legend());
                    board
                },
            },
        ];
        // The clash plaque goes ABOVE the automaton's: when a round has re-opened, "why am I being
        // asked for another move" is the reader's first question and the daemon's step is not.
        if let Some(clash) = self.conflict_plaque(viewer) {
            kids.push(clash);
        }
        kids.push(self.automaton_plaque());
        kids.push(self.move_line(Seat::A, viewer));
        kids.push(self.move_line(Seat::B, viewer));
        kids.push(self.action_menu(viewer));
        Surface(ViewNode::VStack(kids))
    }
}

/// The reason an advance was refused (an honest referee-level / offering-level refusal — nothing
/// commits either way).
///
/// ⚑ `why` is **PLAYER copy** and every caller here writes it as a sentence about the board. The one
/// class that did not was `refuse(e.to_string())` on a `spween_dregg::WorldError`, which pasted an
/// internal architecture's name onto a player's screen at five sites in this file; those call
/// [`refuse_world_error`], which splits the audiences (player sentence back, operator detail logged).
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
            turn_start: board.clone(),
            board,
            turns_played: Vec::new(),
            // `AutomataflRules.openRound board [0, 1]` — no markers, no locks, every seat owes a
            // move. A fresh round state per turn IS `model.py::ClearState`.
            marks: Vec::new(),
            locked: Vec::new(),
            waiting: vec![0, 1],
            conflict_subs: Vec::new(),
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
        // `Resubmit` offers exactly the same affordances as `Commit` — select a piece, seal a
        // destination — over a board with marks on it. The marked squares are already absent from
        // `movable` / `legal_targets` (the LEAN's `moveLegalB` with this turn's marks), so no
        // affordance here can name one.
        if phase.is_sealing() {
            // ORDER MATTERS on a button-budgeted frontend, and the budget is REAL — but it is the
            // renderer's, not this list's, and it is not the number this comment used to name.
            //
            // ⚑ THE CORRECTION. This said "the Discord/Telegram renderers paint the first ≤25
            // actions as buttons and silently drop the rest". Discord's 25 is a hard API ceiling on
            // components. Telegram had NO cap of any kind: `build_present_request*` made every
            // action its own row, so a fresh 11×11 opening painted 36 separate `Select (x,y)` rows
            // and a sealed seat painted the whole ~50-row list lock-prefixed. A comment asserting a
            // bound that did not exist is exactly why that survived — so read the renderer, not
            // this line: `dreggnet_telegram::api::TELEGRAM_KEYBOARD_MAX_ROWS` (16 rows, short
            // labels packed several per row) and `TELEGRAM_KEYBOARD_MAX_LOCKED` (12). Neither drops
            // anything silently: what does not fit is counted in the message text, and every action
            // stays recorded as presented, so `/act` still reaches it.
            //
            // What the order buys, given a budget of any size: at 11×11 the stock opening has 36
            // movable pieces, so putting the SEAL targets after every select left a Discord player
            // able to select a piece and never able to seal it. The live selection's targets
            // therefore come FIRST (the affordance the phase is waiting on), then the selects — and
            // the Telegram renderer's own live-before-locked sort preserves this order inside each
            // band rather than reshuffling it. The WEB board is unaffected either way: every square
            // of the `CoordGrid` is its own POST form, so the browser never reads this list.
            //
            // One `commit` affordance per PROPOSABLE target of EITHER seat's live selection (a
            // seat's own board grid shows only its own; the executor re-checks the seat on advance).
            //
            // ⚑ AND THE LABEL SAYS WHICH KIND IT IS. On Discord / Telegram / WeChat there is no CSS
            // and no `data-tag`: the button label is the whole of what a player reads, so a target
            // that would not execute has to say so IN ITS NAME or those frontends keep the exact bug
            // the board just stopped painting. The proposal stays offered — it is legal, and a
            // blocked square goes live the moment the other seat lifts the piece in the way.
            let mut targets: Vec<usize> = Vec::new();
            let mut live: Vec<usize> = Vec::new();
            for seat in [Seat::A, Seat::B] {
                if !session.is_waiting(seat) {
                    continue;
                }
                if let Some(src) = session.sel[seat.idx()] {
                    for t in session.legal_targets(src) {
                        if let Some(i) = index_of(t) {
                            if !targets.contains(&i) {
                                targets.push(i);
                            }
                        }
                    }
                    for t in session.executable_targets(src) {
                        if let Some(i) = index_of(t) {
                            if !live.contains(&i) {
                                live.push(i);
                            }
                        }
                    }
                }
            }
            targets.sort_unstable();
            for idx in targets {
                let c = coord_of(idx);
                out.push(Action::new(
                    if live.contains(&idx) {
                        format!("Seal a move to ({},{})", c.0, c.1)
                    } else {
                        format!(
                            "Seal a move to ({},{}) — BLOCKED: a piece is in the way, so it only \
                             runs if the other seat moves that piece",
                            c.0, c.1
                        )
                    },
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
                if !session.phase().is_sealing() {
                    return refuse("the commit phase is closed this round");
                }
                if !session.is_waiting(seat) {
                    return refuse(
                        "your move is LOCKED this round — it was not part of the clash, so it \
                         stands as sealed and you do not re-submit",
                    );
                }
                if session.committed[i].is_some() {
                    return refuse("your move is already sealed this round");
                }
                let Some(idx) = usize::try_from(input.arg).ok().filter(|&i| i < CELLS) else {
                    return refuse(format!("square {} is off the board", input.arg));
                };
                let c = coord_of(idx);
                // ⚑ THE MARKS RE-CHECK, at the SOURCE end. A marked coordinate is illegal as a
                // source for everyone for the rest of the turn (`MoveLegal`: `m.frm ∉ marks`), so a
                // marked square cannot even be picked up — refused by NAME rather than left to fail
                // later as a bare "illegal move".
                if session.is_marked(c) {
                    return refuse(format!(
                        "({},{}) is MARKED — a clash burned that square, and for the rest of this \
                         turn no piece may leave it or land on it",
                        c.0, c.1
                    ));
                }
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
                        refuse(refuse_world_error(&e))
                    }
                }
            }

            COMMIT => {
                if !session.phase().is_sealing() {
                    return refuse("the commit phase is closed this round");
                }
                if !session.is_waiting(seat) {
                    return refuse(
                        "your move is LOCKED this round — it was not part of the clash, so it \
                         stands as sealed and you do not re-submit",
                    );
                }
                if session.committed[i].is_some() {
                    return refuse("your move is already sealed this round");
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
                // the automaton banned as a SOURCE, and ⚑ NEITHER ENDPOINT A MARKED COORDINATE).
                // The marks are passed, so on a re-submission this IS the ruleset's marks-legality
                // re-check: a move onto (or off) a square a clash burned is REFUSED here, and
                // nothing commits. An illegal move commits NOTHING, and a move nobody can
                // adjudicate commits nothing either.
                match rules::move_legal(&session.board, &session.marks, &mv) {
                    Ok(true) => {}
                    Ok(false) if session.is_marked(frm) || session.is_marked(to) => {
                        return refuse(format!(
                            "({},{}) → ({},{}) names a MARKED square: a clash burned {}, and for \
                             the rest of this turn it is illegal as a source AND as a destination, \
                             for both seats",
                            frm.0,
                            frm.1,
                            to.0,
                            to.1,
                            if session.is_marked(frm) {
                                format!("({},{})", frm.0, frm.1)
                            } else {
                                format!("({},{})", to.0, to.1)
                            }
                        ));
                    }
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
                        refuse(refuse_world_error(&e))
                    }
                }
            }

            REVEAL => {
                if !matches!(session.phase(), Phase::Reveal) {
                    return refuse("both moves must be sealed before a reveal");
                }
                if !session.is_waiting(seat) {
                    return refuse(
                        "your move is LOCKED this round — you already opened it, and it stands",
                    );
                }
                if session.revealed[i] {
                    return refuse("you already revealed this round");
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
                        refuse(refuse_world_error(&e))
                    }
                }
            }

            RESOLVE => {
                if !matches!(session.phase(), Phase::Resolve) {
                    return refuse("both seats must reveal before the round resolves");
                }
                let ma = session.committed[0].expect("sealed");
                let mb = session.committed[1].expect("sealed");
                let stock_goals = match goals() {
                    Ok(g) => g,
                    Err(why) => {
                        return refuse(format!("the goal assignment is unavailable: {why}"));
                    }
                };
                // ⚑ **ONE ROUND, DECIDED ENTIRELY BY THE LEAN** — `AutomataflRules.roundStep`
                // through `@[export] dregg_automatafl_rules`, ONE call:
                //
                //   round TIE BOARD GOALS marks locked waiting subs
                //     → `A marks locked waiting`   (re-enter: the clash is MARKED)
                //     → `R win BOARD`              (resolved: the moves applied, the daemon stepped,
                //                                   the win checked ON ENTRY)
                //
                // Nothing below computes the clash set, the marks, the freeze, the lock set or the
                // waiting set: `round` returns all five. The surface's only job is to CARRY them.
                //
                // `subs` is the WAITING seats' submissions; a locked seat's move rides in `locked`,
                // which is where `roundStep` expects it (`all := rs.locked ++ fresh`).
                let subs: Vec<Move> = session
                    .waiting
                    .iter()
                    .filter_map(|w| session.committed[*w as usize])
                    .collect();
                let outcome = match rules::round(
                    &session.board,
                    stock_goals,
                    &session.marks,
                    &session.locked,
                    &session.waiting,
                    &subs,
                ) {
                    Ok(o) => o,
                    Err(why) => {
                        return refuse(format!("the game oracle could not run the round: {why}"));
                    }
                };

                // ── THE CONFLICT ARM: the round did NOT resolve. ────────────────────────────────
                if let rules::RoundOutcome::Again {
                    marks,
                    locked,
                    waiting,
                } = outcome
                {
                    // A re-entry that names NO seat would deadlock the turn (the same round would
                    // repeat forever with nobody able to submit). At n=2 this is unreachable — a
                    // fork/collide over two moves always names both — but it is refused rather than
                    // hung, because a surface that can hang is worse than one that says no.
                    if waiting.is_empty() {
                        return refuse(
                            "the ruleset marked a contested square but named no seat to \
                             re-submit — the turn cannot continue, so nothing is committed",
                        );
                    }
                    // The termination fact, checked rather than assumed: the executor's `resubmit`
                    // case pins `marked` strictly monotone, so a re-entry that marks nothing is
                    // refused THERE — this is the same refusal, by name, before any write.
                    if marks.len() <= session.marks.len() {
                        return refuse(format!(
                            "the round re-entered without marking a new square ({} → {}), which \
                             would let the turn re-enter forever — nothing is committed",
                            session.marks.len(),
                            marks.len()
                        ));
                    }
                    let before = (
                        session.marks.clone(),
                        session.locked.clone(),
                        session.waiting.clone(),
                        session.conflict_subs.clone(),
                        session.sel,
                        session.committed,
                        session.seal,
                        session.revealed,
                    );
                    // THE ROUND, RECORDED — the move set this round CONSIDERED (`locked ++ subs`,
                    // as the pair the seats hold). This is one `MultiRoundTurn::conflict_subs`
                    // entry, and it is what the Leg C leaf for this round is filled from.
                    session.conflict_subs.push([ma, mb]);
                    session.marks = marks;
                    session.locked = locked;
                    session.waiting = waiting;
                    // RE-OPEN COMMIT FOR EXACTLY THE WAITING SEATS. A locked seat keeps its
                    // selection, its seal, its plaintext and its reveal — its move STANDS. A waiting
                    // seat is wound back to "choose a piece", carrying the marks forward, so its
                    // next submission is re-checked against them (`COMMIT`'s `move_legal` above).
                    for w in session.waiting.clone() {
                        let k = w as usize;
                        session.sel[k] = None;
                        session.committed[k] = None;
                        session.seal[k] = 0;
                        session.revealed[k] = false;
                    }
                    // ONE REAL TURN under the `resubmit` method: board + turn_no + winner immutable,
                    // `marked` strictly monotone and ≤ CELLS (M3's n² bound, as a cell tooth).
                    return match session.game.commit_state(RESUBMIT, &session.state()) {
                        Ok(receipt) => {
                            session.turns += 1;
                            Outcome::Landed {
                                receipt,
                                ended: false,
                            }
                        }
                        Err(e) => {
                            // Nothing committed — restore the whole round state (anti-ghost). An
                            // unlanded re-entry is not a re-entry: the seats keep their moves.
                            session.marks = before.0;
                            session.locked = before.1;
                            session.waiting = before.2;
                            session.conflict_subs = before.3;
                            session.sel = before.4;
                            session.committed = before.5;
                            session.seal = before.6;
                            session.revealed = before.7;
                            refuse(refuse_world_error(&e))
                        }
                    };
                }

                // ── THE RESOLVED ARM: the round was clean. ──────────────────────────────────────
                let rules::RoundOutcome::Resolved { board: next, win } = outcome else {
                    unreachable!("the `Again` arm returned above");
                };
                // THE DAEMON'S STEP, RECORDED. The turn is `automatonStepCfg ∘ resolveMoves`, so the
                // board the automaton actually senses is the MID board (the round's moves already
                // applied) — read it there, exactly once, and keep the reading for the surface. The
                // step used to leave no trace at all: the reader saw two boards and had to diff.
                // The MID is asked for WITH THIS TURN'S MARKS, so on a turn that re-entered it is
                // the same mid the resolution used.
                let mut all_moves = session.locked.clone();
                all_moves.extend(subs.iter().copied());
                let mid = match rules::resolve_mid(&session.board, &session.marks, &all_moves) {
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
                    session.turn_start.clone(),
                    session.marks.clone(),
                    session.locked.clone(),
                    session.waiting.clone(),
                    session.conflict_subs.clone(),
                );
                session.last_step = Some(step);
                session.board = next;
                session.turn_no += 1;
                session.sel = [None, None];
                session.committed = [None, None];
                session.seal = [0, 0];
                session.revealed = [false, false];
                let capped = session.turn_no >= MAX_TURNS;
                // ⚑ ADJUDICATE THE CAP, do not draw it. `MAX_TURNS` used to end the match with
                // `winner = None` — a terminal rule no theorem had ever seen. The ruleset owns this
                // decision (`AutomataflRules.adjudicateCapped`, with `adjudicate_seated` and
                // `adjudicate_sound` proven): the seat strictly nearer its own goal wins, a seat
                // owning goals beats one owning none, exact parity is a genuine draw. Only consulted
                // when the cap actually bites and nobody has already won on entry.
                session.winner = match winner {
                    Some(w) => Some(w),
                    None if capped => {
                        match rules::adjudicate_capped(&session.board, stock_goals) {
                            // `adjudicate_capped` speaks the ruleset's wire vocabulary — a seat
                            // INDEX — while `session.winner` holds the surface's `Seat`. The gap
                            // is one `map`; leaving it unbridged made `dregg-automatafl` fail to
                            // compile, and because it is upstream of the bot and the web crate it
                            // took three unrelated lanes down with it for hours.
                            Ok(adjudicated) => adjudicated.map(Seat::from_idx),
                            Err(why) => {
                                // ANTI-GHOST. This arm used to return with the surface already
                                // advanced — the board moved, the turn counter moved, the seals were
                                // cleared — while the executor had committed NOTHING. Restore the
                                // pre-resolution state first, so a refusal is a refusal.
                                session.board = before.0;
                                session.sel = before.1;
                                session.committed = before.2;
                                session.seal = before.3;
                                session.revealed = before.4;
                                session.turn_no = before.5;
                                session.last_step = before.6;
                                return refuse(format!(
                                    "the game oracle could not adjudicate the capped match: {why}"
                                ));
                            }
                        }
                    }
                    None => None,
                };
                session.ended = session.winner.is_some() || capped;
                // RECORD THE TURN, WHOLE — its start board, every conflict round it went through,
                // and the pair that finally resolved. Appended only once the executor accepts the
                // resolution below (a refused resolution pops it). This is the `MultiRoundTurn`
                // the Leg C braid folds when `conflict_subs` is non-empty.
                session.turns_played.push(PlayedTurn {
                    start: before.7.clone(),
                    conflict_subs: std::mem::take(&mut session.conflict_subs),
                    clean_subs: [ma, mb],
                });
                // ⚑ CLEAR STATE (`model.py::ClearState`): markers, locks and pending moves die at
                // turn end, and the next turn opens on the resolved board with every seat owing a
                // move — `AutomataflRules.openRound`.
                session.marks.clear();
                session.locked.clear();
                session.waiting = vec![0, 1];
                session.turn_start = session.board.clone();

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
                        // INCLUDING the turn history and the whole round state: an unlanded round is
                        // not a played round, and the seats keep the moves they had opened.
                        session.board = before.0;
                        session.sel = before.1;
                        session.committed = before.2;
                        session.seal = before.3;
                        session.revealed = before.4;
                        session.turn_no = before.5;
                        session.last_step = before.6;
                        session.turn_start = before.7;
                        session.marks = before.8;
                        session.locked = before.9;
                        session.waiting = before.10;
                        session.conflict_subs = before.11;
                        session.winner = None;
                        session.ended = false;
                        session.turns_played.pop();
                        refuse(refuse_world_error(&e))
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
        // ⚑ THE ROUND STATE IS COMMITTED TOO. `marked` is the cell's record of how many squares this
        // turn has burned, and it is what the `resubmit` case pins strictly monotone — so a session
        // whose marks disagree with the cell's count has a termination tooth reading a number nobody
        // is standing behind.
        if committed.marked != session.marks.len() as u64 {
            return VerifyReport::broken(
                turns,
                format!(
                    "the committed marked-square count ({}) diverged from the round state's {} \
                     marks",
                    committed.marked,
                    session.marks.len()
                ),
            );
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
        // ⚑ A LOCKED seat is offered NOTHING but the resolve: it does not re-submit, and a clock
        // that reads this list must not forfeit it for failing to press a button it was never
        // handed. That is what makes `owes_a_move` and this list agree.
        let waiting = session.is_waiting(seat);
        for action in &mut all {
            let mine = match action.turn.as_str() {
                SELECT | COMMIT => waiting && phase.is_sealing() && session.committed[i].is_none(),
                REVEAL => waiting && matches!(phase, Phase::Reveal) && !session.revealed[i],
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
