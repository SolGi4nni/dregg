//! # The **Offering** — automatafl playable on every dreggnet frontend.
//!
//! [`AutomataflOffering`] hosts an n=2 automatafl match as a [`dreggnet_offerings::Offering`]: the
//! same `open`/`actions`/`advance`/`verify`/`render`/`render_for`/`price` shape every frontend
//! (web / Discord / Telegram / WeChat) already drives. It is the coordinate-grid sibling of
//! `dregg-multiway-tug`'s `TugOffering`: where the tug paints a hidden HAND, automatafl paints a
//! hidden MOVE on a shared BOARD.
//!
//! **The board is a [`deos_view::ViewNode::CoordGrid`]** — one [`deos_view::CoordCell`] per square,
//! the particle as the glyph (`·` vacuum, `R` repulsor, `A` attractor, `@` automaton), the
//! automaton cell marked, and each affordance-bearing square carrying the `{turn, arg}` a click
//! fires. Selecting one of your pieces LIGHTS ITS ROOK LINE: every legal target of that source
//! (same row or column, in-bounds, not the automaton's square — exactly
//! [`crate::reference::move_valid`]) is painted in the highlight-set; an illegal target (a diagonal,
//! the source itself, the automaton) is NOT.
//!
//! **The simultaneous-move shape, rendered.** Automatafl's turn is not alternating: both players
//! move at once. So the surface runs COMMIT → REVEAL → RESOLVE:
//! 1. **commit** — each seat selects a source and seals a destination. The executor stores only the
//!    COMMITMENT (a blake3 seal over the move + a per-turn nonce), never the plaintext;
//! 2. **reveal** — each seat opens its seal (the plaintext lands on the cell, checked against the
//!    commitment it opens);
//! 3. **resolve** — ONE real turn applies [`crate::reference::apply_turn`]: invalid moves filtered,
//!    conflicts dropped, the surviving moves applied, and the automaton takes its step.
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
//! `new == apply_turn(old, moves)`); this surface drives the same reference oracle the descriptors
//! pin.

use deos_view::{CoordCell, MenuItem, PillCase, ViewNode};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::game::{
    AutomataflGame, CELLS, COMMIT, GOAL_A, GOAL_B, MatchState, N, RESOLVE, REVEAL, SELECT,
    coord_of, index_of, opening_board,
};
use crate::reference::{ATT, AUTO, Board, Coord, Move, REP, VAC, apply_turn, move_valid};

/// The default match seed when a [`SessionConfig`] pins none.
const DEFAULT_SEED: u64 = 0xA07F;

/// A match runs at most this many resolved turns before it is called a draw (the surface's own
/// clock — the executor is happy to keep going).
const MAX_TURNS: u64 = 64;

/// A seat at the table (automatafl is n=2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seat {
    /// Seat A — goal square [`GOAL_A`].
    A,
    /// Seat B — goal square [`GOAL_B`].
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

    /// The seat's goal square — the automaton arriving here wins the match for them.
    pub fn goal(self) -> Coord {
        match self {
            Seat::A => GOAL_A,
            Seat::B => GOAL_B,
        }
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

/// A live automatafl match: the deployed executor game, the reference board (the witness oracle the
/// AIR pins), the two seats, and each seat's SEALED move (the plaintext the opponent cannot see).
pub struct AutomataflSession {
    /// The deployed executor game — every advance commits this state as ONE real verified turn.
    game: AutomataflGame,
    /// The reference board (the oracle: `apply_turn` computes each resolution).
    board: Board,
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

    /// The reference board (the committed position).
    pub fn board(&self) -> &Board {
        &self.board
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

    /// The LEGAL TARGETS of `src` — exactly the rook line [`move_valid`] admits (same row or column,
    /// distinct, in-bounds, and never the automaton's square). The highlight-set the board paints.
    pub fn legal_targets(&self, src: Coord) -> Vec<Coord> {
        (0..CELLS)
            .map(coord_of)
            .filter(|&to| {
                move_valid(
                    &self.board,
                    &Move {
                        who: 0,
                        frm: src,
                        to,
                    },
                )
            })
            .collect()
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
        let mut targets: Vec<Coord> = Vec::new();
        for &src in &selections {
            for t in self.legal_targets(src) {
                if !targets.contains(&t) {
                    targets.push(t);
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

            let (tag, highlight) = if is_auto {
                ("accent", true)
            } else if is_selected {
                ("warn", true)
            } else if is_target {
                ("good", true)
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

            let mut glyph = Self::glyph(p).to_string();
            if p == VAC && c == GOAL_A {
                glyph = "a".to_string(); // seat A's goal square
            } else if p == VAC && c == GOAL_B {
                glyph = "b".to_string();
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
                    text: format!("goal A ({},{})", GOAL_A.0, GOAL_A.1),
                    tag: "good".to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
                ViewNode::Pill {
                    text: format!("goal B ({},{})", GOAL_B.0, GOAL_B.1),
                    tag: "good".to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
            ]),
            ViewNode::Section {
                title: "The board".to_string(),
                tag: String::new(),
                children: vec![
                    ViewNode::Text(
                        "R = repulsor · A = attractor · @ = the automaton · a/b = the goals. \
                         Click a piece to select it — its rook line lights up."
                            .to_string(),
                    ),
                    self.board_grid(viewer),
                ],
            },
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
        let board = opening_board();
        let session = AutomataflSession {
            game,
            board,
            seats: [None, None],
            sel: [None, None],
            committed: [None, None],
            seal: [0, 0],
            revealed: [false, false],
            turn_no: 0,
            commits: 0,
            reveals: 0,
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
                // THE LEGALITY TOOTH — exactly the reference's `move_valid` (rook-line, distinct,
                // in-bounds, never the automaton). An illegal move commits NOTHING.
                if !move_valid(&session.board, &mv) {
                    return refuse(format!(
                        "illegal move ({},{}) → ({},{}): a move is a rook line to a distinct \
                         in-bounds square, and never touches the automaton",
                        frm.0, frm.1, to.0, to.1
                    ));
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
                // THE RESOLUTION — the pure transition the AIR re-checks in-circuit: validity
                // filter → conflict resolve → apply → the automaton's step.
                let next = apply_turn(&session.board, &[ma, mb]);
                let winner = if next.auto == GOAL_A {
                    Some(Seat::A)
                } else if next.auto == GOAL_B {
                    Some(Seat::B)
                } else {
                    None
                };

                let before = (
                    session.board.clone(),
                    session.sel,
                    session.committed,
                    session.seal,
                    session.revealed,
                    session.turn_no,
                );
                session.board = next;
                session.turn_no += 1;
                session.sel = [None, None];
                session.committed = [None, None];
                session.seal = [0, 0];
                session.revealed = [false, false];
                session.winner = winner;
                session.ended = winner.is_some() || session.turn_no >= MAX_TURNS;

                match session.game.commit_state(RESOLVE, &session.state()) {
                    Ok(receipt) => {
                        session.turns += 1;
                        Outcome::Landed {
                            receipt,
                            ended: session.ended,
                        }
                    }
                    Err(e) => {
                        // Nothing committed — restore the pre-resolution surface (anti-ghost).
                        session.board = before.0;
                        session.sel = before.1;
                        session.committed = before.2;
                        session.seal = before.3;
                        session.revealed = before.4;
                        session.turn_no = before.5;
                        session.winner = None;
                        session.ended = false;
                        refuse(e.to_string())
                    }
                }
            }

            other => refuse(format!("unknown action method `{other}`")),
        }
    }

    /// Re-verify the committed match: the executor's COMMITTED board must be exactly the reference
    /// board (translation validation — the substrate reproduces the game), every square must hold a
    /// real particle code, and there must be exactly one automaton, where the state says it is.
    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let committed = session.game.read_state();
        let turns = session.turns;
        if committed.cells != session.board.cells {
            return VerifyReport::broken(turns, "the committed board diverged from the reference");
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
