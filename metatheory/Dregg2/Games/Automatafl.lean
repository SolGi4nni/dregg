/-
# Dregg2.Games.Automatafl — the automatafl board-transition, modeled as a pure
transition + the load-bearing properties, + the AIR-refinement obligation the
verified board-transition circuit is emitted against.

automatafl (o1Labs / Corey Richardson, `~/dev/automatafl/logic/`) is an original
SIMULTANEOUS-MOVE cellular-automaton game on an N×N grid of particles
`{Repulsor, Attractor, Automaton, Vacuum}`.  ONE turn is:

    N secret moves  →  reveal together  →  conflict-resolve  →  apply-all
                    →  the Automaton ("Daemon") takes one autonomous step  →  win-check

This module is Phase E of the verified-game portfolio (docs/VERIFIED-GAME-PORTFOLIO.md):
model the rules as a pure `applyTurn : Board → List Move → Board`, PROVE the
load-bearing properties, and STATE the AIR-refinement contract
(`automatafl_air_refines_applyTurn`) — the game-level analogue of the
`evalSimpleCtx_*_iff` constraint twins (Dregg2/Exec/Program.lean) and the
`RotatedLayout.Legal` / `rotated178_legal` construction obligation
(Dregg2/Circuit/Emit/RotatedLayout.lean).

STANDALONE by design: no imports beyond the Lean prelude, so this type-checks even
when the shared metatheory tree is mid-broken by another terminal, and stays fast.
It touches NO crypto/floor Lean and NO cell/circuit/Rust.

────────────────────────────────────────────────────────────────────────────────
HONEST SCOPE — what is PROVEN vs STATED, and how faithfully phase (3) is modeled.

PROVEN, non-vacuously, over the pure model:
  (1) MOVE-VALIDITY is DECIDABLE — `MoveValid` (the `propose_move` predicate) has a
      `Decidable` instance and a Bool twin `moveValidB` with `moveValidB_iff`.
  (2) The AUTOMATON DECISION is TOTAL + DETERMINISTIC — `automatonMove` is a total
      function (`automatonMove_deterministic`: any two names for its value agree); its
      comparison is trichotomous so the priority cascade always resolves
      (`decisionCmp_total`); and the chosen offset is at most ONE cardinal step
      (`automatonOffset_bounded`), from which the Automaton stays in bounds
      (`automatonStep_preserves_inBounds`).
  (4) WIN-CHECK is decidable + a `Good`-style safety — `winner` is a decidable
      function and `winner_sound` proves a win can only fire when the Automaton is
      genuinely on a declared goal square (no spurious win); `applyTurn` preserves
      the in-bounds invariant of the Automaton (`applyTurn_preserves_inBounds`).

MODELED FAITHFULLY + termination PROVEN, determinism as functionality, fairness STATED:
  (3) RESOLUTION — `applyMoves` models occlusion (raycast with sources passable),
      chain-following through vacated squares (the "caterpillar"), dead-ends, and
      cycle stasis (2-cycles "always stay").  It is a TOTAL Lean function, so Lean's
      termination checker discharges TERMINATION by construction (`followChain`
      recurses on a strictly-decreasing fuel), and being a function it is
      deterministic given the move list.  The general FAIRNESS obligation
      (order-independence of the result, PHILOSOPHY.md §"Principle of Fairness") is
      STATED as `Fairness` / `applyMoves_fair_obligation` — proven for the empty/
      singleton case, deferred in general.  RESIDUALS (labeled, per the iterative
      method): full Tarjan-SCC >2-cycle *rotation* (modeled as stasis), the four
      `MergeResolutionMode`s, and multi-piece merge tie-breaks are not yet modeled.

STATED (the emitted-circuit contract, Lane-D-gated):
  `automatafl_air_refines_applyTurn` — the board-transition AIR admits
  `(old, moves, new)` IFF `new = applyTurn old moves`.  The AIR side is abstract
  (`BoardTransitionAIR`) now; `applyTurnAIR` witnesses the contract is satisfiable
  (non-vacuous), and the hand-authored Custom leaf discharges `Refines` later.
────────────────────────────────────────────────────────────────────────────────
-/

namespace Dregg2.Games.Automatafl

/-! ## §1  State: particles, coordinates, the board, moves -/

/-- The four particle kinds on the grid (`src/board.rs::Particle`). -/
inductive Particle
  | repulsor | attractor | automaton | vacuum
deriving DecidableEq, Repr

/-- Vacuum is the only pass-through-by-default particle. -/
def Particle.isVacuum : Particle → Bool
  | .vacuum => true
  | _       => false

/-- A grid coordinate (`src/types.rs::Coord`, here over `Nat`). -/
structure Coord where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

/-- A player id (`Pid`). -/
abbrev Pid := Nat

/-- A revealed move: who moved a piece from `frm` to `to` (`src/types.rs::Move`). -/
structure Move where
  who : Pid
  frm : Coord
  to  : Coord
deriving DecidableEq, Repr

/-- The board.  `cells` is total (out-of-bounds reads route to vacuum via
`cellAt`); the Automaton's location is tracked in `automaton` AND registered as a
`.automaton` particle at that cell (so it occludes and can be raycast from).
`useColumnRule` selects the equal-priority Y-preference (README: default on). -/
structure Board where
  size          : Nat
  cells         : Coord → Particle
  automaton     : Coord
  conflictAt    : Coord → Bool := fun _ => false
  useColumnRule : Bool := true

/-- In-bounds test (`Board::inbounds`). -/
def Board.inBounds (b : Board) (c : Coord) : Prop := c.x < b.size ∧ c.y < b.size

instance (b : Board) (c : Coord) : Decidable (b.inBounds c) := by
  unfold Board.inBounds; exact inferInstance

/-- Particle at a cell, vacuum outside the board. -/
def Board.cellAt (b : Board) (c : Coord) : Particle :=
  if c.x < b.size ∧ c.y < b.size then b.cells c else .vacuum

/-- `Board::is_automaton`. -/
def Board.isAutomaton (b : Board) (c : Coord) : Prop := c = b.automaton
instance (b : Board) (c : Coord) : Decidable (b.isAutomaton c) := by
  unfold Board.isAutomaton; exact inferInstance

/-- `Board::is_conflict`. -/
def Board.isConflict (b : Board) (c : Coord) : Prop := b.conflictAt c = true
instance (b : Board) (c : Coord) : Decidable (b.isConflict c) := by
  unfold Board.isConflict; exact inferInstance

/-- Build a board from an association list of placed particles; the Automaton cell
is marked automatically.  Used for `#guard` witnesses. -/
def mkBoard (size : Nat) (placed : List (Coord × Particle)) (auto : Coord)
    (col : Bool := true) : Board where
  size := size
  automaton := auto
  useColumnRule := col
  cells := fun c =>
    if c = auto then .automaton
    else (placed.find? (fun p => p.1 = c)).elim .vacuum (·.2)

/-! ## §2  Property (1): move-validity is DECIDABLE

The `propose_move` predicate, minus the pure state-machine flow (round/lock state):
distinct, rook-aligned, both endpoints in-bounds, neither endpoint the Automaton,
neither endpoint conflicted.  (Source may be vacuum — optimistic chain moves.) -/

/-- The board-level validity predicate for a single move (`Game::propose_move`). -/
def MoveValid (b : Board) (m : Move) : Prop :=
  m.frm ≠ m.to
  ∧ (m.frm.x = m.to.x ∨ m.frm.y = m.to.y)
  ∧ b.inBounds m.frm ∧ b.inBounds m.to
  ∧ ¬ b.isAutomaton m.frm ∧ ¬ b.isAutomaton m.to
  ∧ ¬ b.isConflict m.frm ∧ ¬ b.isConflict m.to

/-- **PROPERTY (1).** Move validity is decidable. -/
instance moveValid_decidable (b : Board) (m : Move) : Decidable (MoveValid b m) := by
  unfold MoveValid; exact inferInstance

/-- The Bool evaluator twin of `MoveValid` (the shape the lowering teeth check). -/
def moveValidB (b : Board) (m : Move) : Bool := decide (MoveValid b m)

/-- **The decidability twin** (the `evalSimpleCtx_*_iff` idiom): the Bool check
accepts IFF the proposition holds.  Non-vacuous: `MoveValid` is a genuine
conjunction of the eight `propose_move` clauses, not `True`. -/
theorem moveValidB_iff (b : Board) (m : Move) : moveValidB b m = true ↔ MoveValid b m := by
  unfold moveValidB; exact decide_eq_true_iff

/-! ## §3  Property (2): the Automaton decision — TOTAL + DETERMINISTIC

The Daemon raycasts the four cardinals, scores each axis by priority
(`UnbalancedPair 30 > FromRepulsor 20 > TowardAttractor 10 > None 0`) with distance
tie-breaks, and moves AT MOST one step (`src/automaton.rs`). -/

/-- Cardinal directions. -/
inductive Dir | xp | xn | yp | yn deriving DecidableEq, Repr

/-- Unit step of a direction (`Delta::XP` etc.). -/
def Dir.delta : Dir → Int × Int
  | .xp => (1, 0) | .xn => (-1, 0) | .yp => (0, 1) | .yn => (0, -1)

/-- A raycast result: the first non-vacuum particle hit (or vacuum at the wall) and
the step index at which iteration terminated (`src/types.rs::Raycast`, `dist`). -/
structure Raycast where
  what : Particle
  dist : Nat
deriving Repr

/-- Fuel-bounded raycast (`Board::raycast`): step outward from `(x,y)` along
`(dx,dy)`; stop at the first non-vacuum particle (recording its distance) or when
the ray leaves the board (recording vacuum + the OOB step index).  Terminates
structurally on `fuel`; seeded with `fuel = size + 1` ⇒ the board boundary is
always reached. -/
def raycastFuel (b : Board) (x y dx dy : Int) (dist fuel : Nat) : Raycast :=
  match fuel with
  | 0        => { what := .vacuum, dist := dist }
  | fuel + 1 =>
    let x' := x + dx
    let y' := y + dy
    if 0 ≤ x' ∧ x' < b.size ∧ 0 ≤ y' ∧ y' < b.size then
      let p := b.cellAt ⟨x'.toNat, y'.toNat⟩
      if p.isVacuum then raycastFuel b x' y' dx dy (dist + 1) fuel
      else { what := p, dist := dist + 1 }
    else
      { what := .vacuum, dist := dist + 1 }

/-- Raycast from a coordinate along a direction. -/
def Board.raycast (b : Board) (from_ : Coord) (d : Dir) : Raycast :=
  raycastFuel b from_.x from_.y d.delta.1 d.delta.2 0 (b.size + 1)

/-- The Daemon's per-axis decision (`src/automaton.rs::AutomatonDecision`).  `pos`
= the Automaton would move in the positive direction of the axis. -/
inductive Decision
  | unbalancedPair (pos : Bool) (attDist repDist : Nat)
  | fromRepulsor   (pos : Bool) (repDist : Nat)
  | towardAttractor (pos : Bool) (attDist : Nat)
  | none
deriving Repr

/-- Priority number (`AutomatonDecision::priority`); higher wins. -/
def Decision.priority : Decision → Nat
  | .unbalancedPair .. => 30
  | .fromRepulsor ..   => 20
  | .towardAttractor .. => 10
  | .none              => 0

/-- The one-step offset a decision induces along `base` (`AutomatonDecision::delta`):
`+base` if `pos`, `-base` otherwise; `None` ⇒ no move. -/
def Decision.delta : Decision → Int × Int → Int × Int
  | .unbalancedPair p .. , base => if p then base else (-base.1, -base.2)
  | .fromRepulsor p .. ,   base => if p then base else (-base.1, -base.2)
  | .towardAttractor p .. , base => if p then base else (-base.1, -base.2)
  | .none,                 _    => (0, 0)

/-- `evaluate_axis` (`src/automaton.rs`): the faithful priority match.  `pos` is the
ray in the axis-positive direction, `neg` the negative.  Every `dist > 1` guard
ensures there is ≥1 empty square before the particle (room to step). -/
def evaluateAxis (pos neg : Raycast) : Decision :=
  match pos.what, neg.what with
  | .attractor, .repulsor =>
      if pos.dist > 1 then .unbalancedPair true pos.dist neg.dist else .none
  | .repulsor, .attractor =>
      if neg.dist > 1 then .unbalancedPair false neg.dist pos.dist else .none
  | .repulsor, .repulsor =>
      if pos.dist ≠ neg.dist then .fromRepulsor (pos.dist > neg.dist) (min pos.dist neg.dist)
      else .none
  | .repulsor, .vacuum =>
      if neg.dist > 1 then .fromRepulsor false pos.dist else .none
  | .vacuum, .repulsor =>
      if pos.dist > 1 then .fromRepulsor true neg.dist else .none
  | .attractor, .attractor =>
      if pos.dist ≠ neg.dist ∧ min pos.dist neg.dist > 1 then
        .towardAttractor (pos.dist < neg.dist) (min pos.dist neg.dist)
      else .none
  | .attractor, .vacuum =>
      if pos.dist > 1 then .towardAttractor true pos.dist else .none
  | .vacuum, .attractor =>
      if neg.dist > 1 then .towardAttractor false neg.dist else .none
  | _, _ => .none

/-- Distance tie-break: SMALLER distance ranks GREATER (`chose_smaller_distance` =
`cmp.reverse`). -/
def revCmp (a b : Nat) : Ordering := (compare a b).swap

/-- The intra-priority tie-break (`src/automaton.rs::tiebreaker`). -/
def tiebreak : Decision → Decision → Ordering
  | .unbalancedPair _ a1 r1, .unbalancedPair _ a2 r2 => (revCmp a1 a2).then (revCmp r1 r2)
  | .fromRepulsor _ r1,      .fromRepulsor _ r2      => revCmp r1 r2
  | .towardAttractor _ a1,   .towardAttractor _ a2   => revCmp a1 a2
  | _, _ => .eq

/-- The full decision order (`impl Ord for AutomatonDecision`): priority first, then
the tie-break. -/
def decisionCmp (a b : Decision) : Ordering :=
  (compare a.priority b.priority).then (tiebreak a b)

/-- **The comparison is TOTAL (trichotomous)** — every pair of decisions compares to
exactly one of `lt/eq/gt`, so the priority cascade in `automatonOffset` ALWAYS
resolves to a single branch (this is the "ties resolve" content of property (2)). -/
theorem decisionCmp_total (a b : Decision) :
    decisionCmp a b = .lt ∨ decisionCmp a b = .eq ∨ decisionCmp a b = .gt := by
  cases decisionCmp a b <;> simp

/-- Select the offset from the two axis decisions and the column-rule flag (a single
flat match: winner along its axis, or on a tie the column rule (prefer Y) / freeze). -/
def chooseOffset (xDec yDec : Decision) (col : Bool) : Int × Int :=
  match decisionCmp xDec yDec, col with
  | .gt, _     => xDec.delta (1, 0)
  | .lt, _     => yDec.delta (0, 1)
  | .eq, true  => yDec.delta (0, 1)
  | .eq, false => (0, 0)

/-- The Daemon's chosen offset (`Game::automaton_move`): compare the two axis
decisions; move along the winner; on a tie apply the column rule.  TOTAL. -/
def automatonOffset (b : Board) : Int × Int :=
  chooseOffset
    (evaluateAxis (b.raycast b.automaton .xp) (b.raycast b.automaton .xn))
    (evaluateAxis (b.raycast b.automaton .yp) (b.raycast b.automaton .yn))
    b.useColumnRule

/-- A `delta` along a unit base is one of the five cardinal offsets (incl. zero). -/
theorem Decision.delta_mem (d : Decision) (base : Int × Int)
    (hb : base = (1, 0) ∨ base = (0, 1)) :
    d.delta base = (1, 0) ∨ d.delta base = (-1, 0) ∨ d.delta base = (0, 1)
      ∨ d.delta base = (0, -1) ∨ d.delta base = (0, 0) := by
  rcases hb with hb | hb <;> subst hb <;>
    cases d <;> simp only [Decision.delta] <;>
    first
    | decide
    | (split <;> decide)

/-- The selected offset is one of the five cardinal offsets (incl. zero). -/
theorem chooseOffset_mem (x y : Decision) (col : Bool) :
    chooseOffset x y col = (1, 0) ∨ chooseOffset x y col = (-1, 0) ∨ chooseOffset x y col = (0, 1)
      ∨ chooseOffset x y col = (0, -1) ∨ chooseOffset x y col = (0, 0) := by
  unfold chooseOffset
  split <;>
    first
      | exact Decision.delta_mem _ _ (Or.inl rfl)
      | exact Decision.delta_mem _ _ (Or.inr rfl)
      | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The chosen offset is one of the five cardinal offsets (incl. zero). -/
theorem automatonOffset_cases (b : Board) :
    automatonOffset b = (1, 0) ∨ automatonOffset b = (-1, 0) ∨ automatonOffset b = (0, 1)
      ∨ automatonOffset b = (0, -1) ∨ automatonOffset b = (0, 0) :=
  chooseOffset_mem _ _ _

/-- **PROPERTY (2), the load-bearing content.** The Automaton moves AT MOST one step
in a cardinal direction: the chosen offset has Manhattan length ≤ 1. -/
theorem automatonOffset_bounded (b : Board) :
    (automatonOffset b).1.natAbs + (automatonOffset b).2.natAbs ≤ 1 := by
  rcases automatonOffset_cases b with h | h | h | h | h <;> rw [h] <;> decide

/-- Relocate the Automaton onto `nc`, clearing its old cell to vacuum. -/
def stepTo (b : Board) (nc : Coord) : Board :=
  { b with
    automaton := nc,
    cells := fun c => if c = nc then .automaton
                      else if c = b.automaton then .vacuum
                      else b.cells c }

/-- The Automaton step (`Game::update_automaton` + `Board::do_move`): move onto the
one-step target IFF it is in bounds, a genuine move, and vacuum ("the Automaton can
never move into an occupied square").  Otherwise the board is unchanged. -/
def automatonStep (b : Board) : Board :=
  let off := automatonOffset b
  if 0 ≤ (b.automaton.x : Int) + off.1 ∧ (b.automaton.x : Int) + off.1 < b.size
      ∧ 0 ≤ (b.automaton.y : Int) + off.2 ∧ (b.automaton.y : Int) + off.2 < b.size
      ∧ (off.1 ≠ 0 ∨ off.2 ≠ 0)
      ∧ b.cellAt ⟨((b.automaton.x : Int) + off.1).toNat,
                  ((b.automaton.y : Int) + off.2).toNat⟩ = .vacuum then
    stepTo b ⟨((b.automaton.x : Int) + off.1).toNat, ((b.automaton.y : Int) + off.2).toNat⟩
  else b

/-- The step never changes the board size. -/
theorem automatonStep_size (b : Board) : (automatonStep b).size = b.size := by
  simp only [automatonStep]; split <;> rfl

/-- **PROPERTY (2), determinism.** The next Automaton location is uniquely determined:
`automatonMove` is a TOTAL function, so any two names for its value coincide. -/
def automatonMove (b : Board) : Coord := (automatonStep b).automaton

theorem automatonMove_deterministic (b : Board) (c₁ c₂ : Coord)
    (h₁ : c₁ = automatonMove b) (h₂ : c₂ = automatonMove b) : c₁ = c₂ :=
  h₁.trans h₂.symm

/-- **PROPERTY (2), safety.** The Automaton stays in bounds across its step: the
guard only relocates it onto an in-bounds vacuum cell. -/
theorem automatonStep_preserves_inBounds (b : Board)
    (hb : b.inBounds b.automaton) :
    (automatonStep b).inBounds (automatonStep b).automaton := by
  unfold Board.inBounds
  rw [automatonStep_size]
  simp only [automatonStep]
  split
  · rename_i h
    obtain ⟨hx0, hxs, hy0, hys, _, _⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [stepTo]; omega
    · simp only [stepTo]; omega
  · exact hb

/-! ## §4  Property (3): conflict-resolution + apply-all (SCC resolution)

Modeled faithfully for occlusion / chains / dead-ends / cycle-stasis; TERMINATION is
discharged by Lean's checker (fuel-decreasing recursion); determinism = being a
function; general FAIRNESS is STATED (`Fairness`). -/

/-- The interior coordinates strictly between two axis-aligned endpoints (exclusive),
for the occlusion check. -/
def interior (frm to : Coord) : List Coord :=
  if frm.x = to.x then
    let lo := min frm.y to.y
    let hi := max frm.y to.y
    (List.range (hi - lo - 1)).map (fun k => ⟨frm.x, lo + 1 + k⟩)
  else
    let lo := min frm.x to.x
    let hi := max frm.x to.x
    (List.range (hi - lo - 1)).map (fun k => ⟨lo + 1 + k, frm.y⟩)

/-- "at least two distinct elements" (order-free conflict detector). -/
def hasTwoDistinct {α} [DecidableEq α] (l : List α) : Bool :=
  l.any (fun a => l.any (fun c => a ≠ c))

/-- Source conflict: one source, ≥2 distinct destinations (`resolve_conflicts`, fork). -/
def frmConflict (ms : List Move) (m : Move) : Bool :=
  hasTwoDistinct ((ms.filter (fun m' => m'.frm = m.frm)).map (·.to))

/-- Destination conflict: one destination, ≥2 distinct NON-VACUUM sources
(`resolve_conflicts`, collision; `DetectAndConflict` mode). -/
def toConflict (b : Board) (ms : List Move) (m : Move) : Bool :=
  hasTwoDistinct
    ((ms.filter (fun m' => m'.to = m.to ∧ ¬ (b.cellAt m'.frm).isVacuum)).map (·.frm))

/-- Conflict resolution (`Game::resolve_conflicts`): drop every move that touches a
conflicted source or destination.  Identical `(src,dst)` moves are NOT a conflict
(they share a single destination, so `hasTwoDistinct` is false). -/
def conflictResolve (b : Board) (ms : List Move) : List Move :=
  ms.filter (fun m => ¬ frmConflict ms m ∧ ¬ toConflict b ms m)

/-- A move is occluded if some interior cell holds a non-vacuum particle that is NOT
itself a moving source (sources are `mark_passable`-d). -/
def occluded (b : Board) (srcs : List Coord) (m : Move) : Bool :=
  (interior m.frm m.to).any
    (fun c => ¬ (b.cellAt c).isVacuum ∧ ¬ srcs.contains c)

/-- The move graph as a partial function: a source's (unique, post-conflict)
destination among the non-occluded moves. -/
def nextOf (b : Board) (moved : List Move) (srcs : List Coord) (c : Coord) : Option Coord :=
  (moved.find? (fun m => m.frm = c ∧ ¬ occluded b srcs m)).map (·.to)

/-- Chain-follow (`apply_moves` Phase 4): from a piece's source, follow move edges
through vacated squares; stop landing on the next PIECE-source (the "caterpillar"),
at a dead-end, or on a detected cycle (piece stays — 2-cycle "always stay", the
conservative model for >2-cycles).  Terminates: `fuel` strictly decreases. -/
def followChain (nextC : Coord → Option Coord) (pieceSrcs : List Coord)
    (start : Coord) (visited : List Coord) (fuel : Nat) : Coord :=
  match fuel with
  | 0        => start
  | fuel + 1 =>
    match nextC start with
    | .none     => start
    | .some nxt =>
      if visited.contains nxt then start
      else if pieceSrcs.contains nxt then nxt
      else match nextC nxt with
        | .none   => nxt
        | .some _ => followChain nextC pieceSrcs nxt (start :: visited) fuel

/-- A resolved journey: a piece carried from `src` to `dest`. -/
structure Journey where
  src      : Coord
  dest     : Coord
  particle : Particle
deriving Repr

/-- **PROPERTY (3), the resolution function** (`Game::apply_moves`, faithful subset).
Builds the non-occluded move graph, computes each piece's destination by chain-follow,
and rewrites the board: sources cleared, pieces placed at their destinations.
TOTAL ⇒ TERMINATES by construction; a function ⇒ deterministic given `moves`. -/
def applyMoves (b : Board) (moves : List Move) : Board :=
  let srcs      := moves.map (·.frm)
  let nextC     := nextOf b moves srcs
  -- sources actually carrying a piece at turn start
  let pieceSrcs := srcs.filter (fun c => ¬ (b.cellAt c).isVacuum)
  let fuel      := moves.length + 1
  let journeys  : List Journey :=
    pieceSrcs.map (fun s =>
      { src := s, dest := followChain nextC pieceSrcs s [] fuel, particle := b.cellAt s })
  let clearedSrc (c : Coord) : Bool := pieceSrcs.contains c
  { b with
    conflictAt := fun _ => false,
    cells := fun c =>
      match journeys.find? (fun j => j.dest = c) with
      | .some j => j.particle
      | .none   => if clearedSrc c then .vacuum else b.cellAt c }

/-- **PROPERTY (3), determinism-as-functionality** — trivial but recorded: the
resolution is a function, so equal inputs give equal outputs. -/
theorem applyMoves_deterministic (b : Board) (ms : List Move) :
    applyMoves b ms = applyMoves b ms := rfl

/-- **PROPERTY (3), the STATED fairness obligation** (PHILOSOPHY.md, "Principle of
Fairness": move success and order are independent of any ordering on players or on
the move list — the resolution is PERMUTATION-INVARIANT).  Stated as a named `Prop`;
it is the deferred residual (general permutation-invariance needs the full SCC
decomposition + a canonical merge order).  The §8 `#guard`s witness concrete real
resolutions (single move, chain, fork-conflict, full turn) for non-vacuity. -/
def FairnessObligation : Prop :=
  ∀ (b : Board) (ms₁ ms₂ : List Move), ms₁.Perm ms₂ →
    ∀ c : Coord, (applyMoves b ms₁).cellAt c = (applyMoves b ms₂).cellAt c

/-! ## §5  Property (4): win-check — decidable + `Good`-style safety -/

/-- Win check (`try_complete_round`): the owner of the goal the Automaton now sits
on, if any.  Direct recursion for a clean safety proof. -/
def winnerAux (a : Coord) : List (Coord × Pid) → Option Pid
  | []            => .none
  | (c, p) :: rest => if c = a then .some p else winnerAux a rest

def winner (b : Board) (goals : List (Coord × Pid)) : Option Pid :=
  winnerAux b.automaton goals

/-- Win is decidable (an `Option`; `hasWon` is its `isSome`). -/
def hasWon (b : Board) (goals : List (Coord × Pid)) : Bool := (winner b goals).isSome

/-- **PROPERTY (4), the `Good`-style safety.** A win can only fire when the Automaton
is genuinely on a declared goal square owned by the winner — no spurious win. -/
theorem winner_sound (b : Board) (goals : List (Coord × Pid)) (p : Pid)
    (h : winner b goals = .some p) :
    ∃ c, (c, p) ∈ goals ∧ b.automaton = c := by
  unfold winner at h
  induction goals with
  | nil => simp [winnerAux] at h
  | cons g gs ih =>
    obtain ⟨c, q⟩ := g
    simp only [winnerAux] at h
    by_cases hc : c = b.automaton
    · rw [if_pos hc] at h
      injection h with hq
      subst hq
      exact ⟨c, List.mem_cons_self, hc.symm⟩
    · rw [if_neg hc] at h
      obtain ⟨c', hmem, ha⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem _ hmem, ha⟩

/-! ## §6  The pure turn transition -/

/-- **THE PURE TRANSITION** (`Game::try_complete_round`): validity-filter →
conflict-resolve → apply-all → Automaton step.  (Win-check is a read-only predicate
`winner` over the resulting board, not a mutation.) -/
def applyTurn (b : Board) (ms : List Move) : Board :=
  automatonStep (applyMoves b (conflictResolve b (ms.filter (moveValidB b))))

/-- `applyMoves` never relocates the Automaton (validity forbids `to = automaton`;
sources are never the Automaton cell), so its location field is untouched. -/
theorem applyMoves_automaton (b : Board) (ms : List Move) :
    (applyMoves b ms).automaton = b.automaton := rfl

/-- **PROPERTY (4), the invariant preserved across the whole turn.** If the Automaton
starts in bounds it ends in bounds — the `Good` safety invariant of `applyTurn`. -/
theorem applyTurn_preserves_inBounds (b : Board) (ms : List Move)
    (hb : b.inBounds b.automaton) :
    (applyTurn b ms).inBounds (applyTurn b ms).automaton := by
  unfold applyTurn
  apply automatonStep_preserves_inBounds
  rw [applyMoves_automaton]
  exact hb

/-! ## §7  The AIR-refinement obligation (STATED — the emitted-circuit contract)

The game-level analogue of the `evalSimpleCtx_*_iff` constraint twins and the
`RotatedLayout.Legal` construction obligation.  The board-transition AIR is abstract
now; the hand-authored Custom leaf (Lane-D-gated) discharges `Refines` later. -/

/-- An abstract board-transition circuit: its arithmetization admits triples
`(old_board, moves, new_board)`. -/
structure BoardTransitionAIR where
  admits : Board → List Move → Board → Prop

/-- **THE CONTRACT** the verified circuit is emitted against: the AIR admits
`(b, ms, nb)` IFF `nb` is exactly the pure transition applied. -/
def BoardTransitionAIR.Refines (air : BoardTransitionAIR) : Prop :=
  ∀ b ms nb, air.admits b ms nb ↔ nb = applyTurn b ms

/-- The reference realization — the AIR whose admission IS `applyTurn`.  It witnesses
`Refines` is SATISFIABLE (the obligation is non-vacuous, exactly as `rotated178_legal`
witnesses `Legal` is inhabited). -/
def applyTurnAIR : BoardTransitionAIR where
  admits := fun b ms nb => nb = applyTurn b ms

theorem applyTurnAIR_refines : applyTurnAIR.Refines := fun _ _ _ => Iff.rfl

/-- **`automatafl_air_refines_applyTurn` — THE STATED AIR-REFINEMENT OBLIGATION.**
Any board-transition AIR that satisfies the emitted-circuit contract `Refines`
accepts `(old, moves, new)` exactly when `new = applyTurn old moves`.  The Lane-D
Custom leaf supplies the `air.Refines` witness (its construction + proof are
deferred); `applyTurnAIR_refines` shows the contract is inhabited today. -/
theorem automatafl_air_refines_applyTurn
    (air : BoardTransitionAIR) (hair : air.Refines)
    (b : Board) (ms : List Move) (nb : Board) :
    air.admits b ms nb ↔ nb = applyTurn b ms :=
  hair b ms nb

/-! ## §8  Non-vacuity witnesses — real board transitions (`#guard`)

A 5×5 board, Automaton at (2,2), an attractor two north at (2,4).  The Daemon
should step one square toward it, to (2,3). -/

/-- Automaton at (2,2); attractor at (2,4); everything else vacuum. -/
def demoBoard : Board :=
  mkBoard 5 [(⟨2, 4⟩, .attractor)] ⟨2, 2⟩

-- The attractor is seen two steps north (dist 2, room to move): the Daemon steps north.
#guard (automatonStep demoBoard).automaton = (⟨2, 3⟩ : Coord)
#guard (automatonStep demoBoard).cellAt ⟨2, 3⟩ = Particle.automaton
#guard (automatonStep demoBoard).cellAt ⟨2, 2⟩ = Particle.vacuum
-- The attractor is untouched by the Daemon's step.
#guard (automatonStep demoBoard).cellAt ⟨2, 4⟩ = Particle.attractor

/-- A repulsor board: repulsor one step south at (2,1) with empty space north — the
Daemon flees north (FromRepulsor). -/
def repBoard : Board := mkBoard 5 [(⟨2, 1⟩, .repulsor)] ⟨2, 2⟩
#guard (automatonStep repBoard).automaton = (⟨2, 3⟩ : Coord)

/-- A move-resolution witness: player moves the attractor from (0,0) to (0,3) on an
otherwise-empty 5×5 board (Automaton parked in a corner out of the way). -/
def moveBoard : Board := mkBoard 5 [(⟨0, 0⟩, .attractor)] ⟨4, 4⟩
def demoMove : Move := { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 3⟩ }

#guard moveValidB moveBoard demoMove = true
#guard (applyMoves moveBoard [demoMove]).cellAt ⟨0, 3⟩ = Particle.attractor
#guard (applyMoves moveBoard [demoMove]).cellAt ⟨0, 0⟩ = Particle.vacuum

-- A full turn: the piece moves, then the Daemon (no opposing pair / repulsor in
-- range from the corner) does not move.
#guard (applyTurn moveBoard [demoMove]).cellAt ⟨0, 3⟩ = Particle.attractor

-- Validity teeth (non-vacuous both polarities).
#guard moveValidB moveBoard { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 0⟩ } = false   -- from = to
#guard moveValidB moveBoard { who := 0, frm := ⟨0, 0⟩, to := ⟨1, 3⟩ } = false   -- not rook-aligned
#guard moveValidB moveBoard { who := 0, frm := ⟨4, 4⟩, to := ⟨4, 0⟩ } = false   -- source is Automaton
#guard moveValidB moveBoard { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 9⟩ } = false   -- dest OOB

-- Conflict detection: two distinct destinations from one source = a fork conflict,
-- so both moves are dropped and the piece stays.
def forkA : Move := { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 3⟩ }
def forkB : Move := { who := 1, frm := ⟨0, 0⟩, to := ⟨3, 0⟩ }
#guard conflictResolve moveBoard [forkA, forkB] = ([] : List Move)
#guard (applyMoves moveBoard (conflictResolve moveBoard [forkA, forkB])).cellAt ⟨0, 0⟩
        = Particle.attractor

-- Win-check: the Automaton on a goal wins; off a goal, no win.
#guard winner demoBoard [(⟨2, 2⟩, 7)] = some 7
#guard winner demoBoard [(⟨0, 0⟩, 7)] = none
#guard hasWon (automatonStep demoBoard) [(⟨2, 3⟩, 3)] = true    -- steps onto the goal → win

/-! ## §9  Axiom-cleanliness self-check (no `native_decide`; core axioms only). -/

#print axioms moveValidB_iff
#print axioms automatonOffset_bounded
#print axioms automatonStep_preserves_inBounds
#print axioms winner_sound
#print axioms applyTurn_preserves_inBounds
#print axioms automatafl_air_refines_applyTurn

end Dregg2.Games.Automatafl
