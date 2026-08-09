import Dregg2.Games.AutomataflRules

/-!
# `Dregg2.Games.AutomataflFFI` — the RUNTIME-CALLABLE automatafl game oracle

⚑ SUBSTRATE. The automatafl game semantics are **Lean-authored** (`Dregg2.Games.AutomataflRules`,
the rules-faithful spec) and the AIR over them is Lean-emitted (`Dregg2.Circuit.Emit.Automatafl*`).
This module adds NO semantics: it is a wire codec around the existing spec functions plus the
`@[export]` the deployed Rust surface calls, so `dregg-automatafl` computes a turn BY CALLING THE
PROVEN LEAN instead of by consulting a Rust transcription.

## What this replaces, and why it is a repair rather than a refactor

`dregg-automatafl/src/reference.rs` was a hand transcription of `~/dev/automatafl/logic/src/game.rs`
— a NON-CANONICAL experiment. The four-way conformance audit
(`docs/reference/AUTOMATAFL-RULES-CONFORMANCE-AUDIT.md`) found nine divergences from the
Creator-Approved ruleset in that lineage, three of which DESTROY PIECES. Two were live in the Rust
oracle the witness generators consulted:

* **2-cycles.** `logic/` (and therefore `reference.rs`) SWAPPED the two pieces; the README and
  `AutomataflRules.twoCyc` keep both pieces PUT. `dregg-automatafl/src/resolve_witness.rs` carried a
  comment admitting the descriptor "deliberately diverges from `reference::resolve_mid`" on exactly
  this input — i.e. the oracle was already known not to be a valid cross-check of the descriptor.
* **The inclusive path check.** `reference.rs::occluded` scans only the strict interior, so a mover
  could overwrite a stationary piece standing on its destination. `AutomataflRules.blockedB` scans
  the path INCLUSIVE of the destination (`model.py::CanMove`), so the move simply fails.

Both are unreachable from Rust now: the only answer source is the Lean below. §5's teeth pin both
answers, so the repair cannot silently regress to the transcription's.

## The wire (`String → String`), fail-closed

Single line, space-separated tokens, verb first. A malformed wire answers `"0"` — REFUSE. Every
success answers `"1"` followed by the verb's payload. No token is ever empty (the cell string of a
`0 × 0` board is written `-`).

```
BOARD  := size cells autoX autoY colRule      -- cells = size*size digits in {0,1,2,3}, row-major
                                              -- (y*size + x); `-` when size = 0
COORDS := k  then k × [ x y ]
MOVES  := k  then k × [ who fromX fromY toX toY ]
GOALS  := k  then k × [ x y seat ]
PIDS   := k  then k × [ pid ]
TIE    := 0 column | 1 row | 2 freeze         -- `AutomataflRules.TieBreak`
```

Cell digits are the canonical particle codes `{vacuum 0, repulsor 1, attractor 2, automaton 3}` —
the same `particleCode` the emitted descriptors pack (`Emit.AutomataflCommit.particleCode`), so the
oracle and the AIR speak one alphabet.

**Operand order: the BOARD always comes first** (after the tie-break, when there is one). Every
other operand's coordinates are decoded against `board.size`, and `BOARD` is a fixed five tokens, so
board-first is what makes the grammar parseable in one left-to-right pass.

Move coordinates are read as SIGNED decimals because the caller's coordinate type is signed. A
negative coordinate decodes to the sentinel `⟨size, size⟩`, which is out of bounds at every size.
That cannot change an answer: every verb below filters its moves through `moveLegalB`, which
requires `inBounds` at both endpoints, so a negative coordinate and the sentinel are both simply
illegal.

### Verbs

| request                                         | response                                        |
|-------------------------------------------------|-------------------------------------------------|
| `stock`                                         | `1 BOARD` — `stockTwoPlayer` (11×11)            |
| `goals SIZE`                                    | `1 GOALS` — `stockGoals2`                       |
| `sense TIE BOARD`                               | `1` + 4 rays + 2 decisions + offset (see below) |
| `step TIE BOARD`                                | `1 BOARD` — `automatonStepCfg`                  |
| `mid BOARD COORDS MOVES`                        | `1 BOARD` — `resolveMoves` over the legal moves |
| `turn TIE BOARD GOALS COORDS MOVES`             | `1 win BOARD` (`win = -1` for none)             |
| `legal BOARD COORDS who fX fY tX tY`            | `1 0` / `1 1` — `moveLegalB`                    |
| `clash BOARD COORDS MOVES`                      | `1 COORDS` — `roundStep`'s conflicted set       |
| `targets BOARD COORDS who fX fY`                | `1 COORDS` — every legal destination of `frm`   |
| `round TIE BOARD GOALS COORDS MOVES PIDS MOVES` | `1 A COORDS MOVES PIDS` / `1 R win BOARD`       |

`sense` reports the raycasts in the order `xp xn yp yn` as `what dist` pairs, then the X and Y axis
decisions as `variant pos attDist repDist` (variant `0 none`, `1 towardAttractor`, `2 fromRepulsor`,
`3 unbalancedPair` — the priority order over ten; absent distance fields are `0`), then the chosen
offset `offX offY`. That is the whole of the automaton's decision, so the Leg-A witness generator
fills its trace from the Lean's own intermediate values instead of recomputing them.

`round` is `roundStep` in full: `1 A marks locked waiting` when the round demands re-entry, and
`1 R win BOARD` when it resolves. The two `MOVES` operands are the round's LOCKED moves and this
round's SUBMISSIONS, in that order; `PIDS` is `waiting`.

## Import discipline

This module sits in the `Dregg2.FFI` boundary closure, so its initializer runs with the rest of the
runtime and `dregg-lean-ffi/build.rs` splices its object like any other export. It imports only
`Dregg2.Games.AutomataflRules` (which brings `Dregg2.Games.Automatafl` and `Mathlib.Data.List.Dedup`
— `dedup` is load-bearing in `clashCoords`, not decoration).
-/

namespace Dregg2.Games.AutomataflFFI

open Dregg2.Games.Automatafl
open Dregg2.Games.AutomataflRules

/-! ## §1 — tokens -/

/-- Parse an unsigned decimal token. -/
@[inline] def natOf? (s : String) : Option Nat := s.toNat?

/-- Parse a signed decimal token. -/
def intOf? (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(Int.ofNat n))
  else s.toNat?.map Int.ofNat

/-- The particle a cell digit denotes. Anything outside `{1,2,3}` is vacuum, so the decode is
total; `encodeCells` only ever emits `0..3`. -/
def codeToParticle : Nat → Particle
  | 1 => .repulsor
  | 2 => .attractor
  | 3 => .automaton
  | _ => .vacuum

/-- The canonical particle code (`Emit.AutomataflCommit.particleCode`, over `Nat`). -/
def particleCode : Particle → Nat
  | .vacuum => 0
  | .repulsor => 1
  | .attractor => 2
  | .automaton => 3

/-- `codeToParticle` inverts `particleCode` — the wire alphabet is faithful. -/
theorem codeToParticle_particleCode (p : Particle) : codeToParticle (particleCode p) = p := by
  cases p <;> rfl

/-! ## §2 — decode -/

/-- A cell-digit string to a particle array. A character outside `'0'..'3'` decodes to vacuum. -/
def parseCells (s : String) : Array Particle :=
  if s == "-" then #[]
  else s.toList.foldl (fun acc c => acc.push (codeToParticle (c.toNat - 48))) #[]

/-- Decode a coordinate whose components are SIGNED: a negative component becomes the
out-of-bounds sentinel `⟨size, size⟩` (see the header — every verb factors through `inBounds`). -/
def coordOf? (size : Nat) (xs ys : String) : Option Coord :=
  match intOf? xs, intOf? ys with
  | some x, some y =>
      if x < 0 || y < 0 then some ⟨size, size⟩ else some ⟨x.toNat, y.toNat⟩
  | _, _ => none

/-- Decode `size cells autoX autoY colRule`. The cells are taken AS GIVEN — the decoder is faithful,
not repairing: a board whose automaton cell does not carry code `3` is answered for as written. The
`cells` function agrees with `Board.cellAt` on the nose (out-of-bounds reads are vacuum, never a
row-wrapped alias). -/
def parseBoard : List String → Option (Board × List String)
  | sizeT :: cellsT :: axT :: ayT :: colT :: rest =>
    match natOf? sizeT, natOf? axT, natOf? ayT, natOf? colT with
    | some size, some ax, some ay, some col =>
      let arr := parseCells cellsT
      if arr.size == size * size then
        some ({ size := size
                cells := fun c =>
                  if c.x < size && c.y < size then (arr[c.y * size + c.x]?).getD .vacuum
                  else .vacuum
                automaton := ⟨ax, ay⟩
                conflictAt := fun _ => false
                useColumnRule := col != 0 }, rest)
      else none
    | _, _, _, _ => none
  | _ => none

/-- Decode `k` coordinate pairs. -/
def parseCoords (size : Nat) : Nat → List String → Option (List Coord × List String)
  | 0, rest => some ([], rest)
  | n + 1, xT :: yT :: rest =>
    match coordOf? size xT yT with
    | some c =>
      match parseCoords size n rest with
      | some (cs, tl) => some (c :: cs, tl)
      | none => none
    | none => none
  | _ + 1, _ => none

/-- Decode a length-prefixed coordinate list. -/
def parseCoordList (size : Nat) : List String → Option (List Coord × List String)
  | kT :: rest =>
    match natOf? kT with
    | some k => parseCoords size k rest
    | none => none
  | [] => none

/-- Decode `k` moves. -/
def parseMoves (size : Nat) : Nat → List String → Option (List Move × List String)
  | 0, rest => some ([], rest)
  | n + 1, whoT :: fxT :: fyT :: txT :: tyT :: rest =>
    match natOf? whoT, coordOf? size fxT fyT, coordOf? size txT tyT with
    | some who, some src, some dst =>
      match parseMoves size n rest with
      | some (ms, tl) => some ((⟨who, src, dst⟩ : Move) :: ms, tl)
      | none => none
    | _, _, _ => none
  | _ + 1, _ => none

/-- Decode a length-prefixed move list. -/
def parseMoveList (size : Nat) : List String → Option (List Move × List String)
  | kT :: rest =>
    match natOf? kT with
    | some k => parseMoves size k rest
    | none => none
  | [] => none

/-- Decode `k` goal entries. -/
def parseGoalEntries (size : Nat) : Nat → List String → Option (List (Coord × Pid) × List String)
  | 0, rest => some ([], rest)
  | n + 1, xT :: yT :: sT :: rest =>
    match coordOf? size xT yT, natOf? sT with
    | some c, some seat =>
      match parseGoalEntries size n rest with
      | some (es, tl) => some ((c, seat) :: es, tl)
      | none => none
    | _, _ => none
  | _ + 1, _ => none

/-- Decode a length-prefixed goal assignment. -/
def parseGoals (size : Nat) : List String → Option (GoalAssignment × List String)
  | kT :: rest =>
    match natOf? kT with
    | some k =>
      match parseGoalEntries size k rest with
      | some (es, tl) => some (⟨es⟩, tl)
      | none => none
    | none => none
  | [] => none

/-- Decode `k` player ids. -/
def parsePids : Nat → List String → Option (List Pid × List String)
  | 0, rest => some ([], rest)
  | n + 1, pT :: rest =>
    match natOf? pT with
    | some p =>
      match parsePids n rest with
      | some (ps, tl) => some (p :: ps, tl)
      | none => none
    | none => none
  | _ + 1, _ => none

/-- Decode a length-prefixed player-id list. -/
def parsePidList : List String → Option (List Pid × List String)
  | kT :: rest =>
    match natOf? kT with
    | some k => parsePids k rest
    | none => none
  | [] => none

/-- Decode the tie-break token. -/
def parseTie : List String → Option (TieBreak × List String)
  | "0" :: rest => some (.column, rest)
  | "1" :: rest => some (.row, rest)
  | "2" :: rest => some (.freeze, rest)
  | _ => none

/-! ## §3 — encode -/

/-- The cell-digit string of a board, row-major (`y * size + x`). `-` for the empty board so no
token is ever empty. -/
def encodeCells (b : Board) : String :=
  let n := b.size
  if n * n == 0 then "-"
  else
    String.ofList ((List.range (n * n)).map
      (fun i => Char.ofNat (48 + particleCode (b.cellAt ⟨i % n, i / n⟩))))

/-- `size cells autoX autoY colRule`. -/
def encodeBoard (b : Board) : String :=
  toString b.size ++ " " ++ encodeCells b ++ " " ++
  toString b.automaton.x ++ " " ++ toString b.automaton.y ++ " " ++
  (if b.useColumnRule then "1" else "0")

/-- `k` then `k` coordinate pairs. -/
def encodeCoords (cs : List Coord) : String :=
  toString cs.length ++ String.join (cs.map (fun c => " " ++ toString c.x ++ " " ++ toString c.y))

/-- `k` then `k` moves. -/
def encodeMoves (ms : List Move) : String :=
  toString ms.length ++ String.join (ms.map (fun m =>
    " " ++ toString m.who ++ " " ++ toString m.frm.x ++ " " ++ toString m.frm.y ++ " " ++
    toString m.to.x ++ " " ++ toString m.to.y))

/-- `k` then `k` goal entries. -/
def encodeGoals (g : GoalAssignment) : String :=
  toString g.entries.length ++ String.join (g.entries.map (fun e =>
    " " ++ toString e.1.x ++ " " ++ toString e.1.y ++ " " ++ toString e.2))

/-- `k` then `k` player ids. -/
def encodePids (ps : List Pid) : String :=
  toString ps.length ++ String.join (ps.map (fun p => " " ++ toString p))

/-- `what dist`, the raycast as the caller reads it. -/
def encodeRay (r : Raycast) : String :=
  toString (particleCode r.what) ++ " " ++ toString r.dist

/-- The decision variant code: the priority over ten (`0 none`, `1 towardAttractor`,
`2 fromRepulsor`, `3 unbalancedPair`). -/
def decisionVariant : Decision → Nat
  | .none => 0
  | .towardAttractor .. => 1
  | .fromRepulsor .. => 2
  | .unbalancedPair .. => 3

/-- Did the decision point along the axis-POSITIVE direction? (`false` for `none`.) -/
def decisionPos : Decision → Bool
  | .none => false
  | .towardAttractor p _ => p
  | .fromRepulsor p _ => p
  | .unbalancedPair p _ _ => p

/-- The attractor distance the decision was taken on; `0` when the variant carries none. -/
def decisionAttDist : Decision → Nat
  | .towardAttractor _ a => a
  | .unbalancedPair _ a _ => a
  | _ => 0

/-- The repulsor distance the decision was taken on; `0` when the variant carries none. -/
def decisionRepDist : Decision → Nat
  | .fromRepulsor _ r => r
  | .unbalancedPair _ _ r => r
  | _ => 0

/-- `variant pos attDist repDist`. -/
def encodeDecision (d : Decision) : String :=
  toString (decisionVariant d) ++ " " ++ (if decisionPos d then "1" else "0") ++ " " ++
  toString (decisionAttDist d) ++ " " ++ toString (decisionRepDist d)

/-- `offX offY`. -/
def encodeOffset (o : Int × Int) : String := toString o.1 ++ " " ++ toString o.2

/-- The winner token: the seat, or `-1`. -/
def encodeWin : Option Pid → String
  | none => "-1"
  | some p => toString p

/-- A nearest-goal distance token: the `Nat`, or `-1` for a seat that owns NO goal corner
(`goalDistance = none`). Same absent-sentinel discipline as `encodeWin`, so a caller reading a
negative number knows the seat is unseated rather than adjacent. -/
def encodeDist : Option Nat → String
  | none => "-1"
  | some d => toString d

/-! ## §4 — the verbs

Each verb is the spec function it names, wrapped in the codec. The only composition added here is
the `moveLegalB` filter, which is `roundStep`'s own
(`subs.filter (… moveLegalB rs.board rs.marks …)`) with `waiting` taken to be every seat — a caller
that wants the seat filter uses `round`. -/

/-- The legal submissions of a round: `roundStep`'s filter, without the `waiting` restriction. -/
def legalOf (b : Board) (marks : List Coord) (ms : List Move) : List Move :=
  ms.filter (fun m => moveLegalB b marks m)

/-- The conflicted coordinates of a round — `roundStep`'s `cs`: the fork/collide clashes, or, when
there are none, the unresolved merge landings. Empty ⟺ the round RESOLVES. -/
def clashOf (b : Board) (marks : List Coord) (ms : List Move) : List Coord :=
  let all := legalOf b marks ms
  let clash := clashCoords b all
  if clash.isEmpty then unresolved b all else clash

/-- **Every legal destination of `frm`** for seat `who` — `moveLegalB` applied over the whole board.
This is the PROPOSABLE set: what the rules let a seat submit.

⚑ It says NOTHING about what stands in the way. `MoveLegal` is a rook line, distinct endpoints, both
in bounds, the automaton banned as a SOURCE, and neither endpoint marked — occupancy is not one of
its clauses, by ruling (D). A surface that paints this as its legal-move set therefore lights
straight through every piece on the rook line. `liveTargetsOf` below is the set that would actually
EXECUTE. -/
def targetsOf (b : Board) (marks : List Coord) (who : Pid) (frm : Coord) : List Coord :=
  (List.range (b.size * b.size)).filterMap (fun i =>
    let c : Coord := ⟨i % b.size, i / b.size⟩
    if moveLegalB b marks ⟨who, frm, c⟩ then some c else none)

/-- **Every destination of `frm` that would actually EXECUTE** — `moveLegalB` AND the ruleset's own
inclusive path check (`blockedB`), against `ms` as the ambient move set plus the proposed move.

This is the composed predicate the two halves of §2/§4 make: `moveLegalB` answers *"may this be
PROPOSED?"* and `blockedB` answers *"will it RUN?"*. They are different questions and the ruleset
means them to be — the author's *"designating a move to an occupied square is fine, it just fails to
execute, it doesn't generate a conflict and shouldn't"*. A playable surface needs BOTH: the
proposable set is what it may accept, the live set is what it may promise.

⚑ **IT IS CONDITIONAL, AND THAT IS WHY BOTH SETS EXIST.** Every submitted move's SOURCE is PASSABLE
while the round resolves (`mark_passable` / `PC_F_PASSABLE`), whether or not that move itself
executes. So a destination flips from blocked to live the moment somebody picks the blocker up, and
`liveTargetsOf b marks [] who frm ⊆ liveTargetsOf b marks ms who frm` is NOT a theorem of this
definition — the answer moves with `ms`. A caller passes what it is entitled to know: the round's
LOCKED moves (public — the ruleset published them when it marked the clash), never an opponent's
sealed one. So this answers *"would it execute against the pieces standing there and the moves
already public"*, which is the only version of the question a highlight can honestly ask. -/
def liveTargetsOf (b : Board) (marks : List Coord) (ms : List Move) (who : Pid) (frm : Coord) :
    List Coord :=
  (targetsOf b marks who frm).filter (fun c =>
    let m : Move := ⟨who, frm, c⟩
    !blockedB b (m :: ms) m)

/-- The live set is a SUBSET of the proposable one: nothing executes that could not be proposed. -/
theorem liveTargetsOf_sub_targetsOf (b : Board) (marks : List Coord) (ms : List Move) (who : Pid)
    (frm : Coord) : ∀ c ∈ liveTargetsOf b marks ms who frm, c ∈ targetsOf b marks who frm := by
  intro c hc
  exact List.mem_of_mem_filter hc

/-- The move-resolved intermediate board (Leg R): `resolveMoves` over the legal submissions. -/
def midOf (b : Board) (marks : List Coord) (ms : List Move) : Board :=
  resolveMoves b (legalOf b marks ms)

/-- The full turn of a single clean round: resolve, step the automaton, check the win ON ENTRY. -/
def turnOf (tb : TieBreak) (g : GoalAssignment) (b : Board) (marks : List Coord)
    (ms : List Move) : Board × Option Pid :=
  let mid := midOf b marks ms
  let after := automatonStepCfg { tieBreak := tb } mid
  (after, winOnEntry mid after g)

/-- The four raycasts, the two axis decisions and the chosen offset — the whole automaton
decision, from the spec's own intermediate values. -/
def senseOf (tb : TieBreak) (b : Board) : String :=
  let xp := b.raycast b.automaton .xp
  let xn := b.raycast b.automaton .xn
  let yp := b.raycast b.automaton .yp
  let yn := b.raycast b.automaton .yn
  let xDec := evaluateAxis xp xn
  let yDec := evaluateAxis yp yn
  encodeRay xp ++ " " ++ encodeRay xn ++ " " ++ encodeRay yp ++ " " ++ encodeRay yn ++ " " ++
  encodeDecision xDec ++ " " ++ encodeDecision yDec ++ " " ++
  encodeOffset (chooseOffsetCfg xDec yDec tb)

/-- Render a `roundStep` outcome. -/
def encodeOutcome : RoundOutcome → String
  | .again rs =>
    "A " ++ encodeCoords rs.marks ++ " " ++ encodeMoves rs.locked ++ " " ++ encodePids rs.waiting
  | .resolved b w => "R " ++ encodeWin w ++ " " ++ encodeBoard b

/-- The whole decision, verb-dispatched. `none` ⇒ the wire was malformed ⇒ the caller sees `"0"`. -/
def decide? (toks : List String) : Option String :=
  match toks with
  | "stock" :: _ => some (encodeBoard stockTwoPlayer)
  | "goals" :: sizeT :: _ =>
    match natOf? sizeT with
    | some size => some (encodeGoals (stockGoals2 size))
    | none => none
  | "sense" :: rest => do
    let (tb, r1) ← parseTie rest
    let (b, _) ← parseBoard r1
    some (senseOf tb b)
  | "step" :: rest => do
    let (tb, r1) ← parseTie rest
    let (b, _) ← parseBoard r1
    some (encodeBoard (automatonStepCfg { tieBreak := tb } b))
  | "mid" :: rest => do
    let (b, r1) ← parseBoard rest
    let (marks, r2) ← parseCoordList b.size r1
    let (ms, _) ← parseMoveList b.size r2
    some (encodeBoard (midOf b marks ms))
  | "turn" :: rest => do
    let (tb, r1) ← parseTie rest
    let (b, r2) ← parseBoard r1
    let (g, r3) ← parseGoals b.size r2
    let (marks, r4) ← parseCoordList b.size r3
    let (ms, _) ← parseMoveList b.size r4
    let (after, win) := turnOf tb g b marks ms
    some (encodeWin win ++ " " ++ encodeBoard after)
  -- `adjudicate BOARD GOALS` — the CAPPED match's terminal rule. The seat strictly nearer its own
  -- goal wins; a seat that owns goals beats one that owns none; exact parity is a genuine draw
  -- (`-1`). This is the verb that replaces a bare turn-cap draw, and it is the only terminal rule
  -- with soundness theorems behind it: `adjudicate_seated` (the winner always OWNS a goal corner —
  -- the rule cannot award a match to an unseated player) and `adjudicate_sound` (when both seats own
  -- goals, the winner is genuinely NEARER). Operands mirror `turn`: board first, goals decoded
  -- against `b.size`.
  | "adjudicate" :: rest => do
    let (b, r1) ← parseBoard rest
    let (g, _) ← parseGoals b.size r1
    some (encodeWin (adjudicateCapped b.automaton g))
  -- `dist BOARD GOALS` — the two NUMBERS `adjudicate` compares, alongside the verdict they produce:
  -- `d0 d1 win`, where `dK` is `goalDistance` (the Manhattan distance from the automaton to seat
  -- `K`'s NEAREST owned corner, `-1` when it owns none) and `win` is `adjudicateCapped`'s answer.
  -- Same operands as `adjudicate`, a strictly larger payload — no new semantics, and every field is
  -- a spec function applied to the decoded board.
  --
  -- ⚑ Why the verb exists: the played surface was rendering the threat numbers ("seat A · 9 steps
  -- from a goal") from a Manhattan distance HAND-WRITTEN IN RUST, beside a verdict it took from
  -- `adjudicate`. Two computations of the same quantity, one of them unproven, displayed together as
  -- if they agreed. Now the number and the verdict come out of ONE call over `goalDistance` /
  -- `adjudicateCapped`, which is the pair `adjudicate_sound` is stated about.
  | "dist" :: rest => do
    let (b, r1) ← parseBoard rest
    let (g, _) ← parseGoals b.size r1
    some (encodeDist (goalDistance b.automaton g 0) ++ " " ++
          encodeDist (goalDistance b.automaton g 1) ++ " " ++
          encodeWin (adjudicateCapped b.automaton g))
  | "legal" :: rest => do
    let (b, r1) ← parseBoard rest
    let (marks, r2) ← parseCoordList b.size r1
    let (ms, _) ← parseMoves b.size 1 r2
    match ms with
    | [m] => some (if moveLegalB b marks m then "1" else "0")
    | _ => none
  | "targets" :: rest => do
    let (b, r1) ← parseBoard rest
    let (marks, r2) ← parseCoordList b.size r1
    match r2 with
    | whoT :: xT :: yT :: _ => do
      let who ← natOf? whoT
      let frm ← coordOf? b.size xT yT
      some (encodeCoords (targetsOf b marks who frm))
    | _ => none
  -- `livetargets BOARD COORDS MOVES who fX fY` — the destinations that would actually EXECUTE.
  -- Same shape as `targets` with the ambient MOVES operand inserted (board first, then the marks,
  -- then the move list, all decoded against `b.size`), because blocking is a fact about the whole
  -- round's move set and not about the proposed move alone.
  | "livetargets" :: rest => do
    let (b, r1) ← parseBoard rest
    let (marks, r2) ← parseCoordList b.size r1
    let (ms, r3) ← parseMoveList b.size r2
    match r3 with
    | whoT :: xT :: yT :: _ => do
      let who ← natOf? whoT
      let frm ← coordOf? b.size xT yT
      some (encodeCoords (liveTargetsOf b marks ms who frm))
    | _ => none
  | "clash" :: rest => do
    let (b, r1) ← parseBoard rest
    let (marks, r2) ← parseCoordList b.size r1
    let (ms, _) ← parseMoveList b.size r2
    some (encodeCoords (clashOf b marks ms))
  | "round" :: rest => do
    let (tb, r1) ← parseTie rest
    let (b, r2) ← parseBoard r1
    let (g, r3) ← parseGoals b.size r2
    let (marks, r4) ← parseCoordList b.size r3
    let (locked, r5) ← parseMoveList b.size r4
    let (waiting, r6) ← parsePidList r5
    let (subs, _) ← parseMoveList b.size r6
    some (encodeOutcome (roundStep { tieBreak := tb } g
      { board := b, marks := marks, locked := locked, waiting := waiting } subs))
  | _ => none

/-- The whole `String → String` oracle: `"1 …"` on success, `"0"` fail-closed. -/
def rulesWire (s : String) : String :=
  match decide? ((s.splitOn " ").filter (fun t => t != "")) with
  | some out => "1 " ++ out
  | none => "0"

/-- **`@[export dregg_automatafl_rules]`** — the FFI entry `dregg-automatafl` calls. Every board
transition, legality verdict, conflict set and win the deployed automatafl surface reports is
COMPUTED HERE, by `Dregg2.Games.AutomataflRules`. -/
@[export dregg_automatafl_rules]
def rulesFFI (s : String) : String := rulesWire s

/-! ## §5 — teeth (named pins in `AutomataflFFIFixtures` FAIL the build on regression)

The two boards below are the audit's own smallest witnesses. `cycBoard`'s pair is the input on
which the deleted Rust oracle SWAPPED two pieces, and `blockBoard`'s move is the one on which it
OVERWROTE a stationary piece. Both are pinned against the ruleset's answer.

⚑ **THE TEETH NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and the 52 `#guard` wire pins that used to
run at elaboration here made every game-fixture regression a hard failure of every Rust proving
target. The witness BOARDS stay here; the EVALUATION — each pin as a NAMED theorem per
GUARD-DISCIPLINE, `native_decide` + `#assert_compiled` — lives in `AutomataflFFIFixtures.lean`,
rooted in the central guard library: a plain `lake build` still runs every pin, and a stale
fixture reds the guard library instead of the archive. Every pinned expression here mentions
only PUBLIC names, so the pins moved verbatim. -/

/-- The Lean `Automatafl.lean` §8 demo board: automaton at (2,2), a lone attractor at (2,4). -/
def demoBoard : Board := mkBoard 5 [(⟨2, 4⟩, Particle.attractor)] ⟨2, 2⟩

/-- A 2-CYCLE: an attractor at (0,0) and a repulsor at (0,1) each named onto the other's square.
The ruleset says both STAY PUT. -/
def cycBoard : Board :=
  mkBoard 5 [(⟨0, 0⟩, Particle.attractor), (⟨0, 1⟩, Particle.repulsor)] ⟨4, 4⟩

/-- A STATIONARY OCCUPANT on the destination: the attractor at (0,0) is moved onto (0,3), where a
repulsor stands that nobody moves. The inclusive path check blocks the move. -/
def blockBoard : Board :=
  mkBoard 5 [(⟨0, 0⟩, Particle.attractor), (⟨0, 3⟩, Particle.repulsor)] ⟨4, 4⟩

-- The 52 pins — codec round-trips, the stock board and goals, `step`/`sense`, the 2-cycle and
-- inclusive-path answers, ruling (D) legality, `targets`/`livetargets` (both polarities of the
-- shipped-board lie), `clash`/`round`, `adjudicate`/`dist`, and every fail-closed refusal —
-- live as named theorems in `AutomataflFFIFixtures.lean`, with the section narratives beside
-- the pins they justify.

end Dregg2.Games.AutomataflFFI
