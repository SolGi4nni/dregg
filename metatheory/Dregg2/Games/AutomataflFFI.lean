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
The playable surface paints exactly this set as the rook-line highlight, so the affordance a player
sees is the ruleset's own legality and not a Rust re-derivation of it. -/
def targetsOf (b : Board) (marks : List Coord) (who : Pid) (frm : Coord) : List Coord :=
  (List.range (b.size * b.size)).filterMap (fun i =>
    let c : Coord := ⟨i % b.size, i / b.size⟩
    if moveLegalB b marks ⟨who, frm, c⟩ then some c else none)

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

/-! ## §5 — teeth (`#guard` FAILS the build on regression)

The two boards below are the audit's own smallest witnesses. `cycBoard`'s pair is the input on
which the deleted Rust oracle SWAPPED two pieces, and `blockBoard`'s move is the one on which it
OVERWROTE a stationary piece. Both are pinned here against the ruleset's answer. -/

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

-- The codec round-trips a real board: decode ∘ encode is the identity on the wire.
#guard rulesFFI ("mid " ++ encodeBoard demoBoard ++ " 0 0") == "1 " ++ encodeBoard demoBoard
#guard rulesFFI ("mid " ++ encodeBoard stockTwoPlayer ++ " 0 0") == "1 " ++ encodeBoard stockTwoPlayer

-- The stock board is the 11×11 two-player opening, automaton dead centre at (5,5).
#guard rulesFFI "stock" ==
  "1 11 " ++
  "11001110011" ++   -- y = 0   `rroorrroorr`
  "00021112000" ++   -- y = 1   `oooarrraooo`
  "00000000000" ++
  "00000000000" ++
  "22000000022" ++   -- y = 4   `aaoooooooaa`
  "11000300011" ++   -- y = 5   `rrooodooorr` — the automaton dead centre
  "22000000022" ++   -- y = 6
  "00000000000" ++
  "00000000000" ++
  "00021112000" ++   -- y = 9
  "11001110011" ++   -- y = 10
  " 5 5 1"

-- The stock two-player goals: seat 0 owns the `y = 0` corners, seat 1 the `y = 10` corners.
#guard rulesFFI "goals 11" == "1 4 0 0 0 10 0 0 0 10 1 10 10 1"

-- §8's demo step: the automaton walks one square toward the attractor, (2,2) → (2,3).
#guard rulesFFI ("step 0 " ++ encodeBoard demoBoard) ==
  "1 " ++ encodeBoard (mkBoard 5 [(⟨2, 4⟩, Particle.attractor)] ⟨2, 3⟩)

-- The whole automaton decision on the demo board: no X decision, a `towardAttractor` at distance 2
-- on Y, offset (0, +1).
#guard rulesFFI ("sense 0 " ++ encodeBoard demoBoard) == "1 0 3 0 3 2 2 0 3 0 0 0 0 1 1 2 0 0 1"

-- ⚑ THE 2-CYCLE. Both pieces stay put — the board is unchanged. (`reference.rs::resolve_mid`
-- performed the SWAP; `resolve_witness.rs` documented the divergence rather than fixing it.)
#guard rulesFFI ("mid " ++ encodeBoard cycBoard ++ " 0 2 0 0 0 0 1 1 0 1 0 0") ==
  "1 " ++ encodeBoard cycBoard

-- ⚑ THE INCLUSIVE PATH CHECK. A move onto a square held by a piece that nobody moves FAILS, and
-- the mover is replaced at its origin — the board is unchanged. (`reference.rs::occluded` scanned
-- the strict interior only, so the mover overwrote the occupant and DESTROYED it.)
#guard rulesFFI ("mid " ++ encodeBoard blockBoard ++ " 0 1 0 0 0 0 3") ==
  "1 " ++ encodeBoard blockBoard

-- A plain move executes: the attractor at (0,0) walks to (0,2) on the empty file.
#guard rulesFFI ("mid " ++ encodeBoard cycBoard ++ " 0 1 0 0 1 0 3") ==
  "1 " ++ encodeBoard (mkBoard 5 [(⟨0, 3⟩, Particle.repulsor),
                                  (⟨0, 0⟩, Particle.attractor)] ⟨4, 4⟩)

-- ⚑ RULING (D): the automaton square is banned as a move SOURCE ONLY. Naming it as a DESTINATION
-- is LEGAL to propose (and then fails to execute, above). `reference.rs::move_valid` banned both
-- endpoints — `logic/src/game.rs`'s reading, not the README's.
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 0 0 4 4 0 4") == "1 0"
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 0 0 0 0 4 0") == "1 1"
-- A marked coordinate is illegal at EITHER endpoint, for everyone.
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 1 0 2 0 0 0 0 2") == "1 0"
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 1 0 2 0 0 0 0 4") == "1 1"
-- The three plain illegalities: `from == to`, off-axis, out of bounds.
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 0 0 0 0 0 0") == "1 0"
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 0 0 0 0 1 3") == "1 0"
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 0 0 0 0 0 9") == "1 0"
-- A NEGATIVE coordinate is illegal, exactly as the OOB sentinel it decodes to.
#guard rulesFFI ("legal " ++ encodeBoard cycBoard ++ " 0 0 0 0 0 -1") == "1 0"

-- The LEGAL TARGETS of (0,0) on the 5x5 board: the rest of row 0 and the rest of column 0 — the rook
-- line, minus the source itself. (0,1) holds a repulsor and stays legal to NAME: blocking is
-- resolution's job, not legality's (ruling D / clause 3.2).
#guard rulesFFI ("targets " ++ encodeBoard cycBoard ++ " 0 0 0 0") ==
  "1 8 1 0 2 0 3 0 4 0 0 1 0 2 0 3 0 4"
-- From the automaton's own square nothing is legal (it is banned as a SOURCE).
#guard rulesFFI ("targets " ++ encodeBoard cycBoard ++ " 0 0 4 4") == "1 0"

-- A FORK (one source, two destinations) is a conflict on that source; a clean round has none.
#guard rulesFFI ("clash " ++ encodeBoard cycBoard ++ " 0 2 0 0 0 0 3 1 0 0 3 0") == "1 1 0 0"
#guard rulesFFI ("clash " ++ encodeBoard cycBoard ++ " 0 1 0 0 1 0 3") == "1 0"

-- `round` on a clean round RESOLVES to the same board `mid`/`step` compose to, with no win.
#guard rulesFFI ("round 0 " ++ encodeBoard cycBoard ++ " 0 0 0 2 0 1 1 0 0 1 0 3") ==
  "1 R -1 " ++ encodeBoard (mkBoard 5 [(⟨0, 3⟩, Particle.repulsor),
                                       (⟨0, 0⟩, Particle.attractor)] ⟨4, 4⟩)
-- A conflicted round comes back AGAIN, with the contested coordinate marked and its seat re-entered.
#guard rulesFFI ("round 0 " ++ encodeBoard cycBoard ++ " 0 0 0 2 0 1 2 0 0 0 0 3 1 0 0 3 0") ==
  "1 A 1 0 0 0 2 0 1"

-- Fail-closed: no verb, an unknown verb, a truncated board, a lying cell count.
#guard rulesFFI "" == "0"
#guard rulesFFI "bogus" == "0"
#guard rulesFFI "mid 5" == "0"
#guard rulesFFI "mid 5 000 0 0 1 0 0" == "0"
#guard rulesFFI "step 7 5 0000000000000000000000000 4 4 1" == "0"

end Dregg2.Games.AutomataflFFI
