/-
# `AutomataflLegCEmit` — THE LEG C DESCRIPTOR (multi-round braid milestone **M1**)

`docs/reference/AUTOMATAFL-MULTIROUND-BRAID-DESIGN.md` §1, §7 (M1). Leg C is `AutomataflRules.
roundStep`'s **`.again` branch** as a descriptor: a round that hits a fork/collide does NOT resolve —
it marks the conflicted coordinate, drops every move touching it, re-enters the conflicted seats and
recurses over a FROZEN board. Today's fold is silent about that branch (`AutomataflTurnCapstone`
covers only `hclean : clashCoords … = []`, and only at `marks = []`). This file emits the object that
closes it.

⚑ **SUBSTRATE, SAID OUT LOUD.** This is **LEAN-AUTHORED AIR**. Every gate below is a `VmConstraint2`
value emitted here; Rust only fills traces. `dregg-automatafl/src/{air,moves,builder}.rs` stays DEBT
and is not extended.

## Leg C = Leg R's FRONT HALF + a STATE-TRANSITION TAIL

The front half is **not re-authored** — it is `AutomataflResolveEmit.NGen`'s own families, spliced in
at Leg R's own column indices:

| front-half family | what it buys Leg C |
|---|---|
| `NGen.onePin` / `NGen.autoReadConstraints` | the `one` pin and the witnessed automaton read |
| `NGen.validateMove n (mvBase n w)` ×2 | `MoveLegal`'s geometry: in-bounds, rook-aligned, `frm ≠ to`, `frm ≠ auto`, and `fp` IS the source cell |
| `NGen.srcNonVacConstraints` | the source-non-vacuum bits `anz`/`bnz` (`collideAt`'s "distinct NON-VACUUM sources") |
| `NGen.patternBitConstraints` | the four `eq_coords` bits (`eq_ff`, `eq_tt`, `eq_ab`, `eq_ba`) |
| `NGen.selectionConstraints` | **the clash verdict**: `cFork`, `cCollide`, `cSurv` |
| `AutomataflCommit.pack/commitBoardConstraintsAt` | the injective base-4 board commitment, IN and OUT |
| `AutomataflMarks.marksCommitFamilyAt` (M0, ×2) | the `{0,1}` marks indicator, packed and published, IN and OUT |

`cSurv` is already constrained to be exactly `clashCoords rs.board all = []`
(`AutomataflResolveMovesCapstone.surv_iff_clash_empty_of_sat`), so **the clash/clean verdict is
already forced in-circuit** — Leg C consumes it instead of dropping it, and pins it to `0`.

What Leg C **drops** is Leg R's whole resolution tail: `carryConstraints`, `flowThrough*`,
`writeMid*`, `inclOcclusion`, `nonLeave*`, `resolvable*`, `twoCyc`, `midV4`. Nothing downstream of
`SEL0 + 6` survives. It also drops `validateOcclusion`: `AutomataflRules.MoveLegal` has **no**
occlusion conjunct (occlusion is a RESOLUTION notion — `model.py::CanMove` — and `clashCoords` never
reads it), so Leg C has no use for `cOcc`. On the fork/collide path Leg C is therefore genuinely
cheaper than Leg R, exactly as the design predicts.

**The price, stated rather than hidden.** Leg C keeps Leg R's *column indices* verbatim (`mvBase n w`,
`cSelRow`, `cAnz`, `cFork`, `cSurv`, … are the same numerals here as there) so that Leg R's proven,
membership-parameterised extraction lemmas (`validMoveN_of_sat` and friends) re-point into Leg C by
`List.mem_append` plumbing rather than re-derivation. The cost is that the two dropped
`OCC_BLOCK_WIDTH` windows stay allocated and **unconstrained**: `[occBase n 0, RES0 n)` — 250 dead
lanes at `n = 11`. They are read by nothing and bind nothing, so they are prover area, not a
soundness surface. Compacting them is a numeral-only change once M2 is landed; doing it BEFORE M2
would fork the column algebra the front-half lemmas are stated in.

## The state-transition tail (the new work)

```
  csCell[c]      ∈ {0,1}   1 exactly on the conflicted coordinate(s) `cs`
                            = cFork·onehot(frm₀) + cCollide·onehot(to₀)   (the pair case)
  marksOut[c]              = marksIn[c] ∨ csCell[c]                       (degree 2, per cell)
  inMarksFrm/To[w]         = marksIn read at the move's endpoints (two-one-hot gated board read)
  legal[w]                 = ¬inMarksFrm[w] ∧ ¬inMarksTo[w], PINNED to 1  (the `moveLegalB` marks half)
  csFrm/csTo[w]            = csCell read at the move's endpoints
  inClash[w]               = csFrm[w] ∨ csTo[w]                           (this move is dropped)
  lockedOut[s]             = (1 − inClash[s]) · move s                    (seat-indexed, 5 lanes)
  waitingOut[s]            = inClash[s]
```

`legal[w] = 1` is where `marksIn` becomes load-bearing: together with the front half's `validateMove`
gates it is `AutomataflRules.moveLegalB rs.board rs.marks m` **exactly** (`MoveLegal` = `frm ≠ to` ∧
rook-aligned ∧ both in bounds ∧ `¬isAutomaton frm` ∧ `frm ∉ marks` ∧ `to ∉ marks`; the first four are
the front half, the last two are `¬inMarksFrm ∧ ¬inMarksTo` via `marksCode_eq_one_iff_mem`).

**`cSurv` is PINNED TO 0.** A clean round is UNSATISFIABLE as a Leg C, structurally — not merely
excluded by a hypothesis of the refinement theorem. That is design §4.2's "a round with no clash
cannot be folded as a spurious extra Leg C" made a property of the emitted object, and it means M2's
`hclash` is a CONSEQUENCE of `Satisfied2` rather than an assumption.

## The 2-seat scope, stated exactly (this is NOT the general Leg C)

The front half adjudicates **two** moves, so Leg C is the 2-player instance (`LEGC_SEATS = 2`), which
is the design's M1 row and its §2.3 "2-player collapse". Two things follow, and both are EMITTED
consequences rather than assumptions:

* `lockedOut = []` on every satisfying trace — a pair clash is a fork (shared `frm`) or a collide
  (shared `to`), so BOTH moves touch `cs`, so `inClash[0] = inClash[1] = 1`, so both `lockedBit`s are
  gated to `0`. The "innocent seat stays locked" case needs a THIRD move and is M9.
* `lockedIn = []` and `waitingIn[s] = 1` are **pinned**: at `P = 2` no reachable `RoundState` has a
  locked move (round 1 by `openRound`; round `k > 1` by the previous Leg C's forced `lockedOut = 0`),
  and every seat is waiting. The pins refuse no honest witness at `P = 2`; at `P > 2` they are FALSE,
  which is exactly why `LEGC_SEATS` is `2` and not a parameter pretending to generality.

The seat↔move identification is `seat s owns move s`. Leg R's `moveDecodeN` hard-codes `who = 0`
(design §9.2); Leg C's `legcMoveDecode` uses the seat index, and binding *that* to a player account
is Leg S's job, not this file's.

## What lands here (the M1 gate)

| # | object | status |
|---|---|---|
| 1 | `legCConstraints n` / `automataflLegCDescN n` | LEAN-AUTHORED AIR, `n`-generic |
| 2 | the tail gates `cs` / `marksOut` / `lockedOut` / `waitingOut` | emitted, two-sided `#guard`-canaried |
| 3 | the RoundState window at BOTH ends (board ‖ marks ‖ locked ‖ waiting ‖ auto) | emitted, PI-bound |
| 4 | the MEMBERSHIP interface (§5.1) | PROVEN, `#assert_axioms`-clean — every `_of_mem` hypothesis M2 reuses, discharged |
| 5 | `roundStateDecodeIn/Out` + `RoundStateAgrees` | the exact objects and the exact relation M2 is held to |
| 6 | byte-pinned wire goldens | `n = 5` + `n = 11`, in `AutomataflLegCGolden` |

**One correction to the design doc, found by building the object.** §1.4 states the refinement as
`roundStep … = .again (roundStateDecodeOut …)`. That is **false**: `roundStep` accumulates
`marks := (rs.marks ++ cs).dedup` in INSERTION order, and an `n²` indicator board can only be read
back in ROW-MAJOR order. §8.6 exhibits a two-round example where the two lists differ. The provable
statement is equality up to `List.Perm` on `marks` (`RoundStateAgrees`), which is exactly what the
rules read — `MoveLegal` touches `marks` only through `∉`, `RoundWF` only through `Nodup`.

**NOT here** (and not claimed): `legC_sat_imp_roundAgainN` — the refinement is M2. This file emits the
object and canaries its gates; no theorem here says the OUT window IS `roundStep`'s `.again` state.
No `EmitByName` registration and no witness generator (M4). No hash sites, no lookups, no tables: the
marks and board packs are base-4 injective, so the RoundState seam stays hash-free and inherits no new
crypto floor — only the deployed FRI floor and the witness-generation perimeter, like everything else.
-/
import Dregg2.Circuit.Emit.AutomataflMarks
import Dregg2.Circuit.Emit.AutomataflResolveRefine

namespace Dregg2.Circuit.Emit.AutomataflLegCEmit

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflMarks (MarksBoard marksCommitFamilyAt marksDecodeAt marksBoardOf
  marksWindowLanes)
open Dregg2.Circuit.Emit.AutomataflResolveRefine (boardDecodeOldN)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Games.Automatafl (Board Coord Move Particle Pid)
open Dregg2.Games.AutomataflRules (RoundState)
open Dregg2.Circuit (Assignment)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 — The seat count and the window lane arithmetic.

`LEGC_SEATS` is `2` deliberately (see the header). The lane-count functions take `P` so M5's
RoundState-window arithmetic and M9's widening are stated once, in terms of the seat count. -/

/-- The seats Leg C adjudicates. The front half is a TWO-move block, so this is `2`; M9 widens it
together with the `P²`-pairwise clash engine. -/
def LEGC_SEATS : Nat := 2

/-- `locked` as a seat-indexed table: `P` fixed slots `[lockedBit ‖ fromX ‖ fromY ‖ toX ‖ toY]`
(design §2.3 — a set has no canonical felt vector until an order is imposed, and the seat index is
that order). -/
def lockedLanes (P : Nat) : Nat := 5 * P

/-- `waiting` as a seat indicator: `P` bits. -/
def waitingLanes (P : Nat) : Nat := P

/-- The whole RoundState window `[ boardPack ‖ marksPack ‖ lockedVec ‖ waitingInd ‖ auto ]` at ONE
end. `marksWindowLanes n = feltCount n` is M0's `#guard`ed lane count. -/
def roundStateWindowLanes (n P : Nat) : Nat :=
  NGen.RFC n + marksWindowLanes n + lockedLanes P + waitingLanes P + 2

/-! ## §2 — The column layout.

`[0, CAR0 n)` is Leg R's front half VERBATIM (same numerals). Leg C's tail begins exactly where Leg
R's resolution tail did. -/

/-- Leg C's tail base — where Leg R's `CAR0` (the carries) began. Everything below is new. -/
def LEGC0 (n : Nat) : Nat := NGen.CAR0 n

/-- The packed IN-board felts (the OLD board, `⌈n²/15⌉` of them). -/
def cPackInFelt (n : Nat) (j : Nat) : Nat := LEGC0 n + j
/-- The packed OUT-board felts. The board is FROZEN across a clash round, so these pack `mid`, which
is gated cell-wise equal to `old`. -/
def cPackOutFelt (n : Nat) (j : Nat) : Nat := LEGC0 n + NGen.RFC n + j

/-- Base of the marks block. -/
def MARKS0 (n : Nat) : Nat := LEGC0 n + 2 * NGen.RFC n
/-- `marksIn` indicator cell `c` (linear index `y·n + x`). -/
def cMarksInCell (n : Nat) (c : Nat) : Nat := MARKS0 n + c
/-- `marksIn` packed felt `j`. -/
def cMarksInFelt (n : Nat) (j : Nat) : Nat := MARKS0 n + NGen.KK n + j
/-- `marksOut` indicator cell `c`. -/
def cMarksOutCell (n : Nat) (c : Nat) : Nat := MARKS0 n + NGen.KK n + NGen.RFC n + c
/-- `marksOut` packed felt `j`. -/
def cMarksOutFelt (n : Nat) (j : Nat) : Nat := MARKS0 n + 2 * NGen.KK n + NGen.RFC n + j

/-- Base of the clash-delta block. -/
def CS0 (n : Nat) : Nat := MARKS0 n + 2 * NGen.KK n + 2 * NGen.RFC n
/-- **The clash delta** — `1` exactly on the conflicted coordinate(s) `cs` of THIS round. -/
def cCsCell (n : Nat) (c : Nat) : Nat := CS0 n + c

/-- Base of the destination one-hot block. Leg R's destination one-hots (`cEty`/`cEtx`) live inside
the DROPPED occlusion block, so Leg C allocates its own — `2n` lanes per move, the only new one-hots
in the file. -/
def TSEL0 (n : Nat) : Nat := CS0 n + NGen.KK n
def TSEL_WIDTH (n : Nat) : Nat := 2 * n
/-- Destination-ROW selector `j` of move `w` (one-hot at `cTy`). -/
def cTSelRow (n : Nat) (w j : Nat) : Nat := TSEL0 n + TSEL_WIDTH n * w + j
/-- Destination-COLUMN selector `j` of move `w` (one-hot at `cTx`). -/
def cTSelCol (n : Nat) (w j : Nat) : Nat := TSEL0 n + TSEL_WIDTH n * w + n + j

/-- Base of the per-move query block. -/
def MVQ0 (n : Nat) : Nat := TSEL0 n + 2 * TSEL_WIDTH n
def MVQ_WIDTH : Nat := 6
/-- `marksIn[frm[w]]` — the source-endpoint marks read. -/
def cInMarksFrm (n : Nat) (w : Nat) : Nat := MVQ0 n + MVQ_WIDTH * w + 0
/-- `marksIn[to[w]]` — the destination-endpoint marks read. -/
def cInMarksTo (n : Nat) (w : Nat) : Nat := MVQ0 n + MVQ_WIDTH * w + 1
/-- `legal[w] = ¬inMarksFrm ∧ ¬inMarksTo` — the marks half of `moveLegalB`, pinned to `1`. -/
def cLegal (n : Nat) (w : Nat) : Nat := MVQ0 n + MVQ_WIDTH * w + 2
/-- `cs[frm[w]]`. -/
def cCsFrm (n : Nat) (w : Nat) : Nat := MVQ0 n + MVQ_WIDTH * w + 3
/-- `cs[to[w]]`. -/
def cCsTo (n : Nat) (w : Nat) : Nat := MVQ0 n + MVQ_WIDTH * w + 4
/-- `inClash[w] = cs[frm] ∨ cs[to]` — this move is dropped and its seat re-enters. -/
def cInClash (n : Nat) (w : Nat) : Nat := MVQ0 n + MVQ_WIDTH * w + 5

/-- Base of the seat-indexed locked/waiting block. -/
def SEAT0 (n : Nat) : Nat := MVQ0 n + 2 * MVQ_WIDTH
def SEAT_WIDTH : Nat := 12
def cLockedInBit (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 0
def cLockedInFx (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 1
def cLockedInFy (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 2
def cLockedInTx (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 3
def cLockedInTy (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 4
def cLockedOutBit (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 5
def cLockedOutFx (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 6
def cLockedOutFy (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 7
def cLockedOutTx (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 8
def cLockedOutTy (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 9
def cWaitingInBit (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 10
def cWaitingOutBit (n : Nat) (s : Nat) : Nat := SEAT0 n + SEAT_WIDTH * s + 11

/-- The Leg C trace width. -/
def LEGC_WIDTH (n : Nat) : Nat := SEAT0 n + SEAT_WIDTH * LEGC_SEATS

/-! ## §3 — The PI layout (append-only past Leg R's `0 .. AUTO_PI_BASE + 1`).

```
  PI[0 .. 16)                 door prefix                    (free)
  PI[16 .. 16+RFC)            pack(board)  IN                (= Leg R's pack_in)
  PI[16+RFC .. 16+2·RFC)      pack(board)  OUT               (board FROZEN: gated equal to IN)
  PI[AUTO_PI_BASE], +1        ax, ay                         (unchanged)
  ── appended; Leg R's window untouched ──
  PI[…]  pack(marksIn) ‖ pack(marksOut) ‖ lockedIn ‖ lockedOut ‖ waitingIn ‖ waitingOut
```
-/

/-- `marksIn`'s published window — M0 §9's `AUTO_PI_BASE n + 2`, verbatim. -/
def piMarksIn (n : Nat) : Nat := NGen.AUTO_PI_BASE n + 2
/-- `marksOut`'s published window. -/
def piMarksOut (n : Nat) : Nat := piMarksIn n + NGen.RFC n
def piLockedIn (n : Nat) : Nat := piMarksOut n + NGen.RFC n
def piLockedOut (n : Nat) : Nat := piLockedIn n + lockedLanes LEGC_SEATS
def piWaitingIn (n : Nat) : Nat := piLockedOut n + lockedLanes LEGC_SEATS
def piWaitingOut (n : Nat) : Nat := piWaitingIn n + waitingLanes LEGC_SEATS
/-- The Leg C PI count. -/
def LEGC_PI_COUNT (n : Nat) : Nat := piWaitingOut n + waitingLanes LEGC_SEATS

/-! ## §4 — The gate families. -/

/-- A boundary binding of a trace column to a public input (the shape
`AutomataflCommit.commitBoardConstraintsAt` uses). -/
def piPin (col pi : Nat) : VmConstraint2 := .base (.piBinding VmRow.first col pi)

/-- **The two-one-hot gated board read**, `out − Σ_y Σ_x rowSel[y]·colSel[x]·cell[y·n+x]` — literally
the shape of `NGen.sourceReadHead`, re-pointed at an arbitrary indicator board and an arbitrary pair
of one-hots. This is the ONE primitive the marks lookups and the `cs` lookups are built from. -/
def readAtHead (n : Nat) (outCol : Nat) (rowSel colSel cellCol : Nat → Nat) : Head :=
  (List.range n).foldl (fun h y =>
    (List.range n).foldl (fun h2 x =>
      h2.addProd (-1) [rowSel y, colSel x, cellCol (y * n + x)]) h) (Head.lin 1 outCol)

/-- The OR of two bits as a degree-2 head: `out − a − b + a·b == 0`. -/
def orHead (out a b : Nat) : Head :=
  (((Head.lin 1 out).addLin (-1) a).addLin (-1) b).addProd 1 [a, b]

/-- The NOR of two bits as a degree-2 head: `out − 1 + a + b − a·b == 0` (i.e. `out = ¬a ∧ ¬b`). -/
def norHead (out a b : Nat) : Head :=
  ((((Head.lin 1 out).addConst (-1)).addLin 1 a).addLin 1 b).addProd (-1) [a, b]

/-- The board-cell alphabet gates, IN and OUT. Leg R's `NGen.boardRangeConstraints` has a third
component for `cMidV4`, a column Leg C does not have; this is the same family over the two boards
Leg C does have, and it is the `{0,1,2,3}` precondition the base-4 pack needs. -/
def legCBoardRangeConstraints (n : Nat) : List VmConstraint2 :=
  ((List.range (NGen.KK n)).map (fun c => cg (memberExpr (NGen.old n c) [0, 1, 2, 3])))
  ++ ((List.range (NGen.KK n)).map (fun c => cg (memberExpr (NGen.mid n c) [0, 1, 2, 3])))

/-- **THE BOARD IS FROZEN.** `roundStep`'s `.again` carries `board := rs.board` — a clash round
mutates nothing on the board. The OUT board column is gated cell-wise equal to the IN board column,
so the published OUT window is the published IN window and the whole clash braid runs at one board. -/
def boardFrozenConstraints (n : Nat) : List VmConstraint2 :=
  (List.range (NGen.KK n)).map (fun c =>
    cgH ((Head.lin 1 (NGen.mid n c)).addLin (-1) (NGen.old n c)))

/-- The board commitment at Leg C's own felt columns — `NGen.commitBoardsConstraints`'s family with
the OUT pack pointed at the frozen `mid` board instead of Leg R's `cMidV4`. -/
def legCBoardCommitConstraints (n : Nat) : List VmConstraint2 :=
  AutomataflCommit.packBoardConstraintsAt n (NGen.old n) (cPackInFelt n)
  ++ AutomataflCommit.packBoardConstraintsAt n (NGen.mid n) (cPackOutFelt n)
  ++ AutomataflCommit.commitBoardConstraintsAt n (cPackInFelt n) 16
  ++ AutomataflCommit.commitBoardConstraintsAt n (cPackOutFelt n) (16 + NGen.RFC n)
  ++ AutomataflCommit.autoCoordCommitConstraints (NGen.AX_C n) (NGen.AY_C n) (NGen.AUTO_PI_BASE n)

/-- **The marks commitment, twice** — M0's `marksCommitFamilyAt` at Leg C's own bases, exactly as
`AutomataflMarks` §9 prescribes. `{0,1}` range gates ‖ base-4 pack gates ‖ PI bindings, per end. The
pack is NOT re-implemented here. -/
def legCMarksConstraints (n : Nat) : List VmConstraint2 :=
  marksCommitFamilyAt n (cMarksInCell n) (cMarksInFelt n) (piMarksIn n)
  ++ marksCommitFamilyAt n (cMarksOutCell n) (cMarksOutFelt n) (piMarksOut n)

/-- The destination one-hot selector lists of move `w`. -/
def tSelRowCols (n : Nat) (w : Nat) : List Nat := (List.range n).map (cTSelRow n w)
def tSelColCols (n : Nat) (w : Nat) : List Nat := (List.range n).map (cTSelCol n w)

/-- The destination one-hots of move `w`, pinned at its `(tx, ty)` columns — `oneHotAtCol`, the same
combinator `validateMove` uses for the SOURCE one-hots. -/
def destOneHotConstraints (n : Nat) (w : Nat) : List VmConstraint2 :=
  oneHotAtCol (tSelRowCols n w) (NGen.cTy n (NGen.mvBase n w))
  ++ oneHotAtCol (tSelColCols n w) (NGen.cTx n (NGen.mvBase n w))

/-- **THE MARKS LEGALITY GATE** — `moveLegalB rs.board rs.marks m`'s marks half, forced.

`inMarksFrm[w]`/`inMarksTo[w]` are `marksIn` read at the move's two endpoints through the SOURCE
one-hots (`validateMove`'s, already pinned at `(fx,fy)`) and the DESTINATION one-hots (this file's,
pinned at `(tx,ty)`). `legal[w]` is their NOR, and it is PINNED to `1`: a submission naming a marked
square makes the leaf UNSAT, which is exactly `roundStep`'s `subs.filter (… moveLegalB …)` refusing
to admit it. The geometric half of `MoveLegal` is already forced by `NGen.validateMove`. -/
def legalityConstraints (n : Nat) (w : Nat) : List VmConstraint2 :=
  [ cgH (readAtHead n (cInMarksFrm n w) (NGen.cSelRow n (NGen.mvBase n w))
          (NGen.cSelCol n (NGen.mvBase n w)) (cMarksInCell n))
  , cgH (readAtHead n (cInMarksTo n w) (cTSelRow n w) (cTSelCol n w) (cMarksInCell n))
  , cgH (norHead (cLegal n w) (cInMarksFrm n w) (cInMarksTo n w))
  , cgH ((Head.lin 1 (cLegal n w)).addConst (-1)) ]

/-- **THE CLASH PIN.** `cSurv = 0`. `surv_iff_clash_empty_of_sat` makes `cSurv = 1` equivalent to
`clashCoords = []`, so this single degree-1 gate makes a CLEAN round structurally UNSATISFIABLE as a
Leg C — design §4.2's "the prover cannot inject a spurious extra round", emitted rather than assumed.
-/
def clashPin (n : Nat) : VmConstraint2 := cgH (Head.lin 1 (NGen.cSurv n))

/-- **THE CLASH DELTA `cs`.** For a PAIR, `clashCoords_pair_iff` says the conflicted coordinate is
the shared SOURCE on a fork and the shared DESTINATION on a collide, and `cFork · cCollide = 0` (a
fork needs `eq_ff = 1`, a collide needs `eq_ff = 0`). So

    csCell[c] = cFork·srcOneHot₀[c] + cCollide·dstOneHot₀[c]

is a `{0,1}` indicator supported exactly on `cs`, degree 3, reusing move 0's own one-hots. The
per-cell `gBin` makes "the delta is an indicator" a gate rather than a derivation, which is what the
degree-2 OR below needs. -/
def csCellHead (n : Nat) (c : Nat) : Head :=
  ((Head.lin 1 (cCsCell n c)).addProd (-1)
      [NGen.cFork n, NGen.cSelRow n (NGen.mvBase n 0) (c / n), NGen.cSelCol n (NGen.mvBase n 0) (c % n)]).addProd
    (-1) [NGen.cCollide n, cTSelRow n 0 (c / n), cTSelCol n 0 (c % n)]

def csConstraints (n : Nat) : List VmConstraint2 :=
  ((List.range (NGen.KK n)).map (fun c => cg (gBin (cCsCell n c))))
  ++ ((List.range (NGen.KK n)).map (fun c => cgH (csCellHead n c)))

/-- **`marksOut = marksIn ∨ cs`** — `roundStep`'s `marks := (rs.marks ++ cs).dedup`, on the indicator
representation where `++`-then-`dedup` IS the pointwise OR. Degree 2, one gate per cell. This is the
gate the "forged `marksOut` that DROPS the new mark" canary in §7 bites on. -/
def marksOrConstraints (n : Nat) : List VmConstraint2 :=
  (List.range (NGen.KK n)).map (fun c =>
    cgH (orHead (cMarksOutCell n c) (cMarksInCell n c) (cCsCell n c)))

/-- **The drop test** — `inClash[w] = cs[frm[w]] ∨ cs[to[w]]`, i.e. `roundStep`'s
`cs.contains m.frm || cs.contains m.to`. Reads `csCell` through the same two one-hot pairs the marks
reads use. (The design writes this against `marksOut`; against `cs` it is the same predicate, because
every move of the round is `marksIn`-legal by the gate above — and stating it on `cs` keeps the gate
independent of the OR gate, so a forged `marksOut` cannot launder a move back into `locked`.) -/
def inClashConstraints (n : Nat) (w : Nat) : List VmConstraint2 :=
  [ cgH (readAtHead n (cCsFrm n w) (NGen.cSelRow n (NGen.mvBase n w))
          (NGen.cSelCol n (NGen.mvBase n w)) (cCsCell n))
  , cgH (readAtHead n (cCsTo n w) (cTSelRow n w) (cTSelCol n w) (cCsCell n))
  , cgH (orHead (cInClash n w) (cCsFrm n w) (cCsTo n w)) ]

/-- **The seat table.**

IN: `lockedIn[s] = 0` and `waitingIn[s] = 1` — the `P = 2` collapse, pinned (header §"2-seat scope").

OUT: `lockedOut[s] = (1 − inClash[s]) · move s` and `waitingOut[s] = inClash[s]` — `roundStep`'s two
filters, re-keyed by seat. The coordinate lanes are gated to the seat's own move columns THROUGH the
locked bit, so a dropped seat's slot is all-zero and a standing seat's slot is its move verbatim: a
locked move can be DROPPED but never mutated (design §3.3). -/
def seatConstraints (n : Nat) (s : Nat) : List VmConstraint2 :=
  [ cgH (Head.lin 1 (cLockedInBit n s))
  , cgH (Head.lin 1 (cLockedInFx n s))
  , cgH (Head.lin 1 (cLockedInFy n s))
  , cgH (Head.lin 1 (cLockedInTx n s))
  , cgH (Head.lin 1 (cLockedInTy n s))
  , cgH ((Head.lin 1 (cWaitingInBit n s)).addConst (-1))
  , cgH (((Head.lin 1 (cLockedOutBit n s)).addConst (-1)).addLin 1 (cInClash n s))
  , cgH ((Head.lin 1 (cLockedOutFx n s)).addProd (-1)
      [cLockedOutBit n s, NGen.cFx n (NGen.mvBase n s)])
  , cgH ((Head.lin 1 (cLockedOutFy n s)).addProd (-1)
      [cLockedOutBit n s, NGen.cFy n (NGen.mvBase n s)])
  , cgH ((Head.lin 1 (cLockedOutTx n s)).addProd (-1)
      [cLockedOutBit n s, NGen.cTx n (NGen.mvBase n s)])
  , cgH ((Head.lin 1 (cLockedOutTy n s)).addProd (-1)
      [cLockedOutBit n s, NGen.cTy n (NGen.mvBase n s)])
  , cgH ((Head.lin 1 (cWaitingOutBit n s)).addLin (-1) (cInClash n s)) ]

/-- The seat table's PI bindings — the `lockedVec ‖ waitingInd` half of the RoundState window, at
BOTH ends. These are what M5's `cb.connect` compares across a seam. -/
def seatCommitConstraints (n : Nat) (s : Nat) : List VmConstraint2 :=
  [ piPin (cLockedInBit n s) (piLockedIn n + 5 * s)
  , piPin (cLockedInFx n s) (piLockedIn n + 5 * s + 1)
  , piPin (cLockedInFy n s) (piLockedIn n + 5 * s + 2)
  , piPin (cLockedInTx n s) (piLockedIn n + 5 * s + 3)
  , piPin (cLockedInTy n s) (piLockedIn n + 5 * s + 4)
  , piPin (cLockedOutBit n s) (piLockedOut n + 5 * s)
  , piPin (cLockedOutFx n s) (piLockedOut n + 5 * s + 1)
  , piPin (cLockedOutFy n s) (piLockedOut n + 5 * s + 2)
  , piPin (cLockedOutTx n s) (piLockedOut n + 5 * s + 3)
  , piPin (cLockedOutTy n s) (piLockedOut n + 5 * s + 4)
  , piPin (cWaitingInBit n s) (piWaitingIn n + s)
  , piPin (cWaitingOutBit n s) (piWaitingOut n + s) ]

/-! ## §5 — The descriptor. -/

/-- **`legCFamilies n`** — Leg C's constraint families, IN EMISSION ORDER: the front half (Leg R's
own families, verbatim), the clash pin, then the state-transition tail. The commitment families are
emitted LAST, exactly as in Leg R.

Carried as a LIST OF FAMILIES rather than a fold of `++` on purpose: membership of a family in the
descriptor is then ONE `List.mem_flatten` step instead of a twenty-deep `mem_append_left` climb, and
that membership is what every `_of_mem` extraction lemma M2 reuses takes as its hypothesis (§6.5).
The flattened VALUE is the same list either way, so the wire golden is unaffected. -/
def legCFamilies (n : Nat) : List (List VmConstraint2) :=
  [ [ NGen.onePin n ]
  , legCBoardRangeConstraints n
  , NGen.autoReadConstraints n
  , NGen.validateMove n (NGen.mvBase n 0)
  , NGen.validateMove n (NGen.mvBase n 1)
  , NGen.srcNonVacConstraints n                                      -- the non-vacuum source bits
  , NGen.patternBitConstraints n                                     -- the four eq_coords bits
  , NGen.selectionConstraints n                                      -- cFork / cCollide / cSurv
  , [ clashPin n ]                                                   -- THIS ROUND IS A CLASH
  , boardFrozenConstraints n                                         -- the board does not move
  , destOneHotConstraints n 0, destOneHotConstraints n 1
  , legalityConstraints n 0, legalityConstraints n 1                 -- the moveLegalB marks half
  , csConstraints n                                                  -- the clash delta
  , marksOrConstraints n                                             -- marksOut = marksIn ∨ cs
  , inClashConstraints n 0, inClashConstraints n 1
  , seatConstraints n 0, seatConstraints n 1
  , seatCommitConstraints n 0, seatCommitConstraints n 1
  , legCMarksConstraints n                                           -- M0, twice
  , legCBoardCommitConstraints n ]                                   -- LAST

/-- The emitted constraint list. -/
def legCConstraints (n : Nat) : List VmConstraint2 := (legCFamilies n).flatten

/-- **`automataflLegCDescN n`** — THE LEG C DESCRIPTOR, `n`-generic. Unlike
`automataflResolveDescN`, the `name` is computed from `n`, so the emitted object never advertises a
size it is not (`AutomataflNGenGolden` exists to patch exactly that latent bug for Leg R). -/
def automataflLegCDescN (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-legc-n" ++ toString n
  , traceWidth  := LEGC_WIDTH n
  , piCount     := LEGC_PI_COUNT n
  , tables      := []
  , constraints := legCConstraints n
  , hashSites   := []
  , ranges      := [] }

/-! ## §5.1 — THE MEMBERSHIP INTERFACE (what M2 hands to every `_of_mem` extraction lemma).

Every reusable refinement lemma in this tree — `AutomataflResolveRefine.validMoveN_of_sat`,
`AutomataflMarks.marksAlpha_of_mem`, `marksPack_pi_of_mem`, `AutomataflCommitRefine.pack_pi_of_mem` —
is parameterised by "this gate is IN the descriptor". These are those hypotheses, discharged once
here so M2 never re-climbs an append chain. They are the reason Leg C splices the front half in
verbatim instead of re-authoring it. -/

/-- One step from a family to the descriptor. -/
theorem mem_legC {n : Nat} {g : VmConstraint2} {fam : List VmConstraint2}
    (hf : fam ∈ legCFamilies n) (hg : g ∈ fam) :
    g ∈ (automataflLegCDescN n).constraints :=
  List.mem_flatten.mpr ⟨fam, hf, hg⟩

/-- **The front half is genuinely spliced in**: `validateMove`'s gates for either move are Leg C's
gates. This is `validMoveN_of_sat`'s `hmv`, discharged. -/
theorem mem_validateMove {n w : Nat} (hw : w = 0 ∨ w = 1) {g : VmConstraint2}
    (hg : g ∈ NGen.validateMove n (NGen.mvBase n w)) :
    g ∈ (automataflLegCDescN n).constraints := by
  rcases hw with rfl | rfl
  · exact mem_legC (by simp [legCFamilies]) hg
  · exact mem_legC (by simp [legCFamilies]) hg

/-- The clash-verdict block (`cFork`/`cCollide`/`cSurv`) is Leg C's — so the reference bridge
`surv_iff_clash_empty_of_sat` rests on gates this descriptor actually emits. -/
theorem mem_selection {n : Nat} {g : VmConstraint2} (hg : g ∈ NGen.selectionConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_patternBit {n : Nat} {g : VmConstraint2} (hg : g ∈ NGen.patternBitConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_srcNonVac {n : Nat} {g : VmConstraint2} (hg : g ∈ NGen.srcNonVacConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_autoRead {n : Nat} {g : VmConstraint2} (hg : g ∈ NGen.autoReadConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_boardRange {n : Nat} {g : VmConstraint2} (hg : g ∈ legCBoardRangeConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

/-- **THE CLASH PIN IS EMITTED.** With `surv_iff_clash_empty_of_sat`, this is what makes M2's
`hclash` a consequence of `Satisfied2` rather than a hypothesis. -/
theorem mem_clashPin (n : Nat) : clashPin n ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) (List.mem_singleton_self _)

theorem mem_boardFrozen {n : Nat} {g : VmConstraint2} (hg : g ∈ boardFrozenConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_marksFamily {n : Nat} {g : VmConstraint2} (hg : g ∈ legCMarksConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_boardCommit {n : Nat} {g : VmConstraint2} (hg : g ∈ legCBoardCommitConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_cs {n : Nat} {g : VmConstraint2} (hg : g ∈ csConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_marksOr {n : Nat} {g : VmConstraint2} (hg : g ∈ marksOrConstraints n) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) hg

theorem mem_legality {n w : Nat} (hw : w = 0 ∨ w = 1) {g : VmConstraint2}
    (hg : g ∈ legalityConstraints n w) : g ∈ (automataflLegCDescN n).constraints := by
  rcases hw with rfl | rfl
  · exact mem_legC (by simp [legCFamilies]) hg
  · exact mem_legC (by simp [legCFamilies]) hg

theorem mem_inClash {n w : Nat} (hw : w = 0 ∨ w = 1) {g : VmConstraint2}
    (hg : g ∈ inClashConstraints n w) : g ∈ (automataflLegCDescN n).constraints := by
  rcases hw with rfl | rfl
  · exact mem_legC (by simp [legCFamilies]) hg
  · exact mem_legC (by simp [legCFamilies]) hg

theorem mem_destOneHot {n w : Nat} (hw : w = 0 ∨ w = 1) {g : VmConstraint2}
    (hg : g ∈ destOneHotConstraints n w) : g ∈ (automataflLegCDescN n).constraints := by
  rcases hw with rfl | rfl
  · exact mem_legC (by simp [legCFamilies]) hg
  · exact mem_legC (by simp [legCFamilies]) hg

theorem mem_seat {n s : Nat} (hs : s = 0 ∨ s = 1) {g : VmConstraint2}
    (hg : g ∈ seatConstraints n s) : g ∈ (automataflLegCDescN n).constraints := by
  rcases hs with rfl | rfl
  · exact mem_legC (by simp [legCFamilies]) hg
  · exact mem_legC (by simp [legCFamilies]) hg

theorem mem_seatCommit {n s : Nat} (hs : s = 0 ∨ s = 1) {g : VmConstraint2}
    (hg : g ∈ seatCommitConstraints n s) : g ∈ (automataflLegCDescN n).constraints := by
  rcases hs with rfl | rfl
  · exact mem_legC (by simp [legCFamilies]) hg
  · exact mem_legC (by simp [legCFamilies]) hg

/-! ### §5.2 — The three marks ingredients M0's transport asks for, at BOTH windows.

`AutomataflMarks.marksAlpha_of_mem` wants the `{0,1}` gate; `marksPack_pi_of_mem` wants the pack gate
and the `.piBinding`. These produce all three at Leg C's own bases, for `marksIn` and `marksOut`. -/

/-- The `{0,1}` alphabet gate of marks cell `idx`, at either window. -/
theorem mem_marks_range {n idx : Nat} (hidx : idx < n * n) (cellCol feltCol : Nat → Nat)
    (piBase : Nat) :
    (.base (.gate (AutomataflCommit.memberExpr (cellCol idx) [0, 1])) : VmConstraint2)
      ∈ marksCommitFamilyAt n cellCol feltCol piBase := by
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩

/-- The base-4 pack gate of marks felt `j`, at either window. -/
theorem mem_marks_pack {n j : Nat} (hj : j < AutomataflCommit.feltCount n)
    (cellCol feltCol : Nat → Nat) (piBase : Nat) :
    AutomataflCommit.linGate (AutomataflCommit.packTermsAt n j cellCol feltCol) 0
      ∈ marksCommitFamilyAt n cellCol feltCol piBase :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))

/-- The `.piBinding` of marks felt `j`, at either window. -/
theorem mem_marks_pi {n j : Nat} (hj : j < AutomataflCommit.feltCount n)
    (cellCol feltCol : Nat → Nat) (piBase : Nat) :
    (.base (.piBinding VmRow.first (feltCol j) (piBase + j)) : VmConstraint2)
      ∈ marksCommitFamilyAt n cellCol feltCol piBase :=
  List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- `marksIn`'s family is Leg C's. -/
theorem mem_marksIn {n : Nat} {g : VmConstraint2}
    (hg : g ∈ marksCommitFamilyAt n (cMarksInCell n) (cMarksInFelt n) (piMarksIn n)) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_marksFamily (List.mem_append_left _ hg)

/-- `marksOut`'s family is Leg C's. -/
theorem mem_marksOut {n : Nat} {g : VmConstraint2}
    (hg : g ∈ marksCommitFamilyAt n (cMarksOutCell n) (cMarksOutFelt n) (piMarksOut n)) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_marksFamily (List.mem_append_right _ hg)

/-! ## §6 — The decode: the objects M2's refinement quantifies over. -/

/-- Move `w` decoded, with the seat taken from the MOVE INDEX (`seat s owns move s`). Leg R's
`moveDecodeN` hard-codes `who = 0`; the `waiting`/`locked` routing needs the seat, and at `P = 2` the
index IS the seat. Binding the seat to a player account is Leg S's job (design §9.2). -/
def legcMoveDecode (n : Nat) (e : VmRowEnv) (w : Nat) : Move :=
  Move.mk w
    ⟨(e.loc (NGen.cFx n (NGen.mvBase n w))).toNat, (e.loc (NGen.cFy n (NGen.mvBase n w))).toNat⟩
    ⟨(e.loc (NGen.cTx n (NGen.mvBase n w))).toNat, (e.loc (NGen.cTy n (NGen.mvBase n w))).toNat⟩

/-- This round's submissions (the fresh reveals; at `P = 2` every seat is waiting). -/
def freshSubsDecode (n : Nat) (e : VmRowEnv) : List Move :=
  (List.range LEGC_SEATS).map (legcMoveDecode n e)

/-- A marks indicator column read back as `roundStep`'s `List Coord`, in row-major order — duplicate
free by construction, which is `RoundWF.marksNodup`. -/
def marksListDecode (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) : List Coord :=
  (List.range (n * n)).filterMap (fun i =>
    if e.loc (cellCol i) == 1 then some (⟨i % n, i / n⟩ : Coord) else none)

/-- The seat-indexed locked table read back as `roundStep`'s `List Move` (seat order). -/
def lockedDecodeAt (bitCol fxCol fyCol txCol tyCol : Nat → Nat) (e : VmRowEnv) :
    List Move :=
  ((List.range LEGC_SEATS).filter (fun s => e.loc (bitCol s) == 1)).map (fun s =>
    Move.mk s ⟨(e.loc (fxCol s)).toNat, (e.loc (fyCol s)).toNat⟩
              ⟨(e.loc (txCol s)).toNat, (e.loc (tyCol s)).toNat⟩)

/-- The waiting indicator read back as `roundStep`'s `List Pid` (seat order). -/
def waitingDecodeAt (bitCol : Nat → Nat) (e : VmRowEnv) : List Pid :=
  (List.range LEGC_SEATS).filter (fun s => e.loc (bitCol s) == 1)

/-- **The IN RoundState** — what the round is entered with. -/
def roundStateDecodeIn (n : Nat) (e : VmRowEnv) : RoundState :=
  { board   := boardDecodeOldN n e
  , marks   := marksListDecode n (cMarksInCell n) e
  , locked  := lockedDecodeAt (cLockedInBit n) (cLockedInFx n) (cLockedInFy n) (cLockedInTx n)
                 (cLockedInTy n) e
  , waiting := waitingDecodeAt (cWaitingInBit n) e }

/-- **The OUT RoundState** — what M2 must prove IS `roundStep`'s `.again` state. The board is the
same decoded board: `boardFrozenConstraints` gates the OUT cells equal to the IN cells, and
`roundStep`'s `.again` carries `board := rs.board`. -/
def roundStateDecodeOut (n : Nat) (e : VmRowEnv) : RoundState :=
  { board   := boardDecodeOldN n e
  , marks   := marksListDecode n (cMarksOutCell n) e
  , locked  := lockedDecodeAt (cLockedOutBit n) (cLockedOutFx n) (cLockedOutFy n) (cLockedOutTx n)
                 (cLockedOutTy n) e
  , waiting := waitingDecodeAt (cWaitingOutBit n) e }

/-- The emitted-side marks indicators (M0's decode at Leg C's two bases) — the form
`marks_pack_injective` and `marks_window_eq_imp_mem_iff` consume across a seam. -/
def marksInDecode (n : Nat) (e : VmRowEnv) : MarksBoard := marksDecodeAt n (cMarksInCell n) e
def marksOutDecode (n : Nat) (e : VmRowEnv) : MarksBoard := marksDecodeAt n (cMarksOutCell n) e

/-- **`RoundStateAgrees` — the equality M2 can actually prove, and why it is not `=`.**

`roundStep`'s `.again` carries `marks := (rs.marks ++ cs).dedup` — INSERTION order. An `n²` indicator
board has no insertion order; `marksListDecode` reads it back in ROW-MAJOR order. From round 2 on the
two lists genuinely differ (§8.6 exhibits it: the spec says `[(2,0), (0,0)]`, the window says
`[(0,0), (2,0)]`), so `roundStateDecodeOut … = .again`'s state is **FALSE** as literal equality and
must not be stated. They are PERMUTATIONS of each other, and permutation is everything the rules use:
`MoveLegal` reads `marks` only through `∉`, and `RoundWF` only through `Nodup` — both
permutation-invariant. This is M0's own honest caveat ("a `List Coord` also carries order and
duplicates, which no `n²` indicator can recover and which the spec never reads") made into the
relation M2 is held to, so M2 can neither prove something false nor quietly weaken to "same set,
roughly".

The board is compared the way the rest of this tree compares boards (cell-wise + size + automaton):
`Board` carries function fields, so `=` on it is not decidable and not what any capstone states. -/
def RoundStateAgrees (rs1 rs2 : RoundState) : Prop :=
  rs1.board.size = rs2.board.size
  ∧ rs1.board.automaton = rs2.board.automaton
  ∧ (∀ c : Coord, rs1.board.cellAt c = rs2.board.cellAt c)
  ∧ rs1.marks.Perm rs2.marks
  ∧ rs1.locked = rs2.locked
  ∧ rs1.waiting = rs2.waiting

/-! ## §7 — The emitted SHAPE (`#guard`). The wire goldens are byte-pinned in
`AutomataflLegCGolden` (they are 553 KiB at `n = 11` / 153 KiB at `n = 5`, so they live in their own
leaf, exactly as `AutomataflNGenGolden` does for Leg R). -/

-- THE DEPLOYED SIZE. Compare Leg R at `n = 11`: 1273 columns / 36 PIs / 1618 constraints. Leg C is
-- narrower AND cheaper — it drops the entire resolution tail — while carrying the WIDER RoundState
-- window (78 PIs vs 36: +2·9 marks felts, +2·10 locked lanes, +2·2 waiting bits).
#guard (automataflLegCDescN 11).name == "dregg-automatafl-legc-n11"
#guard (automataflLegCDescN 11).traceWidth == 1208
#guard (automataflLegCDescN 11).piCount == 78
#guard (automataflLegCDescN 11).constraints.length == 1425
#guard (automataflLegCDescN 11).tables.length == 0
#guard (automataflLegCDescN 11).hashSites.length == 0        -- HASH-FREE, by construction
#guard (automataflLegCDescN 11).ranges.length == 0
#guard (automataflLegCDescN 11).constraints.all
  (fun c => match c with | .lookup _ => false | _ => true)   -- NO LOOKUPS: no chip-table soundness
-- the canary size (the audit witnesses' 5×5 board) and the minimal instance.
#guard (automataflLegCDescN 5).traceWidth == 536
#guard (automataflLegCDescN 5).piCount == 50
#guard (automataflLegCDescN 5).constraints.length == 521
#guard (automataflLegCDescN 2).traceWidth == 315
#guard (automataflLegCDescN 2).piCount == 46
#guard (automataflLegCDescN 2).constraints.length == 275

-- The PI window, lane for lane, at the deployed size (design §1.4 / §2).
#guard NGen.AUTO_PI_BASE 11 == 34                            -- Leg R's window ends at PI 35
#guard piMarksIn 11 == 36
#guard piMarksOut 11 == 45
#guard piLockedIn 11 == 54
#guard piLockedOut 11 == 64
#guard piWaitingIn 11 == 74
#guard piWaitingOut 11 == 76
#guard LEGC_PI_COUNT 11 == 78
#guard roundStateWindowLanes 11 LEGC_SEATS == 32             -- 9 board + 9 marks + 10 locked + 2 waiting + 2 auto
#guard marksWindowLanes 11 == 9                              -- M0's lane count, consumed not re-derived

-- The column layout at the deployed size: the front half is Leg R's, numeral for numeral, and the
-- tail starts exactly where Leg R's resolution tail did.
#guard LEGC0 11 == NGen.CAR0 11
#guard LEGC0 11 == 729
#guard NGen.cSurv 11 == 728                                  -- the clash verdict is the last front column
#guard MARKS0 11 == 747
#guard CS0 11 == 1007
#guard TSEL0 11 == 1128
#guard MVQ0 11 == 1172
#guard SEAT0 11 == 1184
#guard LEGC_WIDTH 11 == 1208
-- THE DEAD WINDOW, pinned so it cannot grow unnoticed: the two dropped occlusion blocks.
#guard NGen.occBase 11 0 == 413
#guard NGen.RES0 11 == 663
#guard NGen.RES0 11 - NGen.occBase 11 0 == 250

-- The family sizes at `n = 11` (the tail is the small half; the front half is the reused half).
#guard (legCBoardRangeConstraints 11).length == 242
#guard (boardFrozenConstraints 11).length == 121
#guard (legCBoardCommitConstraints 11).length == 38
#guard (legCMarksConstraints 11).length == 278               -- 2 × M0's 139
#guard (csConstraints 11).length == 242                      -- 121 gBin + 121 delta heads
#guard (marksOrConstraints 11).length == 121
#guard (destOneHotConstraints 11 0).length == 26
#guard (legalityConstraints 11 0).length == 4
#guard (inClashConstraints 11 0).length == 3
#guard (seatConstraints 11 0).length == 12
#guard (seatCommitConstraints 11 0).length == 12

/-! ## §8 — TWO-SIDED CANARIES on the EMITTED gates.

The rows below fill Leg C's TAIL columns for a real round and evaluate the tail gate families on
them. They are NOT full satisfying traces — the front half's coordinate decompositions, inverses and
`eq_coords` blocks are a witness generator's job (M4) — and nothing here is called a proof. What they
DO establish is that each new gate vanishes on the honest tail assignment and BITES on the forged
one, at a board size where the rules file's own audit witnesses live.

The rounds are the two-move sub-rounds of the audit witnesses `AutomataflRules` uses for D4a/D4b (the
same `collBoard`/`d5Board` M0 packs): a COLLIDE at `(2,0)` and a FORK at `(0,0)`. -/

open Dregg2.Games.AutomataflRules

/-- `AutomataflRules`' own `mv` / `cfgCol` / `noGoals` are `private`; these are the same values. -/
private def cfgColC : GameConfig := ⟨.column⟩
private def noGoalsC : GoalAssignment := ⟨[]⟩
private def mkMvC (w : Pid) (a d : Coord) : Move := ⟨w, a, d⟩

/-! ### §8.1 — The SPEC side: what `roundStep` does on these rounds. -/

/-- The D4a COLLIDE, as a two-seat round: both seats drive into `(2,0)` from non-vacuum sources. -/
def collideOut : RoundOutcome :=
  roundStep cfgColC noGoalsC (openRound collBoard [0, 1]) [d4A, d4B]
/-- The D4b FORK, as a two-seat round: both seats leave `(0,0)` for different squares. -/
def forkOut : RoundOutcome :=
  roundStep cfgColC noGoalsC (openRound d5Board [0, 1]) [d5A, d5B]
/-- A CLEAN two-seat round on the same board: distinct sources, distinct destinations. -/
def cleanOut : RoundOutcome :=
  roundStep cfgColC noGoalsC (openRound collBoard [0, 1])
    [mkMvC 0 ⟨0, 0⟩ ⟨0, 2⟩, mkMvC 1 ⟨4, 0⟩ ⟨4, 2⟩]

#guard clashCoords collBoard [d4A, d4B] = [(⟨2, 0⟩ : Coord)]         -- collide at the shared dest
#guard clashCoords d5Board [d5A, d5B] = [(⟨0, 0⟩ : Coord)]           -- fork at the shared source
#guard clashCoords collBoard [mkMvC 0 ⟨0, 0⟩ ⟨0, 2⟩, mkMvC 1 ⟨4, 0⟩ ⟨4, 2⟩] = ([] : List Coord)
-- the `.again` RoundState Leg C must emit: marks grow by the conflicted coord, NOTHING locks, and
-- BOTH seats re-enter (the 2-player collapse — there is no innocent seat in a pair clash).
#guard collideOut.isAgain = true
#guard collideOut.marks = [(⟨2, 0⟩ : Coord)]
#guard collideOut.locked = ([] : List Move)
#guard collideOut.waiting = [0, 1]
#guard forkOut.isAgain = true
#guard forkOut.marks = [(⟨0, 0⟩ : Coord)]
#guard forkOut.locked = ([] : List Move)
#guard forkOut.waiting = [0, 1]
#guard cleanOut.isAgain = false                                       -- a clean round RESOLVES …
-- … and Leg C's `cSurv = 0` pin is exactly what refuses to fold it as a re-entry round (§8.4).

/-! ### §8.2 — The emitted-side rows. -/

/-- A sparse row: the listed columns carry the listed felts, every other column is `0`. -/
def rowOf (upd : List (Nat × ℤ)) : Assignment := fun c => (upd.lookup c).getD 0

/-- The move-`w` columns Leg C's tail gates read: the four coordinates, the SOURCE one-hots (which
`NGen.validateMove` pins) and the DESTINATION one-hots (which this file pins). -/
def moveCols (n w fx fy tx ty : Nat) : List (Nat × ℤ) :=
  [ (NGen.cFx n (NGen.mvBase n w), (fx : ℤ)), (NGen.cFy n (NGen.mvBase n w), (fy : ℤ))
  , (NGen.cTx n (NGen.mvBase n w), (tx : ℤ)), (NGen.cTy n (NGen.mvBase n w), (ty : ℤ))
  , (NGen.cSelRow n (NGen.mvBase n w) fy, 1), (NGen.cSelCol n (NGen.mvBase n w) fx, 1)
  , (cTSelRow n w ty, 1), (cTSelCol n w tx, 1) ]

/-- **THE COLLIDE ROUND**, `n = 5`: `d4A = 0:(0,0)→(2,0)`, `d4B = 1:(4,0)→(2,0)`. `cs = {(2,0)}`
(linear index `2`, so the marks pack's felt 0 is `4² = 16` — M0's `packMarks` canary value). Round 1,
so `marksIn = ∅`. -/
def collideRow : Assignment := rowOf (
  [ (NGen.cSurv 5, 0), (NGen.cFork 5, 0), (NGen.cCollide 5, 1) ]
  ++ moveCols 5 0 0 0 2 0 ++ moveCols 5 1 4 0 2 0
  ++ [ (cCsCell 5 2, 1), (cMarksOutCell 5 2, 1), (cMarksOutFelt 5 0, 16) ]
  ++ [ (cLegal 5 0, 1), (cLegal 5 1, 1)
     , (cCsTo 5 0, 1), (cInClash 5 0, 1), (cCsTo 5 1, 1), (cInClash 5 1, 1) ]
  ++ [ (cWaitingInBit 5 0, 1), (cWaitingInBit 5 1, 1)
     , (cWaitingOutBit 5 0, 1), (cWaitingOutBit 5 1, 1) ])

/-- **THE FORK ROUND**, `n = 5`: `d5A = 0:(0,0)→(0,2)`, `d5B = 1:(0,0)→(2,0)`. `cs = {(0,0)}`
(linear index `0`, marks felt 0 = `4⁰ = 1`). Both moves are dropped at their SOURCE this time. -/
def forkRow : Assignment := rowOf (
  [ (NGen.cSurv 5, 0), (NGen.cFork 5, 1), (NGen.cCollide 5, 0) ]
  ++ moveCols 5 0 0 0 0 2 ++ moveCols 5 1 0 0 2 0
  ++ [ (cCsCell 5 0, 1), (cMarksOutCell 5 0, 1), (cMarksOutFelt 5 0, 1) ]
  ++ [ (cLegal 5 0, 1), (cLegal 5 1, 1)
     , (cCsFrm 5 0, 1), (cInClash 5 0, 1), (cCsFrm 5 1, 1), (cInClash 5 1, 1) ]
  ++ [ (cWaitingInBit 5 0, 1), (cWaitingInBit 5 1, 1)
     , (cWaitingOutBit 5 0, 1), (cWaitingOutBit 5 1, 1) ])

/-- The row as a `VmRowEnv` (the decode reads `loc` only). -/
def envOf (a : Assignment) : VmRowEnv := ⟨a, a, a⟩

/-- Does every GATE of a family vanish on this row? (`piBinding`s carry no polynomial and are
skipped; `gateCount` below shows the answer is not vacuously `true`.) -/
def gatesVanish (cs : List VmConstraint2) (a : Assignment) : Bool :=
  cs.all (fun c => match c with | .base (.gate e) => e.eval a == 0 | _ => true)

def gateCount (cs : List VmConstraint2) : Nat :=
  (cs.filter (fun c => match c with | .base (.gate _) => true | _ => false)).length

/-! ### §8.3 — The HONEST side: every tail family vanishes on both clash rows. -/

#guard gateCount (csConstraints 5) == 50
#guard gateCount (marksOrConstraints 5) == 25
#guard gateCount (legCMarksConstraints 5) == 54
#guard gateCount (seatConstraints 5 0) == 12
#guard gateCount (destOneHotConstraints 5 0) == 14

#guard gatesVanish (csConstraints 5) collideRow                       -- cs IS the conflicted coord
#guard gatesVanish (marksOrConstraints 5) collideRow                  -- marksOut = marksIn ∨ cs
#guard gatesVanish (legCMarksConstraints 5) collideRow                -- {0,1} alphabet + both packs
#guard gatesVanish (legalityConstraints 5 0) collideRow               -- the marks-legality gate
#guard gatesVanish (legalityConstraints 5 1) collideRow
#guard gatesVanish (inClashConstraints 5 0) collideRow                -- the drop test
#guard gatesVanish (inClashConstraints 5 1) collideRow
#guard gatesVanish (destOneHotConstraints 5 0) collideRow
#guard gatesVanish (destOneHotConstraints 5 1) collideRow
#guard gatesVanish (seatConstraints 5 0) collideRow                   -- lockedOut = 0, waitingOut = 1
#guard gatesVanish (seatConstraints 5 1) collideRow
#guard gatesVanish [clashPin 5] collideRow                            -- cSurv = 0: this IS a clash
#guard gatesVanish (boardFrozenConstraints 5) collideRow              -- the board did not move

#guard gatesVanish (csConstraints 5) forkRow
#guard gatesVanish (marksOrConstraints 5) forkRow
#guard gatesVanish (legCMarksConstraints 5) forkRow
#guard gatesVanish (legalityConstraints 5 0) forkRow
#guard gatesVanish (legalityConstraints 5 1) forkRow
#guard gatesVanish (inClashConstraints 5 0) forkRow
#guard gatesVanish (inClashConstraints 5 1) forkRow
#guard gatesVanish (destOneHotConstraints 5 0) forkRow
#guard gatesVanish (destOneHotConstraints 5 1) forkRow
#guard gatesVanish (seatConstraints 5 0) forkRow
#guard gatesVanish (seatConstraints 5 1) forkRow
#guard gatesVanish [clashPin 5] forkRow

/-! **THE SPEC CORRESPONDENCE, COMPUTED.** The decoded OUT window's marks / locked / waiting ARE
`roundStep`'s `.again` RoundState on these rounds — the M2 statement, checked at a point. (M2 proves
it over ALL satisfying traces; this is the canary that says the statement is not false.) -/
#guard marksListDecode 5 (cMarksOutCell 5) (envOf collideRow) = collideOut.marks
#guard marksListDecode 5 (cMarksInCell 5) (envOf collideRow) = ([] : List Coord)
#guard lockedDecodeAt (cLockedOutBit 5) (cLockedOutFx 5) (cLockedOutFy 5) (cLockedOutTx 5)
  (cLockedOutTy 5) (envOf collideRow) = collideOut.locked
#guard waitingDecodeAt (cWaitingOutBit 5) (envOf collideRow) = collideOut.waiting
#guard marksListDecode 5 (cMarksOutCell 5) (envOf forkRow) = forkOut.marks
#guard lockedDecodeAt (cLockedOutBit 5) (cLockedOutFx 5) (cLockedOutFy 5) (cLockedOutTx 5)
  (cLockedOutTy 5) (envOf forkRow) = forkOut.locked
#guard waitingDecodeAt (cWaitingOutBit 5) (envOf forkRow) = forkOut.waiting
-- the two moves decode to the audit witnesses themselves (seat = move index).
#guard freshSubsDecode 5 (envOf collideRow) = [d4A, d4B]
#guard freshSubsDecode 5 (envOf forkRow) = [d5A, d5B]
-- and the published marks window IS M0's pack of that very marks set.
#guard AutomataflMarks.packMarks (marksBoardOf 5 collideOut.marks) 5 = [16, 0]
#guard AutomataflMarks.packMarks (marksBoardOf 5 forkOut.marks) 5 = [1, 0]

/-! ### §8.4 — THE LOAD-BEARING NEGATIVES. Each row below is the honest one with ONE lie in it. -/

/-- **THE FORGED `marksOut` THAT DROPS THE NEW MARK.** The prover keeps `marksIn` and refuses to
absorb `cs`, so next round the conflicted square is legal again and the turn never terminates. The
OR gate at that cell evaluates to `−1`. -/
def forgedDropRow : Assignment := fun c => if c = cMarksOutCell 5 2 then 0 else collideRow c
#guard gatesVanish (marksOrConstraints 5) forgedDropRow = false

/-- The same lie one level up: the felt is re-packed consistently with the dropped cell, so the pack
gate is happy — and the OR gate still refuses. (Forging the FELT instead is M0's
`marks_forge_rejected`, re-pointed at `cMarksOutFelt`.) -/
def forgedDropPackRow : Assignment :=
  fun c => if c = cMarksOutCell 5 2 then 0 else if c = cMarksOutFelt 5 0 then 0 else collideRow c
#guard gatesVanish (legCMarksConstraints 5) forgedDropPackRow          -- the PACK is consistent …
#guard gatesVanish (marksOrConstraints 5) forgedDropPackRow = false    -- … the OR gate still BITES

/-- **A FORGED `marksOut` THAT INVENTS A MARK** (poisoning a square no conflict touched). -/
def forgedAddRow : Assignment := fun c => if c = cMarksOutCell 5 7 then 1 else collideRow c
#guard gatesVanish (marksOrConstraints 5) forgedAddRow = false

/-- **A FORGED CLASH DELTA** — `cs` claimed at a coordinate neither move names. -/
def forgedCsRow : Assignment := fun c => if c = cCsCell 5 7 then 1 else collideRow c
#guard gatesVanish (csConstraints 5) forgedCsRow = false

/-- **A FORGED `lockedOut`** — the conflicted seat 0 tries to keep its move standing. -/
def forgedLockRow : Assignment := fun c => if c = cLockedOutBit 5 0 then 1 else collideRow c
#guard gatesVanish (seatConstraints 5 0) forgedLockRow = false

/-- **A FORGED `waitingOut`** — the conflicted seat 1 tries not to re-enter. -/
def forgedWaitRow : Assignment := fun c => if c = cWaitingOutBit 5 1 then 0 else collideRow c
#guard gatesVanish (seatConstraints 5 1) forgedWaitRow = false

/-- **THE MARKS LEGALITY GATE BITES.** `marksIn` now holds the source square of move 0 — the square
was marked in an earlier round, so `moveLegalB` REFUSES this submission and it may not enter `all`.
The `legal = ¬inMarksFrm ∧ ¬inMarksTo` gate (pinned to 1) is what refuses it, and this is the ONLY
place `marksIn` is consumed. -/
def markedSourceRow : Assignment :=
  fun c => if c = cMarksInCell 5 0 then 1 else if c = cInMarksFrm 5 0 then 1 else collideRow c
#guard gatesVanish (legalityConstraints 5 0) markedSourceRow = false
/-- …and lying about the READ instead of the gate does not help: the read is a gate too. -/
def markedSourceHiddenRow : Assignment :=
  fun c => if c = cMarksInCell 5 0 then 1 else collideRow c
#guard gatesVanish (legalityConstraints 5 0) markedSourceHiddenRow = false

/-- **A CLEAN ROUND IS UNSATISFIABLE AS A LEG C.** `cSurv = 1` is `clashCoords = []`
(`surv_iff_clash_empty_of_sat`), and the clash pin gates it to `0`. So the prover cannot pad a turn
with spurious identity re-entry rounds: Leg C is UNSAT on a clean round, not an identity on it. -/
def cleanRow : Assignment := fun c => if c = NGen.cSurv 5 then 1 else collideRow c
#guard gatesVanish [clashPin 5] cleanRow = false

/-! ### §8.5 — What these canaries do NOT show (say it, do not let it drift).

* They exercise the TAIL. The front half's own gates (`validateMove`'s decompositions, the
  `eq_coords` blocks, the `cFork`/`cCollide`/`cSurv` selection algebra) are Leg R's, already
  canaried and proven there; a row satisfying ALL of `legCConstraints` at once is M4's witness
  generator, and `gatesVanish (legCConstraints 5) collideRow` is FALSE for exactly that reason.
* `#guard` is evaluation at a point. That `csCell` is the conflicted coordinate FOR EVERY satisfying
  trace is `legC_sat_imp_roundAgainN` (M2), which is not in this file.
* The "innocent seat stays locked" case is not exercised because it does not exist at `P = 2`
  (header §"2-seat scope"): a pair clash conflicts both seats. It is M9's canary, with M9's engine. -/

#guard gatesVanish (legCConstraints 5) collideRow = false

/-! ### §8.6 — THE ORDER DIVERGENCE, EXHIBITED (why `RoundStateAgrees` uses `Perm`, not `=`).

Round 1 is a collide at `(2,0)`; round 2 is a fork at `(0,0)`. `roundStep` accumulates
`(marks ++ cs).dedup` in INSERTION order — `[(2,0), (0,0)]`. The marks window is an indicator board,
so `marksListDecode` reads it back in ROW-MAJOR order — `[(0,0), (2,0)]`. Both are the same SET and
the same `Nodup` list up to permutation, which is all `MoveLegal` (`∉`) and `RoundWF` (`Nodup`) ever
read; but they are NOT equal, so an M2 stated with `=` on `RoundState` would be proving something
false. Anyone tempted to strengthen `RoundStateAgrees` back to `=` breaks this `#guard` first. -/

/-- Round 1: the D4a collide at `(2,0)`; both seats re-enter with `marks = [(2,0)]`. -/
def twoRoundState1 : RoundState :=
  match collideOut with
  | .again rs => rs
  | .resolved _ _ => openRound collBoard [0, 1]
/-- Round 2: a fork at `(0,0)`, under the round-1 marks. -/
def twoRoundOut2 : RoundOutcome :=
  roundStep cfgColC noGoalsC twoRoundState1 [mkMvC 0 ⟨0, 0⟩ ⟨0, 2⟩, mkMvC 1 ⟨0, 0⟩ ⟨1, 0⟩]
/-- The same marks set as the round-2 window would publish, in the indicator's row-major order. -/
def twoRoundWindowMarks : List Coord :=
  (List.range 25).filterMap (fun i =>
    if twoRoundOut2.marks.contains (⟨i % 5, i / 5⟩ : Coord) then some ⟨i % 5, i / 5⟩ else none)

#guard twoRoundState1.marks = [(⟨2, 0⟩ : Coord)]
#guard twoRoundOut2.isAgain = true
#guard twoRoundOut2.marks = [(⟨2, 0⟩ : Coord), (⟨0, 0⟩ : Coord)]      -- INSERTION order
#guard twoRoundWindowMarks = [(⟨0, 0⟩ : Coord), (⟨2, 0⟩ : Coord)]     -- ROW-MAJOR order
#guard twoRoundOut2.marks ≠ twoRoundWindowMarks                       -- … NOT equal …
#guard twoRoundOut2.marks.isPerm twoRoundWindowMarks                  -- … but a PERMUTATION.
-- and the marks GREW, as M3's `roundStep_marks_strict_growth` says it must.
#guard twoRoundState1.marks.length < twoRoundOut2.marks.length

/-! ## §8.7 — Axiom hygiene: the membership interface rests only on the kernel triple. -/

#assert_axioms mem_legC
#assert_axioms mem_validateMove
#assert_axioms mem_selection
#assert_axioms mem_patternBit
#assert_axioms mem_srcNonVac
#assert_axioms mem_autoRead
#assert_axioms mem_boardRange
#assert_axioms mem_clashPin
#assert_axioms mem_boardFrozen
#assert_axioms mem_marksFamily
#assert_axioms mem_boardCommit
#assert_axioms mem_cs
#assert_axioms mem_marksOr
#assert_axioms mem_legality
#assert_axioms mem_inClash
#assert_axioms mem_destOneHot
#assert_axioms mem_seat
#assert_axioms mem_seatCommit
#assert_axioms mem_marks_range
#assert_axioms mem_marks_pack
#assert_axioms mem_marks_pi
#assert_axioms mem_marksIn
#assert_axioms mem_marksOut

/-! ## §9 — THE INTERFACE M2 PROVES AGAINST.

The refinement theorem this file's object is built for (design §1.4), stated at the objects defined
above so M2 has no room to drift into proving something else:

```lean
theorem legC_sat_imp_roundAgainN (n : Nat) (g : GoalAssignment)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) :
    ∃ rs', roundStep ⟨.column⟩ g (roundStateDecodeIn n (envAt t 0)) (freshSubsDecode n (envAt t 0))
             = .again rs'
           ∧ RoundStateAgrees rs' (roundStateDecodeOut n (envAt t 0))
```

Two things to hold M2 to, both already fixed by the definitions above:

* the conclusion is `RoundStateAgrees`, NOT `=` — the marks list's INSERTION order is not
  recoverable from an indicator board, and §8.6 exhibits a concrete round where the two lists differ.
  `Perm` is exactly what the rules read (`∉`, `Nodup`), so nothing is lost; but `=` would be false and
  a set-flavoured hand-wave would be weaker than provable.
* what is NOT a hypothesis: `hclash`. `clashPin` gates `cSurv = 0` (`mem_clashPin`), and
  `surv_iff_clash_empty_of_sat` turns that into `clashCoords ≠ []`, so the clash branch is forced by
  `Satisfied2` itself.

The pieces M2 needs, and where they already are:

* **the front half** — `AutomataflResolveRefine.validMoveN_of_sat` and the rest of that family are
  already MEMBERSHIP-PARAMETERISED (`hmv : g ∈ NGen.validateMove n (mvBase n w) → g ∈ D.constraints`),
  and §5.1 discharges exactly those hypotheses (`mem_validateMove`, `mem_selection`, `mem_srcNonVac`,
  `mem_patternBit`, `mem_autoRead`, `mem_boardRange`) in ONE `List.mem_flatten` step — Leg C emits the
  same constraint VALUES at the same columns. Nothing is re-derived.
* **the clash verdict** — `surv_iff_clash_empty_of_sat` is keyed on `Satisfied2 (automataflResolveDescN n)`
  through `resolveFactsN_of_sat`, which also pulls the occlusion/carry facts Leg C does not emit. M2
  needs the `_of_mem` restatement of the SELECTION block alone (`NGen.srcNonVacConstraints`,
  `patternBitConstraints`, `selectionConstraints`, which Leg C emits verbatim). That is membership
  plumbing over already-proven algebra, not new mathematics — but it is real work and it is M2's
  first task, not a freebie.
* **the marks half** — `AutomataflMarks.marksAlpha_of_mem` / `marksPack_pi_of_mem` are host-form
  already; `marksCode_eq_one_iff_mem` lines the indicator up against `rs.marks : List Coord` inside
  the `moveLegalB` conjuncts, and `marks_pack_injective` keeps the seam hash-free.
* **the board** — `AutomataflCommitRefine.pack_pi_of_mem` transports both windows;
  `boardFrozenConstraints` is what makes the OUT window the IN window.
* **termination** — M3 (`AutomataflTermination`) is landed: `roundStep_marks_strict_growth` and
  `againDepth_le` give the fold its `n²` fuel, and `RoundWF` is preserved by the OUT state Leg C
  emits (`marksNodup` is structural in `marksListDecode`'s row-major filter; `lockedLegal` is vacuous
  because `lockedOut = []` at `P = 2`).

M5 consumes `roundStateWindowLanes n P` (32 lanes at `n = 11`, `P = 2`) and the PI bases in §3. -/

end Dregg2.Circuit.Emit.AutomataflLegCEmit
