/-
# Dregg2.Circuit.Emit.AutomataflStepEmit — the EMIT-FROM-LEAN author of the automatafl
board-transition automaton-step (D1) descriptor (`dregg-automatafl-step-d1-n2`).

## What this file IS, and the law it closes

Law #1: ZERO Rust-authored constraints. The automatafl board-transition AIR was authored in RUST
(`dregg-automatafl/src/air.rs`, `automaton_gadget`) with NO Lean emit — the same
hand-transcription debt `DyckStackEmit.lean` ended for the Dyck parse circuit. This file is the Lean
author that moves it OFF Rust: the D1 automaton-step constraints are authored here as IR-v2
`VmConstraint2` nodes, byte-pinned by an `emitVmJson2` `#guard`, re-derived onto disk by
`EmitByName.lean` + `scripts/emit_descriptors.py`, and put under the drift gate.

The SEMANTIC target this descriptor refines (Stage 2, NOT in this file) is
`Dregg2.Games.Automatafl.automatonStep` — the pure `raycast → evaluateAxis → chooseOffset → step`
transition. This file is Stage 1: the descriptor STRUCTURE + byte-pin + emit registration.

## The AIR shape (`air.rs::automaton_gadget` ↦ IR-v2 carrier)

The D1 AIR is a SINGLE-ROW circuit: almost every constraint is a per-row polynomial gate
(`assert_zero` of a `Head` = a sum-of-products), a boolean pin (`assert_binary`), or a small-set
membership (`assert_member`) — all `.base (.gate e)` over an `EmittedExpr`, no `WindowGate`. The two
board commitments, which are degree-1 pack gates whose packed felts ride first-row `PiBinding`s.
(The Rust original used two arity-16 `Poseidon2Chip` `MerkleHash8` lookups here; those are RETIRED —
see §4b.6 / §4d — so this descriptor now emits NO lookup at all.)

The `Builder` primitives (`dregg-automatafl/src/builder.rs`) lower as:

| Rust `Builder` primitive                | IR-v2 carrier authored here                          |
|-----------------------------------------|------------------------------------------------------|
| `assert_zero(Head)`                     | `Base(Gate(headToExpr Head))`                        |
| `assert_binary(c)`                      | `Base(Gate(c·(c−1)))`                                |
| `assert_member(c, set)`                 | `Base(Gate(∏_{s∈set}(c−s)))`                         |
| `one_hot` (Σ=1 + Σ j·selⱼ = index)      | two gates                                            |
| `decompose_coord_le` (bit range)        | per bit: a binary gate + one recomposition gate      |
| `one_hot_rowcol` read (√n)              | the row + col one-hots, addressed by `selRow·selCol` |
| `shifted_read_rowcol_gated` (ray step)  | one gate `rc − Σ gate·selRow·selCol·board`           |
| `cond_nonzero(sel, val)`                | one gate `sel·(val·inv − 1)` (fresh inverse column)  |

## The board size — n = 2 (the minimal COMPLETE instance)

The gadget is board-size-generic (the constraint FAMILIES are functions of `n` only, never of the
witnessed board). This file instantiates the smallest complete board, `n = 2` (the D3 resolution
size), which exercises every front-end family — board columns, coordinate range, the auto row×column
one-hot pin, and the four ray scans with the prefix-sum in-bounds bit — at a tractable byte-pin. The
deployed leaves run at `n = 5` / `n = 11`; scaling `NN` re-emits the same families at the larger
counts (a follow-up, byte-pin re-pins mechanically).

## SCOPE — the COMPLETE automaton-step gate set (Stage 1a front-end + Stage 1b back-end)

STAGE 1a (§4, the front-end): the board columns (old + new) WITH their per-cell particle range
checks (`assert_member(cell, {0,1,2,3})`, `boardRangeConstraints` — without them a witnessed cell
`≥ 4` decodes to VACUUM in the reference while the circuit's vacancy test blocks, and the Stage-2
refinement is FALSE over satisfying witnesses), the door-PI prefix, the automaton
position pin (`ax`/`ay` bit-range + the auto row×column one-hot + the `AUTO == Σ selRow·selCol·board`
dot product), and the FOUR ray scans (per step: the prefix-sum in-bounds bit, the gated shifted
row×column read, the hit one-hot, the `dist`/`what` recompositions, the vacuum-before / in-bounds-
before occlusion gates, the hit-in-bounds bit, and the `cond_nonzero` in-bounds-hit witness).

STAGE 1b (§4b, the back-end): `decide_axis` (the 9-case `evaluateAxis` truth table ×2 axes, with its
`forced_ge0` range gadgets `gpd/gnd/lt/gt/le/gmin` + the gated `min` gadget + the gated `assert_case`
field equalities) · `choose_offset` (the 20-bit score-compare `sgt/slt`, `xmove/ymove`, the column
rule, and the `ox`/`oy` offset equalities) · the STEP (target read, target-in-bounds `tib`,
`targ_vac`, `offnz`, `moved`, the gated `sel_target` row×column one-hot) · the per-cell board-update
equalities · THE PACKED BOARD COMMITMENT (§4d: `⌈n²/15⌉` base-4 pack gates per board, their
`.piBinding`s, and the automaton coordinate).

This is the FULL `automaton_gadget` + commitment gate set — the descriptor is COMPLETE for
D1/n=2. What is NOT in this file: the Stage-2 refinement proof (`Satisfied2 ⇒ automatonStep`) and
Leg R. Scaling `NN` re-emits the same families at `n = 5`/`n = 11` (byte-pin re-pins mechanically).

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its full wire string + shape `#guard`s. NEW file;
imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.AutomataflCommit

namespace Dregg2.Circuit.Emit.AutomataflStepEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleN emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Constants (`reference.rs`). Particle felt codes; the board is `n×n`. -/

/-- The board dimension. The gadget families are `NN`-generic; this file emits the `n = 2` instance. -/
def NN : Nat := 2
/-- `k = n²`, the number of board cells. -/
def KK : Nat := NN * NN
/-- The automaton particle felt code (`reference.rs::AUTO`). Cells hold `{VAC=0, REP=1, ATT=2, AUTO=3}`. -/
def AUTO : ℤ := 3

/-! ## §2 — The column layout (the `Builder::alloc` order of `build_d1_bound` + `automaton_gadget`).

Columns are allocated exactly in the Rust order so the emitted var indices mirror the gadget:
old cells, new cells, `ax`/`ay`, the two coordinate bit-decompositions, the auto row/col one-hots,
then a fixed 10-column block per ray. -/

/-- `old[i]` — cell `i` of the source board (columns `0..k`). All ray/auto reads are over this board. -/
def old (i : Nat) : Nat := i
/-- `new[i]` — cell `i` of the claimed-next board (columns `k..2k`). Allocated now to keep the layout
stable for the DEFERRED board-update family; unconstrained until it lands. -/
def new (i : Nat) : Nat := KK + i
/-- The automaton x/y coordinate columns. -/
def AX : Nat := 2 * KK
def AY : Nat := 2 * KK + 1
/-- `decompose_coord_le` bits for `ax` (max `= n−1`, so `rbits = 1` at `n = 2`): lower then upper edge. -/
def axLoBit : Nat := 2 * KK + 2
def axHiBit : Nat := 2 * KK + 3
/-- `decompose_coord_le` bits for `ay`. -/
def ayLoBit : Nat := 2 * KK + 4
def ayHiBit : Nat := 2 * KK + 5
/-- The auto ROW one-hot (pinned to `ay`) — `sel_auto_row[y]`. -/
def selRow (y : Nat) : Nat := 2 * KK + 6 + y
/-- The auto COLUMN one-hot (pinned to `ax`) — `sel_auto_col[x]`. -/
def selCol (x : Nat) : Nat := 2 * KK + 6 + NN + x
/-- The first column of ray `d`'s 10-column block (`ib×2, rc×2, hit×2, dist, what, hib, inv`). -/
def rayBase (d : Nat) : Nat := 2 * KK + 6 + 2 * NN + 10 * d
/-- `ib` (in-bounds bit) for ray `d`, step `kk ∈ {1..n}`. -/
def rIb (d kk : Nat) : Nat := rayBase d + 2 * (kk - 1)
/-- `rc` (gated cell read) for ray `d`, step `kk`. -/
def rRc (d kk : Nat) : Nat := rayBase d + 2 * (kk - 1) + 1
/-- `hit` one-hot bit for ray `d`, step `kk`. -/
def rHit (d kk : Nat) : Nat := rayBase d + 4 + (kk - 1)
/-- `dist` (recomposed hit distance) for ray `d`. -/
def rDist (d : Nat) : Nat := rayBase d + 6
/-- `what` (recomposed hit particle) for ray `d`. -/
def rWhat (d : Nat) : Nat := rayBase d + 7
/-- `hib` (in-bounds-at-hit bit) for ray `d`. -/
def rHib (d : Nat) : Nat := rayBase d + 8
/-- `inv` (the `cond_nonzero` witnessed inverse) for ray `d`. -/
def rInv (d : Nat) : Nat := rayBase d + 9
/-- Front-end trace width (Stage 1a): `2k + 2 (coords) + 4 (coord bits) + 2n (auto one-hots) +
10·4 (rays)` = 58. The Stage-1b families continue the Rust `alloc` order from column 58. -/
def A_FRONT_WIDTH : Nat := 2 * KK + 6 + 2 * NN + 10 * 4
/-- Total main-trace width at `n = 2`: front-end (58) + `decide_axis` ×2 (94) + `choose_offset` (57)
+ the step (44) — the two `decide_axis` return their own `variant/pos/att/rep` that `choose_offset`
reuses, so the running `alloc` counter lands at `A_BACK_TAIL = 252` — plus the PACKED COMMITMENT's
`2·⌈n²/15⌉ = 2` felt columns (`[252, 254)`) plus the two NEW-automaton-coordinate columns
`nax`/`nay` (`[254, 256)`) = 256. (Was 269 under the retired 17-column `board_root8` block; the
pack is 15× denser per felt, so the commitment costs 2 columns instead of 17.) Pinned against the
`n`-parametric `A_WIDTH_N 2` in §5. -/
def A_WIDTH : Nat := 256
/-- The door state-binding PI prefix (`old8 ‖ new8`, PIs `[0..16)`) plus the packed OLD board
(`[16, 17)`), the packed NEW board (`[17, 18)`), the OLD automaton coordinate (`[18], [19]`) and the
NEW automaton coordinate (`[20], [21]`) at `n = 2`. (Was 32 under the two 8-lane `board_root8`
digests.) -/
def A_PI_COUNT : Nat := 22

/-! ## §3 — `Head`: the `builder.rs` linear/product head, in Lean.

`Head` mirrors `Builder`'s `Head` (`Σ (coeff, cols) + constant`). `headToExpr` lowers it to the
`EmittedExpr` polynomial the IR-v2 gate carries (zero-coefficient terms dropped for a clean gate;
Lean is the source of truth, so the canonical form is the authored one). -/

/-- A linear/product head: `Σ (coeff, cols) + constant`; `cols = []` is the constant term. -/
structure Head where
  terms : List (ℤ × List Nat)
  const : ℤ

namespace Head
def zero : Head := ⟨[], 0⟩
def c (k : ℤ) : Head := ⟨[], k⟩
def lin (coeff : ℤ) (col : Nat) : Head := ⟨[(coeff, [col])], 0⟩
def addLin (h : Head) (coeff : ℤ) (col : Nat) : Head := ⟨h.terms ++ [(coeff, [col])], h.const⟩
def addProd (h : Head) (coeff : ℤ) (cols : List Nat) : Head := ⟨h.terms ++ [(coeff, cols)], h.const⟩
def addConst (h : Head) (k : ℤ) : Head := ⟨h.terms, h.const + k⟩
def scale (h : Head) (k : ℤ) : Head := ⟨h.terms.map (fun t => (t.1 * k, t.2)), h.const * k⟩
def append (h o : Head) : Head := ⟨h.terms ++ o.terms, h.const + o.const⟩
end Head

instance : Inhabited Head := ⟨Head.zero⟩

/-- The product `∏ vars` (empty product `= 1`), left-associated. -/
def varsProd : List Nat → EmittedExpr
  | []        => .const 1
  | co :: rest => rest.foldl (fun acc v => .mul acc (.var v)) (.var co)

/-- One term `coeff · ∏ cols` as an `EmittedExpr` (coeff `1` elides the multiplier). -/
def termToExpr : ℤ × List Nat → EmittedExpr
  | (coeff, [])   => .const coeff
  | (coeff, cols) => if coeff == 1 then varsProd cols else .mul (.const coeff) (varsProd cols)

/-- Lower a `Head` to the gate `EmittedExpr` (a left-folded sum; zero-coeff terms dropped). -/
def headToExpr (h : Head) : EmittedExpr :=
  let ts := (h.terms.filter (fun t => t.1 != 0)).map termToExpr
  let ts := if h.const == 0 then ts else ts ++ [.const h.const]
  match ts with
  | []       => .const 0
  | e :: rest => rest.foldl (fun acc x => .add acc x) e

/-- Is a `Head` identically zero (no nonzero terms, zero constant)? Skipped rather than emitted as a
vacuous `0 == 0` gate. -/
def headIsZero (h : Head) : Bool := (h.terms.filter (fun t => t.1 != 0)).isEmpty && h.const == 0

/-- `x·(x−1)` — the boolean pin (`assert_binary`). -/
def gBin (co : Nat) : EmittedExpr := .mul (.var co) (.add (.var co) (.const (-1)))

/-- `∏_{s∈set}(col − s)` — the membership gate (`assert_member`), left-associated. -/
def memberExpr (col : Nat) (set : List ℤ) : EmittedExpr :=
  match set with
  | []        => .const 1
  | s :: rest => rest.foldl (fun acc t => .mul acc (.add (.var col) (.const (-t))))
                   (.add (.var col) (.const (-s)))

/-- A per-row gate from a raw `EmittedExpr`. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A per-row gate from a `Head`. -/
def cgH (h : Head) : VmConstraint2 := .base (.gate (headToExpr h))

/-! ## §4 — The front-end gadget families (`automaton_gadget`, lines ~294–481). -/

/-- `decompose_coord_le(col, n−1)` at `n = 2` (`rbits = 1`): the lower edge `col = b_lo` and the upper
edge `(n−1) − col = b_hi`, each a boolean bit + its recomposition gate. -/
def decomposeConstraints (col loBit hiBit : Nat) : List VmConstraint2 :=
  [ cg (gBin loBit)
  , cgH ((Head.lin 1 col).addLin (-1) loBit)                      -- col − b_lo == 0
  , cg (gBin hiBit)
  , cgH (((Head.c ((NN : ℤ) - 1)).addLin (-1) col).addLin (-1) hiBit) ]  -- (n−1) − col − b_hi == 0

/-- A one-hot's two gates: `Σ selⱼ == 1` and `Σ j·selⱼ == indexHead`. -/
def oneHotConstraints (sels : List Nat) (idxHead : Head) : List VmConstraint2 :=
  (sels.map (fun co => cg (gBin co)))
  ++ [ cgH (sels.foldl (fun h co => h.addLin 1 co) (Head.c (-1))) ]
  ++ [ cgH (((List.range sels.length).foldl (fun h (j : Nat) => h.addLin (j : ℤ) (sels[j]!)) Head.zero).append
              (idxHead.scale (-1))) ]

/-- The AUTO pin: `AUTO == Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x]`. -/
def autoPinHead : Head :=
  (List.range NN).foldl (fun h (y : Nat) =>
    (List.range NN).foldl (fun h2 (x : Nat) =>
      h2.addProd 1 [selRow y, selCol x, old (y * NN + x)]) h) (Head.c (-AUTO))

/-- The in-window auto-selector columns for ray `(dx, dy)` step `kk` — the PREFIX-SUM in-bounds
support. `step = auto + kk·d` is in bounds iff the auto's along-axis coordinate lies in the window
that keeps it on the board: `(+x): ax ≤ n−1−kk`, `(−x): ax ≥ kk`, likewise `y`. Since `sel_auto_*`
is single-hot at `(ax, ay)`, the SUM of the in-window selectors is exactly `[step in bounds]`. -/
def inWindowCols (dx dy : ℤ) (kk : Nat) : List Nat :=
  ((List.range NN).filterMap (fun (t : Nat) =>
      bif (dx == 1 && decide ((t : ℤ) ≤ (NN : ℤ) - 1 - (kk : ℤ)))
          || (dx == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
      then some (selCol t) else none))
  ++ ((List.range NN).filterMap (fun (t : Nat) =>
      bif (dy == 1 && decide ((t : ℤ) ≤ (NN : ℤ) - 1 - (kk : ℤ)))
          || (dy == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
      then some (selRow t) else none))

/-- `ib == Σ (in-window auto selectors)` — the prefix-sum in-bounds gate for ray `d` step `kk`. -/
def ibEqHead (d : Nat) (dx dy : ℤ) (kk : Nat) : Head :=
  (Head.lin 1 (rIb d kk)).append
    (((inWindowCols dx dy kk).foldl (fun h co => h.addLin 1 co) Head.zero).scale (-1))

/-- The gated shifted row×column read: `rc − Σ_{cell in bounds} ib·selRow[y]·selCol[x]·old[(y+sy)·n+(x+sx)] == 0`
with `(sx, sy) = (kk·dx, kk·dy)`. Reuses the auto one-hot shifted by the cardinal step (no fresh
selectors) — the ray-scan reduction. Out-of-bounds steps drop every term ⇒ `rc == 0` (wall vacuum). -/
def rcReadHead (d : Nat) (dx dy : ℤ) (kk : Nat) : Head :=
  let sx := (kk : ℤ) * dx
  let sy := (kk : ℤ) * dy
  (List.range NN).foldl (fun h (y : Nat) =>
    let ty := (y : ℤ) + sy
    bif decide (0 ≤ ty ∧ ty < (NN : ℤ)) then
      (List.range NN).foldl (fun h2 (x : Nat) =>
        let tx := (x : ℤ) + sx
        bif decide (0 ≤ tx ∧ tx < (NN : ℤ)) then
          h2.addProd (-1) [rIb d kk, selRow y, selCol x, old (ty.toNat * NN + tx.toNat)]
        else h2) h
    else h) (Head.lin 1 (rRc d kk))

/-- The vacuum-before / in-bounds-before occlusion gates: for each earlier step `i`, every later hit
`j > i` forces `rc[i] == 0` (vacuum before the hit) and `ib[i] == 1` (in bounds before the hit). -/
def beforeConstraints (d : Nat) : List VmConstraint2 :=
  (List.range NN).flatMap (fun (i : Nat) =>
    let js := (List.range NN).filter (fun (j : Nat) => decide (j > i))
    let vacH := js.foldl (fun h (j : Nat) => h.addProd 1 [rHit d (j + 1), rRc d (i + 1)]) Head.zero
    let inbH := js.foldl (fun h (j : Nat) =>
      (h.addLin 1 (rHit d (j + 1))).addProd (-1) [rHit d (j + 1), rIb d (i + 1)]) Head.zero
    (bif headIsZero vacH then [] else [cgH vacH])
    ++ (bif headIsZero inbH then [] else [cgH inbH]))

/-- ONE ray scan (`automaton_gadget`'s per-direction block), for ray `d` heading `(dx, dy)`. -/
def rayConstraints (d : Nat) (dx dy : ℤ) : List VmConstraint2 :=
  -- per step kk ∈ {1..n}: the in-bounds bit + its prefix-sum gate + the gated shifted read.
  ((List.range' 1 NN).flatMap (fun (kk : Nat) =>
      [ cg (gBin (rIb d kk)), cgH (ibEqHead d dx dy kk), cgH (rcReadHead d dx dy kk) ]))
  -- the hit one-hot over steps 1..n: booleans then Σ == 1.
  ++ ((List.range' 1 NN).map (fun (kk : Nat) => cg (gBin (rHit d kk))))
  ++ [ cgH ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit d kk)) (Head.c (-1))) ]
  -- dist = Σ kk·hit_kk.
  ++ [ cgH ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit d kk))
              (Head.lin (-1) (rDist d))) ]
  -- what ∈ {VAC, REP, ATT} and what = Σ hit_kk·rc_kk.
  ++ [ cg (memberExpr (rWhat d) [0, 1, 2])
     , cgH ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit d kk, rRc d kk])
              (Head.lin (-1) (rWhat d))) ]
  -- occlusion: vacuum-before + in-bounds-before.
  ++ beforeConstraints d
  -- hib = Σ hit_kk·ib_kk (in bounds at the hit).
  ++ [ cgH ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit d kk, rIb d kk])
              (Head.lin (-1) (rHib d))) ]
  -- (1 − hib)·what == 0  (an OOB hit reads wall vacuum).
  ++ [ cgH ((Head.lin 1 (rWhat d)).addProd (-1) [rHib d, rWhat d]) ]
  -- cond_nonzero: hib·(what·inv − 1) == 0  (an in-bounds hit read a genuine non-vacuum particle).
  ++ [ cg (.mul (.var (rHib d)) (.add (.mul (.var (rWhat d)) (.var (rInv d))) (.const (-1)))) ]

/-- **The board-cell RANGE CHECKS** — `assert_member(cell, {VAC,REP,ATT,AUTO})` for every OLD and
every NEW board column.

Without these the board columns are UNCONSTRAINED felts that enter only the base-4 pack gate
leaf, so a witness could carry `old[c] ≥ 4`: the reference `codeToParticle` decodes such a cell to
VACUUM (the automaton would step onto it) while the circuit's `targ_vac = [tcell = 0]` blocks — the
descriptor and the reference genuinely DISAGREE on the whole window `tcell ∈ [4, p)`. That is a
soundness hole in the emitted object, not a proof-bookkeeping artifact: it makes the Stage-2
refinement FALSE over satisfying witnesses. These `KK` + `KK` membership gates close it, and they are
what makes the OLD-board validity envelope DERIVABLE from the descriptor rather than an `hvalid`
hypothesis carried into the capstone. The NEW columns are range-checked on the same footing so the
CLAIMED next board is decodable too (the refinement's conclusion is about `boardDecode new`). -/
def boardRangeConstraints : List VmConstraint2 :=
  ((List.range KK).map (fun c => cg (memberExpr (old c) [0, 1, 2, 3])))
  ++ ((List.range KK).map (fun c => cg (memberExpr (new c) [0, 1, 2, 3])))

/-- The full front-end constraint list, in `automaton_gadget`'s emission order. -/
def frontEndConstraints : List VmConstraint2 :=
  boardRangeConstraints
  ++ decomposeConstraints AX axLoBit axHiBit
  ++ decomposeConstraints AY ayLoBit ayHiBit
  ++ oneHotConstraints [selRow 0, selRow 1] (Head.lin 1 AY)   -- the row one-hot is pinned to ay
  ++ oneHotConstraints [selCol 0, selCol 1] (Head.lin 1 AX)   -- the col one-hot is pinned to ax
  ++ [ cgH autoPinHead ]
  ++ rayConstraints 0 1 0      -- XP
  ++ rayConstraints 1 (-1) 0   -- XN
  ++ rayConstraints 2 0 1      -- YP
  ++ rayConstraints 3 0 (-1)   -- YN

/-! ## §4b — The Stage-1b back-end families (`automaton_gadget` lines ~484–701).

The decision derivation (`decide_axis` ×2, `choose_offset`), the step, the board-update equalities,
— authored in Lean on the same `builder.rs` primitives the
front-end used, continuing the Rust `alloc` order from column 58. -/

/-- Score-compare constants (`reference.rs::SCORE_PRI`/`SCORE_ATT`) and the range widths
(`air.rs::SCORE_RBITS`/`SMALL_RBITS`).

## ⚠ TWO BOARD-SIZE CEILINGS, AND THE COUPLING BETWEEN THEM

Both are DOCUMENTED AND ACCEPTED (author's call: a 34×34 automatafl board is absurd).  They are
recorded here because the second one is a SOUNDNESS ceiling, not a capacity ceiling, and because
lifting the first one WITHOUT the second converts a harmless failure into a silent one.

**CEILING 1 — `SMALL_RBITS = 5` ⇒ `decide_axis` is UNSATISFIABLE at `n ≥ 34`.**  Every small range
gadget decomposes its value into `SMALL_RBITS` bits, so it can only certify `0 ≤ v ≤ 2^5 − 1 = 31`.
The coordinate/distance bounds fed through those gadgets grow with the board (`tx ≤ n−1`,
`ty ≤ n−1`, ray distances, `min`), so from `n = 34` on there is NO satisfying assignment: the
descriptor simply cannot be proved against.  This FAILS CLOSED — no proof exists, nothing is
accepted — which is why it is tolerable.

**CEILING 2 — `SCORE_ATT = 100` is a RADIX, so the score embedding stops matching `decisionCmp` at
distance ≥ 100 (defect #9).**  The comparison is arithmetised as the single integer
`SCORE_PRI·variant − SCORE_ATT·attDist − repDist`, i.e. a base-`SCORE_ATT` positional number with
`repDist` in the ones place.  That is order-isomorphic to the lexicographic `decisionCmp`
(priority, then reversed `attDist`, then reversed `repDist`) ONLY while `repDist < SCORE_ATT = 100`.
At `repDist ≥ 100` the ones place CARRIES into the `attDist` place and the emitted comparison ranks
two decisions differently from the reference `decisionCmp` — the circuit accepts an Automaton step
the reference does not take.  This FAILS OPEN.

**⚑ THE COUPLING — widening `SMALL_RBITS` ALONE IS A SOUNDNESS HOLE.**  Ceiling 1 currently caps
the board at `n ≤ 33`, and every distance on such a board is `< 34 < 100`, so ceiling 2 is
UNREACHABLE: defect #9 is masked by the satisfiability ceiling, and only by it.  Widening
`SMALL_RBITS` to support larger boards pushes `n` past 99, at which point distances reach 100, the
radix carries, and the masked defect #9 becomes LIVE — a fail-closed capacity limit turned into a
fail-open soundness hole, with every proof still verifying.  **`SCORE_ATT` (and `SCORE_PRI`, which
must stay above `SCORE_ATT · maxAttDist`) MUST be widened in the SAME change, with the reference
`decisionCmp` agreement re-proved at the new radix.**  Do not treat `SMALL_RBITS` as a lone knob. -/
def SCORE_PRI : ℤ := 100000
def SCORE_ATT : ℤ := 100
def SMALL_RBITS : Nat := 5
def SCORE_RBITS : Nat := 20
/-- The canonical `n = 2` board's column-rule flag baked by `automaton_gadget`'s `col` pin
(`assert_zero(col − src.col_rule)`); the reference boards run `col_rule = true`. -/
def COL_RULE : ℤ := 1

/-- `[start, start+len)` — a contiguous run of range-decomposition bit columns. -/
def bitsFrom (start len : Nat) : List Nat := (List.range len).map (start + ·)

/-! ### §4b.1 — The range gadget (`builder.rs::range_nonneg`/`forced_ge0`). -/

/-- `range_nonneg(term, bits)`: each bit is boolean, and `term − Σ_k 2^k·b_k == 0`. -/
def rangeNonneg (term : Head) (bits : List Nat) : List VmConstraint2 :=
  (bits.map (fun b => cg (gBin b)))
  ++ [ cgH ((List.range bits.length).foldl
              (fun h (k : Nat) => h.addLin (-((2 : ℤ) ^ k)) (bits[k]!)) term) ]

/-- `forced_ge0`'s recomposed head `term = 2·ib·d + ib − d − 1` (the non-negativity witness a
range gadget then pins). -/
def forcedGe0Term (ib : Nat) (d : Head) : Head :=
  let h1 := d.terms.foldl (fun h (t : ℤ × List Nat) => h.addProd (2 * t.1) (ib :: t.2)) Head.zero
  let h2 := h1.addProd (2 * d.const) [ib]
  let h3 := h2.addLin 1 ib
  ((h3.append (d.scale (-1))).addConst (-1))

/-- `forced_ge0(ib, d, bits)`: `ib` boolean + the range gadget over `2·ib·d + ib − d − 1`. The bit
`ib` is pinned to `[d ≥ 0]` (a forged bit has no satisfying decomposition). -/
def forcedGe0Constraints (ib : Nat) (d : Head) (bits : List Nat) : List VmConstraint2 :=
  cg (gBin ib) :: rangeNonneg (forcedGe0Term ib d) bits

/-! ### §4b.2 — Gated one-hots + row×column reads (`builder.rs::one_hot_gated`/`read_rowcol_gated`). -/

/-- `one_hot_gated`'s index gate: `Σ j·sel_j − gate·index_head == 0`. -/
def idxGatedHead (sels : List Nat) (gate : Nat) (idxHead : Head) : Head :=
  let base := (List.range sels.length).foldl (fun h (j : Nat) => h.addLin (j : ℤ) (sels[j]!)) Head.zero
  ((idxHead.terms.foldl (fun h (t : ℤ × List Nat) => h.addProd (-t.1) (gate :: t.2)) base).addProd
    (-idxHead.const) [gate])

/-- `one_hot_gated(sels, gate, index_head)`: booleans, `Σ sel == gate`, and the gated index pin. -/
def oneHotGatedConstraints (sels : List Nat) (gate : Nat) (idxHead : Head) : List VmConstraint2 :=
  (sels.map (fun c => cg (gBin c)))
  ++ [ cgH (sels.foldl (fun h c => h.addLin 1 c) (Head.lin (-1) gate)) ]
  ++ [ cgH (idxGatedHead sels gate idxHead) ]

/-- The row×column gated read body: `value − Σ_y Σ_x selRow[y]·selCol[x]·board[y·n+x]`. -/
def readRowcolHead (selRow selCol board : List Nat) (n value : Nat) : Head :=
  (List.range n).foldl (fun h (y : Nat) =>
    (List.range n).foldl (fun h2 (x : Nat) =>
      h2.addProd (-1) [selRow[y]!, selCol[x]!, board[y * n + x]!]) h)
    (Head.lin 1 value)

/-- `read_rowcol_gated`: the row one-hot (pinned to `yHead`), the column one-hot (pinned to
`xHead`), then the gated dot-product read into `value`. -/
def readRowcolGatedConstraints (selRow selCol : List Nat) (gate : Nat)
    (xHead yHead : Head) (board : List Nat) (n value : Nat) : List VmConstraint2 :=
  oneHotGatedConstraints selRow gate yHead
  ++ oneHotGatedConstraints selCol gate xHead
  ++ [ cgH (readRowcolHead selRow selCol board n value) ]

/-! ### §4b.3 — `decide_axis`: the 9-case `evaluate_axis` truth table (`air.rs` ~61–277). -/

/-- `assert_case(gate, field, formula)`: `gate·(field − formula) == 0`, expanded so `gate` (the
`ipw[i]·inw[j]` case selector) multiplies every term. -/
def assertCase (gate : List Nat) (fieldCol : Nat) (formula : Head) : VmConstraint2 :=
  let h0 := Head.zero.addProd 1 (gate ++ [fieldCol])
  let h1 := formula.terms.foldl (fun h (t : ℤ × List Nat) => h.addProd (-t.1) (gate ++ t.2)) h0
  cgH (if formula.const == 0 then h1 else h1.addProd (-formula.const) gate)

/-- The nine `(pw, nw)` cases of `evaluate_axis`, each a `(variant, pos, att, rep)` formula tuple
gated by `ipw[i]·inw[j]` (`air.rs`'s `cases` table). `pd`/`nd`/`min` are the distance columns; the
`gpd/gnd/lt/gt/le/gmin` bits are the range-gadget comparison witnesses. -/
def decideCasesConstraints (ipw inw fields : List Nat)
    (pd nd minC gpd gnd lt gt _le gm : Nat) : List VmConstraint2 :=
  let Z := Head.zero
  let cases : List ((Nat × Nat) × List Head) :=
    [ ((2, 1), [Head.lin 3 gpd, Head.lin 1 gpd, Z.addProd 1 [gpd, pd], Z.addProd 1 [gpd, nd]])
    , ((1, 2), [Head.lin 3 gnd, Z, Z.addProd 1 [gnd, nd], Z.addProd 1 [gnd, pd]])
    , ((1, 1), [(Head.lin 2 lt).addLin 2 gt, Head.lin 1 gt, Z,
                (Z.addProd 1 [lt, minC]).addProd 1 [gt, minC]])
    , ((1, 0), [Head.lin 2 gnd, Z, Z, Z.addProd 1 [gnd, pd]])
    , ((0, 1), [Head.lin 2 gpd, Head.lin 1 gpd, Z, Z.addProd 1 [gpd, nd]])
    , ((2, 2), [(Z.addProd 1 [lt, gm]).addProd 1 [gt, gm], Z.addProd 1 [lt, gm],
                (Z.addProd 1 [lt, gm, minC]).addProd 1 [gt, gm, minC], Z])
    , ((2, 0), [Head.lin 1 gpd, Head.lin 1 gpd, Z.addProd 1 [gpd, pd], Z])
    , ((0, 2), [Head.lin 1 gnd, Z, Z.addProd 1 [gnd, nd], Z])
    , ((0, 0), [Z, Z, Z, Z]) ]
  cases.flatMap (fun (c : (Nat × Nat) × List Head) =>
    let gate := [ipw[c.1.1]!, inw[c.1.2]!]
    (List.range 4).map (fun (k : Nat) => assertCase gate (fields[k]!) ((c.2)[k]!)))

/-- **`decide_axis`** (`air.rs::decide_axis`) at column base `b`, over the two rays' `what`
(`pwCol`/`nwCol`) and `dist` (`pdCol`/`ndCol`) columns. Emits the witnessed `variant/pos/att/rep`
(`b..b+3`), the two `ipw`/`inw` one-hots, the six range-gadget guard/compare bits, the `min` gadget,
and the 9-case truth table. Returns nothing — the decision columns are read by `choose_offset`. -/
def decideAxisConstraints (b : Nat) (pwCol nwCol pdCol ndCol : Nat) : List VmConstraint2 :=
  let ipw := [b + 4, b + 5, b + 6]
  let inw := [b + 7, b + 8, b + 9]
  let gpdIb := b + 10; let gndIb := b + 16; let ltIb := b + 22
  let gtIb := b + 28; let leIb := b + 34; let minC := b + 40; let gmIb := b + 41
  [ cg (memberExpr b [0, 1, 2, 3]) ]                 -- variant ∈ {0,1,2,3}
  ++ [ cg (gBin (b + 1)) ]                            -- pos boolean
  ++ oneHotConstraints ipw (Head.lin 1 pwCol)
  ++ oneHotConstraints inw (Head.lin 1 nwCol)
  ++ forcedGe0Constraints gpdIb ((Head.lin 1 pdCol).addConst (-2)) (bitsFrom (b + 11) SMALL_RBITS)
  ++ forcedGe0Constraints gndIb ((Head.lin 1 ndCol).addConst (-2)) (bitsFrom (b + 17) SMALL_RBITS)
  ++ forcedGe0Constraints ltIb (((Head.lin 1 ndCol).addLin (-1) pdCol).addConst (-1))
       (bitsFrom (b + 23) SMALL_RBITS)
  ++ forcedGe0Constraints gtIb (((Head.lin 1 pdCol).addLin (-1) ndCol).addConst (-1))
       (bitsFrom (b + 29) SMALL_RBITS)
  ++ forcedGe0Constraints leIb ((Head.lin 1 ndCol).addLin (-1) pdCol) (bitsFrom (b + 35) SMALL_RBITS)
  -- min − (le·pd + (1−le)·nd) == 0  =>  min − le·pd − nd + le·nd == 0.
  ++ [ cgH ((((Head.lin 1 minC).addProd (-1) [leIb, pdCol]).addLin (-1) ndCol).addProd 1 [leIb, ndCol]) ]
  ++ forcedGe0Constraints gmIb ((Head.lin 1 minC).addConst (-2)) (bitsFrom (b + 42) SMALL_RBITS)
  ++ decideCasesConstraints ipw inw [b, b + 1, b + 2, b + 3] pdCol ndCol minC gpdIb gndIb ltIb gtIb leIb gmIb

/-! ### §4b.4 — `choose_offset`: the score comparison (`air.rs` ~511–583). -/

/-- The score head `variant·PRI − att·ATT − rep` (`air.rs::score_head`). -/
def scoreHead (variantCol attCol repCol : Nat) : Head :=
  ((Head.lin SCORE_PRI variantCol).addLin (-SCORE_ATT) attCol).addLin (-1) repCol

/-- The `xdec`/`ydec` decision column bases (each `decide_axis`'s `variant/pos/att/rep` block). -/
def X_VAR : Nat := 58
def X_POS : Nat := 59
def X_ATT : Nat := 60
def X_REP : Nat := 61
def Y_VAR : Nat := 105
def Y_POS : Nat := 106
def Y_ATT : Nat := 107
def Y_REP : Nat := 108

/-- The `choose_offset` column block: `sgt`/`slt` (20-bit score compare), `xmove`/`ymove`
(5-bit), `col`, `ox`, `oy`. -/
def SGT_IB : Nat := 152
def SLT_IB : Nat := 173
def XMOVE_IB : Nat := 194
def YMOVE_IB : Nat := 200
def COL_C : Nat := 206
def OX_C : Nat := 207
def OY_C : Nat := 208

/-- `f·<extra>` pushed into the `oy` head, `f = 2·ymove·posy − ymove` (`air.rs`'s `push_f`). -/
def pushF (h : Head) (sign : ℤ) (extra : List Nat) : Head :=
  (h.addProd (-sign * 2) ([YMOVE_IB, Y_POS] ++ extra)).addProd sign ([YMOVE_IB] ++ extra)

/-- The `oy` equality `oy − (2·posy−1)·ymove·ywins == 0`, expanded as in `air.rs` (566–582). -/
def oyHead : Head :=
  pushF (pushF (pushF (pushF (Head.lin 1 OY_C) 1 [SLT_IB]) 1 [COL_C]) (-1) [SGT_IB, COL_C])
    (-1) [SLT_IB, COL_C]

/-- **`choose_offset`** — the score-compare bits, the column rule, and the two offset equalities. -/
def chooseOffsetConstraints : List VmConstraint2 :=
  let sx := scoreHead X_VAR X_ATT X_REP
  let sy := scoreHead Y_VAR Y_ATT Y_REP
  forcedGe0Constraints SGT_IB ((sx.append (sy.scale (-1))).addConst (-1)) (bitsFrom 153 SCORE_RBITS)
  ++ forcedGe0Constraints SLT_IB ((sy.append (sx.scale (-1))).addConst (-1)) (bitsFrom 174 SCORE_RBITS)
  ++ forcedGe0Constraints XMOVE_IB ((Head.lin 1 X_VAR).addConst (-1)) (bitsFrom 195 SMALL_RBITS)
  ++ forcedGe0Constraints YMOVE_IB ((Head.lin 1 Y_VAR).addConst (-1)) (bitsFrom 201 SMALL_RBITS)
  ++ [ cg (gBin COL_C) ]                                     -- col boolean
  ++ [ cgH ((Head.lin 1 COL_C).addConst (-COL_RULE)) ]       -- col == col_rule
  ++ [ cg (memberExpr OX_C [-1, 0, 1]) ]                     -- ox ∈ {-1,0,1}
  ++ [ cg (memberExpr OY_C [-1, 0, 1]) ]                     -- oy ∈ {-1,0,1}
  -- ox − 2·sgt·xmove·posx + sgt·xmove == 0.
  ++ [ cgH (((Head.lin 1 OX_C).addProd (-2) [SGT_IB, XMOVE_IB, X_POS]).addProd 1 [SGT_IB, XMOVE_IB]) ]
  ++ [ cgH oyHead ]

/-! ### §4b.5 — The step + board-update equalities (`air.rs` ~585–701). -/

/-- The `k = n²` board cell columns (`old[c] = c`). -/
def oldCols : List Nat := (List.range KK).map old

/-- **The step**: target in-bounds bits, the gated target read, `targ_vac`/`offnz`/`moved`, the
gated `sel_target` row×column one-hot, and the per-cell board-update equalities. -/
def stepConstraints : List VmConstraint2 :=
  let txH := (Head.lin 1 AX).addLin 1 OX_C     -- ax + ox
  let tyH := (Head.lin 1 AY).addLin 1 OY_C     -- ay + oy
  let selTargRow := [248, 249]; let selTargCol := [250, 251]
  forcedGe0Constraints 209 txH (bitsFrom 210 SMALL_RBITS)                             -- [tx ≥ 0]
  ++ forcedGe0Constraints 215 (((Head.c ((NN : ℤ) - 1)).addLin (-1) AX).addLin (-1) OX_C)
       (bitsFrom 216 SMALL_RBITS)                                                     -- [tx ≤ n−1]
  ++ forcedGe0Constraints 221 tyH (bitsFrom 222 SMALL_RBITS)                          -- [ty ≥ 0]
  ++ forcedGe0Constraints 227 (((Head.c ((NN : ℤ) - 1)).addLin (-1) AY).addLin (-1) OY_C)
       (bitsFrom 228 SMALL_RBITS)                                                     -- [ty ≤ n−1]
  ++ [ cgH ((Head.lin 1 233).addProd (-1) [209, 215, 221, 227]) ]                     -- tib = ∏ edges
  ++ readRowcolGatedConstraints [235, 236] [237, 238] 233 txH tyH oldCols NN 234      -- target read
  ++ forcedGe0Constraints 239 ((Head.lin 1 234).addConst (-1)) (bitsFrom 240 SMALL_RBITS) -- [tcell ≥ 1]
  ++ [ cgH (((Head.lin 1 245).addLin 1 239).addConst (-1)) ]                          -- targ_vac = 1 − nz
  ++ [ cgH (((Head.lin 1 246).addProd (-1) [OX_C, OX_C]).addProd (-1) [OY_C, OY_C]) ] -- offnz = ox²+oy²
  ++ [ cgH ((Head.lin 1 247).addProd (-1) [246, 233, 245]) ]                          -- m = offnz·tib·targ_vac
  ++ oneHotGatedConstraints selTargRow 247 tyH                                        -- sel_target row
  ++ oneHotGatedConstraints selTargCol 247 txH                                        -- sel_target col
  -- board update: new[c] − old[c] − AUTO·m·selT[c] + m·selT[c]·old[c] + m·selAuto[c]·old[c] == 0.
  ++ (List.range KK).map (fun (c : Nat) =>
       let x := c % NN; let y := c / NN
       cgH (((((Head.lin 1 (new c)).addLin (-1) (old c)).addProd (-AUTO)
                 [247, selTargRow[y]!, selTargCol[x]!]).addProd 1
                 [247, selTargRow[y]!, selTargCol[x]!, old c]).addProd 1
                 [247, selRow y, selCol x, old c]))

/-! ### §4b.6 — `board_root8` RETIRED. The commitment leg is now the PACKED base-4 board commitment
(`§4d`), emitted `n`-parametrically AFTER this frozen back-end. The `MerkleHash8` node8 pair it
replaced folded ONE zero-padded 8-lane leaf, so it was well-defined only for `k = n² ≤ 8` (`n ≤ 2`)
and it charged a Poseidon2 collision/permutation-soundness assumption for a commitment that the pack
delivers with a degree-1 gate and NO crypto at all. -/

/-- The full Stage-1b constraint list appended to the front-end, in `automaton_gadget`'s emission
order: front-end · `decide_axis(xdec)` · `decide_axis(ydec)` · `choose_offset` · the step + board
update. The COMMITMENT is no longer part of this frozen block — see `§4d`. -/
def backEndConstraints : List VmConstraint2 :=
  decideAxisConstraints 58 (rWhat 0) (rWhat 1) (rDist 0) (rDist 1)   -- xdec: rays XP, XN
  ++ decideAxisConstraints 105 (rWhat 2) (rWhat 3) (rDist 2) (rDist 3) -- ydec: rays YP, YN
  ++ chooseOffsetConstraints
  ++ stepConstraints

/-! ## §4c — `descN n`: the board size as an explicit PARAMETER (AUTOMATAFL-NGENERIC-DESIGN §4).

`NGen` threads the board dimension `n` through the Stage-1a FRONT-END — the `n²` board cells, the
coordinate one-hots (`(List.range n).map …`) and the four ray scans (`List.range' 1 n`). The pure
`Head`/gate combinators (`cgH`, `oneHotConstraints`, `memberExpr`, …) are reused as-is.

`automataflStepDescN 2` is DEFINITIONALLY EQUAL to the byte-golden `automataflStepDesc` below (same
numerals, same list), so every existing byte-golden `#guard` and `by decide` gate-membership proof
over `automataflStepDesc.constraints` is preserved.

The Stage-1b BACK-END is now `n`-PARAMETRIC too (§4c.1): `decide_axis` ×2, `choose_offset` and the
step no longer sit at absolute `n = 2` offsets — every block base is a function of `n` derived from
`A_FRONT_WIDTH n` (`A_DECIDE_X_BASE`/`A_DECIDE_Y_BASE`/`A_CHOOSE_BASE`/`A_STEP_BASE`/`A_BACK_TAIL`),
mirroring how `AutomataflResolveEmit`'s `NGen` derives `RES0`/`SEL0`/`MH0`. The front-end ray-block
spacing is `RAY_W n = 3n+4` (not the old frozen `10`). Every base reduces to the frozen numeral at
`n = 2` (`58`/`105`/`152`/`209`/`252`), so `automataflStepDescN 2` stays byte-identical to the golden;
at `n = 11` the blocks tile without overlap (§6.2 `maxColList` pins). The frozen-`n=2` top-level
`chooseOffsetConstraints`/`stepConstraints`/`backEndConstraints` are RETAINED below only as an
independent `n = 2` oracle the parametric versions are cross-checked against (`.length ==`, and the
full byte-for-byte identity is the descN 2 wire golden). -/
namespace NGen

set_option linter.unusedVariables false

def KK (n : Nat) : Nat := n * n
/-- `decompose_coord_le`'s bit width — `ceil(log2 n)`, the number of bits needed to hold a coordinate
in `[0, n)`. `1` at `n = 2`, `4` at `n = 11`. MIRRORS `AutomataflResolveEmit.NGen.COORD_RBITS`
verbatim. This is what makes the auto-coordinate decode SATISFIABLE at `n ≥ 4`: the old frozen 2-bit
gadget pinned `col ∈ {0,1} ∩ {n−2, n−1} = ∅`; the `COORD_RBITS n`-bit range decodes `col ∈ [0, n)`. -/
def COORD_RBITS (n : Nat) : Nat := if n ≤ 1 then 1 else Nat.log2 (n - 1) + 1
def old (n : Nat) (i : Nat) : Nat := i
def new (n : Nat) (i : Nat) : Nat := (KK n) + i
def AX (n : Nat) : Nat := 2 * (KK n)
def AY (n : Nat) : Nat := 2 * (KK n) + 1
/-- `decompose_coord_le` bit runs for `ax` / `ay`, each `COORD_RBITS n` wide, laid out
`ax.lo ax.hi ay.lo ay.hi`. At `n = 2` (`COORD_RBITS 2 = 1`) these are the single columns
`2k+2 … 2k+5` — byte-identical to the old frozen 2-bit layout; at `n ≥ 3` each edge widens. -/
def axLoBit (n : Nat) : Nat := 2 * (KK n) + 2
def axHiBit (n : Nat) : Nat := 2 * (KK n) + 2 + (COORD_RBITS n)
def ayLoBit (n : Nat) : Nat := 2 * (KK n) + 2 + 2 * (COORD_RBITS n)
def ayHiBit (n : Nat) : Nat := 2 * (KK n) + 2 + 3 * (COORD_RBITS n)
def selRow (n : Nat) (y : Nat) : Nat := 2 * (KK n) + 2 + 4 * (COORD_RBITS n) + y
def selCol (n : Nat) (x : Nat) : Nat := 2 * (KK n) + 2 + 4 * (COORD_RBITS n) + n + x
/-- Per-ray column block width, `n`-parametric: `2n` interleaved `ib`/`rc` reads (steps `1..n`),
`n` `hit` one-hot bits, then `dist`/`what`/`hib`/`inv` (4). At `n = 2` this is `10` — byte-identical
to the old frozen 10-column-per-ray spacing; at `n ≥ 3` the `hit` block and the `dist`/`what` tail
NO LONGER OVERLAP the widened `ib`/`rc` reads (the old `+4`/`+6`/… offsets were frozen at `n = 2`). -/
def RAY_W (n : Nat) : Nat := 3 * n + 4
def rayBase (n : Nat) (d : Nat) : Nat := 2 * (KK n) + 2 + 4 * (COORD_RBITS n) + 2 * n + (RAY_W n) * d
def rIb (n : Nat) (d kk : Nat) : Nat := (rayBase n) d + 2 * (kk - 1)
def rRc (n : Nat) (d kk : Nat) : Nat := (rayBase n) d + 2 * (kk - 1) + 1
def rHit (n : Nat) (d kk : Nat) : Nat := (rayBase n) d + 2 * n + (kk - 1)
def rDist (n : Nat) (d : Nat) : Nat := (rayBase n) d + 3 * n
def rWhat (n : Nat) (d : Nat) : Nat := (rayBase n) d + 3 * n + 1
def rHib (n : Nat) (d : Nat) : Nat := (rayBase n) d + 3 * n + 2
def rInv (n : Nat) (d : Nat) : Nat := (rayBase n) d + 3 * n + 3
def A_FRONT_WIDTH (n : Nat) : Nat := 2 * (KK n) + 2 + 4 * (COORD_RBITS n) + 2 * n + (RAY_W n) * 4
/-- `Builder::range_nonneg(head, rbits)` with bits at `bit0 ..< bit0+rbits`: each bit boolean, then
the recomposition `head − Σ 2^k·b_k == 0`. MIRRORS `AutomataflResolveEmit.rangeNonnegConstraints`
verbatim (the RESOLVE emitter's `decompose_coord_le` combinator). -/
def rangeNonnegConstraints (h : Head) (bit0 rbits : Nat) : List VmConstraint2 :=
  (List.range rbits).map (fun k => cg (gBin (bit0 + k)))
  ++ [ cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k)) h) ]
/-- `decompose_coord_le(col, n−1)` — the `COORD_RBITS n`-bit range decomposition of BOTH edges: the
lower edge `col = Σ 2^k b_k` and the upper edge `(n−1) − col = Σ 2^k b'_k`. MIRRORS
`AutomataflResolveEmit.NGen.decomposeConstraints` exactly — same combinator, same bit-width. At
`n = 2` (`COORD_RBITS 2 = 1`) this reduces to the old frozen two-bit form; at `n ≥ 3` it decodes the
coordinate into `[0, n)` with no wrap (`AutomataflCoord.coordN_of_sat`), fixing the `n ≥ 4`
unsatisfiability of the old single-bit-per-edge gadget. -/
def decomposeConstraints (n : Nat) (col loBit0 hiBit0 : Nat) : List VmConstraint2 :=
  rangeNonnegConstraints (Head.lin 1 col) loBit0 (COORD_RBITS n)
  ++ rangeNonnegConstraints ((Head.c ((n : ℤ) - 1)).addLin (-1) col) hiBit0 (COORD_RBITS n)
def autoPinHead (n : Nat) : Head :=
  (List.range n).foldl (fun h (y : Nat) =>
    (List.range n).foldl (fun h2 (x : Nat) =>
      h2.addProd 1 [(selRow n) y, (selCol n) x, (old n) (y * n + x)]) h) (Head.c (-AUTO))
def inWindowCols (n : Nat) (dx dy : ℤ) (kk : Nat) : List Nat :=
  ((List.range n).filterMap (fun (t : Nat) =>
      bif (dx == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
          || (dx == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
      then some ((selCol n) t) else none))
  ++ ((List.range n).filterMap (fun (t : Nat) =>
      bif (dy == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
          || (dy == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
      then some ((selRow n) t) else none))
def ibEqHead (n : Nat) (d : Nat) (dx dy : ℤ) (kk : Nat) : Head :=
  (Head.lin 1 ((rIb n) d kk)).append
    ((((inWindowCols n) dx dy kk).foldl (fun h co => h.addLin 1 co) Head.zero).scale (-1))
def rcReadHead (n : Nat) (d : Nat) (dx dy : ℤ) (kk : Nat) : Head :=
  let sx := (kk : ℤ) * dx
  let sy := (kk : ℤ) * dy
  (List.range n).foldl (fun h (y : Nat) =>
    let ty := (y : ℤ) + sy
    bif decide (0 ≤ ty ∧ ty < (n : ℤ)) then
      (List.range n).foldl (fun h2 (x : Nat) =>
        let tx := (x : ℤ) + sx
        bif decide (0 ≤ tx ∧ tx < (n : ℤ)) then
          h2.addProd (-1) [(rIb n) d kk, (selRow n) y, (selCol n) x, (old n) (ty.toNat * n + tx.toNat)]
        else h2) h
    else h) (Head.lin 1 ((rRc n) d kk))
def beforeConstraints (n : Nat) (d : Nat) : List VmConstraint2 :=
  (List.range n).flatMap (fun (i : Nat) =>
    let js := (List.range n).filter (fun (j : Nat) => decide (j > i))
    let vacH := js.foldl (fun h (j : Nat) => h.addProd 1 [(rHit n) d (j + 1), (rRc n) d (i + 1)]) Head.zero
    let inbH := js.foldl (fun h (j : Nat) =>
      (h.addLin 1 ((rHit n) d (j + 1))).addProd (-1) [(rHit n) d (j + 1), (rIb n) d (i + 1)]) Head.zero
    (bif headIsZero vacH then [] else [cgH vacH])
    ++ (bif headIsZero inbH then [] else [cgH inbH]))
def rayConstraints (n : Nat) (d : Nat) (dx dy : ℤ) : List VmConstraint2 :=
  -- per step kk ∈ {1..n}: the in-bounds bit + its prefix-sum gate + the gated shifted read.
  ((List.range' 1 n).flatMap (fun (kk : Nat) =>
      [ cg (gBin ((rIb n) d kk)), cgH ((ibEqHead n) d dx dy kk), cgH ((rcReadHead n) d dx dy kk) ]))
  -- the hit one-hot over steps 1..n: booleans then Σ == 1.
  ++ ((List.range' 1 n).map (fun (kk : Nat) => cg (gBin ((rHit n) d kk))))
  ++ [ cgH ((List.range' 1 n).foldl (fun h (kk : Nat) => h.addLin 1 ((rHit n) d kk)) (Head.c (-1))) ]
  -- dist = Σ kk·hit_kk.
  ++ [ cgH ((List.range' 1 n).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) ((rHit n) d kk))
              (Head.lin (-1) ((rDist n) d))) ]
  -- what ∈ {VAC, REP, ATT} and what = Σ hit_kk·rc_kk.
  ++ [ cg (memberExpr ((rWhat n) d) [0, 1, 2])
     , cgH ((List.range' 1 n).foldl (fun h (kk : Nat) => h.addProd 1 [(rHit n) d kk, (rRc n) d kk])
              (Head.lin (-1) ((rWhat n) d))) ]
  -- occlusion: vacuum-before + in-bounds-before.
  ++ (beforeConstraints n) d
  -- hib = Σ hit_kk·ib_kk (in bounds at the hit).
  ++ [ cgH ((List.range' 1 n).foldl (fun h (kk : Nat) => h.addProd 1 [(rHit n) d kk, (rIb n) d kk])
              (Head.lin (-1) ((rHib n) d))) ]
  -- (1 − hib)·what == 0  (an OOB hit reads wall vacuum).
  ++ [ cgH ((Head.lin 1 ((rWhat n) d)).addProd (-1) [(rHib n) d, (rWhat n) d]) ]
  -- cond_nonzero: hib·(what·inv − 1) == 0  (an in-bounds hit read a genuine non-vacuum particle).
  ++ [ cg (.mul (.var ((rHib n) d)) (.add (.mul (.var ((rWhat n) d)) (.var ((rInv n) d))) (.const (-1)))) ]
def boardRangeConstraints (n : Nat) : List VmConstraint2 :=
  ((List.range (KK n)).map (fun c => cg (memberExpr ((old n) c) [0, 1, 2, 3])))
  ++ ((List.range (KK n)).map (fun c => cg (memberExpr ((new n) c) [0, 1, 2, 3])))
def frontEndConstraints (n : Nat) : List VmConstraint2 :=
  (boardRangeConstraints n)
  ++ (decomposeConstraints n) (AX n) (axLoBit n) (axHiBit n)
  ++ (decomposeConstraints n) (AY n) (ayLoBit n) (ayHiBit n)
  ++ oneHotConstraints ((List.range n).map (selRow n)) (Head.lin 1 (AY n))   -- the row one-hot @ ay (n-wide)
  ++ oneHotConstraints ((List.range n).map (selCol n)) (Head.lin 1 (AX n))   -- the col one-hot @ ax (n-wide)
  ++ [ cgH (autoPinHead n) ]
  ++ (rayConstraints n) 0 1 0      -- XP
  ++ (rayConstraints n) 1 (-1) 0   -- XN
  ++ (rayConstraints n) 2 0 1      -- YP
  ++ (rayConstraints n) 3 0 (-1)   -- YN

/-! ### §4c.1 — The `n`-PARAMETRIC Stage-1b BACK-END layout.

The back-end blocks (`decide_axis` ×2, `choose_offset`, the step) were authored at FROZEN `n = 2`
ABSOLUTE offsets (`58`, `105`, `152`, `209`, tail `252`) — so at `n ≥ 3` they OVERLAPPED the widened
front-end (whose width `A_FRONT_WIDTH n` grows with `n`: `n²` board cells, the `n`-wide auto one-hots,
the `RAY_W n`-wide ray blocks). Here every back-end base is a FUNCTION of `n`, derived from
`A_FRONT_WIDTH n`, exactly as `AutomataflResolveEmit`'s `NGen` derives `RES0`/`SEL0`/`MH0`.

The `decide_axis` and `choose_offset` block WIDTHS are CONSTANT in `n` (their sub-gadgets are the
`what`-alphabet one-hots — always size 3 — and fixed-width range gadgets `SMALL_RBITS`/`SCORE_RBITS`);
only the STEP grows (`A_ST_W n = 35 + 4n`, from its two `n`-wide row×column one-hots on the read and
the update). Every offset below reduces to the frozen numeral at `n = 2` (`A_DECIDE_X_BASE 2 = 58`,
`A_CHOOSE_BASE 2 = 152`, `A_STEP_BASE 2 = 209`, `A_BACK_TAIL 2 = 252`), so `automataflStepDescN 2`
stays byte-identical to the golden. -/

/-- `decide_axis` block width (constant in `n`): 4 fields + 6 (`ipw`/`inw` size-3 one-hots) +
6 range gadgets × (1 + `SMALL_RBITS`) + 1 (`min`). -/
def A_DA_W : Nat := 47
/-- `choose_offset` block width (constant in `n`): 2×(1+`SCORE_RBITS`) + 2×(1+`SMALL_RBITS`) + 3. -/
def A_CO_W : Nat := 57
/-- The step block width, `n`-growing: 4 edge range gadgets (24) + `tib` + `tcell` + the `n`-wide
target-read row×column one-hots (2n) + the `tcell ≥ 1` gadget (6) + `targ_vac`/`offnz`/`m` (3) +
the `n`-wide `sel_target` update row×column one-hots (2n). -/
def A_ST_W (n : Nat) : Nat := 35 + 4 * n
def A_DECIDE_X_BASE (n : Nat) : Nat := A_FRONT_WIDTH n
def A_DECIDE_Y_BASE (n : Nat) : Nat := A_FRONT_WIDTH n + A_DA_W
def A_CHOOSE_BASE (n : Nat) : Nat := A_FRONT_WIDTH n + 2 * A_DA_W
def A_STEP_BASE (n : Nat) : Nat := A_FRONT_WIDTH n + 2 * A_DA_W + A_CO_W
/-- First column past the (now `n`-parametric) Stage-1b back-end — where the packed commitment felts
begin. `A_BACK_TAIL 2 = 252`. -/
def A_BACK_TAIL (n : Nat) : Nat := A_STEP_BASE n + A_ST_W n

/-- **`choose_offset`** at `n`-parametric offsets (`air.rs` ~511–583) — the `xdec`/`ydec` decision
columns are read from `A_DECIDE_{X,Y}_BASE n`, the block's own `sgt`/`slt`/`xmove`/`ymove`/`col`/`ox`/
`oy` columns from `A_CHOOSE_BASE n`. Byte-identical to the frozen `chooseOffsetConstraints` at `n=2`. -/
def chooseOffsetConstraints (n : Nat) : List VmConstraint2 :=
  let xVar := A_DECIDE_X_BASE n; let xPos := xVar + 1; let xAtt := xVar + 2; let xRep := xVar + 3
  let yVar := A_DECIDE_Y_BASE n; let yAtt := yVar + 2; let yRep := yVar + 3
  let sgt := A_CHOOSE_BASE n; let slt := sgt + 21; let xmove := sgt + 42; let ymove := sgt + 48
  let colC := sgt + 54; let oxC := sgt + 55; let oyC := sgt + 56
  let sx := scoreHead xVar xAtt xRep
  let sy := scoreHead yVar yAtt yRep
  let pushF := fun (h : Head) (sign : ℤ) (extra : List Nat) =>
    (h.addProd (-sign * 2) ([ymove, yVar + 1] ++ extra)).addProd sign ([ymove] ++ extra)
  let oyH := pushF (pushF (pushF (pushF (Head.lin 1 oyC) 1 [slt]) 1 [colC]) (-1) [sgt, colC]) (-1) [slt, colC]
  forcedGe0Constraints sgt ((sx.append (sy.scale (-1))).addConst (-1)) (bitsFrom (sgt + 1) SCORE_RBITS)
  ++ forcedGe0Constraints slt ((sy.append (sx.scale (-1))).addConst (-1)) (bitsFrom (slt + 1) SCORE_RBITS)
  ++ forcedGe0Constraints xmove ((Head.lin 1 xVar).addConst (-1)) (bitsFrom (xmove + 1) SMALL_RBITS)
  ++ forcedGe0Constraints ymove ((Head.lin 1 yVar).addConst (-1)) (bitsFrom (ymove + 1) SMALL_RBITS)
  ++ [ cg (gBin colC) ]
  ++ [ cgH ((Head.lin 1 colC).addConst (-COL_RULE)) ]
  ++ [ cg (memberExpr oxC [-1, 0, 1]) ]
  ++ [ cg (memberExpr oyC [-1, 0, 1]) ]
  ++ [ cgH (((Head.lin 1 oxC).addProd (-2) [sgt, xmove, xPos]).addProd 1 [sgt, xmove]) ]
  ++ [ cgH oyH ]

/-- **The step + board-update equalities** at `n`-parametric offsets (`air.rs` ~585–701). The step
block begins at `A_STEP_BASE n`; the two row×column one-hots (target read, `sel_target` update) and
the board-update fold are all `n`-wide. Byte-identical to the frozen `stepConstraints` at `n = 2`. -/
def stepConstraints (n : Nat) : List VmConstraint2 :=
  let s := A_STEP_BASE n
  let oxC := A_CHOOSE_BASE n + 55; let oyC := A_CHOOSE_BASE n + 56
  let axc := AX n; let ayc := AY n
  let txH := (Head.lin 1 axc).addLin 1 oxC     -- ax + ox
  let tyH := (Head.lin 1 ayc).addLin 1 oyC     -- ay + oy
  let tib := s + 24
  let tcell := s + 25
  let selTargRowRead := (List.range n).map (fun j => s + 26 + j)
  let selTargColRead := (List.range n).map (fun j => s + 26 + n + j)
  let nzIb := s + 26 + 2 * n
  let targVac := s + 32 + 2 * n
  let offnz := s + 33 + 2 * n
  let m := s + 34 + 2 * n
  let selTargRowUpd := (List.range n).map (fun j => s + 35 + 2 * n + j)
  let selTargColUpd := (List.range n).map (fun j => s + 35 + 3 * n + j)
  let oldColsN := (List.range (KK n)).map (old n)
  forcedGe0Constraints s txH (bitsFrom (s + 1) SMALL_RBITS)                              -- [tx ≥ 0]
  ++ forcedGe0Constraints (s + 6) (((Head.c ((n : ℤ) - 1)).addLin (-1) axc).addLin (-1) oxC)
       (bitsFrom (s + 7) SMALL_RBITS)                                                    -- [tx ≤ n−1]
  ++ forcedGe0Constraints (s + 12) tyH (bitsFrom (s + 13) SMALL_RBITS)                   -- [ty ≥ 0]
  ++ forcedGe0Constraints (s + 18) (((Head.c ((n : ℤ) - 1)).addLin (-1) ayc).addLin (-1) oyC)
       (bitsFrom (s + 19) SMALL_RBITS)                                                   -- [ty ≤ n−1]
  ++ [ cgH ((Head.lin 1 tib).addProd (-1) [s, s + 6, s + 12, s + 18]) ]                  -- tib = ∏ edges
  ++ readRowcolGatedConstraints selTargRowRead selTargColRead tib txH tyH oldColsN n tcell  -- target read
  ++ forcedGe0Constraints nzIb ((Head.lin 1 tcell).addConst (-1)) (bitsFrom (nzIb + 1) SMALL_RBITS) -- [tcell ≥ 1]
  ++ [ cgH (((Head.lin 1 targVac).addLin 1 nzIb).addConst (-1)) ]                        -- targ_vac = 1 − nz
  ++ [ cgH (((Head.lin 1 offnz).addProd (-1) [oxC, oxC]).addProd (-1) [oyC, oyC]) ]      -- offnz = ox²+oy²
  ++ [ cgH ((Head.lin 1 m).addProd (-1) [offnz, tib, targVac]) ]                         -- m = offnz·tib·targ_vac
  ++ oneHotGatedConstraints selTargRowUpd m tyH                                          -- sel_target row
  ++ oneHotGatedConstraints selTargColUpd m txH                                          -- sel_target col
  -- board update: new[c] − old[c] − AUTO·m·selT[c] + m·selT[c]·old[c] + m·selAuto[c]·old[c] == 0.
  ++ (List.range (KK n)).map (fun (c : Nat) =>
       let x := c % n; let y := c / n
       cgH (((((Head.lin 1 (new n c)).addLin (-1) (old n c)).addProd (-AUTO)
                 [m, selTargRowUpd[y]!, selTargColUpd[x]!]).addProd 1
                 [m, selTargRowUpd[y]!, selTargColUpd[x]!, old n c]).addProd 1
                 [m, selRow n y, selCol n x, old n c]))

/-- **The full `n`-parametric Stage-1b back-end**: `decide_axis(xdec)` · `decide_axis(ydec)` ·
`choose_offset` · the step. `decideAxisConstraints` is already fully base-parametric (every internal
offset is `b + k`), so it is reused verbatim with `n`-derived bases and the `n`-parametric ray
`what`/`dist` columns. `backEndConstraints n = 2` is byte-identical to the frozen `backEndConstraints`. -/
def backEndConstraints (n : Nat) : List VmConstraint2 :=
  decideAxisConstraints (A_DECIDE_X_BASE n) (rWhat n 0) (rWhat n 1) (rDist n 0) (rDist n 1)   -- xdec
  ++ decideAxisConstraints (A_DECIDE_Y_BASE n) (rWhat n 2) (rWhat n 3) (rDist n 2) (rDist n 3) -- ydec
  ++ chooseOffsetConstraints n
  ++ stepConstraints n

end NGen

/-! ## §4d — THE PACKED BOARD COMMITMENT (Leg A), `n`-parametric.

The commitment that replaced `bind_board_roots`. Both boards this leg carries — the OLD cells at
`NGen.old` and the CLAIMED NEW cells at `NGen.new` — get the `AutomataflCommit` family re-pointed to
their own base: `⌈n²/15⌉` degree-1 pack gates each, then each packed felt bound directly to a public
input. The alphabet precondition the pack needs (`cell ∈ {0,1,2,3}`) is ALREADY emitted by
`NGen.boardRangeConstraints` on both boards, so nothing extra is asserted.

WHAT CHANGED AND WHY IT MATTERS AT `n = 11`: the retired `board_root8` pair hashed ONE 8-lane leaf
holding cells `[0,1,2,3]` / `[4,5,6,7]` — LITERAL column numerals, no `n` anywhere. At `n = 11` it
would have committed 8 of the 121 cells and silently ignored the other 113. The pack family is a
fold over `feltCount n`, so it commits EVERY cell at every `n` (`feltCount 11 = 9` felts).

COLUMN LAYOUT: the Stage-1b back-end above (§4c.1) is now `n`-parametric — its tail is
`NGen.A_BACK_TAIL n`, which tracks the `n`-threaded front-end — so the packed felts are allocated at a
straight tail `packFeltBase n = NGen.A_BACK_TAIL n` (not the old `max(front-end, 252)` guard that
papered over a frozen back-end). At every `n` the back-end tiles above the front-end with no overlap
(§6.2 pins), and the commitment sits above the back-end.

PI LAYOUT: `[16, 16+fc)` = the OLD board pack · `[16+fc, 16+2fc)` = the NEW board pack ·
`[16+2fc]`/`[16+2fc+1]` = the witnessed OLD automaton coordinate `(AX, AY)` ·
`[16+2fc+2]`/`[16+2fc+3]` = the NEW automaton coordinate `(AX + m·OX, AY + m·OY)` — the fold OUT
window's `auto_out` (see §4d.1). The coordinate is published because a `Board` is cells AND an automaton
position: cell agreement alone cannot recover the coordinate (no gate forbids a second `AUTO`-coded
cell), so the fold has to see it. -/

/-- Felts per board at size `n` (`⌈n²/15⌉`). -/
abbrev AFC (n : Nat) : Nat := AutomataflCommit.feltCount n

/-- Base column of the packed felts: the first column past the (now `n`-parametric) Stage-1b
back-end (`NGen.A_BACK_TAIL n`). The back-end no longer overlaps the widened front-end, so this is a
straight tail — not the old `max(front-end, 252)` guard that papered over the frozen back-end. -/
def packFeltBase (n : Nat) : Nat := NGen.A_BACK_TAIL n

/-- Packed-felt column `j` of the OLD board. -/
def packOldFelt (n j : Nat) : Nat := packFeltBase n + j
/-- Packed-felt column `j` of the NEW board. -/
def packNewFelt (n j : Nat) : Nat := packFeltBase n + AFC n + j

/-- PI index of the published automaton x-coordinate (y is the next one). -/
def AUTO_PI_BASE (n : Nat) : Nat := 16 + 2 * AFC n

/-- The chosen-offset columns (`choose_offset`'s `ox`/`oy`; `A_CHOOSE_BASE n + 55/56`), reduced to
`OX_C = 207` / `OY_C = 208` at `n = 2`. -/
def offXCol (n : Nat) : Nat := NGen.A_CHOOSE_BASE n + 55
def offYCol (n : Nat) : Nat := NGen.A_CHOOSE_BASE n + 56
/-- The MOVE-MASK column `m = offnz·tib·targ_vac` (`NGen.A_STEP_BASE n + 34 + 2n`) — the boolean the
step block already computes, and the SAME column the capstone `astep_sat_imp_automatonStepN` reads to
say when the reference automaton actually moves. `maskCol 2 = 247`, `maskCol 11 = 637`. -/
def maskCol (n : Nat) : Nat := NGen.A_STEP_BASE n + 34 + 2 * n
/-- The NEW automaton-coordinate columns (`nax = ax + m·ox`, `nay = ay + m·oy`), appended past the two
packed felt tuples — the first columns of the row's tail. `newAutoBase 2 = 254`. -/
def newAutoBase (n : Nat) : Nat := packFeltBase n + 2 * AFC n
def NAXcol (n : Nat) : Nat := newAutoBase n
def NAYcol (n : Nat) : Nat := newAutoBase n + 1

/-- **The Leg-A commitment family** — pack gates for both boards, the PI bindings for both packs,
the OLD automaton-coordinate bindings, and (§4d.1) the NEW automaton-coordinate
`(ax + m·ox, ay + m·oy)` pins + bindings. Emitted LAST, and the new-auto family is emitted AFTER the
old-auto one, so every structured membership proof for the preceding families (incl.
`astepN_autoX_mem`) keeps its position under a single extra `mem_append_left`. §4d.1: `nax`/`nay` are
two fresh DEGREE-2-pinned columns (`nax − ax − m·ox == 0`, `nay − ay − m·oy == 0`) bound to
`PI[AUTO_PI_BASE+2]`/`[+3]`. Gating the offset on the move mask is what makes the published
coordinate the reference automaton's post-step position UNCONDITIONALLY — including the BLOCKED step,
where the reference stays put and the old degree-1 `ax+ox` pin overshot (see
`newAutoCoordCommitConstraints` for why that was a fail-closed completeness bug at the fold seam). -/
def commitBoardsConstraints (n : Nat) : List VmConstraint2 :=
  AutomataflCommit.packBoardConstraintsAt n (NGen.old n) (packOldFelt n)
  ++ AutomataflCommit.packBoardConstraintsAt n (NGen.new n) (packNewFelt n)
  ++ AutomataflCommit.commitBoardConstraintsAt n (packOldFelt n) 16
  ++ AutomataflCommit.commitBoardConstraintsAt n (packNewFelt n) (16 + AFC n)
  ++ AutomataflCommit.autoCoordCommitConstraints (NGen.AX n) (NGen.AY n) (AUTO_PI_BASE n)
  ++ AutomataflCommit.newAutoCoordCommitConstraints
       (NGen.AX n) (offXCol n) (NGen.AY n) (offYCol n) (maskCol n) (NAXcol n) (NAYcol n)
       (AUTO_PI_BASE n + 2)

/-- Trace width at size `n`: the packed felts, then the two NEW-automaton-coordinate columns, close
the row. -/
def A_WIDTH_N (n : Nat) : Nat := packFeltBase n + 2 * AFC n + 2
/-- PI count at size `n`: the 16-felt state prefix, two packs, the OLD automaton coordinate, and the
NEW automaton coordinate. -/
def A_PI_COUNT_N (n : Nat) : Nat := AUTO_PI_BASE n + 4

/-- **`automataflStepDescN n`** — the automaton-step (D1) descriptor with the board size `n` an
EXPLICIT parameter (AUTOMATAFL-NGENERIC-DESIGN §4). The FRONT-END (`NGen.frontEndConstraints`), the
Stage-1b BACK-END (`NGen.backEndConstraints`) AND the COMMITMENT (§4d) are now ALL `n`-threaded, and
their column blocks tile without overlap at every `n` (front-end ⊕ decide_axis ×2 ⊕ choose_offset ⊕
step ⊕ packed felts). `automataflStepDescN 2` is defeq to the byte-golden `automataflStepDesc`. -/
def automataflStepDescN (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-step-d1-n2"
  , traceWidth  := A_WIDTH_N n
  , piCount     := A_PI_COUNT_N n
  , tables      := []
  , constraints := NGen.frontEndConstraints n ++ NGen.backEndConstraints n ++ commitBoardsConstraints n
  , hashSites   := []
  , ranges      := [] }

/-- **`automataflStepDesc`** — the automatafl automaton-step (D1) descriptor, AUTHORED IN LEAN.
Stage 1a authored the board + auto-pin + four-ray-scan front-end; Stage 1b completes it with the
`decide_axis` truth table (×2 axes), `choose_offset`, the step, the board-update equalities, and the
PACKED BOARD COMMITMENT (§4d) — the full automaton-step gate set. -/
def automataflStepDesc : EffectVmDescriptor2 := automataflStepDescN 2

/-! ## §5 — The byte-pinned wire golden + shape pins.

`EmitByName.lean` routes `emitVmJson2 automataflStepDesc` to
`circuit/descriptors/by-name/automatafl-step.json`, and `scripts/check-descriptor-drift.sh`
re-derives that file from THIS emission on every run. A drift on either side breaks this `#guard`
(Lean) or the drift gate (disk). The wire pins the COMPLETE D1/n=2 gate set — the Stage-1a front-end
(§4), the Stage-1b back-end (§4c.1, `n`-parametric, `= 2`), the packed board commitment (§4d) and
the NEW-automaton-coordinate pins/bindings (§4d.1): 409 constraints over 256 columns and 22 public
inputs. -/

#guard emitVmJson2 automataflStepDesc ==
"{\"name\":\"dregg-automatafl-step-d1-n2\",\"ir\":2,\"trace_width\":256,\"public_input_count\":22,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":20}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":21}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":23}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":19}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":19}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":18}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"var\",\"v\":25}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":17}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":2}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":30}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":31}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":35}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":31}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":29}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":28}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":30}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"var\",\"v\":35}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":37}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":40}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":41}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":39}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":41}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":39}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":38}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":40}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":47}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":50}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":51}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"var\",\"v\":53}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}},\"r\":{\"t\":\"var\",\"v\":52}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":53}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"var\",\"v\":49}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":51}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":49}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":48}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":56}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"var\",\"v\":48}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"var\",\"v\":55}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":64}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":67}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":35}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":68}}},\"r\":{\"t\":\"var\",\"v\":68}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":69}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":70}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":71}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":72}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":73}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":77},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":77},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":78},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":78},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":74}}},\"r\":{\"t\":\"var\",\"v\":74}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":75}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":76}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":77}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":78}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":79}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":83},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":83},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":80}}},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":81}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":82}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":83}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":84}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":85}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":89},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":89},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"var\",\"v\":34}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":86}}},\"r\":{\"t\":\"var\",\"v\":86}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":87}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":88}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":90}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":91}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"var\",\"v\":92}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":93}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":94}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":95}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":96}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":97}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"var\",\"v\":34}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":100},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":100},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":101},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":101},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"var\",\"v\":98}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":99}}},\"r\":{\"t\":\"var\",\"v\":99}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":98}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":100}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":102}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":103}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":104}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":60}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}},\"r\":{\"t\":\"var\",\"v\":24}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}},\"r\":{\"t\":\"var\",\"v\":34}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":74}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":59}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":60}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":74}},\"r\":{\"t\":\"var\",\"v\":34}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":74}},\"r\":{\"t\":\"var\",\"v\":24}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":80}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":86}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":86}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":60}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"var\",\"v\":98}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":86}},\"r\":{\"t\":\"var\",\"v\":98}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":74}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":59}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":60}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":74}},\"r\":{\"t\":\"var\",\"v\":24}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":60}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"var\",\"v\":68}},\"r\":{\"t\":\"var\",\"v\":34}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"var\",\"v\":99}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":86}},\"r\":{\"t\":\"var\",\"v\":99}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"var\",\"v\":99}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":60}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"var\",\"v\":99}},\"r\":{\"t\":\"var\",\"v\":98}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":86}},\"r\":{\"t\":\"var\",\"v\":99}},\"r\":{\"t\":\"var\",\"v\":98}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":61}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":68}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":68}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":60}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":68}},\"r\":{\"t\":\"var\",\"v\":24}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":61}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":58}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":74}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":59}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":60}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":74}},\"r\":{\"t\":\"var\",\"v\":34}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":67}},\"r\":{\"t\":\"var\",\"v\":61}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":58}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":59}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":60}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":65}},\"r\":{\"t\":\"var\",\"v\":61}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":110}},\"r\":{\"t\":\"var\",\"v\":111}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":111}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":112},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":112},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":112},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":114}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":116},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":116},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":115}}},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":117}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":118}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":119}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":120}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":121}}},\"r\":{\"t\":\"var\",\"v\":121}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":122}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":123}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":124}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":125}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":126}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"var\",\"v\":127}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":128}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":129}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":130}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":131}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":132}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"var\",\"v\":54}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":133}}},\"r\":{\"t\":\"var\",\"v\":133}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"var\",\"v\":54}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":134}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":135}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":136}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":137}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":138}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":140},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":140},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"var\",\"v\":139}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":140}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":141}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":142}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":143}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":144}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":145},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"var\",\"v\":54}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":146},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":146},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":151},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":151},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":146},\"r\":{\"t\":\"var\",\"v\":145}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":146}}},\"r\":{\"t\":\"var\",\"v\":146}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":145}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":147}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":148}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":149}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":150}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":107}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":108}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":54}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":121}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":106}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":107}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":121}},\"r\":{\"t\":\"var\",\"v\":54}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":108}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":121}},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":127}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":133}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":133}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":107}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":108}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":127}},\"r\":{\"t\":\"var\",\"v\":145}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":133}},\"r\":{\"t\":\"var\",\"v\":145}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":121}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":106}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":107}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":108}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":121}},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":107}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":108}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":54}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":127}},\"r\":{\"t\":\"var\",\"v\":146}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":133}},\"r\":{\"t\":\"var\",\"v\":146}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":127}},\"r\":{\"t\":\"var\",\"v\":146}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":107}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":127}},\"r\":{\"t\":\"var\",\"v\":146}},\"r\":{\"t\":\"var\",\"v\":145}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":133}},\"r\":{\"t\":\"var\",\"v\":146}},\"r\":{\"t\":\"var\",\"v\":145}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":108}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":115}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":115}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":107}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":108}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":105}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":121}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":106}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":107}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":121}},\"r\":{\"t\":\"var\",\"v\":54}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":108}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":105}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":106}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":107}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"var\",\"v\":112}},\"r\":{\"t\":\"var\",\"v\":108}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":162},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":162},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":163},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":163},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":200000},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":58}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-200},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":61}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-200000},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":105}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":200},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":107}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":108}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":152}}},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-100000},\"r\":{\"t\":\"var\",\"v\":58}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":100},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":100000},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-100},\"r\":{\"t\":\"var\",\"v\":107}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":108}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":153}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":154}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":155}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":156}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":157}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":158}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":159}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":160}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":161}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-512},\"r\":{\"t\":\"var\",\"v\":162}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1024},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2048},\"r\":{\"t\":\"var\",\"v\":164}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4096},\"r\":{\"t\":\"var\",\"v\":165}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8192},\"r\":{\"t\":\"var\",\"v\":166}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16384},\"r\":{\"t\":\"var\",\"v\":167}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32768},\"r\":{\"t\":\"var\",\"v\":168}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":169}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-131072},\"r\":{\"t\":\"var\",\"v\":170}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-262144},\"r\":{\"t\":\"var\",\"v\":171}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-524288},\"r\":{\"t\":\"var\",\"v\":172}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":174},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":174},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":178},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":178},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":190},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":190},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":191},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":191},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":192},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":192},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":193},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":193},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":200000},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-200},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"var\",\"v\":107}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"var\",\"v\":108}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-200000},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"var\",\"v\":58}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":200},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"var\",\"v\":61}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":173}}},\"r\":{\"t\":\"var\",\"v\":173}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-100000},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":100},\"r\":{\"t\":\"var\",\"v\":107}}},\"r\":{\"t\":\"var\",\"v\":108}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":100000},\"r\":{\"t\":\"var\",\"v\":58}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-100},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":61}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":174}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":175}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":176}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":177}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":179}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":180}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":181}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":182}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-512},\"r\":{\"t\":\"var\",\"v\":183}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1024},\"r\":{\"t\":\"var\",\"v\":184}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2048},\"r\":{\"t\":\"var\",\"v\":185}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4096},\"r\":{\"t\":\"var\",\"v\":186}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8192},\"r\":{\"t\":\"var\",\"v\":187}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16384},\"r\":{\"t\":\"var\",\"v\":188}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32768},\"r\":{\"t\":\"var\",\"v\":189}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":190}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-131072},\"r\":{\"t\":\"var\",\"v\":191}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-262144},\"r\":{\"t\":\"var\",\"v\":192}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-524288},\"r\":{\"t\":\"var\",\"v\":193}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":196},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":196},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":197},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":197},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":198},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":198},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":199},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":199},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"var\",\"v\":58}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":194}}},\"r\":{\"t\":\"var\",\"v\":194}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":58}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":195}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":196}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":197}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":198}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":199}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":201},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":201},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":203},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":203},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":204},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":204},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":205},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":205},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":200}}},\"r\":{\"t\":\"var\",\"v\":200}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":201}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":202}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":203}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":204}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":205}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"const\",\"v\":1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"const\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"const\",\"v\":1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"const\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":194}},\"r\":{\"t\":\"var\",\"v\":59}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":194}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"var\",\"v\":173}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":173}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"var\",\"v\":206}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":206}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"var\",\"v\":206}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"var\",\"v\":206}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":106}},\"r\":{\"t\":\"var\",\"v\":173}},\"r\":{\"t\":\"var\",\"v\":206}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"var\",\"v\":173}},\"r\":{\"t\":\"var\",\"v\":206}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":210},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":210},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":211},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":211},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":213},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":213},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"var\",\"v\":207}}}},\"r\":{\"t\":\"var\",\"v\":209}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":207}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":210}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":211}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":212}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":213}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":214}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":216},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":216},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":217},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":217},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":218},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":218},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":219},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":219},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":220},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":220},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"var\",\"v\":207}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":215}}},\"r\":{\"t\":\"var\",\"v\":215}},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"var\",\"v\":207}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":216}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":217}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":218}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":219}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":220}}},\"r\":{\"t\":\"const\",\"v\":-2}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":222},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":222},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":223},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":223},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":224},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":224},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":225},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":225},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"var\",\"v\":208}}}},\"r\":{\"t\":\"var\",\"v\":221}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":208}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":222}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":223}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":224}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":225}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":226}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":228},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":228},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":229},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":229},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":230},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":230},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":231},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":231},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":232},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":232},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"var\",\"v\":208}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":227}}},\"r\":{\"t\":\"var\",\"v\":227}},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"var\",\"v\":208}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":228}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":229}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":230}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":231}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":232}}},\"r\":{\"t\":\"const\",\"v\":-2}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"var\",\"v\":215}},\"r\":{\"t\":\"var\",\"v\":221}},\"r\":{\"t\":\"var\",\"v\":227}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":233}},\"r\":{\"t\":\"var\",\"v\":235}},\"r\":{\"t\":\"var\",\"v\":236}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"var\",\"v\":208}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":237},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":237},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":233}},\"r\":{\"t\":\"var\",\"v\":237}},\"r\":{\"t\":\"var\",\"v\":238}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"var\",\"v\":8}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"var\",\"v\":207}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":234},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"var\",\"v\":237}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"var\",\"v\":238}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"var\",\"v\":237}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"var\",\"v\":238}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":240},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":240},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":241},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":241},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":242},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":242},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":243},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":243},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":244},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":244},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"var\",\"v\":234}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":239}}},\"r\":{\"t\":\"var\",\"v\":239}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":234}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":240}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":241}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":242}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":243}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":244}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":245},\"r\":{\"t\":\"var\",\"v\":239}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":246},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"var\",\"v\":207}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"var\",\"v\":208}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":246},\"r\":{\"t\":\"var\",\"v\":233}},\"r\":{\"t\":\"var\",\"v\":245}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":248},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":248},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":247}},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"var\",\"v\":249}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":208}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":250},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":250},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":251},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":251},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":247}},\"r\":{\"t\":\"var\",\"v\":250}},\"r\":{\"t\":\"var\",\"v\":251}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":251},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":8}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":207}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"var\",\"v\":250}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"var\",\"v\":250}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"var\",\"v\":251}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"var\",\"v\":251}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":249}},\"r\":{\"t\":\"var\",\"v\":250}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":249}},\"r\":{\"t\":\"var\",\"v\":250}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":249}},\"r\":{\"t\":\"var\",\"v\":251}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":249}},\"r\":{\"t\":\"var\",\"v\":251}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":252},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":253},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":7}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":252,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":253,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":19},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":207}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":255},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"var\",\"v\":208}}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":254,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":255,\"pi_index\":21}],\"hash_sites\":[],\"ranges\":[]}"

/-! ### Shape pins. -/

#guard automataflStepDesc.name == "dregg-automatafl-step-d1-n2"
#guard automataflStepDesc.traceWidth == 256
#guard automataflStepDesc.traceWidth == A_WIDTH
#guard automataflStepDesc.traceWidth == A_WIDTH_N 2
#guard automataflStepDesc.piCount == 22
#guard automataflStepDesc.piCount == A_PI_COUNT
#guard automataflStepDesc.piCount == A_PI_COUNT_N 2
-- 399 + the commitment leg (1 old pack + 1 new pack + 1 + 1 PI bindings + 2 old-auto-coord
-- + 2 new-auto pin gates + 2 new-auto PI bindings) = 409.
#guard automataflStepDesc.constraints.length == 409
#guard (commitBoardsConstraints 2).length == 10
#guard automataflStepDesc.tables.length == 0
#guard automataflStepDesc.hashSites.length == 0
-- THE COMMITMENT IS NO LONGER A LOOKUP. The retired `board_root8` pair was the descriptor's ONLY
-- chip lookup; the pack is two degree-1 gates, so the whole Leg-A object is now gates + bindings.
#guard automataflStepDesc.constraints.all (fun c => match c with | .lookup _ => false | _ => true)


/-! ## §6 — Layout-tiling pins + `descN 11` shape pins.

`automataflStepDescN n` now tiles CLEANLY at every `n`. Every column block is a function of `n`
derived from `A_FRONT_WIDTH n`: front-end `[0, A_FRONT_WIDTH n)` · decide_axis(xdec)
`[A_DECIDE_X_BASE, A_DECIDE_Y_BASE)` · decide_axis(ydec) `[A_DECIDE_Y_BASE, A_CHOOSE_BASE)` ·
choose_offset `[A_CHOOSE_BASE, A_STEP_BASE)` · step `[A_STEP_BASE, A_BACK_TAIL)` · packed commitment
`[A_BACK_TAIL, A_WIDTH_N)`.

The `maxCol*` guards are NOT definitional: `maxColList cs` computes the LARGEST trace column any gate
in `cs` actually references, and each pin asserts a block's top column is exactly one below the next
block's base — so a future gate widened past its declared block width would break them (this is the
`AutomataflResolveEmit` "last column + 1 == next base" discipline). -/

/-- Largest trace column an `EmittedExpr` references (`const ↦ 0`). -/
def maxColExpr : EmittedExpr → Nat
  | .var c   => c
  | .const _ => 0
  | .add l r => max (maxColExpr l) (maxColExpr r)
  | .mul l r => max (maxColExpr l) (maxColExpr r)

/-- Largest trace column a `VmConstraint2` references. PI indices live in a separate space and are
excluded; a `.piBinding` contributes only its TRACE column. -/
def maxColC : VmConstraint2 → Nat
  | .base (.gate e)            => maxColExpr e
  | .base (.boundary _ e)      => maxColExpr e
  | .base (.transition hi lo)  => max hi lo
  | .base (.piBinding _ col _) => col
  | _                          => 0

/-- Largest trace column over a constraint list (empty ↦ 0). -/
def maxColList (cs : List VmConstraint2) : Nat := cs.foldl (fun m c => max m (maxColC c)) 0

/-! ### §6.1 — n = 2 base pins (byte-identical to the frozen absolute layout) + tiling. -/
#guard NGen.A_FRONT_WIDTH 2 == 58
#guard NGen.A_DECIDE_X_BASE 2 == 58
#guard NGen.A_DECIDE_Y_BASE 2 == 105
#guard NGen.A_CHOOSE_BASE 2 == 152
#guard NGen.A_STEP_BASE 2 == 209
#guard NGen.A_BACK_TAIL 2 == 252
#guard packFeltBase 2 == 252
-- the move mask the new-auto pin multiplies by IS the step block's own `m` column.
#guard maskCol 2 == 247
#guard maskCol 2 < NGen.A_BACK_TAIL 2
-- the n-parametric back-end reproduces the FROZEN n = 2 absolute-column back-end (length here; the
-- FULL byte-for-byte identity is the descN 2 wire golden below, which emits front ++ back ++ commit):
#guard (NGen.backEndConstraints 2).length == backEndConstraints.length
-- each segment's TOP referenced column is exactly one below the next segment's base (n = 2):
#guard maxColList (NGen.frontEndConstraints 2) + 1 == NGen.A_FRONT_WIDTH 2
#guard maxColList (decideAxisConstraints (NGen.A_DECIDE_X_BASE 2) (NGen.rWhat 2 0) (NGen.rWhat 2 1)
        (NGen.rDist 2 0) (NGen.rDist 2 1)) + 1 == NGen.A_DECIDE_Y_BASE 2
#guard maxColList (decideAxisConstraints (NGen.A_DECIDE_Y_BASE 2) (NGen.rWhat 2 2) (NGen.rWhat 2 3)
        (NGen.rDist 2 2) (NGen.rDist 2 3)) + 1 == NGen.A_CHOOSE_BASE 2
#guard maxColList (NGen.chooseOffsetConstraints 2) + 1 == NGen.A_STEP_BASE 2
#guard maxColList (NGen.stepConstraints 2) + 1 == NGen.A_BACK_TAIL 2
#guard maxColList (NGen.backEndConstraints 2) + 1 == NGen.A_BACK_TAIL 2
#guard maxColList (automataflStepDescN 2).constraints + 1 == A_WIDTH_N 2   -- 256

/-! ### §6.2 — n = 11: the widened front-end AND the rebuilt back-end tile with NO overlap.

Under the OLD frozen layout the back-end sat at absolute `[58, 252)` while the front-end already
grew past `252`; the ray blocks were themselves frozen at 10 columns/ray and overlapped internally
at `n ≥ 3`. Both are fixed: the ray blocks are `RAY_W n = 3n+4` wide and the back-end base tracks
`A_FRONT_WIDTH n`. -/
example : EffectVmDescriptor2 := automataflStepDescN 11
#guard (NGen.boardRangeConstraints 11).length == 2 * 121
#guard (NGen.boardRangeConstraints 11).length == 242
#guard NGen.KK 11 == 121
-- THE COMMITMENT EMITS AT n = 11: 9 pack gates per board + 9 PI bindings per board + the coordinate.
#guard AFC 11 == 9
#guard (AutomataflCommit.packBoardConstraintsAt 11 (NGen.old 11) (packOldFelt 11)).length == 9
#guard (AutomataflCommit.packBoardConstraintsAt 11 (NGen.new 11) (packNewFelt 11)).length == 9
#guard (AutomataflCommit.commitBoardConstraintsAt 11 (packOldFelt 11) 16).length == 9
-- 38 (packs + commits + old-auto) + 4 (new-auto: 2 pin gates + 2 PI bindings) = 42.
#guard (commitBoardsConstraints 11).length == 42
#guard (automataflStepDescN 11).piCount == 38
-- every cell of the 11×11 board is covered by some pack gate (the leaf could not do this)
#guard 11 * 11 <= 15 * AFC 11
-- the ray blocks tile INTERNALLY at n = 11 (ib/rc reads ⊕ hit one-hot ⊕ dist/what/hib/inv), the fix
-- the old 10-column-frozen accessors could not satisfy:
#guard NGen.rRc 11 0 11 + 1 == NGen.rHit 11 0 1
#guard NGen.rHit 11 0 11 + 1 == NGen.rDist 11 0
#guard NGen.rInv 11 0 + 1 == NGen.rayBase 11 1
#guard NGen.rInv 11 3 + 1 == NGen.A_FRONT_WIDTH 11
-- the back-end block bases at n = 11 (re-pinned: the front-end widened by 12 = 4·(COORD_RBITS 11 − 1)
-- = 4·3 columns, since each of the four coord edges is now 4 bits, not 1 — the auto-coordinate is
-- genuinely decodable in [0,11) rather than pinned to the empty {0,1}∩{9,10}):
#guard NGen.A_FRONT_WIDTH 11 == 430
#guard NGen.A_DECIDE_X_BASE 11 == 430
#guard NGen.A_DECIDE_Y_BASE 11 == 477
#guard NGen.A_CHOOSE_BASE 11 == 524
#guard NGen.A_STEP_BASE 11 == 581
#guard NGen.A_BACK_TAIL 11 == 660
#guard packFeltBase 11 == 660
-- 678 (front ⊕ back ⊕ 18 packed felts) + 2 new-auto columns (nax=678, nay=679) = 680.
#guard (automataflStepDescN 11).traceWidth == 680
#guard NAXcol 11 == 678
#guard NAYcol 11 == 679
#guard AUTO_PI_BASE 11 + 2 == 36
#guard offXCol 11 == 579
#guard NGen.AX 11 == 242
-- the mask column at the deployed size, and that it lands INSIDE the step block (not the tail):
#guard maskCol 11 == 637
#guard NGen.A_STEP_BASE 11 <= maskCol 11 && maskCol 11 < NGen.A_BACK_TAIL 11
-- each back-end block's TOP referenced column is exactly one below the next block's base (n = 11) —
-- the back-end no longer overlaps the widened front-end OR the packed commitment:
#guard maxColList (NGen.frontEndConstraints 11) + 1 == NGen.A_FRONT_WIDTH 11
#guard maxColList (decideAxisConstraints (NGen.A_DECIDE_X_BASE 11) (NGen.rWhat 11 0) (NGen.rWhat 11 1)
        (NGen.rDist 11 0) (NGen.rDist 11 1)) + 1 == NGen.A_DECIDE_Y_BASE 11
#guard maxColList (decideAxisConstraints (NGen.A_DECIDE_Y_BASE 11) (NGen.rWhat 11 2) (NGen.rWhat 11 3)
        (NGen.rDist 11 2) (NGen.rDist 11 3)) + 1 == NGen.A_CHOOSE_BASE 11
#guard maxColList (NGen.chooseOffsetConstraints 11) + 1 == NGen.A_STEP_BASE 11
#guard maxColList (NGen.stepConstraints 11) + 1 == NGen.A_BACK_TAIL 11
#guard maxColList (NGen.backEndConstraints 11) + 1 == NGen.A_BACK_TAIL 11
-- descN 2 is the frozen object: the parametric front-end agrees with the n = 2 instance.
#guard NGen.KK 2 == KK
#guard (NGen.boardRangeConstraints 2).length == boardRangeConstraints.length
#guard (NGen.frontEndConstraints 2).length == frontEndConstraints.length

-- THE COORDINATE-GADGET FIX: the auto-coordinate decompose is now `COORD_RBITS n`-bit per edge
-- (`rangeNonnegConstraints`, mirroring `AutomataflResolveEmit`), NOT the old frozen 1-bit-per-edge
-- gadget. At n = 2, `COORD_RBITS 2 = 1`, so it reduces to the old two-bit form (byte-golden held); at
-- n ≥ 3 each edge widens, so the decoded coordinate ranges over the FULL [0,n) instead of the old
-- `{0,1} ∩ {n−2, n−1}` (which was `{1}` at n = 3 and EMPTY — descriptor UNSATISFIABLE — at n ≥ 4).
#guard NGen.COORD_RBITS 2 == 1
#guard NGen.COORD_RBITS 3 == 2
#guard NGen.COORD_RBITS 11 == 4
-- each edge is one `range_nonneg` (`COORD_RBITS n` bits + 1 recomposition), two edges per coordinate:
#guard (NGen.decomposeConstraints 2 (NGen.AX 2) (NGen.axLoBit 2) (NGen.axHiBit 2)).length == 4
#guard (NGen.decomposeConstraints 3 (NGen.AX 3) (NGen.axLoBit 3) (NGen.axHiBit 3)).length == 6
#guard (NGen.decomposeConstraints 11 (NGen.AX 11) (NGen.axLoBit 11) (NGen.axHiBit 11)).length == 10
-- the auto-coord bit runs do not overlap the auto one-hot selectors at n = 11 (COORD_RBITS-spaced):
#guard NGen.ayHiBit 11 + NGen.COORD_RBITS 11 == NGen.selRow 11 0

end Dregg2.Circuit.Emit.AutomataflStepEmit
