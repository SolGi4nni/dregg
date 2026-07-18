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

The D1 AIR is a SINGLE-ROW circuit: every constraint is a per-row polynomial gate (`assert_zero`
of a `Head` = a sum-of-products), a boolean pin (`assert_binary`), or a small-set membership
(`assert_member`). There are NO cross-row/transition constraints, so every carrier here is
`.base (.gate e)` over an `EmittedExpr` — no `WindowGate`, no `Lookup` (the board-root Merkle
`MerkleHash8` chip lookups belong to the DEFERRED `board_root8` family, see §REMAINING).

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

## SCOPE — what is authored here (Stage 1a), and what REMAINS (§REMAINING)

AUTHORED (this file): the board columns (old + new), the door-PI ABI (`piCount = 16`), the automaton
position pin (`ax`/`ay` bit-range + the auto row×column one-hot + the `AUTO == Σ selRow·selCol·board`
dot product), and the FOUR ray scans (per step: the prefix-sum in-bounds bit, the gated shifted
row×column read, the hit one-hot, the `dist`/`what` recompositions, the vacuum-before / in-bounds-
before occlusion gates, the hit-in-bounds bit, and the `cond_nonzero` in-bounds-hit witness).

REMAINING (deferred, each appends to this descriptor + re-pins): `decide_axis` (the 9-case
`evaluateAxis` truth table, ×2 axes) · `choose_offset` (the score-compare) · the STEP
(target/in-bounds/vacuum/moved) · the board-update equalities · `board_root8` (the two `MerkleHash8`
board-root chip lookups + their `bind_pi`s, PIs `[16..32)`).

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + shape `#guard`s. NEW file;
imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.AutomataflStepEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 emitVmJson2)

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
/-- Total main-trace width: `2k + 2 (coords) + 4 (coord bits) + 2n (auto one-hots) + 10·4 (rays)`. -/
def A_WIDTH : Nat := 2 * KK + 6 + 2 * NN + 10 * 4
/-- The door state-binding PI prefix ABI (`build_d1_bound` `add_pi`s `old8 ‖ new8`, opaque here). -/
def A_PI_COUNT : Nat := 16

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

/-- The full front-end constraint list, in `automaton_gadget`'s emission order. -/
def frontEndConstraints : List VmConstraint2 :=
  decomposeConstraints AX axLoBit axHiBit
  ++ decomposeConstraints AY ayLoBit ayHiBit
  ++ oneHotConstraints [selRow 0, selRow 1] (Head.lin 1 AY)   -- the row one-hot is pinned to ay
  ++ oneHotConstraints [selCol 0, selCol 1] (Head.lin 1 AX)   -- the col one-hot is pinned to ax
  ++ [ cgH autoPinHead ]
  ++ rayConstraints 0 1 0      -- XP
  ++ rayConstraints 1 (-1) 0   -- XN
  ++ rayConstraints 2 0 1      -- YP
  ++ rayConstraints 3 0 (-1)   -- YN

/-- **`automataflStepDesc`** — the automatafl automaton-step (D1) descriptor, AUTHORED IN LEAN.
Stage 1a: the board + auto-pin + four-ray-scan front-end (see §SCOPE). The `decide_axis` truth
table, `choose_offset`, the step, the board-update equalities, and `board_root8` are the tracked
remainder (§REMAINING), each appending to `frontEndConstraints` and re-pinning the wire golden. -/
def automataflStepDesc : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-step-d1-n2"
  , traceWidth  := A_WIDTH
  , piCount     := A_PI_COUNT
  , tables      := []
  , constraints := frontEndConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §5 — The byte-pinned wire golden + shape pins.

`EmitByName.lean` routes `emitVmJson2 automataflStepDesc` to
`circuit/descriptors/by-name/automatafl-step.json`, and `scripts/check-descriptor-drift.sh`
re-derives that file from THIS emission on every run. A drift on either side breaks this `#guard`
(Lean) or the drift gate (disk). The wire pins EXACTLY the Stage-1a front-end authored above (§4);
appending a §REMAINING family re-pins this string. -/

#guard emitVmJson2 automataflStepDesc ==
  "{\"name\":\"dregg-automatafl-step-d1-n2\",\"ir\":2,\"trace_width\":58,\"public_input_count\":16,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":20}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":21}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":23}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":19}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":19}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":18}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"var\",\"v\":25}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":17}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":2}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":30}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":31}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":35}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":31}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":29}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":28}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":30}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"var\",\"v\":35}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":37}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":40}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":41}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":39}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":41}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":39}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":38}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":40}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":47}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":50}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":51}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"var\",\"v\":53}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}},\"r\":{\"t\":\"var\",\"v\":52}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":53}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"var\",\"v\":49}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":51}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":49}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":48}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":56}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"var\",\"v\":48}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"var\",\"v\":55}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":-1}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ### Shape pins. -/

#guard automataflStepDesc.name == "dregg-automatafl-step-d1-n2"
#guard automataflStepDesc.traceWidth == 58
#guard automataflStepDesc.traceWidth == A_WIDTH
#guard automataflStepDesc.piCount == 16
#guard automataflStepDesc.constraints.length == 85
#guard automataflStepDesc.tables.length == 0
#guard automataflStepDesc.hashSites.length == 0

end Dregg2.Circuit.Emit.AutomataflStepEmit
