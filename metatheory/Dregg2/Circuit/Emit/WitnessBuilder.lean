/-
# Dregg2.Circuit.Emit.WitnessBuilder — the reusable witness-assembly core (compute → place → compose)

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

Every `KimchiRender*` module hand-rolls the SAME two-step pattern: a **compute-fn** (a Lean function
`inputs → field values`) followed by a **placement** (a `cellAt`/`witAt col row` that lays each
computed value into the 15×N column-major grid per the gate's `generate_witness` column order), then
the fixed assembly `(List.range 15).map (fun col => (List.range N).map (fun row => cellAt col row))`.
Concretely:

  * `KimchiRenderPoseidon.witAt` (`KimchiRenderPoseidon.lean:103-108`) — column-block dispatch on the
    `STATE_ORDER = [0,2,3,4,1]` `round_to_cols` map, pulling `laneI (5r+i) j` per block;
  * `KimchiRenderCompleteAdd.cellAt` (`:136-137`) — row-0 = the eleven `completeAddWitness` cells;
  * `KimchiRenderVarBaseMul.cellAt` (`:150-151`) — row-0 = `currRow`, row-1 = `nextRow`;
  * `KimchiRenderEndoMul.cellAt` (`:153-154`) / `KimchiRenderEndoMulScalar.cellAt` (`:107-108`) — same.

Every one repeats the `(List.range 15).map (…(List.range N).map…)` assembly by hand. **This file is
that reusable core.** `WitnessBuilder` factors the pattern into `toGrid`/`compose`: a per-gate
"cell spec" (a `List (Cell × Int)` — which computed value goes in which `{row,col}`) composed into a
single circuit witness whose cells are indexed exactly as `KimchiPlacement.place` indexes its wire
cells. It is what the **step_main assembly** needs that the per-gate fns do not give: a combinator
where two gates sharing a copied wire get a CONSISTENT value in both cells (the copy-permutation
constraint) — because the composing front-end fills every cell of a variable's class from ONE env
entry, so a copy class holds one value by construction.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles". Reproducing an existing gate's
witness through this builder is SYNTHESIS FIDELITY, pinned by `#guard` (interpreter-reduced), not a
refinement theorem. The one machine-checked claim here is small and concrete: that on a specific
two-gate circuit the composed grid satisfies `place`'s copy-permutation σ (a `by decide` theorem over
that circuit), and that the check is FALSIFIABLE (a hand-broken grid fails it, also `by decide`).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The combinator, the grid engine, and both front-ends are authored
in Lean. It touches NO existing gate module — it reproduces `KimchiRenderPoseidon.poseidonWitness`
byte-for-byte through the builder (read-only reference), demonstrating the factoring generalizes
without a refactor. `proof-systems` authors no constraint; nothing Rust is written here.

## Axiom hygiene / build

NO `main` (roots cleanly into `PicklesSynthesis`). `#guard`s reduce in the interpreter; the two
copy-permutation theorems are `by decide` over a small circuit; no `sorry`/`native_decide`. Imports
`KimchiPlacement` (Cell/PVar/PGate/`circuitPositions`/`permPairs`/`rowPositions`) and
`KimchiRenderPoseidon` (`laneI`/`poseidonWitness`, read-only, for the byte-identity pin).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiRenderPoseidon

namespace Dregg2.Circuit.Emit.WitnessBuilder

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiRenderPoseidon (laneI poseidonWitness)

set_option autoImplicit false

/-! ## §1 — the core: cell placements, the grid engine, and the compose combinator.

A witness is a 15×N COLUMN-MAJOR grid (`grid[col][row]`), exactly the shape every `KimchiRender*`
module emits. A `CellVal` is one placement (a computed value at a `{row,col}`); a `GateWitness` is one
gate's list of placements — the composable unit each render module produces by hand. -/

/-- One placement: computed value `.2` occupies grid cell `.1 = {row,col}`. -/
abbrev CellVal := Cell × Int

/-- One gate's witness contribution: the cells THIS gate fills, with what values. Producing this from
    `(compute-fn, placement)` is exactly what each `KimchiRender*` module hand-rolls. -/
abbrev GateWitness := List CellVal

/-- Read cell `{row,col}` from a column-major grid `g` (`g[col][row]`); `0` if out of range. -/
def gridAt (g : List (List Int)) (c : Cell) : Int := (g.getD c.col []).getD c.row 0

/-! ### The grid engine, and the index that makes it linear.

MEASURED at the step_main-fragment scale rung (`KimchiComposeStepFragment`, commit `3c3f61b24`):
`compose` took 514 / 6075 / 83808 ms at 454 / 1674 / 4058 rows — a fitted exponent of **2.01**,
extrapolating to ~2.6 h at `step_main`'s ~17,806 rows. The cause was one `find?` over the WHOLE
placement list for each of the `numCols × numRows` grid cells: O(cells · placements).

`cellIndex` buckets the placement list by ROW in one pass, so a cell reads a bucket of ~`numCols`
entries instead of all of them. It is `Array`+`List`, NOT `Std.HashMap`, deliberately:
`Array.replicate`/`Array.modify`/`Array.getD` reduce in the KERNEL, so §3's `by decide` σ theorems
still hold on the same definitions the interpreter runs. -/

/-- **THE CELL → VALUE INDEX.** The placement list bucketed by row, in ONE pass: bucket `r` holds the
    placements of row `r` in LIST ORDER (fold the reversed list and cons), so `find?`'s FIRST-WINS
    semantics is preserved exactly — including a prepended override. A placement whose row is ≥
    `numRows` is dropped by `Array.modify`'s out-of-bounds no-op, and such a row is never read. -/
def cellIndex (numRows : Nat) (ps : List CellVal) : Array (List CellVal) :=
  ps.reverse.foldl (fun a p => a.modify p.1.row (p :: ·)) (Array.replicate numRows [])

/-- **THE GRID ENGINE.** Assemble a `numCols × numRows` column-major grid from a flat placement list:
    each `{row,col}` takes its placed value (FIRST placement wins on a repeat — so a variable-consistent
    front-end that lists a cell once per class is well-defined, and a prepended override is honoured),
    an unplaced cell is `0`. This is the `(List.range numCols).map (…(List.range numRows).map…)`
    assembly the five render modules each repeat, hoisted once. Every placement in bucket `row` has
    that row, so testing the COLUMN alone is the same test as testing the whole cell. -/
def toGrid (numCols numRows : Nat) (ps : List CellVal) : List (List Int) :=
  let idx := cellIndex numRows ps
  (List.range numCols).map (fun col =>
    (List.range numRows).map (fun row =>
      match (idx.getD row []).find? (fun p => p.1.col == col) with
      | some p => p.2
      | none => 0))

/-- **SPEC** of `toGrid`: the scanning definition — one `find?` over the whole placement list per
    cell. Kept as the differential reference `toGrid` is pinned against below. -/
def toGridSpec (numCols numRows : Nat) (ps : List CellVal) : List (List Int) :=
  (List.range numCols).map (fun col =>
    (List.range numRows).map (fun row =>
      match ps.find? (fun p => p.1 == (⟨row, col⟩ : Cell)) with
      | some p => p.2
      | none => 0))

/-- **COMPOSE** per-gate witnesses into one circuit witness grid — the combinator the step_main
    assembly needs: concatenate the gate contributions, lay them into the grid ONCE. -/
def compose (numCols numRows : Nat) (gs : List GateWitness) : List (List Int) :=
  toGrid numCols numRows gs.flatten

/-! ### The index changes nothing (the differential pin, and it can go red).

§2's `poseidonWitnessBuilt == poseidonWitness` already routes 180 cells through `toGrid` and pins
them byte-identical to the hand-rolled render module. These add what that module cannot reach: a
placement list long enough for the index to matter, cells placed OUTSIDE the grid, and every cell
placed TWICE with different values — so `toGrid`'s FIRST-WINS rule is observable, and reversing the
list (which flips which placement wins) is the RED control. -/

/-- 15 placements per row over `n` rows, columns spread `mod 17` (so some land outside the 15-column
    grid), then the whole list REPEATED with different values. -/
def gridProbeCells (n : Nat) : List CellVal :=
  let base := (List.range n).flatMap (fun r =>
    (List.range 15).map (fun c => ((⟨r, (c * 7 + r) % 17⟩ : Cell), (Int.ofNat (r * 15 + c)))))
  base ++ base.map (fun p => (p.1, p.2 + 1000))

-- ⚑ THE INDEX IS FAITHFUL — indexed and scanning grids are equal, cell for cell, including a
-- prepended override and a placement whose row is off the grid entirely.
#guard toGrid 15 40 (gridProbeCells 40) == toGridSpec 15 40 (gridProbeCells 40)
#guard toGrid 15 40 (((⟨3, 2⟩ : Cell), (-99 : Int)) :: ((⟨99, 0⟩ : Cell), (5 : Int))
                       :: gridProbeCells 40)
        == toGridSpec 15 40 (((⟨3, 2⟩ : Cell), (-99 : Int)) :: ((⟨99, 0⟩ : Cell), (5 : Int))
                               :: gridProbeCells 40)

-- ⚑ IT CAN GO RED. Reversing the placement list flips WHICH duplicate wins; if the index did not
-- preserve first-wins order the two would agree. They must not.
#guard (toGrid 15 40 (gridProbeCells 40) == toGridSpec 15 40 (gridProbeCells 40).reverse) == false
#guard (toGrid 15 40 (gridProbeCells 40).reverse == toGridSpec 15 40 (gridProbeCells 40)) == false

/-- Place a 3-lane field state `[v0,v1,v2]` into row `row`, columns `colBase, colBase+1, colBase+2`
    (a Poseidon `round_to_cols` block; also the generic "3 lanes of one EC coordinate" primitive). -/
def placeBlock (row colBase : Nat) (lanes : List Int) : GateWitness :=
  (List.range 3).map (fun j => ((⟨row, colBase + j⟩ : Cell), lanes.getD j 0))

/-! ## §2 — front-end A (advice / self-wired gates): reproduce `poseidonWitness` byte-identically.

The Poseidon witness has no copy wires — its state chains across rows through the gate's Curr/Next
reference — so it is pure DIRECT placement. The placement semantics is the `STATE_ORDER` column map;
the compute-fn is `laneI` (dregg's own `PastaPoseidon.Ref.permFrom`, imported read-only). We rebuild
the whole 15×12 grid through `compose` and pin it equal to the hand-rolled `poseidonWitness`. -/

/-- `STATE_ORDER = [0,2,3,4,1]` (o1js `poseidon.rs::round_to_cols`): round-slot `i`'s 3 lanes live at
    columns `STATE_ORDER[i]*3 .. +2`. -/
def poseidonStateOrder : List Nat := [0, 2, 3, 4, 1]
def poseidonRoundCol (i : Nat) : Nat := (poseidonStateOrder.getD i 0) * 3

/-- The `GateWitness` for ONE Poseidon gate row `r`: the 5 round-states `s(5r+i)` (`i=0..4`), each a
    3-lane block placed at `poseidonRoundCol i`. `state k j` = lane `j` of the k-th round state (the
    compute-fn is a PARAMETER; the placement is the fixed `STATE_ORDER` column map). -/
def poseidonRowWitness (state : Nat → Nat → Int) (r : Nat) : GateWitness :=
  (List.range 5).flatMap (fun i =>
    placeBlock r (poseidonRoundCol i) ((List.range 3).map (fun j => state (5 * r + i) j)))

/-- The closing `Zero`-gate row `r`: the permutation output `s(outRound)` in cols 0,1,2 (rest default 0). -/
def poseidonTailWitness (state : Nat → Nat → Int) (r outRound : Nat) : GateWitness :=
  placeBlock r 0 ((List.range 3).map (fun j => state outRound j))

/-- The WHOLE Poseidon circuit witness, COMPOSED from the 11 gate rows + the closing `Zero` row via
    `WitnessBuilder.compose` — makes NO reference to `poseidonWitness`'s hand-rolled `witAt`. -/
def poseidonWitnessBuilt : List (List Int) :=
  compose 15 12
    (((List.range 11).map (poseidonRowWitness laneI)) ++ [poseidonTailWitness laneI 11 55])

-- Structural: same 15×12 shape as the render module emits.
#guard poseidonWitnessBuilt.length == 15
#guard (poseidonWitnessBuilt.map (·.length)).all (· == 12)

-- ⚑ BYTE-IDENTICAL (the gate). The WitnessBuilder-composed grid equals
-- `KimchiRenderPoseidon.poseidonWitness` cell-for-cell — the abstraction reproduces the hand-rolled
-- witness (all 180 field-element cells, including the STATE_ORDER block permutation and the row-11
-- output tail) WITHOUT touching that module. Falsifiable: any placement/column-order drift diverges.
#guard poseidonWitnessBuilt == poseidonWitness

/-! ## §3 — front-end B (copied wires): COMPOSE two gates sharing a variable, consistently.

The property the step_main assembly needs and the per-gate fns cannot give: two gates sharing a copied
wire must hold ONE value across both cells (PLONK's copy-permutation σ). The composing front-end
`gateVarWitness` fills every permutation cell of a gate from a SHARED variable→value env, so a copied
variable is filled identically in every cell of its class — the constraint holds by construction, and
we pin it against `place`'s ACTUAL σ (`permPairs (circuitPositions …)`, the same permutation `place`
wires). -/

/-- A variable→value assignment (`External i` / `Internal i` ↦ its witness value). -/
abbrev VarEnv := List (PVar × Int)

def envLookup (env : VarEnv) (v : PVar) : Int :=
  match env.find? (fun p => p.1 == v) with
  | some p => p.2
  | none => 0

/-- **THE COMPOSING FRONT-END.** One gate's `GateWitness` at absolute row `absRow`: place each of its
    permutation-column variables' value (from the shared `env`) at that variable's cell. A variable
    shared with another gate is filled from the SAME env entry in BOTH — so the copy class is
    single-valued. `rowPositions` (read-only from `KimchiPlacement`) is the exact `{row,col}` map. -/
def gateVarWitness (absRow : Nat) (g : PGate) (env : VarEnv) : GateWitness :=
  (rowPositions absRow g.permVars).map (fun vc => (vc.2, envLookup env vc.1))

/-- Two generic gates sharing wire `x = external 0` ("gate A's output feeds gate B"), each with a
    private var. `x` occupies (0,0),(0,3) in gate A and (1,0) in gate B — a 3-cell copy class spanning
    both rows; `external 1`/`external 2` are per-gate singletons. -/
def gA : PGate :=
  { kind := .generic
  , permVars := [some (.external 0), some (.external 1), none, some (.external 0), none, none, none]
  , coeffs := [] }
def gB : PGate :=
  { kind := .generic
  , permVars := [some (.external 0), some (.external 2), none, none, none, none, none]
  , coeffs := [] }
def sharedGates : List PGate := [gA, gB]

/-- The witness values: the shared wire `x = 42`, gate A's private `= 7`, gate B's private `= 9`. -/
def sharedEnv : VarEnv := [(.external 0, 42), (.external 1, 7), (.external 2, 9)]

/-- Gate A's and gate B's witnesses, built INDEPENDENTLY from the shared env… -/
def gAWit : GateWitness := gateVarWitness 0 gA sharedEnv
def gBWit : GateWitness := gateVarWitness 1 gB sharedEnv

/-- …then COMPOSED into one grid. The shared wire `external 0` was filled from the SAME env in both,
    so its three cells agree. -/
def sharedGrid : List (List Int) := compose 15 2 [gAWit, gBWit]

-- The shared wire is CONSISTENT across the two gates: its cell in gate A and its cell in gate B both
-- carry 42, and they are equal (the smallest concrete "copy holds" pin).
#guard gridAt sharedGrid ⟨0, 3⟩ == 42
#guard gridAt sharedGrid ⟨1, 0⟩ == 42
#guard gridAt sharedGrid ⟨0, 3⟩ == gridAt sharedGrid ⟨1, 0⟩

/-- **THE COPY-PERMUTATION HOLDS (machine-checked, this circuit).** Every σ-linked pair of cells — σ
    being `place`'s ACTUAL permutation `permPairs (circuitPositions 0 sharedGates)` — holds the same
    value in the composed grid. This is the property the assembly climb needs: composing two gates
    that share a wire yields a witness satisfying the copy constraint. Non-vacuous: `external 0`'s
    class `{(0,0),(0,3),(1,0)}` contributes the cross-row pair `(0,3)↦(1,0)`. -/
theorem sharedGrid_copy_perm_holds :
    (permPairs (circuitPositions 0 sharedGates)).all
      (fun pr => gridAt sharedGrid pr.1 == gridAt sharedGrid pr.2) = true := by decide

/-! ### §3a — falsifiability: the copy-permutation check BITES. -/

/-- A hand-broken grid: the shared wire's gate-B cell forced to 99 instead of 42 (what a NON-composing
    per-gate fn that re-assigns the wire independently would produce). `toGrid` is first-wins, so the
    prepended override lands. -/
def brokenGrid : List (List Int) :=
  toGrid 15 2 ((⟨1, 0⟩, (99 : Int)) :: (gAWit ++ gBWit))

/-- **THE CHECK CAN GO RED.** With the shared wire inconsistent across the two gates, `place`'s σ
    links a `42` cell to a `99` cell — the copy-permutation constraint FAILS. So §3's `= true` is a
    real gate, not a tautology. -/
theorem brokenGrid_copy_perm_FAILS :
    (permPairs (circuitPositions 0 sharedGates)).all
      (fun pr => gridAt brokenGrid pr.1 == gridAt brokenGrid pr.2) = false := by decide

#assert_axioms sharedGrid_copy_perm_holds
#assert_axioms brokenGrid_copy_perm_FAILS

end Dregg2.Circuit.Emit.WitnessBuilder
