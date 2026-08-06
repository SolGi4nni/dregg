/-
# Dregg2.Circuit.Emit.KimchiComposeMSM — the FIRST MULTI-gate composition with a CROSS-gate copy wire

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

Every prior Pickles-synthesis rung proved a SINGLE-gate circuit: `KimchiRenderCompleteAdd`,
`KimchiRenderVarBaseMul`, … each assemble ONE custom gate (plus its closing `Zero`), place it with the
byte-verified `KimchiPlacement.place`, witness it in Lean, and a pure-Rust kimchi prover accepts. What
NO single-gate circuit ever exercised is the thing the whole `step_main` assembly rests on: **a
variable computed in one gate's row COPIED, via the copy-permutation (σ), into another gate's row** —
cross-gate wiring, not intra-gate.

This file assembles the smallest REAL `step_main` fragment that has one: **a 2-step MSM accumulation**
— `var_base_mul` produces an output point `[n]·T` at its `Next` row cols 0,1 (`x5,y5`,
`varbasemul.rs:61-64`), and a `complete_add` consumes that SAME point as its first input `(x1,y1)`
(the accumulator update `acc ← acc + [n]·T`, the literal heart of the in-circuit MSM the kimchi
verifier runs). The var_base_mul output cell and the complete_add input cell are placed into ONE
equivalence class by `place`, so σ wires them together. That wire is the whole point.

The composition reuses the sibling render modules READ-ONLY: `KimchiRenderVarBaseMul` supplies the
two-row var_base_mul grid + its output point `(accX 5, accY 5)`; `KimchiRenderCompleteAdd` supplies the
`completeAddWitness` generator. This file authors only the CROSS-GATE PLACEMENT (the `PGate` list whose
`permVars` share `V_x`/`V_y` across three rows) and the fused witness grid.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** a Mina-valid proof. The
reportable increment is that the byte-exact single-gate emitters COMPOSE into a multi-gate circuit a
pure-Rust kimchi prover accepts, and — proved in the `pickles-compose-harness` — whose cross-gate σ
GENUINELY BINDS: desyncing the shared value in one row is rejected by the wiring, not merely a gate.

## ⚑ THE CLEAN WIRING PROBE (why there is a trailing `Zero` carrying the output point)

The real MSM wire is `x5 : (1,0) ↔ (2,0)` (var_base_mul output ↔ complete_add input). Both endpoints
are ALSO gate-constrained (var_base_mul reads its Next row; complete_add reads `x1`), so a single-cell
flip of either is rejected by a GATE as well as by σ — it cannot ISOLATE the wiring. To isolate it, the
shared output point is also materialized in the circuit's standard trailing `Zero` row (row 3, cols
0,1) and placed into the SAME class: `x5`'s class is `{(1,0),(2,0),(3,0)}`. The `Zero` gate reads
nothing and no other gate reads row 3, so cell `(3,0)` is constrained by σ AND BY NOTHING ELSE. The
harness flips `(3,0)` — rejected ⟹ the rejection is the copy-permutation, full stop. The companion
`composeUnwired` circuit (row 3 NOT placed into the class) is the control: the SAME `(3,0)` flip is
ACCEPTED there, proving the wired rejection is the WIRE, not adjacency.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gates, the cross-gate placement (`place`, imported read-only),
and the witness are authored in Lean. `proof-systems` RUNS the artifact and authors no constraint. The
`VarBaseMul`/`CompleteAdd` constraint polynomials are proof-systems' fixed gate semantics; the SAME
polynomials are transcribed read-only in `KimchiVerify` (the checkers the `#guard`s below answer to).

## Axiom hygiene / build

NO `main` (roots cleanly into `PicklesSynthesis`; the emit driver is `EmitComposeMsmJson.lean`).
`#guard`s reduce in the interpreter; no `sorry`/`native_decide`. Imports `KimchiPlacement`,
`KimchiRenderVarBaseMul` + `KimchiRenderCompleteAdd` (read-only reuse), `KimchiVerify` (the checkers),
`PastaCurve` (`Gp`, `pN`).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve

namespace Dregg2.Circuit.Emit.KimchiComposeMSM

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (currRow nextRow accX accY)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiVerify (varBaseMulConstraints completeAddConstraints)
open Dregg2.Circuit.Emit.PastaCurve (Gp)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §1 — the shared variables and the two addends.

`V_x`/`V_y` are the copy-permutation variables carrying the var_base_mul OUTPUT point across rows 1
(its `Next` row), 2 (the complete_add input), and 3 (the trailing `Zero`). The second complete_add
addend `S = G` is the (fixed) accumulator; the emitted row is the `add_fast` (distinct-x) case. -/

/-- The shared output-point x variable (the copy-permutation cycle `{(1,0),(2,0),(3,0)}`). -/
def V_x : PVar := .external 0
/-- The shared output-point y variable (the copy-permutation cycle `{(1,1),(2,1),(3,1)}`). -/
def V_y : PVar := .external 1

/-- The var_base_mul OUTPUT point `[n]·T = acc₅` (its `Next` row cols 0,1 = `x5,y5`). -/
def outX : Nat := accX 5
def outY : Nat := accY 5

/-- The second complete_add addend `S` — the accumulator being updated. `G` (distinct-x from the
output point, so the row is the `add_fast` case). -/
def S : Nat × Nat := Gp

/-- The eleven complete_add cells for `(x5,y5) + S`: `x1 = outX`, `y1 = outY` (the SHARED input),
`x2,y2 = S`, then `x3,y3,inf,same_x,s,inf_z,x21_inv`. -/
def caCells2 : List Nat := completeAddWitness outX outY S.1 S.2

/-! ## §2 — the WIRED circuit: var_base_mul (rows 0–1) → complete_add (row 2), trailing Zero (row 3).

Row 0 is the `VarBaseMul` gate (reads Curr+Next); row 1 its `Next` `Zero` row (holds `x5,y5` at cols
0,1); row 2 the `CompleteAdd` (reads only itself); row 3 the trailing `Zero` (read by NOTHING). The
shared `V_x`/`V_y` sit in cols 0,1 of rows 1,2,3 → each a 3-cycle under σ. -/

def sharedHead : List (Option PVar) := [some V_x, some V_y, none, none, none, none, none]
def sevenNones : List (Option PVar) := List.replicate 7 none

/-- The Lean-authored WIRED circuit. -/
def composeGates : List PGate :=
  [ { kind := .varBaseMul, permVars := sevenNones, coeffs := [] }   -- row 0: VBSM
  , { kind := .zero,       permVars := sharedHead, coeffs := [] }   -- row 1: Next (x5,y5 shared)
  , { kind := .completeAdd, permVars := sharedHead, coeffs := [] }  -- row 2: acc ← acc + [n]T
  , { kind := .zero,       permVars := sharedHead, coeffs := [] } ] -- row 3: trailing Zero (probe)

/-- The placed WIRED circuit (σ = the three cross-gate 3-cycles + self-wires). -/
def composePlaced : List PlacedGate := place 0 composeGates

/-! ### §2a — the UNWIRED control: identical EXCEPT row 3 is NOT in the shared class.

Row 3's cols 0,1 become unplaced (`none`), so `x5`'s class shrinks to `{(1,0),(2,0)}` and `(3,0)`
self-wires. The witness is UNCHANGED (row 3 still holds `x5,y5`), so its honest proof still verifies —
but flipping `(3,0)` is now ACCEPTED (no gate, no σ cycle). This is the "just adjacent, not wired"
control the wired `(3,0)` rejection is measured against. -/
def composeGatesUnwired : List PGate :=
  [ { kind := .varBaseMul, permVars := sevenNones, coeffs := [] }
  , { kind := .zero,       permVars := sharedHead, coeffs := [] }
  , { kind := .completeAdd, permVars := sharedHead, coeffs := [] }
  , { kind := .zero,       permVars := sevenNones, coeffs := [] } ]  -- row 3 NOT shared

def composePlacedUnwired : List PlacedGate := place 0 composeGatesUnwired

/-! ## §3 — the fused witness grid (15 columns × 4 rows).

Rows 0,1 are the var_base_mul grid VERBATIM (`currRow`/`nextRow`); row 2 the complete_add cells; row 3
the trailing `Zero` holding the output point in cols 0,1 (the σ probe) and 0 elsewhere. Because
`caCells2[0] = outX = nextRow[0]` and `caCells2[1] = outY = nextRow[1]`, every cell of each shared
class holds the SAME value in the honest witness — σ is satisfied. -/
def cellAt (col row : Nat) : Int :=
  if row == 0 then (currRow.getD col 0 : Int)
  else if row == 1 then (nextRow.getD col 0 : Int)
  else if row == 2 then (caCells2.getD col 0 : Int)
  else (if col == 0 then (outX : Int) else if col == 1 then (outY : Int) else 0)

/-- The Lean-computed witness: 15 columns × 4 rows. Shared by the wired + unwired circuits. -/
def composeWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range 4).map (fun row => cellAt col row))

/-! ## §4 — the JSON renderer (same shape the sibling `KimchiRender*` modules emit; the harness parses it). -/



/-! ⚑ **ONE RENDERER.** The copy of `renderCircuit` this module carried — one of eleven, each with
its own private `q`/`qt`/`qs`, `renderCell`, `renderWires`, `renderIntList`, `renderGate`,
`renderGates`, `renderWitness` — is DELETED. `KimchiCircuitJson.renderCircuit` is a pure function of
a `KimchiCircuit` VALUE, and `renderCircuit_base_is_the_open_coded_shape` pins over EVERY argument
that it emits the chain the deleted copy emitted. -/

/-- The rendered WIRED composed circuit (0 public inputs, 4 rows). -/
def composeMsmJson : String :=
  renderCircuit { name := "composeMsm_vbm_then_add", pubSize := 0, numRows := 4
                , gates := composePlaced, witness := composeWitness }
/-- The rendered UNWIRED control circuit (row 3 not shared). -/
def composeMsmUnwiredJson : String :=
  renderCircuit { name := "composeMsm_vbm_then_add_UNWIRED", pubSize := 0, numRows := 4
                , gates := composePlacedUnwired, witness := composeWitness }

/-! ## §5 — the in-CI pins (`#guard`; interpreter-reduced). -/

-- Structural: 4 gates, 7 wires each, 15×4 witness grid.
#guard composeGates.length == 4
#guard composePlaced.length == 4
#guard (composePlaced.map (fun g => g.wires.length)).all (· == 7)
#guard composeWitness.length == 15
#guard (composeWitness.map (·.length)).all (· == 4)

-- typ byte-exact vs o1js ordinals: VarBaseMul(4), Zero(0), CompleteAdd(3), Zero(0).
#guard (composePlaced.getD 0 default).kind.ordinal == 4
#guard (composePlaced.getD 1 default).kind.ordinal == 0
#guard (composePlaced.getD 2 default).kind.ordinal == 3
#guard (composePlaced.getD 3 default).kind.ordinal == 0

-- ⚑ THE CROSS-GATE COPY-PERMUTATION (the property this rung establishes on the Lean side).
-- `x5`'s class `{(1,0),(2,0),(3,0)}` is the 3-cycle (1,0)→(2,0)→(3,0)→(1,0); `y5`'s is the col-1 twin.
-- The FULL placed wires of rows 1,2,3 (col 0,1 crossing gate rows; cols 2..6 self-wired):
#guard (composePlaced.getD 1 default).wires
        == [⟨2,0⟩, ⟨2,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,5⟩, ⟨1,6⟩]   -- vbm Next → complete_add
#guard (composePlaced.getD 2 default).wires
        == [⟨3,0⟩, ⟨3,1⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,6⟩]   -- complete_add → trailing Zero
#guard (composePlaced.getD 3 default).wires
        == [⟨1,0⟩, ⟨1,1⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨3,6⟩]   -- trailing Zero → back to vbm Next (cycle closes)
-- Row 0 (VarBaseMul) is all self-wired (it shares no variable).
#guard (composePlaced.getD 0 default).wires
        == [⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨0,4⟩, ⟨0,5⟩, ⟨0,6⟩]

-- ⚑ THE UNWIRED CONTROL differs in EXACTLY the probe cells: `x5`'s class is `{(1,0),(2,0)}` (a 2-cycle),
-- and row 3 self-wires — so `(3,0)` is in NO σ cycle. Everything else is identical.
#guard (composePlacedUnwired.getD 1 default).wires
        == [⟨2,0⟩, ⟨2,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,5⟩, ⟨1,6⟩]
#guard (composePlacedUnwired.getD 2 default).wires
        == [⟨1,0⟩, ⟨1,1⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,6⟩]   -- 2-cycle closes at row 1 (no row 3 hop)
#guard (composePlacedUnwired.getD 3 default).wires
        == [⟨3,0⟩, ⟨3,1⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨3,6⟩]   -- ALL self — (3,0) unconstrained by σ

-- ⚑ THE COMPOSITION SEMANTICS: the complete_add's first input IS the var_base_mul output, cell-for-cell.
#guard caCells2.getD 0 0 == outX          -- complete_add x1 = var_base_mul x5
#guard caCells2.getD 1 0 == outY          -- complete_add y1 = var_base_mul y5
#guard nextRow.getD 0 0 == outX           -- var_base_mul Next row really holds x5 at col 0
#guard nextRow.getD 1 0 == outY
-- The honest witness makes every shared cell equal (σ is satisfiable): (1,0)=(2,0)=(3,0)=outX.
#guard cellAt 0 1 == (outX : Int) && cellAt 0 2 == (outX : Int) && cellAt 0 3 == (outX : Int)
#guard cellAt 1 1 == (outY : Int) && cellAt 1 2 == (outY : Int) && cellAt 1 3 == (outY : Int)

-- The `add_fast` (distinct-x) case: same_x = 0, inf = 0 (the two addends have different x).
#guard caCells2.getD 7 0 == 0             -- same_x
#guard caCells2.getD 6 0 == 0             -- inf
#guard caCells2.getD 2 0 == S.1 && caCells2.getD 3 0 == S.2   -- second addend is S = G

-- The complete_add OUTPUT (x3,y3) is ON the Pallas curve `y² = x³ + 5`.
#guard ((caCells2.getD 5 0) * (caCells2.getD 5 0)) % pN
        == (((caCells2.getD 4 0) * (caCells2.getD 4 0) % pN) * (caCells2.getD 4 0) % pN + 5) % pN

-- ⚑ NON-VACUITY IN LEAN, both gates: the fused rows satisfy the SAME checkers the real proof uses
-- (`varBaseMulConstraints`, `completeAddConstraints`, imported read-only from `KimchiVerify`), over ZMod pN.
#guard (varBaseMulConstraints (R := ZMod pN)
          (currRow.map (fun n => (n : ZMod pN))) (nextRow.map (fun n => (n : ZMod pN)))).all
        (fun z => decide (z = 0))
#guard (completeAddConstraints (R := ZMod pN) (caCells2.map (fun n => (n : ZMod pN)))).all
        (fun z => decide (z = 0))

end Dregg2.Circuit.Emit.KimchiComposeMSM
