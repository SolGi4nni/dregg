/-
# Dregg2.Circuit.Emit.KimchiRender — render a Lean-PLACED circuit to a proof-systems gate list (R4a)

## ⚑ THE RUNG THIS IS (R4a), AND WHAT IT IS NOT

R1 (`KimchiPlacement`) made the copy-permutation `wires` byte-exact vs o1js; `KimchiCustomGates`
made `typ`+`coeffs` byte-exact. **This file is the RENDER**: it turns `KimchiPlacement.place`'s
`List PlacedGate` (each gate's `typ` ordinal, seven `{row,col}` copy-permutation wires, and generic
coefficients) plus a Lean-emitted application witness into the concrete JSON the pure-Rust kimchi
prover (`proof-systems` tag 0.3.0) consumes at its `make_prover_index` / `ConstraintSystem::create`
front door. The companion Rust harness (`pickles-r4-harness`) reads this JSON, builds the
`Vec<CircuitGate>` + `[Vec<Fp>; 15]` witness, and PROVES + VERIFIES it.

This is **Phase A / R4a**: it demonstrates that a **LEAN-SYNTHESIZED** circuit (gates+wires+coeffs
authored in Lean, placed by Lean's byte-verified `place`, emitted from Lean) is a REAL, provable,
binding kimchi circuit. It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", and
**NOT** a Mina-valid Pickles proof (that is R4b — the step/wrap wrap, gated on the retarget-fork; the
kimchi proof here is an INNER proof, not a Pickles-recursion proof).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The circuit (`bindingGates`), its placement (`place`, imported
read-only from `KimchiPlacement`), its coefficients, and its witness are all authored/derived in
Lean. `proof-systems` is the Rust PROVER that RUNS the Lean-emitted artifact — it authors no
constraint. The generic-gate constraint polynomial `c₀·w₀+c₁·w₁+c₂·w₂+c₃·w₀·w₁+c₄` is
`proof-systems`' fixed gate semantics (`generic.rs`); choosing the coefficients IS the synthesis.

## The binding circuit (SMALLEST provable Lean-placed circuit that BINDS)

Case A / case B (`KimchiPlacement`) are the byte-golden WIRE cases but carry `coeffs = []` — a
generic gate with all-zero coefficients is vacuously satisfied, so it cannot demonstrate binding
(a tamper would be accepted). This file therefore ALSO renders case A / case B purely as a
render-fidelity check (the emitted `placed_wires` must equal the o1js `o1js_wires` goldens, checked
in Rust), and uses a SEPARATE circuit — placed by the SAME `place` pass — that carries real
coefficients for the prove/verify/tamper milestone:

  * `a = external 0`, `b = external 1`, `p = internal 0`.
  * Row 0 (`Mul`): coeffs `[0,0,-1,1,0, 0,0,0,0,0]` ⇒ `p = a·b`  (`c₂·w₂ + c₃·w₀·w₁ = -p + a·b = 0`).
  * Row 1 (`Const 35`): coeffs `[1,0,0,0,-35, 0,0,0,0,0]` ⇒ `w₀ = 35`  (`c₀·w₀ + c₄ = p - 35 = 0`).
  * `p` is wired (copy-permutation) across `(0,2)`, `(1,0)`, `(1,3)`: gate 0 computes it, gate 1
    constrains it to 35, and `(1,3)` is a FREE copy target (the generic gate does not read col 3),
    so a tamper of `(1,3)` is caught ONLY by the permutation — proving the R1 placement wires are
    load-bearing in a real proof, not just byte-diffed.

## Axiom hygiene / build
This is a SCRATCH executable (like `EmitAllJson`): run it with
`lake env lean --run Dregg2/Circuit/Emit/KimchiRender.lean` (after `lake build
Dregg2.Circuit.Emit.KimchiPlacement`). It imports `KimchiPlacement` only.
-/
import Dregg2.Circuit.Emit.KimchiPlacement

namespace Dregg2.Circuit.Emit.KimchiRender

open Dregg2.Circuit.Emit.KimchiPlacement

set_option autoImplicit false

/-! ## §1 — the binding circuit, authored in Lean and placed by `place`. -/

/-- The Lean-authored binding circuit: `p = a·b` (row 0, `Mul`) ∧ `p = 35` (row 1, `Const 35`),
with `p` copy-wired across both rows plus a free copy cell `(1,3)`. Ten generic coefficients per
gate (`GENERIC_COEFFS·2 = 10`, `generic.rs`). -/
def bindingGates : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.internal 0), none, none, none, none]
    , coeffs := [0, 0, -1, 1, 0,  0, 0, 0, 0, 0] }
  , { kind := .generic
    , permVars := [some (.internal 0), none, none, some (.internal 0), none, none, none]
    , coeffs := [1, 0, 0, 0, -35,  0, 0, 0, 0, 0] } ]

/-- The placed circuit — `place`'s byte-verified copy-permutation pass applied to `bindingGates`. -/
def bindingPlaced : List PlacedGate := place 0 bindingGates

/-- **CONTROL circuit** for the copy-permutation binding claim: identical to `bindingGates` EXCEPT
the free cell `(1,3)` now holds a FRESH variable (`external 2`) instead of `p`, so `(1,3)` is no
longer copy-wired — it is a singleton the generic gate does not read, hence UNCONSTRAINED. `p`
stays constrained (`(0,2)↔(1,0)`, `p = a·b = 35`). The harness proves: the SAME flip of `(1,3)`
that the copy circuit REJECTS is ACCEPTED here — so the rejection above is the placement WIRE
binding, nothing else. -/
def noCopyGates : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.internal 0), none, none, none, none]
    , coeffs := [0, 0, -1, 1, 0,  0, 0, 0, 0, 0] }
  , { kind := .generic
    , permVars := [some (.internal 0), none, none, some (.external 2), none, none, none]
    , coeffs := [1, 0, 0, 0, -35,  0, 0, 0, 0, 0] } ]

def noCopyPlaced : List PlacedGate := place 0 noCopyGates

/-- The Lean-emitted application witness (Route-B style): 15 columns × 2 rows, `a=5, b=7, p=35`.
`col0=[a,p]=[5,35]`, `col1=[b,_]=[7,0]`, `col2=[p,_]=[35,0]`, `col3=[_,p]=[0,35]`, cols 4..14 = 0.
Satisfies both gate constraints and every copy: `p` is 35 at `(0,2)`, `(1,0)`, `(1,3)`. -/
def bindingWitness : List (List Int) :=
  [ [5, 35], [7, 0], [35, 0], [0, 35],
    [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0] ]

/-! ## §2 — the JSON renderer (brace literals kept out of `s!` interpolation). -/

private def q (s : String) : String := "\"" ++ s ++ "\""

private def renderCell (c : Cell) : String :=
  "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"

private def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"

private def renderWireList (wss : List (List Cell)) : String :=
  "[" ++ String.intercalate "," (wss.map renderWires) ++ "]"

/-- Coefficients/witness values are emitted as DECIMAL STRINGS (signed) so the Rust side reduces
them into `Fp` losslessly regardless of magnitude/sign. -/
private def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => q (toString i))) ++ "]"

private def renderGate (g : PlacedGate) : String :=
  "{" ++ q "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ q "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ q "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"

private def renderGates (gs : List PlacedGate) : String :=
  "[" ++ String.intercalate "," (gs.map renderGate) ++ "]"

private def renderWitness (w : List (List Int)) : String :=
  "[" ++ String.intercalate "," (w.map renderIntList) ++ "]"

/-- A provable circuit: name, public-input size, row count, placed gates, witness columns. -/
def renderCircuit (name : String) (pubSize numRows : Nat)
    (gs : List PlacedGate) (w : List (List Int)) : String :=
  "{" ++ q "name" ++ ":" ++ q name ++ ","
       ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
       ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
       ++ q "gates" ++ ":" ++ renderGates gs ++ ","
       ++ q "witness" ++ ":" ++ renderWitness w ++ "}"

/-- A wire-fidelity check object: the render's `placed_wires` (from `place`) vs the o1js `o1js_wires`
golden. The Rust harness parses both and asserts equality — a differential that the render
(Lean → JSON → Rust parse) did not corrupt the byte-exact placement. -/
def renderWireCheck (name : String) (placed o1js : List (List Cell)) : String :=
  "{" ++ q "name" ++ ":" ++ q name ++ ","
       ++ q "placed_wires" ++ ":" ++ renderWireList placed ++ ","
       ++ q "o1js_wires" ++ ":" ++ renderWireList o1js ++ "}"

end Dregg2.Circuit.Emit.KimchiRender

/-! ## §3 — emit (top-level `main`, as `lake env lean --run` requires). -/

open Dregg2.Circuit.Emit.KimchiPlacement in
open Dregg2.Circuit.Emit.KimchiRender in
def main : IO Unit := do
  let dir := "/tmp/pickles-r4"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/binding.json")
    (renderCircuit "bindingMulConst" 0 2 bindingPlaced bindingWitness)
  IO.FS.writeFile (dir ++ "/nocopy.json")
    (renderCircuit "noCopyControl" 0 2 noCopyPlaced bindingWitness)
  IO.FS.writeFile (dir ++ "/caseA.json")
    (renderWireCheck "caseA" ((place 0 caseA).map (·.wires)) caseA_o1js)
  IO.FS.writeFile (dir ++ "/caseB.json")
    (renderWireCheck "caseB" ((place 0 caseB).map (·.wires)) caseB_o1js)
  IO.println "KimchiRender: wrote /tmp/pickles-r4/{binding,caseA,caseB}.json"
