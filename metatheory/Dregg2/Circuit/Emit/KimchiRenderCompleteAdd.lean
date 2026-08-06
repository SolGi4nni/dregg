/-
# Dregg2.Circuit.Emit.KimchiRenderCompleteAdd — a REAL `complete_add` circuit, Lean-synthesized

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiCustomGates.mkCompleteAdd` is a `complete_add` ROW BUILDER taking the eleven witness columns
as arguments, and `KimchiVerify.completeAddConstraints` is the CHECKER — but **no function computed
the eleven cells (`x3 y3 inf same_x s inf_z x21_inv`) from the two input points P, Q.** This file
supplies that witness generator (`completeAddWitness`) and then does for `complete_add` exactly what
`KimchiRenderPoseidon` did for `Poseidon`: assemble the gate in Lean, place it with the byte-verified
`KimchiPlacement.place`, COMPUTE the witness IN LEAN (the affine `add_fast` cells over the Pallas base
field Fp), and render the JSON that the `pickles-curvegate-harness` Rust crate proves + verifies pure-
Rust. The `complete_add` gate is COEFF-FREE (`coeffs = []`, byte-exact vs o1js — trivially and
`custom-gate-diff.mjs`-confirmed), so binding is demonstrated by WITNESS tampers (a constrained cell
flip is rejected; an unconstrained-cell flip is accepted) rather than a coeff tamper.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** a Mina-valid proof. The
kimchi proof is an INNER proof; the reportable increment is that the Lean-authored `complete_add`
witness generator produces a witness that a pure-Rust kimchi prover ACCEPTS, whose output point is
`3·G_Pallas` (cross-checked against dregg's own independent Jacobian KAT `PastaCurve.Gp3`).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate (`caGates`), the placement (`place`, imported read-only
from `KimchiPlacement`), and the witness (`completeAddWitness`, computed from the affine group law over
`Fp` with a Lean `fInv` = Fermat modular inverse) are all authored in Lean. `proof-systems` is the Rust
PROVER that RUNS the artifact — it authors no constraint. The `CompleteAdd` gate's seven constraint
polynomials are `proof-systems`' fixed gate semantics (`complete_add.rs`); the SAME polynomials are
transcribed read-only in `KimchiVerify.completeAddConstraints` (the checker this witness answers to).

## The witness layout (transcribed from `complete_add.rs::verify_complete_add`, read-only)

Columns `x1 y1 x2 y2 x3 y3 inf same_x s inf_z x21_inv` = `w₀..w₁₀` (`complete_add.rs:5-7,240-250`).
For inputs P=(x₁,y₁), Q=(x₂,y₂):
  * `same_x = [x₁ = x₂]`; `s = (y₂−y₁)/(x₂−x₁)` if x₁≠x₂ else the doubling slope `3x₁²/(2y₁)`;
  * `x₃ = s² − x₁ − x₂`, `y₃ = s(x₁−x₃) − y₁` (both branches, since `s²=x₁+x₂+x₃` is unconditional);
  * `inf = [x₁=x₂ ∧ y₁≠y₂]` (the result is ∞ only when the x's agree but the y's do not);
  * `inf_z = 0` if y₁=y₂, else `1/(y₂−y₁)` if x₁=x₂, else 0 (`complete_add.rs:280-289`);
  * `x21_inv = 0` if x₁=x₂, else `1/(x₂−x₁)` (`complete_add.rs:291-299`).
The emitted circuit instantiates this at P=G, Q=[2]G (distinct x), so the row is the `add_fast` case
(same_x=0) and the output is [3]G.

## Axiom hygiene / build

NO `main` (roots cleanly into `PicklesSynthesis`; the emit driver is `EmitCompleteAddJson.lean`).
`#guard`s reduce in the interpreter; no `sorry`/`native_decide`. Imports `KimchiPlacement`
(place/PGate/PlacedGate/Cell/PVar), `KimchiCustomGates` (mkCompleteAdd, the checker re-export),
`PastaCurve` (Gp/Gp2/Gp3 KATs + `pN`).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.PastaCurve

namespace Dregg2.Circuit.Emit.KimchiRenderCompleteAdd

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson
open Dregg2.Circuit.Emit.KimchiVerify (completeAddConstraints)
open Dregg2.Circuit.Emit.PastaCurve (Gp Gp2 Gp3)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §1 — the Pallas base field `Fp` arithmetic (`ZMod pN`, computed on `Nat`). -/

/-- `Fp` addition. -/
def fAdd (x y : Nat) : Nat := (x + y) % pN
/-- `Fp` subtraction (`x − y`, kept in `[0,pN)`). -/
def fSub (x y : Nat) : Nat := (x + pN - y % pN) % pN
/-- `Fp` multiplication. -/
def fMul (x y : Nat) : Nat := (x * y) % pN

/-- Square-and-multiply modular exponentiation (`fuel` bounds the exponent bit-length; `pN−2 < 2²⁵⁵`
so 260 is ample). -/
private def modPowAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | (fuel + 1), base, e, acc =>
      if e == 0 then acc
      else
        let acc' := if e % 2 == 1 then (acc * base) % m else acc
        modPowAux m fuel ((base * base) % m) (e / 2) acc'

/-- **`fInv`** — the `Fp` multiplicative inverse via Fermat (`a^(p−2) mod p`), `pN` prime. -/
def fInv (a : Nat) : Nat := modPowAux pN 260 (a % pN) (pN - 2) 1

/-- The affine `add_fast` slope `(y₂−y₁)·inv` at an ALREADY-COMPUTED `inv = (x₂−x₁)⁻¹`. ⚑ Split out
so `completeAddWitness` can share the one inverse with the `x21_inv` cell it also has to store — see
its note. `addSlope` is this at `inv = fInv (fSub x2 x1)`, so there is one formula and one body. -/
def addSlopeWithInv (y1 y2 inv : Nat) : Nat := fMul (fSub y2 y1) inv
/-- The affine `add_fast` slope `(y₂−y₁)/(x₂−x₁)` (distinct-x case). -/
def addSlope (x1 y1 x2 y2 : Nat) : Nat := addSlopeWithInv y1 y2 (fInv (fSub x2 x1))
/-- The doubling slope `3x₁²/(2y₁)`. -/
def dblSlope (x1 y1 : Nat) : Nat := fMul (fMul 3 (fMul x1 x1)) (fInv (fMul 2 y1))

/-! ## §2 — the `complete_add` witness generator (the piece this file adds). -/

/-- **`completeAddWitness P Q`** — the eleven `complete_add` cells `[x₁,y₁,x₂,y₂,x₃,y₃,inf,same_x,s,
inf_z,x21_inv]` for P=(x₁,y₁), Q=(x₂,y₂), computed exactly per `complete_add.rs::verify_complete_add`
(so proof-systems' prover accepts the row). Handles all three cases (add / double / result-∞). -/
def completeAddWitness (x1 y1 x2 y2 : Nat) : List Nat :=
  let sameX := if x1 == x2 then 1 else 0
  -- ⚑ **ONE `fInv` ON `x₂ − x₁`, NOT TWO.** `addSlope`'s divisor and the stored `x21_inv` cell are
  -- the SAME inverse, and each one is a 255-squaring Fermat exponentiation — the single most
  -- expensive primitive in the whole assembly. The `x₁ = x₂` branch still computes none of it.
  let x21Inv := if x1 == x2 then 0 else fInv (fSub x2 x1)
  let s := if x1 == x2 then dblSlope x1 y1 else addSlopeWithInv y1 y2 x21Inv
  let x3 := fSub (fSub (fMul s s) x1) x2
  let y3 := fSub (fMul s (fSub x1 x3)) y1
  let inf := if x1 == x2 && y1 != y2 then 1 else 0
  let infZ := if y1 == y2 then 0 else if x1 == x2 then fInv (fSub y2 y1) else 0
  [x1, y1, x2, y2, x3, y3, inf, sameX, s, infZ, x21Inv]

/-- Affine point doubling (used only to build the second input point [2]G). -/
def dbl (P : Nat × Nat) : Nat × Nat :=
  let s := dblSlope P.1 P.2
  let x3 := fSub (fSub (fMul s s) P.1) P.1
  let y3 := fSub (fMul s (fSub P.1 x3)) P.2
  (x3, y3)

/-- The two input points: P = the Pallas generator G, Q = [2]G. Their x-coordinates differ, so the
emitted row is the `add_fast` (same_x = 0) case, matching the o1js `Group.generator.add(…)` oracle. -/
def P : Nat × Nat := Gp
def Q : Nat × Nat := dbl Gp

/-- The eleven cells for G + [2]G = [3]G. -/
def caCells : List Nat := completeAddWitness P.1 P.2 Q.1 Q.2

/-! ## §3 — the circuit, authored in Lean and placed by `place`. -/

/-- Seven unwired permutation columns ⇒ `place` emits identity self-wires (a standalone `complete_add`
reads its own row's cells directly; no copy constraint to other rows is needed). -/
def sevenNones : List (Option PVar) := List.replicate 7 none

/-- The Lean-authored circuit: one `CompleteAdd` gate (coeff-free) + one closing `Zero` gate. -/
def caGates : List PGate :=
  [ { kind := .completeAdd, permVars := sevenNones, coeffs := [] }
  , { kind := .zero,        permVars := sevenNones, coeffs := [] } ]

/-- The placed circuit (identity σ). -/
def caPlaced : List PlacedGate := place 0 caGates

/-- Column `col`, row `row` of the 15×2 witness grid: row 0 holds the eleven `complete_add` cells in
cols 0..10 (cols 11..14 = 0), row 1 (the `Zero` gate) is all zero. -/
def cellAt (col row : Nat) : Int :=
  if row == 0 then (caCells.getD col 0 : Int) else 0

/-- The Lean-computed witness: 15 columns × 2 rows. -/
def caWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range 2).map (fun row => cellAt col row))

/-! ## §4 — the JSON renderer (same shape `KimchiRenderPoseidon` emits; the harness parses it). -/


/-! ⚑ **ONE RENDERER.** The copy of `renderCircuit` this module carried — one of eleven, each with
its own private `q`/`qt`/`qs`, `renderCell`, `renderWires`, `renderIntList`, `renderGate`,
`renderGates`, `renderWitness` — is DELETED. `KimchiCircuitJson.renderCircuit` is a pure function of
a `KimchiCircuit` VALUE, and `renderCircuit_base_is_the_open_coded_shape` pins over EVERY argument
that it emits the chain the deleted copy emitted. -/

/-- The rendered `complete_add` circuit JSON (0 public inputs, 2 rows). -/
def completeAddJson : String :=
  renderCircuit { name := "completeAddGp_plus_2Gp", pubSize := 0, numRows := 2
                , gates := caPlaced, witness := caWitness }

/-! ## §5 — the in-CI pins (`#guard`; interpreter-reduced). -/

-- Structural: 2 gates (CompleteAdd + Zero), 7 wires each, 11 witness cells, 15×2 grid.
#guard caGates.length == 2
#guard caPlaced.length == 2
#guard (caPlaced.map (fun g => g.wires.length)).all (· == 7)
#guard caCells.length == 11
#guard caWitness.length == 15
#guard (caWitness.map (·.length)).all (· == 2)

-- typ + coeffs byte-exact vs o1js: CompleteAdd (ordinal 3) carrying NO coefficients; Zero (ordinal 0).
#guard (caPlaced.headD default).kind.ordinal == 3
#guard ((caPlaced.headD default).coeffs).length == 0
#guard (caPlaced.getD 1 default).kind.ordinal == 0

-- The `add_fast` (distinct-x) case: same_x = 0, inf = 0.
#guard caCells.getD 7 0 == 0   -- same_x
#guard caCells.getD 6 0 == 0   -- inf
#guard caCells.getD 9 0 == 0   -- inf_z (y₁ ≠ y₂ branch)

-- `x21_inv` really is the inverse of `x₂ − x₁`: `x21_inv · (x₂ − x₁) ≡ 1 (mod p)`.
#guard fMul (caCells.getD 10 0) (fSub Q.1 P.1) == 1

-- ⚑ The OUTPUT point (x₃,y₃) = caCells[4,5] is ON the Pallas curve `y² = x³ + 5`.
#guard fMul (caCells.getD 5 0) (caCells.getD 5 0)
        == fAdd (fMul (caCells.getD 4 0) (fMul (caCells.getD 4 0) (caCells.getD 4 0))) 5

-- ⚑ CHECKER-AS-ORACLE: the output equals [3]G, cross-checked against dregg's INDEPENDENT Jacobian KAT
-- `PastaCurve.Gp3` (an entirely separate computation), via the projective relation
-- `x₃·Z² ≡ X`, `y₃·Z³ ≡ Y (mod p)` for the Jacobian point `Gp3 = (X,Y,Z)`.
#guard fMul (caCells.getD 4 0) (fMul Gp3.2.2 Gp3.2.2) == Gp3.1 % pN
#guard fMul (caCells.getD 5 0) (fMul Gp3.2.2 (fMul Gp3.2.2 Gp3.2.2)) == Gp3.2.1 % pN

-- And the intermediate [2]G matches dregg's Jacobian KAT `Gp2` (validates `dbl`, hence the whole chain).
#guard fMul Q.1 (fMul Gp2.2.2 Gp2.2.2) == Gp2.1 % pN
#guard fMul Q.2 (fMul Gp2.2.2 (fMul Gp2.2.2 Gp2.2.2)) == Gp2.2.1 % pN

-- ⚑ NON-VACUITY IN LEAN: the emitted row satisfies the SAME seven-constraint checker the real proof
-- uses (`completeAddConstraints`, imported read-only from `KimchiVerify`), evaluated over `ZMod pN`.
#guard (completeAddConstraints (R := ZMod pN) (caCells.map (fun n => (n : ZMod pN)))).all
        (fun z => decide (z = 0))

end Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
