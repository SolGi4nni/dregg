/-
# Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar — a REAL `endo_mul_scalar` circuit, Lean-synthesized

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiVerify.endomulScalarConstraints` is the CHECKER for the `EndoMulScalar` gate (the scalar-side
crumb/nybble decode used by `to_field_checked`); this file supplies the missing WITNESS generator and,
like `KimchiRenderPoseidon`/`KimchiRenderCompleteAdd`, assembles the gate in Lean, places it with
`KimchiPlacement.place`, COMPUTES the witness grid IN LEAN, and renders the JSON the
`pickles-curvegate-harness` proves + verifies pure-Rust. The gate is COEFF-FREE (`coeffs = []`,
byte-exact vs o1js), so binding is a WITNESS tamper (a constrained cell flip rejected; an unconstrained
flip accepted).

`EndoMulScalar` is the SIMPLEST of the three curve-multiplication gates: its witness is pure
scalar-field folds — NO elliptic-curve points, NO field inverses. One row decodes 16 scalar bits as 8
two-bit "crumbs" and folds three accumulators (`endomul_scalar.rs:227-288`, read-only):
  * `n₈ = fold(n₀=0): acc ↦ 4·acc + xⱼ`  (the reconstructed scalar; NB **4·**, not 2· — each xⱼ is a
    2-bit crumb; the Rust doc comment's `2·` is a known typo, the code does `double().double()`),
  * `a₈ = fold(a₀=2): acc ↦ 2·acc + c(xⱼ)`, `b₈ = fold(b₀=2): acc ↦ 2·acc + d(xⱼ)`,
where `c`/`d` are the crumb lookup tables `c: 0↦0 1↦0 2↦−1 3↦1`, `d: 0↦−1 1↦1 2↦0 3↦0`
(`endomul_scalar.rs:290-318`). The `endo_scalar` constant enters ONLY the discarded return value
`a·endo + b` (`endomul_scalar.rs:287`), never a witness cell, so no cell depends on it.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** Mina-valid. The kimchi
proof is an INNER proof; the reportable increment is that the Lean `endo_mul_scalar` witness generator
produces a grid a pure-Rust kimchi prover ACCEPTS, and it reconstructs the chosen scalar (`n₈ = S`).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate, the placement (`place`, read-only), and the witness
folds are authored in Lean. `proof-systems` RUNS the artifact — it authors no constraint. The 11
`EndoMulScalar` constraint polynomials are `proof-systems`' fixed gate semantics; the SAME polynomials
are transcribed read-only in `KimchiVerify.endomulScalarConstraints` (the checker the witness answers
to below over `ZMod pN`).

## The witness layout (`endomul_scalar.rs:116-122`, read-only)

Columns `n0=w₀ n8=w₁ a0=w₂ b0=w₃ a8=w₄ b8=w₅ x₀..x₇=w₆..w₁₃` (`w₁₄` unused = 0). Initial `n0=0,
a0=2, b0=2`. Crumb `xⱼ = 2·b1 + b0` = the scalar's base-4 digits MSB-first (`crumbⱼ = (S >> 2(7−j)) &
3`). No Curr/Next chaining inside one gate's 11 constraints.

## Axiom hygiene / build

NO `main` (roots into `PicklesSynthesis`; the emit driver is `EmitCurveGateJson.lean`). `#guard`s
reduce in the interpreter; no `sorry`/`native_decide`. Imports `KimchiPlacement`, `KimchiVerify` (the
checker), `PastaField` (`pN`).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson
open Dregg2.Circuit.Emit.KimchiVerify (endomulScalarConstraints endomulScalarConstsOk)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §1 — the scalar-field arithmetic (`Fp`, on `Nat`) and the crumb lookup tables. -/

private def modPowAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | (fuel + 1), base, e, acc =>
      if e == 0 then acc
      else
        let acc' := if e % 2 == 1 then (acc * base) % m else acc
        modPowAux m fuel ((base * base) % m) (e / 2) acc'

/-- `Fp` inverse via Fermat (used only for the polynomial constants of the non-vacuity guard). -/
def fInv (a : Nat) : Nat := modPowAux pN 260 (a % pN) (pN - 2) 1

/-- `c(x)` lookup as an `Fp` element (`endomul_scalar.rs:296-302`): `0↦0 1↦0 2↦−1 3↦1`. -/
def cFuncFp (x : Nat) : Nat := if x == 2 then pN - 1 else if x == 3 then 1 else 0
/-- `d(x)` lookup as an `Fp` element (`endomul_scalar.rs:311-317`): `0↦−1 1↦1 2↦0 3↦0`. -/
def dFuncFp (x : Nat) : Nat := if x == 0 then pN - 1 else if x == 1 then 1 else 0

/-! ## §2 — the chosen scalar, its crumbs, and the three accumulator folds. -/

/-- The eight crumbs `x₀..x₇` (MSB-first base-4 digits), chosen to exercise ALL FOUR crumb values
{0,1,2,3} so every branch of `c`/`d` is used (non-vacuity of the crumb-range + fold constraints). -/
def crumbs : List Nat := [3, 1, 2, 0, 3, 1, 2, 0]

/-- The reconstructed scalar `S = n₈` (`acc ↦ 4·acc + xⱼ`). -/
def n8val : Nat := crumbs.foldl (fun acc c => (4 * acc + c) % pN) 0
/-- `a₈ = fold(a₀=2): acc ↦ 2·acc + c(xⱼ)`. -/
def a8val : Nat := crumbs.foldl (fun acc c => (2 * acc + cFuncFp c) % pN) 2
/-- `b₈ = fold(b₀=2): acc ↦ 2·acc + d(xⱼ)`. -/
def b8val : Nat := crumbs.foldl (fun acc c => (2 * acc + dFuncFp c) % pN) 2

/-- The 15-column witness row (row 0), in gate column order
`[n0, n8, a0, b0, a8, b8, x₀..x₇, 0]`. -/
def emsRow : List Nat := [0, n8val, 2, 2, a8val, b8val] ++ crumbs ++ [0]

/-! ## §3 — the circuit, authored in Lean and placed by `place`. -/

def sevenNones : List (Option PVar) := List.replicate 7 none

/-- One `EndoMulScalar` gate (coeff-free) + one closing `Zero` gate. -/
def emsGates : List PGate :=
  [ { kind := .endoMulScalar, permVars := sevenNones, coeffs := [] }
  , { kind := .zero,          permVars := sevenNones, coeffs := [] } ]

def emsPlaced : List PlacedGate := place 0 emsGates

/-- Column `col`, row `row`: row 0 holds `emsRow`, row 1 (the `Zero` gate) is all zero. -/
def cellAt (col row : Nat) : Int :=
  if row == 0 then (emsRow.getD col 0 : Int) else 0

def emsWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range 2).map (fun row => cellAt col row))

/-! ## §4 — the JSON renderer (same shape the harness parses). -/



/-! ⚑ **ONE RENDERER.** The copy of `renderCircuit` this module carried — one of eleven, each with
its own private `q`/`qt`/`qs`, `renderCell`, `renderWires`, `renderIntList`, `renderGate`,
`renderGates`, `renderWitness` — is DELETED. `KimchiCircuitJson.renderCircuit` is a pure function of
a `KimchiCircuit` VALUE, and `renderCircuit_base_is_the_open_coded_shape` pins over EVERY argument
that it emits the chain the deleted copy emitted. -/

def endoMulScalarJson : String :=
  renderCircuit { name := "endoMulScalar16bit", pubSize := 0, numRows := 2
                , gates := emsPlaced, witness := emsWitness }

/-! ## §5 — the in-CI pins (`#guard`; interpreter-reduced). -/

-- Structural: 2 gates (EndoMulScalar ord 6 + Zero), 15×2 grid, coeff-free.
#guard emsGates.length == 2
#guard (emsPlaced.headD default).kind.ordinal == 6
#guard ((emsPlaced.headD default).coeffs).length == 0
#guard (emsPlaced.getD 1 default).kind.ordinal == 0
#guard emsWitness.length == 15
#guard (emsWitness.map (·.length)).all (· == 2)
#guard emsRow.length == 15

-- The scalar reconstructs from its own crumbs: `n₈ = Σ crumbⱼ·4^(7−j)`.
#guard n8val == crumbs.foldl (fun acc c => 4 * acc + c) 0
#guard n8val == 3*4^7 + 1*4^6 + 2*4^5 + 0*4^4 + 3*4^3 + 1*4^2 + 2*4^1 + 0

-- The polynomial constants cA=11/6, cB=−5/2, cC=2/3 are the genuine field quotients.
def cA : Nat := (11 * fInv 6) % pN
def cB : Nat := ((pN - 5) * fInv 2) % pN
def cC : Nat := (2 * fInv 3) % pN
#guard endomulScalarConstsOk (R := ZMod pN) (cA : ZMod pN) (cB : ZMod pN) (cC : ZMod pN)

-- ⚑ NON-VACUITY IN LEAN: the emitted row satisfies the SAME eleven-constraint checker the real proof
-- uses (`endomulScalarConstraints`, imported read-only from `KimchiVerify`), over `ZMod pN`. This ties
-- the crumb-lookup witness (`c`/`d` tables) to the constraint's polynomial `cf`/`df` forms (they agree
-- on {0,1,2,3}) and pins the three folds.
#guard (endomulScalarConstraints (R := ZMod pN) (cA : ZMod pN) (cB : ZMod pN) (cC : ZMod pN)
          (emsRow.map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))

end Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
