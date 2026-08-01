/-
# Dregg2.Circuit.Emit.KimchiRenderEndoMul — a REAL `endo_mul` circuit, Lean-synthesized

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiVerify.endoMulConstraints` is the CHECKER for the `EndoMul` (`EndosclMul`) gate — the
endomorphism-optimized variable-base scalar multiplication step. This file supplies the missing WITNESS
generator and, like the sibling `KimchiRender*` modules, assembles the gate in Lean, places it with
`KimchiPlacement.place`, COMPUTES the two-row witness grid IN LEAN (the endo-combined accumulator +
two per-block slopes over the Pallas base field Fp), and renders the JSON the `pickles-curvegate-harness`
proves + verifies pure-Rust. The gate is COEFF-FREE (`coeffs = []`, byte-exact vs o1js).

The gate processes **4 scalar bits** per row (`gen_witness`, `endosclmul.rs:282-373`), with `endo =`
the base-field endomorphism eigenvalue `ζ_p = 5^((p−1)/3) mod p` (= `PastaCurve.zetaP`, an independent
derivation — `endosclmul.rs:219` reads `env.endo_coefficient()`). For base `T=(xt,yt)`, initial
accumulator `(xp,yp)`, bits `b1..b4`:
  * `xq1 = (1 + (endo−1)·b1)·xt` (= `xt` or `ζ·xt`), `yq1 = (2b2−1)·yt`;
    `s1 = (yq1−yp)/(xq1−xp)`, `s2 = 2yp/(2xp+xq1−s1²)−s1`, `xr = xq1+s2²−s1²`, `yr = (xp−xr)·s2−yp`;
  * `xq2 = (1 + (endo−1)·b3)·xt`, `yq2 = (2b4−1)·yt`;
    `s3 = (yq2−yr)/(xq2−xr)`, `s4 = 2yr/(2xr+xq2−s3²)−s3`, `xs = xq2+s4²−s3²`, `ys = (xr−xs)·s4−yr`;
  * `n' = 16·n + 8b1 + 4b2 + 2b3 + b4` (n = 0 at block start).
Stored cells: `s1, s3`, the acc points, the four bits, `n/n'` — `s2/s4` are constraint intermediates.

⚑ VERSION NOTE. This crate proves against `proof-systems` **0.3.0** (checkout `a73ca6e`), whose EndoMul
has **11** constraints and leaves witness column 2 UNUSED. dregg's Lean `endoMulConstraints` is
transcribed from a NEWER proof-systems and has **12** constraints — the twelfth is the distinct-point
witness `(xp−xr)(xr−xs)·inv − 1` reading `inv = w₂`. To satisfy BOTH the 0.3.0 gate (ignores w₂) AND
the Lean 12-constraint checker (the non-vacuity `#guard`), this witness sets
`w₂ = inv = 1/((xp−xr)(xr−xs))`.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** Mina-valid.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate, placement (`place`, read-only), and witness chain are
authored in Lean. `proof-systems` RUNS the artifact. The EndoMul constraint polynomials are
`proof-systems`' fixed gate semantics; `KimchiVerify.endoMulConstraints` is the read-only transcription
the witness answers to below over `ZMod pN`.

## The witness layout (`endosclmul.rs:48-56`, read-only)

CURR: `w0=xt w1=yt w2=Ø(inv) w3=Ø w4=xp w5=yp w6=n w7=xr w8=yr w9=s1 w10=s3 w11=b1 w12=b2 w13=b3
w14=b4`. NEXT: `w4=xs w5=ys w6=n'` (rest Ø for a single block's tail Zero row). `n` = 0 at block start;
the gate reads Curr AND Next.

## Axiom hygiene / build

NO `main`. `#guard`s reduce in the interpreter; no `sorry`/`native_decide`. Imports `KimchiPlacement`,
`KimchiVerify` (the checker), `PastaCurve` (`Gp`, `zetaP`, `pN`).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve

namespace Dregg2.Circuit.Emit.KimchiRenderEndoMul

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiVerify (endoMulConstraints)
open Dregg2.Circuit.Emit.PastaCurve (Gp zetaP)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §1 — the Pallas base field `Fp` arithmetic. -/

def fAdd (x y : Nat) : Nat := (x + y) % pN
def fSub (x y : Nat) : Nat := (x + pN - y % pN) % pN
def fMul (x y : Nat) : Nat := (x * y) % pN

private def modPowAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | (fuel + 1), base, e, acc =>
      if e == 0 then acc
      else
        let acc' := if e % 2 == 1 then (acc * base) % m else acc
        modPowAux m fuel ((base * base) % m) (e / 2) acc'

def fInv (a : Nat) : Nat := modPowAux pN 260 (a % pN) (pN - 2) 1

def dbl (Pt : Nat × Nat) : Nat × Nat :=
  let s := fMul (fMul 3 (fMul Pt.1 Pt.1)) (fInv (fMul 2 Pt.2))
  let x3 := fSub (fSub (fMul s s) Pt.1) Pt.1
  let y3 := fSub (fMul s (fSub Pt.1 x3)) Pt.2
  (x3, y3)

/-! ## §2 — the endo constant and the single 4-bit block. -/

/-- The base-field endomorphism eigenvalue `endo = ζ_p` (`PastaCurve.zetaP`, `5^((p−1)/3) mod p`). -/
def endo : Nat := zetaP

def T : Nat × Nat := Gp
def acc0 : Nat × Nat := dbl Gp

/-- The four bits `b1..b4` (MSB-first), mixed 0/1 to exercise booleanity + both endo/sign branches. -/
def b1 : Nat := 1
def b2 : Nat := 0
def b3 : Nat := 1
def b4 : Nat := 1

/-- `(1 + (endo−1)·b)·xt` — the endo-selected base x-coordinate. -/
def xqOf (b xt : Nat) : Nat := fMul (fAdd 1 (fMul b (fSub endo 1))) xt
/-- `(2b−1)·yt` — the sign-selected base y-coordinate. -/
def yqOf (b yt : Nat) : Nat := fMul (if b == 1 then (1 : Nat) else pN - 1) yt

def xt : Nat := T.1
def yt : Nat := T.2
def xp : Nat := acc0.1
def yp : Nat := acc0.2

-- Block 1.
def xq1 : Nat := xqOf b1 xt
def yq1 : Nat := yqOf b2 yt
def s1 : Nat := fMul (fSub yq1 yp) (fInv (fSub xq1 xp))
def s2 : Nat := fSub (fMul (fMul 2 yp) (fInv (fSub (fAdd (fMul 2 xp) xq1) (fMul s1 s1)))) s1
def xr : Nat := fSub (fAdd xq1 (fMul s2 s2)) (fMul s1 s1)
def yr : Nat := fSub (fMul (fSub xp xr) s2) yp

-- Block 2.
def xq2 : Nat := xqOf b3 xt
def yq2 : Nat := yqOf b4 yt
def s3 : Nat := fMul (fSub yq2 yr) (fInv (fSub xq2 xr))
def s4 : Nat := fSub (fMul (fMul 2 yr) (fInv (fSub (fAdd (fMul 2 xr) xq2) (fMul s3 s3)))) s3
def xs : Nat := fSub (fAdd xq2 (fMul s4 s4)) (fMul s3 s3)
def ys : Nat := fSub (fMul (fSub xr xs) s4) yr

/-- `n' = 16·0 + 8b1 + 4b2 + 2b3 + b4`. -/
def nNextVal : Nat := 8 * b1 + 4 * b2 + 2 * b3 + b4

/-- The distinct-point inverse `w₂ = 1/((xp−xr)(xr−xs))` (satisfies the Lean 12th constraint; the 0.3.0
gate ignores column 2). -/
def invVal : Nat := fInv (fMul (fSub xp xr) (fSub xr xs))

/-! ## §3 — the two witness rows (Curr = EndoMul, Next = Zero tail). -/

/-- Curr row: `[xt, yt, inv, Ø, xp, yp, n=0, xr, yr, s1, s3, b1, b2, b3, b4]`. -/
def currRow : List Nat :=
  [xt, yt, invVal, 0, xp, yp, 0, xr, yr, s1, s3, b1, b2, b3, b4]

/-- Next (tail) row: `[Ø,Ø,Ø,Ø, xs, ys, n', Ø…]`. -/
def nextRow : List Nat :=
  [0, 0, 0, 0, xs, ys, nNextVal, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## §4 — the circuit, authored in Lean and placed by `place`. -/

def sevenNones : List (Option PVar) := List.replicate 7 none

def emGates : List PGate :=
  [ { kind := .endoMul, permVars := sevenNones, coeffs := [] }
  , { kind := .zero,    permVars := sevenNones, coeffs := [] } ]

def emPlaced : List PlacedGate := place 0 emGates

def cellAt (col row : Nat) : Int :=
  if row == 0 then (currRow.getD col 0 : Int) else (nextRow.getD col 0 : Int)

def emWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range 2).map (fun row => cellAt col row))

/-! ## §5 — the JSON renderer. -/

private def qt (s : String) : String := "\"" ++ s ++ "\""
private def renderCell (c : Cell) : String := "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"
private def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"
private def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => qt (toString i))) ++ "]"
private def renderGate (g : PlacedGate) : String :=
  "{" ++ qt "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ qt "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ qt "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"
private def renderGates (gs : List PlacedGate) : String :=
  "[" ++ String.intercalate "," (gs.map renderGate) ++ "]"
private def renderWitness (w : List (List Int)) : String :=
  "[" ++ String.intercalate "," (w.map renderIntList) ++ "]"

def renderCircuit (name : String) (pubSize numRows : Nat)
    (gs : List PlacedGate) (w : List (List Int)) : String :=
  "{" ++ qt "name" ++ ":" ++ qt name ++ ","
       ++ qt "public_input_size" ++ ":" ++ toString pubSize ++ ","
       ++ qt "num_rows" ++ ":" ++ toString numRows ++ ","
       ++ qt "gates" ++ ":" ++ renderGates gs ++ ","
       ++ qt "witness" ++ ":" ++ renderWitness w ++ "}"

def endoMulJson : String := renderCircuit "endoMul4bit" 0 2 emPlaced emWitness

/-! ## §6 — the in-CI pins (`#guard`; interpreter-reduced). -/

#guard emGates.length == 2
#guard (emPlaced.headD default).kind.ordinal == 5       -- EndoMul
#guard ((emPlaced.headD default).coeffs).length == 0
#guard (emPlaced.getD 1 default).kind.ordinal == 0      -- Zero
#guard emWitness.length == 15
#guard (emWitness.map (·.length)).all (· == 2)

-- `endo` is the primitive cube root ζ_p (endo³ ≡ 1, endo ≠ 1).
#guard (endo ^ 3) % pN == 1
#guard endo != 1
#guard nNextVal == 11    -- 8·1 + 4·0 + 2·1 + 1

-- The accumulator points (input, intermediate xr, output xs) stay ON the Pallas curve.
#guard fMul yp yp == fAdd (fMul xp (fMul xp xp)) 5
#guard fMul yr yr == fAdd (fMul xr (fMul xr xr)) 5
#guard fMul ys ys == fAdd (fMul xs (fMul xs xs)) 5

-- ⚑ NON-VACUITY IN LEAN: both rows satisfy the SAME (12-constraint, newer) checker
-- `endoMulConstraints endo w wNext` (imported read-only from `KimchiVerify`), over `ZMod pN` — INCLUDING
-- the distinct-point 12th constraint, since `w₂ = inv` is set. The 0.3.0 harness gate uses the 11-core
-- (ignoring w₂); this `#guard` is therefore a STRICTER check than the harness's own gate.
#guard (endoMulConstraints (R := ZMod pN) (endo : ZMod pN)
          (currRow.map (fun n => (n : ZMod pN))) (nextRow.map (fun n => (n : ZMod pN)))).all
        (fun z => decide (z = 0))

end Dregg2.Circuit.Emit.KimchiRenderEndoMul
