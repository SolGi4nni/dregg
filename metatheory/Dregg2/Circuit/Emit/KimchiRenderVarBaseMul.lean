/-
# Dregg2.Circuit.Emit.KimchiRenderVarBaseMul — a REAL `var_base_mul` circuit, Lean-synthesized

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiVerify.varBaseMulConstraints` is the CHECKER for the `VarBaseMul` gate (variable-base scalar
multiplication — the double-and-add-with-sign step used in-circuit); this file supplies the missing
WITNESS generator and, like the sibling `KimchiRender*` modules, assembles the gate in Lean, places it
with `KimchiPlacement.place`, COMPUTES the two-row witness grid IN LEAN (the chained accumulator points
+ per-bit slopes over the Pallas base field Fp), and renders the JSON the `pickles-curvegate-harness`
proves + verifies pure-Rust. The gate is COEFF-FREE (`coeffs = []`, byte-exact vs o1js), so binding is
a WITNESS tamper.

The gate spans **two rows** (`VBSM` + `Zero`, `create_vbmul`, `varbasemul.rs:135-140`) and processes
**5 scalar bits** (`bits_per_chunk = 5`, `varbasemul.rs:377`). For a base point `T=(xT,yT)`, an initial
accumulator `acc₀`, and 5 bits `bᵢ` (MSB-first), each bit runs one combined step
(`single_bit_witness`, `varbasemul.rs:189-225`):
  * `sᵢ = (yᵢ − (2bᵢ−1)·yT) / (xᵢ − xT)`,
  * `s₂ = 2yᵢ / (2xᵢ + xT − sᵢ²) − sᵢ`,
  * `xᵢ₊₁ = xT + s₂² − sᵢ²`,  `yᵢ₊₁ = (xᵢ − xᵢ₊₁)·s₂ − yᵢ`,   `acc ← (xᵢ₊₁, yᵢ₊₁)`,
i.e. `accᵢ₊₁ = [2]accᵢ + (2bᵢ−1)·T`; and `n' = fold(n=0): acc ↦ 2·acc + bᵢ` (the 5-bit chunk value).
Only `sᵢ`, the acc points, the bits, and `n/n'` are stored — `s₂/rx/t/u` are constraint intermediates,
recomputed from the stored cells.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** Mina-valid. The kimchi
proof is an INNER proof; the reportable increment is that the Lean `var_base_mul` witness generator
produces a two-row grid a pure-Rust kimchi prover ACCEPTS.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate, the placement (`place`, read-only), and the witness
chain are authored in Lean. `proof-systems` RUNS the artifact. The 21 `VarBaseMul` constraint
polynomials are `proof-systems`' fixed gate semantics; the SAME polynomials are transcribed read-only
in `KimchiVerify.varBaseMulConstraints` (the checker the witness answers to below over `ZMod pN`).

## The witness layout (`varbasemul.rs:61-64`, read-only)

CURR (VBSM): `w0=xT w1=yT w2=x0 w3=y0 w4=n w5=n' w6=Ø w7=x1 w8=y1 w9=x2 w10=y2 w11=x3 w12=y3 w13=x4
w14=y4`. NEXT (Zero): `w0=x5 w1=y5 w2=b0 w3=b1 w4=b2 w5=b3 w6=b4 w7=s0 w8=s1 w9=s2 w10=s3 w11=s4
w12..w14=Ø`. `n` at block start is 0; the gate reads Curr AND Next.

## Axiom hygiene / build

NO `main`. `#guard`s reduce in the interpreter; no `sorry`/`native_decide`. Imports `KimchiPlacement`,
`KimchiVerify` (the checker), `PastaCurve` (`Gp`, `pN`).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve

namespace Dregg2.Circuit.Emit.KimchiRenderVarBaseMul

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiVerify (varBaseMulConstraints)
open Dregg2.Circuit.Emit.PastaCurve (Gp)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §1 — the Pallas base field `Fp` arithmetic (`ZMod pN`, on `Nat`). -/

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

/-- Affine doubling (to build the initial accumulator [2]G). -/
def dbl (Pt : Nat × Nat) : Nat × Nat :=
  let s := fMul (fMul 3 (fMul Pt.1 Pt.1)) (fInv (fMul 2 Pt.2))
  let x3 := fSub (fSub (fMul s s) Pt.1) Pt.1
  let y3 := fSub (fMul s (fSub Pt.1 x3)) Pt.2
  (x3, y3)

/-! ## §2 — one `single_bit` step and the 5-bit chain. -/

/-- The per-bit step (`varbasemul.rs:189-225`): returns `(sᵢ, xᵢ₊₁, yᵢ₊₁)`. `bsign = 2b−1 ∈ {−1,1}`. -/
def stepVbm (xT yT xi yi b : Nat) : Nat × Nat × Nat :=
  let bsign := if b == 1 then (1 : Nat) else pN - 1        -- 2b − 1
  let num := fSub yi (fMul bsign yT)
  let den := fSub xi xT
  let s := fMul num (fInv den)
  let ssq := fMul s s
  let s2den := fSub (fAdd (fMul 2 xi) xT) ssq              -- 2xᵢ + xT − sᵢ²
  let s2 := fSub (fMul (fMul 2 yi) (fInv s2den)) s          -- 2yᵢ/s2den − sᵢ
  let xo := fSub (fAdd xT (fMul s2 s2)) ssq                -- xT + s₂² − sᵢ²
  let yo := fSub (fMul (fSub xi xo) s2) yi                 -- (xᵢ − xᵢ₊₁)·s₂ − yᵢ
  (s, xo, yo)

/-- The base point T = G and the initial accumulator acc₀ = [2]G. -/
def T : Nat × Nat := Gp
def acc0 : Nat × Nat := dbl Gp

/-- The five bits (MSB-first), chosen with a mix of 0/1 so booleanity + both slope signs are exercised. -/
def bitsVbm : List Nat := [1, 0, 1, 1, 0]

/-- The chain state: the accumulator points `acc₀..acc₅` and the five slopes `s₀..s₄`. -/
structure Chain where
  accs : List (Nat × Nat)
  slopes : List Nat

/-- Run the 5-bit chain, collecting the 6 accumulator points and 5 slopes. -/
def vbmChain : Chain :=
  let final := bitsVbm.foldl (fun st b =>
      let cur := st.accs.getLastD (0, 0)
      let r := stepVbm T.1 T.2 cur.1 cur.2 b
      { accs := st.accs ++ [(r.2.1, r.2.2)], slopes := st.slopes ++ [r.1] })
    { accs := [acc0], slopes := [] }
  final

def accX (i : Nat) : Nat := (vbmChain.accs.getD i (0, 0)).1
def accY (i : Nat) : Nat := (vbmChain.accs.getD i (0, 0)).2
def slp (i : Nat) : Nat := vbmChain.slopes.getD i 0
def bit (i : Nat) : Nat := bitsVbm.getD i 0

/-- `n'` = the 5-bit chunk value, `fold(0): acc ↦ 2·acc + bᵢ` (MSB-first). -/
def nNextVal : Nat := bitsVbm.foldl (fun acc b => 2 * acc + b) 0

/-! ## §3 — the two witness rows (Curr = VBSM, Next = Zero). -/

/-- Curr row: `[xT, yT, x0, y0, n=0, n', Ø=0, x1, y1, x2, y2, x3, y3, x4, y4]`. -/
def currRow : List Nat :=
  [T.1, T.2, accX 0, accY 0, 0, nNextVal, 0,
   accX 1, accY 1, accX 2, accY 2, accX 3, accY 3, accX 4, accY 4]

/-- Next row: `[x5, y5, b0, b1, b2, b3, b4, s0, s1, s2, s3, s4, Ø, Ø, Ø]`. -/
def nextRow : List Nat :=
  [accX 5, accY 5, bit 0, bit 1, bit 2, bit 3, bit 4,
   slp 0, slp 1, slp 2, slp 3, slp 4, 0, 0, 0]

/-! ## §4 — the circuit, authored in Lean and placed by `place`. -/

def sevenNones : List (Option PVar) := List.replicate 7 none

/-- One `VarBaseMul` gate + one `Zero` gate (the gate reads across both rows). -/
def vbmGates : List PGate :=
  [ { kind := .varBaseMul, permVars := sevenNones, coeffs := [] }
  , { kind := .zero,       permVars := sevenNones, coeffs := [] } ]

def vbmPlaced : List PlacedGate := place 0 vbmGates

def cellAt (col row : Nat) : Int :=
  if row == 0 then (currRow.getD col 0 : Int) else (nextRow.getD col 0 : Int)

def vbmWitness : List (List Int) :=
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

def varBaseMulJson : String := renderCircuit "varBaseMul5bit" 0 2 vbmPlaced vbmWitness

/-! ## §6 — the in-CI pins (`#guard`; interpreter-reduced). -/

#guard vbmGates.length == 2
#guard (vbmPlaced.headD default).kind.ordinal == 4      -- VarBaseMul
#guard ((vbmPlaced.headD default).coeffs).length == 0
#guard (vbmPlaced.getD 1 default).kind.ordinal == 0     -- Zero
#guard vbmWitness.length == 15
#guard (vbmWitness.map (·.length)).all (· == 2)
#guard vbmChain.accs.length == 6
#guard vbmChain.slopes.length == 5

-- `n'` reconstructs the 5-bit chunk `[1,0,1,1,0]₂ = 22`.
#guard nNextVal == 22

-- Every accumulator point stays ON the Pallas curve `y² = x³ + 5` (the chain computes real EC points).
#guard (List.range 6).all (fun i =>
  fMul (accY i) (accY i) == fAdd (fMul (accX i) (fMul (accX i) (accX i))) 5)

-- ⚑ NON-VACUITY IN LEAN: both rows satisfy the SAME 21-constraint checker the real proof uses
-- (`varBaseMulConstraints w wNext`, imported read-only from `KimchiVerify`), over `ZMod pN`.
#guard (varBaseMulConstraints (R := ZMod pN)
          (currRow.map (fun n => (n : ZMod pN))) (nextRow.map (fun n => (n : ZMod pN)))).all
        (fun z => decide (z = 0))

end Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
