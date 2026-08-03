/-
`KimchiStepMain` — the Fp/Pallas VALUE LAYER, below the assembly.

Tonelli–Shanks (`fSqrt`), `Group_map.Bw19`'s Pallas parameters and `gmapFp`, `Generators.h`,
`scale_fast2`'s effective multiplier `bpK`, and the scalar-field arithmetic `check_bulletproof`'s
`rhs` is. ⚑ These were §17's, BELOW the assembly; they are here — above §9 — because a rung's own
value layer needs them (`u = group_map (squeeze)` is a transcript function, not an exhibit).
Nothing here depends on `StepShape`; the pins that DO are in `…Pins12`.
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.KimchiRenderPoseidon
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderPublicInput
import Dregg2.Circuit.Emit.KimchiComposeStepFragment
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Bridge.MinaWrapFtEval0
import Dregg2.Bridge.TickShifts
import Dregg2.Bridge.MinaStepPrevCommitments

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (cFuncFp dFuncFp)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment
  (TermData EndoBlock runVbm endoStep dblA addA onCurveA jOf jDbl jAdd jNeg)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints endomulScalarConstraints)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)
open Dregg2.Bridge.MinaWrapFtEval0 (IDX_Z IDX_SEL IDX_W IDX_COEFF IDX_S)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- `x − y` over `Fp`. Hoisted above §1 (it was §8b's) because `combine`'s `Opt.Maybe` mux
(`common.ml:270-271`) needs a subtraction in R5's value layer, which runs before the compiler. -/
def fSub (x y : Nat) : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub x y

private def fPowAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, base, e, acc =>
      if e == 0 then acc
      else fPowAux f (fMul base base) (e / 2) (if e % 2 == 1 then fMul acc base else acc)

/-- `a^e` in `Fp`. -/
def fPow (a e : Nat) : Nat := fPowAux 300 (a % pN) e 1

/-- Euler's criterion. -/
def fIsSquare (a : Nat) : Bool := a % pN == 0 || fPow a ((pN - 1) / 2) == 1

/-- `Aux.non_residue` (`snarky_group_map/checked_map.ml:5-9`): the first non-square from 2 up. It is
the multiplier `sqrt_flagged`'s `Field.if_` selects when `is_square` is false, so it is a CIRCUIT
constant and not only a witness-generation one. -/
def FP_NONRES : Nat := 5

/-- `Fp`'s two-adicity: `p − 1 = 2^32 · m`. -/
def FP_S : Nat := 32

def FP_M : Nat := (pN - 1) / 2 ^ FP_S

private def fOrd2 : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, t => if t == 1 then 0 else 1 + fOrd2 f (fMul t t)

private def fTsGo : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, R => R
  | f + 1, M, c, t, R =>
      if t == 1 then R
      else
        let i := fOrd2 (FP_S + 2) t
        let b := fPow c (2 ^ (M - i - 1))
        fTsGo f i (fMul b b) (fMul t (fMul b b)) (fMul R b)

/-- A square root in `Fp` (Tonelli–Shanks at `FP_NONRES`). ⚠ WHICH root: the same one arkworks'
`Field::sqrt` returns — pinned against `groupmap`'s own output below, so the choice is measured and
not assumed. Either root satisfies `assert_square`, so it is a witness convention. -/
def fSqrt (a : Nat) : Nat :=
  if a % pN == 0 then 0
  else fTsGo (FP_S + 2) FP_S (fPow FP_NONRES FP_M) (fPow a FP_M) (fPow a ((FP_M + 1) / 2))

def BW_U : Nat := 1

def BW_FU : Nat := 6

def BW_SQ3 : Nat :=
  17006931536212783554987228065028097629383328157457783420645920607630467569011

def BW_SQ3_MU2 : Nat :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

def BW_INV3U2 : Nat :=
  19298681539552699237261830834781317975575370987961040477303117842899978420225

/-- `potential_xs` (`bw19.ml:78-100`), the three candidate abscissae. -/
def bwPotentialXs (t : Nat) : Nat × Nat × Nat :=
  let t2 := fMul t t
  let alpha := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv (fMul (fAdd t2 BW_FU) t2)
  let x1 := fSub BW_SQ3_MU2 (fMul (fMul (fMul t2 t2) alpha) BW_SQ3)
  let x2 := fSub (fSub 0 BW_U) x1
  let tp := fAdd t2 BW_FU
  let x3 := fSub BW_U (fMul (fMul (fMul tp tp) (fMul alpha tp)) BW_INV3U2)
  (x1, x2, x3)

/-- `group_map` (`step_verifier.ml:214-237`): the first candidate whose `y² = x³ + 5` is a square,
with its root. In-circuit this is `Snarky_group_map.Checked.wrap` — all three roots are witnessed and
`sqrt_flagged`'s `is_square` bits select the first (`checked_map.ml:37-53`); the VALUE is this. -/
def gmapFp (t : Nat) : Nat × Nat :=
  let xs := bwPotentialXs t
  let y2 : Nat → Nat := fun x => fAdd (fMul x (fMul x x)) 5
  if fIsSquare (y2 xs.1) then (xs.1, fSqrt (y2 xs.1))
  else if fIsSquare (y2 xs.2.1) then (xs.2.1, fSqrt (y2 xs.2.1))
  else (xs.2.2, fSqrt (y2 xs.2.2))

/-- **`Generators.h`** — `Kimchi_bindings.Protocol.SRS.Fq.urs_h (Backend.Tock.Keypair.load_urs ())`
(`step_main_inputs.ml:306-311`), i.e. the Pallas SRS blinder, `Blake2b512(b"srs_misc" ++ 0u32)`
through `point_of_random_bytes` (`poly-commitment/src/ipa.rs:751-775`) and independent of the SRS
depth. MEASURED off `SRS::<Pallas>::create` (`gmprobe.rs`). ⚑ `step_verifier.ml` uses it TWICE — here
at `:336` and as `x_hat blinding` at `:558` — so pinning it retires a constant two rungs need. -/
def GENERATORS_H : Nat × Nat :=
  (15427374333697483577096356340297985232933727912694971579453397496858943128065,
   2509910240642018366461735648111399592717548684137438645981418079872989533888)

def bpK (sv : Nat) : Nat := (2 ^ 255 + sv) % Dregg2.Circuit.Emit.PastaField.qN

private def qPowAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, base, e, acc =>
      if e == 0 then acc
      else qPowAux f (base * base % Dregg2.Circuit.Emit.PastaField.qN) (e / 2) (if e % 2 == 1 then acc * base % Dregg2.Circuit.Emit.PastaField.qN else acc)

/-- Inverse in the Pallas SCALAR field — the field `z₁` lives in. -/
def qInv (a : Nat) : Nat := qPowAux 300 (a % Dregg2.Circuit.Emit.PastaField.qN) (Dregg2.Circuit.Emit.PastaField.qN - 2) 1

private def bpMul (k : Nat) (P : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (scMulM pN (k % Dregg2.Circuit.Emit.PastaField.qN) P).getD (0, 0, 0)

/-- `rhs = z₁·(G + b·u) + z₂·H`, in Jacobian coordinates so no inversion is needed to compare. -/
def bpRhs (u H : Nat × Nat) (G : Nat × Nat × Nat) (bv z1 z2 : Nat) : Nat × Nat × Nat :=
  let bu := bpMul (bpK bv) (jOf u)
  jAdd (bpMul (bpK z1) (jAdd G bu)) (bpMul (bpK z2) (jOf H))

/-- ⚑ **THE PROVER'S SOLVE.** `G := z₁⁻¹·(lhs − z₂·H) − b·u`. One scalar-field inverse and three
scalar multiplications — the whole cost of re-closing `equal_g` after ANY change to `lhs`. -/
def bpSolveG (u H lhs : Nat × Nat) (bv z1 z2 : Nat) : Nat × Nat × Nat :=
  let bu := bpMul (bpK bv) (jOf u)
  jAdd (bpMul (qInv (bpK z1)) (jAdd (jOf lhs) (jNeg (bpMul (bpK z2) (jOf H))))) (jNeg bu)

/-- `equal_g lhs rhs`, as a Boolean over the VALUES. -/
def bpCloses (u H lhs : Nat × Nat) (G : Nat × Nat × Nat) (bv z1 z2 : Nat) : Bool :=
  jacEqM pN (bpRhs u H G bv z1 z2) (jOf lhs)

end Dregg2.Circuit.Emit.KimchiStepMain
