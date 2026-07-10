import Dregg2.Circuit.OodQuotientConsistency
import Dregg2.Circuit.TraceColumnInterp

/-!
# The BabyBear/ℤ AIR seam

The deployed main-table identity is an identity in `BabyBear`.  The committed semantic residual,
however, is evaluated in `ℤ`.  Additive differences of canonical field representatives lift because
they lie strictly between `-p` and `p`; general `EmittedExpr` gates do not.  In particular,
`((p - 1) + 1) * 1` is zero in BabyBear and is the nonzero integer `p`.

This file therefore gives the OOD chain its honest field-valued landing proposition and proves the
multiplicative counterexample against the actual `VmConstraint2` grammar and BabyBear modulus.
-/

namespace Dregg2.Circuit.FieldIntegerLift

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.TraceColumnInterp
open Dregg2.Circuit.OodQuotientConsistency
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## The lift that is available for additive constraints -/

/-- Reduction modulo BabyBear is injective on the open interval `(-p,p)` around zero. -/
theorem babyBear_zero_lifts_in_centered_range (z : ℤ)
    (hlo : -(babyBearP : ℤ) < z) (hhi : z < babyBearP)
    (hz : (z : BabyBear) = 0) : z = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨k, hk⟩ := hz
  norm_num [babyBearP] at hlo hhi hk ⊢
  omega

/-- Hence subtraction of two canonical BabyBear representatives lifts to integer equality.
The representative bounds are load-bearing; `VmTrace` itself does not currently carry them. -/
theorem canonical_babyBear_sub_eq_zero_lifts (x y : ℤ)
    (hx0 : 0 ≤ x) (hxp : x < babyBearP)
    (hy0 : 0 ≤ y) (hyp : y < babyBearP)
    (hxy : ((x - y : ℤ) : BabyBear) = 0) : x = y := by
  apply sub_eq_zero.mp
  apply babyBear_zero_lifts_in_centered_range (x - y)
  · omega
  · omega
  · exact hxy

/-! ## The field-valued OOD landing -/

/-- The row identity actually asserted by the BabyBear main-table AIR.  No hash argument appears:
the arithmetic quotient does not inspect the semantic hash (the committed `MainAirAccept` retains
one only for its later composition with `Satisfied2`). -/
def MainAirAcceptF (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ c ∈ d.constraints,
    ((arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c : ℤ) : BabyBear) = 0

/-- The concrete BabyBear OOD bridge.  Unlike `OodInterpZ`, its constraint polynomial is not an
unmodeled field: it is exactly the committed trace-column polynomial `constraintPoly d t c`, and
`hCrow` has exactly the statement proved by
`TraceColumnInterp.constraintPoly_eval_eq_arithResidual`. -/
structure OodInterpF (d : EffectVmDescriptor2) (t : VmTrace) where
  hcap : t.rows.length ≤ domainSize
  ζ : BabyBear
  Zp : Polynomial BabyBear
  qp : VmConstraint2 → Polynomial BabyBear
  hZrow : ∀ i < t.rows.length, Zp.eval (rowPt i) = 0
  hood : ∀ c ∈ d.constraints, isArith c →
    (constraintPoly d t c).eval ζ = Zp.eval ζ * (qp c).eval ζ
  hnonexc : ∀ c ∈ d.constraints, isArith c →
    ζ ∉ exceptionalSet (constraintPoly d t c - Zp * qp c)

/-- The committed interpolation theorem supplies `OodInterpF.hCrow` directly; it is not another
premise carried by the bridge. -/
theorem OodInterpF.hCrow {d : EffectVmDescriptor2} {t : VmTrace} (I : OodInterpF d t)
    (i : ℕ) (hi : i < t.rows.length) (c : VmConstraint2) (hc : isArith c) :
    (constraintPoly d t c).eval (rowPt i) =
      ((arithResidual (envAt t i) (i == 0) (i + 1 == t.rows.length) c : ℤ) : BabyBear) :=
  constraintPoly_eval_eq_arithResidual d t I.hcap i hi c hc

/-- BabyBear OOD consistency forces exactly the field-valued per-row AIR identity. -/
theorem ood_forces_mainAirAccept_field (d : EffectVmDescriptor2) (t : VmTrace)
    (I : OodInterpF d t) : MainAirAcceptF d t := by
  intro i hi c hc
  by_cases ha : isArith c
  · have hCq : constraintPoly d t c = I.Zp * I.qp c :=
      ood_consistency (constraintPoly d t c) I.Zp (I.qp c) I.ζ
        (I.hood c hc ha) (I.hnonexc c hc ha)
    rw [← I.hCrow i hi c ha, hCq, eval_mul, I.hZrow i hi, zero_mul]
  · cases c <;> simp_all [isArith, arithResidual]

/-! ## A deployed-modulus multiplicative counterexample -/

/-- The real expression grammar's compound gate `((col 0 + col 1) * col 2)`. -/
def wrapExpr : EmittedExpr :=
  .mul (.add (.var 0) (.var 1)) (.var 2)

/-- Canonical field representatives `p-1, 1, 1` in the three used columns. -/
def wrapRow : Assignment := fun col =>
  if col = 0 then (babyBearP : ℤ) - 1 else if col = 1 then 1 else if col = 2 then 1 else 0

def wrapConstraint : VmConstraint2 := .base (.gate wrapExpr)

def wrapDescriptor : EffectVmDescriptor2 :=
  { name := "babybear-integer-wrap"
  , traceWidth := 3
  , piCount := 0
  , tables := []
  , constraints := [wrapConstraint]
  , hashSites := []
  , ranges := [] }

/-- Two rows ensure the multiplicative gate fires on row zero; the second row is the last-row guard. -/
def wrapTrace : VmTrace :=
  { rows := [wrapRow, zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- Every column actually read by `wrapExpr` is a canonical representative in `[0,p)`. -/
theorem wrapRow_columns_are_canonical :
    (0 ≤ wrapRow 0 ∧ wrapRow 0 < babyBearP) ∧
    (0 ≤ wrapRow 1 ∧ wrapRow 1 < babyBearP) ∧
    (0 ≤ wrapRow 2 ∧ wrapRow 2 < babyBearP) := by
  norm_num [wrapRow, babyBearP]

/-- Over raw integers the row-zero residual is exactly the nonzero BabyBear modulus. -/
theorem wrap_integer_residual :
    arithResidual (envAt wrapTrace 0) (0 == 0) (0 + 1 == wrapTrace.rows.length)
      wrapConstraint = babyBearP := by
  rw [show (0 + 1 == wrapTrace.rows.length) = false by decide]
  norm_num [wrapConstraint, wrapExpr, wrapTrace, wrapRow, arithResidual, envAt,
    EmittedExpr.eval, zeroAsg, babyBearP, List.getD]

/-- The same deployed gate residual is zero in BabyBear. -/
theorem wrap_field_residual :
    ((arithResidual (envAt wrapTrace 0) (0 == 0) (0 + 1 == wrapTrace.rows.length)
      wrapConstraint : ℤ) : BabyBear) = 0 := by
  rw [wrap_integer_residual]
  exact ZMod.natCast_self babyBearP

/- `#eval` prints `2013265921`: the raw-ℤ value hidden by the deployed modular equality. -/
#eval arithResidual (envAt wrapTrace 0) (0 == 0) (0 + 1 == wrapTrace.rows.length)
  wrapConstraint

/-- RESPECTING FIELD POLE: the actual field AIR accepts both rows of the wraparound trace. -/
theorem wrap_mainAirAcceptF : MainAirAcceptF wrapDescriptor wrapTrace := by
  intro i hi c hc
  simp only [wrapDescriptor, List.mem_singleton] at hc
  subst c
  have hi' : i < 2 := by simpa [wrapTrace] using hi
  interval_cases i
  · exact wrap_field_residual
  · simp [wrapTrace, wrapConstraint, arithResidual]

/-- BITING INTEGER POLE: the committed integer `MainAirAccept` rejects that same trace. -/
theorem wrap_not_mainAirAcceptZ :
    ¬ MainAirAccept (fun _ => 0) wrapDescriptor wrapTrace := by
  intro h
  have hzero := mainAirAccept_forces_residual (fun _ => 0) wrapDescriptor wrapTrace h
    0 (by simp [wrapTrace]) wrapConstraint (by simp [wrapDescriptor])
  rw [wrap_integer_residual] at hzero
  norm_num [babyBearP] at hzero

/-- Therefore no unconditional implication from the deployed field landing to the committed integer
landing exists, even for canonical columns and an actual arithmetic `VmConstraint2`. -/
theorem mainAirAcceptF_does_not_imply_MainAirAcceptZ :
    MainAirAcceptF wrapDescriptor wrapTrace ∧
      ¬ MainAirAccept (fun _ => 0) wrapDescriptor wrapTrace :=
  ⟨wrap_mainAirAcceptF, wrap_not_mainAirAcceptZ⟩

#assert_axioms babyBear_zero_lifts_in_centered_range
#assert_axioms canonical_babyBear_sub_eq_zero_lifts
#assert_axioms OodInterpF.hCrow
#assert_axioms ood_forces_mainAirAccept_field
#assert_axioms mainAirAcceptF_does_not_imply_MainAirAcceptZ

end Dregg2.Circuit.FieldIntegerLift
