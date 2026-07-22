/-
# Direct-logic adversarial falsifiers (audit V2)

This file is intentionally not imported by the trusted umbrella.  It records two
accepted relations that sit outside the advertised source semantics unless the
caller's side conditions are retained:

1. the public Gabbay direct-table descriptor accepts a false canonical table when
   the external no-wrap premise is omitted; and
2. the abstract finite-FOL `FOLSatisfied2` carrier accepts a false sentence on an
   empty trace, because its row-wise conclusion and every row-local constraint
   are then vacuous.

Both are positive regression witnesses: the theorems below are expected to
compile.  They do not contradict the qualified soundness theorems in the owning
modules.  They show why those qualifications must become checked live boundaries
rather than API folklore.
-/

import Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding
import Dregg2.Logic.FiniteSignatureFOLDescriptorIR2

namespace Dregg2.Verify.DirectLogicAdversarialFalsifierV2

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.GabbayMatrixSemantics
open Dregg2.Metatheory.GabbayDescriptorIR2
open Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding

set_option autoImplicit false

/-! ## 1. Canonical BabyBear cancellation in the raw public Gabbay descriptor -/

/-- `284861408^2 = -1 (mod BabyBear)`.  The first two nonzero successor
residuals are therefore `1` and `284861408`; their squares cancel in the field. -/
def wrapClaim : ThreeEntryTable where
  input _ := 0
  output j := match j.val with
    | 0 => 2
    | 1 => 284861409
    | _ => 1

theorem wrapClaim_canonical : CanonicalTable wrapClaim := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [wrapClaim, BABYBEAR_MODULUS]

theorem wrapClaim_not_holds :
    ¬ Holds (sourceValuation wrapClaim) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  push Not
  exact ⟨0, by norm_num [wrapClaim]⟩

theorem wrapClaim_residual_exact :
    residualNumerator wrapClaim = 81146021767742465 := by
  norm_num [residualNumerator, wrapClaim]

theorem wrapClaim_residual_wraps :
    residualNumerator wrapClaim = 2013265921 * 40305665 := by
  norm_num [wrapClaim_residual_exact]

theorem wrapClaim_residual_modEq_zero :
    residualNumerator wrapClaim ≡ 0 [ZMOD 2013265921] := by
  rw [Int.modEq_zero_iff_dvd, wrapClaim_residual_wraps]
  exact dvd_mul_right _ _

theorem wrapClaim_no_live_projection_certificate :
    ¬ LiveProjectionCertificate wrapClaim := by
  intro cert
  have h := cert.numeratorNoWrap
  rw [wrapClaim_residual_exact] at h
  norm_num at h

/-- The raw emitted descriptor accepts the false, fully canonical public table.
The missing fact is exactly the non-serialized `LiveProjectionCertificate`. -/
theorem raw_public_descriptor_accepts_wrapClaim (hash : List Int -> Int) :
    Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (directTraceOf wrapClaim) := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [directTraceOf] at hi; omega
    subst i
    simp only [publicDescriptor] at hc
    simp only [publicConstraints, publicPins, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, inputCol, inputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, inputCol, inputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, inputCol, inputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, outputCol, outputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, outputCol, outputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, outputCol, outputPi]
    · simp only [VmConstraint2.holdsAt, always, WindowConstraint.holdsAt,
        Bool.false_eq_true, if_false]
      rw [directAcceptBody_eval]
      exact wrapClaim_residual_modEq_zero
  · intro i hi
    trivial
  · intro i hi r hr
    simp [publicDescriptor] at hr
  · intro op hop
    rw [memLog_publicDescriptor] at hop
    cases hop
  · rw [memLog_publicDescriptor]
    trivial
  · rw [memLog_publicDescriptor]
    exact memCheck_nil _ _
  · rw [memLog_publicDescriptor]
    rfl
  · rw [mapLog_publicDescriptor]
    rfl

/-! ## 2. Empty-trace vacuity in the finite-signature FOL carrier -/

open Dregg2.Logic.FiniteLogicDescriptorIR2
open Dregg2.Logic.FiniteSignatureFOLDescriptorIR2

def falseSentence : Formula demoSignature 0 := .bottom

def emptyTrace : VmTrace :=
  { rows := [], pub := zeroAsg, tf := fun _ => [] }

theorem falseSentence_rejects_every_model (model : Model demoSignature) :
    falseSentence.eval model emptyBound = false := rfl

/-- `FOLSatisfied2` itself has no nonempty-trace premise.  With no rows, every
constraint and canonicality obligation is vacuous, even for `bottom`. -/
theorem empty_trace_satisfies_false_fol (hash : List Int -> Int) :
    FOLSatisfied2 hash falseSentence (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] emptyTrace := by
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    simp [emptyTrace] at hi
  · intro i hi
    simp [emptyTrace] at hi
  · intro i hi
    simp [emptyTrace] at hi
  · intro op hop
    rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor] at hop
    cases hop
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor]
    trivial
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor]
    exact memCheck_nil _ _
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor]
    rfl
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.mapLog_compileDescriptor]
    rfl
  · intro i hi
    simp [emptyTrace] at hi

#assert_all_clean [
  wrapClaim_canonical,
  wrapClaim_not_holds,
  wrapClaim_residual_exact,
  wrapClaim_residual_wraps,
  wrapClaim_residual_modEq_zero,
  wrapClaim_no_live_projection_certificate,
  raw_public_descriptor_accepts_wrapClaim,
  falseSentence_rejects_every_model,
  empty_trace_satisfies_false_fol
]

end Dregg2.Verify.DirectLogicAdversarialFalsifierV2
