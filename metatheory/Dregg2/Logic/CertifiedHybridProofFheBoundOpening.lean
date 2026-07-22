/-
# Dregg2.Logic.CertifiedHybridProofFheBoundOpening

The hybrid certificate carries a concrete proof opening and a conversion
witness from its concrete raw opening.  The generic backend-agreement theorem
is quantified over an arbitrary raw opening; this module closes the small but
important binding gap by specializing agreement to the two openings actually
stored in the certificate.
-/

import Dregg2.Logic.CertifiedHybridProofFhe
import Dregg2.Tactics

namespace Dregg2.Logic.CertifiedHybridProofFhe

set_option autoImplicit false

open Dregg2.Logic.FiniteLogicDescriptorIR2
open Dregg2.Logic.ProofFheSharedOpening
open Dregg2.Metatheory.FOLArithmetizationCorrected
open Dregg2.Metatheory.CertifiedPresentationChange

private theorem opening_ext {n : Nat} {left right : Opening n}
    (hword : left.word = right.word) : left = right := by
  cases left
  cases right
  cases hword
  rfl

/-- A conversion witness determines the proof opening exactly; it is not only
a pointwise canonicity certificate. -/
theorem ConversionWitness.proof_eq_convertedOpening
    {variableCount atomCount : Nat}
    {schema : EqualitySchema variableCount atomCount}
    {raw : Opening variableCount} {proof : Opening atomCount}
    (witness : ConversionWitness schema raw proof) :
    proof = convertedOpening schema raw := by
  apply opening_ext
  funext atom
  exact witness.exact atom

/-- The live proof relation for the opening stored in a certificate is exactly
the source predicate evaluated on that certificate's stored raw opening. -/
theorem Certificate.bound_proof_accepts_iff_source
    {variableCount atomCount : Nat}
    (certificate : Certificate variableCount atomCount) :
    CanonicalLogicSatisfied2 (fun _ => 0) atomCount certificate.dual.source
        (fun _ => 0) (fun _ => ((0 : Int), 0)) []
        certificate.dual.opening.proofTrace <->
      PositiveFormula.Holds
        (atomTruth certificate.schema certificate.rawOpening)
        certificate.formula := by
  rw [certificate.conversion.proof_eq_convertedOpening]
  exact certificate.proof_accepts_iff_source
    certificate.rawOpening certificate.rawCanonical

/-- The proof trace and the hybrid BFV plan stored in one certificate agree on
that certificate's concrete, conversion-bound opening. -/
theorem Certificate.bound_proof_iff_fhe_plan
    {variableCount atomCount : Nat}
    (certificate : Certificate variableCount atomCount) :
    CanonicalLogicSatisfied2 (fun _ => 0) atomCount certificate.dual.source
        (fun _ => 0) (fun _ => ((0 : Int), 0)) []
        certificate.dual.opening.proofTrace <->
      certificate.plan.evalRing certificate.rawOpening = 1 := by
  rw [certificate.conversion.proof_eq_convertedOpening]
  exact certificate.proof_iff_fhe_plan
    certificate.rawOpening certificate.rawCanonical

#assert_all_clean [
  ConversionWitness.proof_eq_convertedOpening,
  Certificate.bound_proof_accepts_iff_source,
  Certificate.bound_proof_iff_fhe_plan
]

end Dregg2.Logic.CertifiedHybridProofFhe
