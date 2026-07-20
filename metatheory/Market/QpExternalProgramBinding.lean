/-
# Market.QpExternalProgramBinding — the external `FHQPB001` program pin.

An internally valid exact QP bundle proves optimality for the public problem
embedded in the artifact.  It does not, by itself, prove that this is the
problem an independent fhIR compiler authorized.  The deployed
`CertQpExact::verify_problem_binding` closes that edge by comparing every
fixed-point field `(P,q,A,l,u)` after lifting the independently compiled
problem at the certificate's scale.

This file states the decoded rational law at that boundary.  Dimensions are
already pinned by the type indices `n` and `mc`; `CompleteProblemIdentity`
then pins all five semantic fields.  Only this complete identity transports
the exact SDD-plus-KKT optimality theorem from the embedded problem to the
authorized one.

The theorem deliberately consumes `ExactKktAccepted`, never
`rustCertQpCheck = true`: positive-tolerance residual acceptance does not
imply exact feasibility, stationarity, normal-cone membership, or optimality.
Wire parsing, fixed-point lifting, SHA-256 program-digest refinement, and the
authentication of the compiled fhIR product remain outside this semantic
module.
-/

import Market.QpCertificateBundle
import Dregg2.Tactics

namespace Market.QpExternalProgramBinding

set_option autoImplicit false

/-- Exact decoded identity checked by the `FHQPB001` external binding step.
The dimension and shape checks in Rust correspond to the common Lean indices;
the five conjuncts correspond exactly to the `p`, `q`, `a`, `l`, and `u`
entry-for-entry comparisons. -/
def CompleteProblemIdentity {n mc : Nat}
    (embedded authorized : Market.RustQpProblem n mc) : Prop :=
  embedded.p = authorized.p ∧
  embedded.q = authorized.q ∧
  embedded.a = authorized.a ∧
  embedded.l = authorized.l ∧
  embedded.u = authorized.u

/-- Executable, fail-closed semantic image of `verify_problem_binding` after
successful shape checking and exact fixed-point decoding. -/
def completeProblemIdentityCheck {n mc : Nat}
    (embedded authorized : Market.RustQpProblem n mc) : Bool :=
  decide (embedded.p = authorized.p) &&
  decide (embedded.q = authorized.q) &&
  decide (embedded.a = authorized.a) &&
  decide (embedded.l = authorized.l) &&
  decide (embedded.u = authorized.u)

theorem completeProblemIdentityCheck_iff {n mc : Nat}
    (embedded authorized : Market.RustQpProblem n mc) :
    completeProblemIdentityCheck embedded authorized = true ↔
      CompleteProblemIdentity embedded authorized := by
  simp [completeProblemIdentityCheck, CompleteProblemIdentity, and_assoc]

/-- Complete field identity reconstructs equality of the decoded public
problems.  No optimizer or convexity fact participates in this structural
step. -/
theorem complete_problem_identity_eq {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    (hbind : CompleteProblemIdentity embedded authorized) :
    embedded = authorized := by
  cases embedded
  cases authorized
  simp_all [CompleteProblemIdentity]

/-- Exact KKT meaning can be transported to the independently authorized
problem only after the complete public-program identity has been established.
-/
theorem complete_binding_transports_exact_kkt {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    {x : Fin n → ℚ} {y : Fin mc → ℚ}
    (hbind : CompleteProblemIdentity embedded authorized)
    (hkkt : Market.QpCertificateBundle.ExactKktAccepted embedded x y) :
    Market.QpCertificateBundle.ExactKktAccepted authorized x y := by
  rw [← complete_problem_identity_eq hbind]
  exact hkkt

/-- **External `FHQPB001` composition.** An exact SDD-plus-KKT bundle for the
embedded problem proves global optimality for an independently authorized
compiled problem only when all of `(P,q,A,l,u)` are identical. -/
theorem externally_bound_bundle_global_optimal {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    {admittedP : Matrix (Fin n) (Fin n) ℚ}
    {x : Fin n → ℚ} {y : Fin mc → ℚ}
    (bundle : Market.QpCertificateBundle.ExactQpCertificateBundle
      embedded admittedP x y)
    (hbind : CompleteProblemIdentity embedded authorized)
    {x' : Fin n → ℚ}
    (hfeas' : Market.RustQpFeasible authorized x') :
    Market.rustQpObjective authorized x ≤
      Market.rustQpObjective authorized x' := by
  have heq : embedded = authorized := complete_problem_identity_eq hbind
  subst authorized
  exact Market.QpCertificateBundle.exact_bundle_global_optimal bundle hfeas'

/-! ## Fail-closed substitution laws. -/

theorem quadratic_objective_substitution_refused {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    (hp : embedded.p ≠ authorized.p) :
    completeProblemIdentityCheck embedded authorized = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  exact hp ((completeProblemIdentityCheck_iff embedded authorized).mp hcheck).1

theorem linear_objective_substitution_refused {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    (hq : embedded.q ≠ authorized.q) :
    completeProblemIdentityCheck embedded authorized = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  exact hq ((completeProblemIdentityCheck_iff embedded authorized).mp hcheck).2.1

theorem constraint_matrix_substitution_refused {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    (ha : embedded.a ≠ authorized.a) :
    completeProblemIdentityCheck embedded authorized = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  exact ha ((completeProblemIdentityCheck_iff embedded authorized).mp hcheck).2.2.1

theorem lower_bound_substitution_refused {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    (hl : embedded.l ≠ authorized.l) :
    completeProblemIdentityCheck embedded authorized = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  exact hl ((completeProblemIdentityCheck_iff embedded authorized).mp hcheck).2.2.2.1

theorem upper_bound_substitution_refused {n mc : Nat}
    {embedded authorized : Market.RustQpProblem n mc}
    (hu : embedded.u ≠ authorized.u) :
    completeProblemIdentityCheck embedded authorized = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  exact hu ((completeProblemIdentityCheck_iff embedded authorized).mp hcheck).2.2.2.2

/-! ## Executable falsifiers.

All fixtures deliberately keep the dimensions and every non-target field
fixed.  In particular, the changed-linear-objective fixture has the same PSD
matrix `P`; this is the substitution a matrix-only binding would miss.
-/

def fixtureAuthorized : Market.RustQpProblem 1 1 := Market.rustQpOne

def fixtureQuadraticObjectiveSubstitution : Market.RustQpProblem 1 1 :=
  { fixtureAuthorized with p := fun _ _ => 2 }

def fixtureLinearObjectiveSubstitution : Market.RustQpProblem 1 1 :=
  { fixtureAuthorized with q := fun _ => -2 }

def fixtureConstraintSubstitution : Market.RustQpProblem 1 1 :=
  { fixtureAuthorized with a := fun _ _ => 2 }

def fixtureLowerBoundSubstitution : Market.RustQpProblem 1 1 :=
  { fixtureAuthorized with l := fun _ => -1 }

def fixtureUpperBoundSubstitution : Market.RustQpProblem 1 1 :=
  { fixtureAuthorized with u := fun _ => 3 }

#guard completeProblemIdentityCheck fixtureAuthorized fixtureAuthorized
#guard !completeProblemIdentityCheck fixtureAuthorized fixtureQuadraticObjectiveSubstitution
#guard !completeProblemIdentityCheck fixtureAuthorized fixtureLinearObjectiveSubstitution
#guard !completeProblemIdentityCheck fixtureAuthorized fixtureConstraintSubstitution
#guard !completeProblemIdentityCheck fixtureAuthorized fixtureLowerBoundSubstitution
#guard !completeProblemIdentityCheck fixtureAuthorized fixtureUpperBoundSubstitution

/- Matrix-only binding accepts the dangerous linear-objective substitution,
while the full external-program gate rejects it. -/
#guard fixtureAuthorized.p = fixtureLinearObjectiveSubstitution.p
#guard !completeProblemIdentityCheck fixtureAuthorized fixtureLinearObjectiveSubstitution

/- The substitution is semantically material: under `q = -2`, the feasible
point `x = 2` has strictly lower objective than the old exact witness `x = 1`.
Thus a certificate for the old problem cannot be treated as an optimality
certificate for the substituted problem merely because `P` is unchanged. -/
#guard Market.rustQpObjective fixtureLinearObjectiveSubstitution (fun _ => 2) <
  Market.rustQpObjective fixtureLinearObjectiveSubstitution (fun _ => 1)

#assert_axioms completeProblemIdentityCheck_iff
#assert_axioms complete_problem_identity_eq
#assert_axioms complete_binding_transports_exact_kkt
#assert_axioms externally_bound_bundle_global_optimal
#assert_axioms quadratic_objective_substitution_refused
#assert_axioms linear_objective_substitution_refused
#assert_axioms constraint_matrix_substitution_refused
#assert_axioms lower_bound_substitution_refused
#assert_axioms upper_bound_substitution_refused

/- Program identity remains a purely structural gate: it must not acquire
certificate, residual, SDD, or optimality semantics. -/
#assert_not_depends_on Market.QpExternalProgramBinding.CompleteProblemIdentity [
  Market.rustCertQpCheck,
  Market.rustPrimalResidual,
  Market.rustDualResidual,
  Market.rustNormalResidual,
  Market.PsdSymm,
  Market.SddPsd.SymmetricDiagonallyDominant]

#assert_all_clean [
  Market.QpExternalProgramBinding.completeProblemIdentityCheck_iff,
  Market.QpExternalProgramBinding.complete_problem_identity_eq,
  Market.QpExternalProgramBinding.complete_binding_transports_exact_kkt,
  Market.QpExternalProgramBinding.externally_bound_bundle_global_optimal,
  Market.QpExternalProgramBinding.quadratic_objective_substitution_refused,
  Market.QpExternalProgramBinding.linear_objective_substitution_refused,
  Market.QpExternalProgramBinding.constraint_matrix_substitution_refused,
  Market.QpExternalProgramBinding.lower_bound_substitution_refused,
  Market.QpExternalProgramBinding.upper_bound_substitution_refused]

end Market.QpExternalProgramBinding
