/-
# Market.QpCertificateBundle — the semantic join behind `FHQPB001`.

The transport bundle carries two independently checked objects: an SDD
admission certificate for the objective matrix and an exact KKT certificate.
Neither fact is sufficient alone.  This file states the small composition law
at their decoded rational meaning:

* the SDD witness names a matrix `admittedP`;
* the KKT witness names a `RustQpProblem`;
* `admittedP = prob.p` is an explicit, load-bearing matrix pin; and
* exact feasibility, stationarity, and normal-cone acceptance imply that the
  witness minimizes the same objective over every feasible point.

Wire parsing, fixed-point decoding, checksums, and authentication remain
outside Lean.  In particular, this theorem does not turn positive-tolerance
`rustCertQpCheck = true` into exact KKT: `rustApprox_accepts_nonexact_stationarity`
proves that implication false.  A carrier refinement may use this theorem only
after establishing the exact propositions below for its decoded values.
-/

import Market.SddPsd
import Market.CertQpRustDenotation
import Dregg2.Tactics

namespace Market.QpCertificateBundle

set_option autoImplicit false

/-- The admission and optimizer certificates must denote exactly the same
rational objective matrix.  This is the semantic form of `FHQPB001`'s
entry-for-entry matrix comparison after fixed-point decoding. -/
def MatrixPinned {n mc : Nat} (prob : Market.RustQpProblem n mc)
    (admittedP : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  admittedP = prob.p

/-- Exact-zero KKT acceptance for the deployed OSQP problem denotation.  This
is intentionally stronger than acceptance by a positive residual tolerance. -/
structure ExactKktAccepted {n mc : Nat} (prob : Market.RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) : Prop where
  feasible : Market.RustQpFeasible prob x
  stationary : Market.RustQpStationary prob x y
  normalCone : Market.RustQpNormalCone prob x y

/-- Semantic meaning of the two certificates joined by `FHQPB001`.  The
admitted matrix is already the decoded rational matrix; transport and scale
refinement are separate obligations. -/
structure ExactQpCertificateBundle {n mc : Nat}
    (prob : Market.RustQpProblem n mc)
    (admittedP : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) : Prop where
  sdd : Market.SddPsd.SymmetricDiagonallyDominant admittedP
  matrixPinned : MatrixPinned prob admittedP
  kkt : ExactKktAccepted prob x y

/-- Matrix equality is the only substitution step between the independent SDD
and KKT meanings.  A valid SDD witness for a different matrix cannot supply
the optimizer's PSD premise. -/
theorem matrix_pin_transports_psd {n mc : Nat}
    {prob : Market.RustQpProblem n mc}
    {admittedP : Matrix (Fin n) (Fin n) ℚ}
    (hSdd : Market.SddPsd.SymmetricDiagonallyDominant admittedP)
    (hPinned : MatrixPinned prob admittedP) :
    Market.PsdSymm prob.p := by
  rw [← hPinned]
  exact Market.SddPsd.sdd_implies_psd hSdd

/-- **FHQPB001 semantic composition.** Exact SDD admission for the exact same
matrix plus exact repaired KKT acceptance proves global optimality. -/
theorem exact_bundle_global_optimal {n mc : Nat}
    {prob : Market.RustQpProblem n mc}
    {admittedP : Matrix (Fin n) (Fin n) ℚ}
    {x : Fin n → ℚ} {y : Fin mc → ℚ}
    (bundle : ExactQpCertificateBundle prob admittedP x y)
    {x' : Fin n → ℚ} (hfeas' : Market.RustQpFeasible prob x') :
    Market.rustQpObjective prob x ≤ Market.rustQpObjective prob x' := by
  exact Market.rustExactKkt_optimal prob
    (matrix_pin_transports_psd bundle.sdd bundle.matrixPinned)
    bundle.kkt.feasible bundle.kkt.stationary bundle.kkt.normalCone hfeas'

#assert_axioms matrix_pin_transports_psd
#assert_axioms exact_bundle_global_optimal

/- The matrix pin is structural equality only.  It must not acquire PSD, SDD,
or KKT semantics: those remain independent certificate obligations. -/
-- POSITIVE CONTROL for the rejectors below: the optimality proof transports PSD across the matrix
-- pin, and that lemma appears only in its proof term.
#assert_depends_on Market.QpCertificateBundle.exact_bundle_global_optimal
  [Market.QpCertificateBundle.matrix_pin_transports_psd]

#assert_not_depends_on Market.QpCertificateBundle.MatrixPinned [
  Market.PsdSymm,
  Market.SddPsd.SymmetricDiagonallyDominant,
  Market.RustQpFeasible,
  Market.RustQpStationary,
  Market.RustQpNormalCone]

/- Exact KKT acceptance does not smuggle in the independent convexity
admission. -/
#assert_not_depends_on Market.QpCertificateBundle.ExactKktAccepted [
  Market.PsdSymm,
  Market.SddPsd.SymmetricDiagonallyDominant,
  Market.SddPsd.sddCheck]

#assert_all_clean [
  Market.QpCertificateBundle.matrix_pin_transports_psd,
  Market.QpCertificateBundle.exact_bundle_global_optimal]

end Market.QpCertificateBundle
