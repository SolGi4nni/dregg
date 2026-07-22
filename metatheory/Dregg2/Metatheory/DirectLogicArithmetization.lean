/-
# Dregg2.Metatheory.DirectLogicArithmetization

Integration root for the corrected direct-logic construction suite.

The imported modules establish seven deliberately separated layers:

* a constructive matrix-language front end for the positive Gabbay fragment,
  with exact rational semantics, certified prime-field projection, a coherent
  adapter between the two formal matrix presentations, and one exact
  three-entry private-witness successor instance in live descriptor IR v2;
* executable countermodels for finite-field cancellation, connective reversal,
  and the published BitLogic swap relation, together with no-wrap and exact
  Boolean repairs;
* an exact finite-signature FOL compiler into live descriptor IR v2, supporting
  public total function tables, arbitrary finite relation signatures, equality,
  every Boolean connective, and exhaustive finite quantification;
* two higher-order/category routes: exact but truth-table-dense finite HOL and
  finite polynomial presentations, and an intensional STLC/shared-net category
  with terminal objects, products, exponentials, evaluation, curry/uncurry, and
  a structural strong-CCC compiler; Yoneda separately gives the fully faithful,
  product- and exponential-preserving semantic embedding of any small CCC into
  presheaves;
* proof-producing local optimization and certified changes of presentation,
  including an auditable finite search over residual, Boolean-graph, and mixed
  representations; the global presentation category is proved not cartesian,
  while evidence families over one fixed meaning form a genuine CCC;
* one-opening proof/FHE coherence: a versioned fail-closed descriptor/BFV
  bundle, an exact theorem binding both backends to the concrete openings stored
  in that bundle, and a certified hybrid plan whose regions may choose bounded
  residual or Boolean evaluation, with exact symbolic cost ledgers; and
* proof-object semantics that do not privilege polynomials: commit-before-seed
  robust descent with explicit OOD, folding, query-miss, and modular-bias terms,
  checked interaction receipts, and realizability/tripos/assembly models.

Scope is load-bearing.  The live Gabbay descriptor is a proved fixed-size
existential private-witness relation, not yet an arbitrary-matrix emitter or an
attestation of an externally named table: its present public-input, hash-site,
and range-site surfaces are empty.  Finite-signature quantifiers are exhaustive
and may expand exponentially; public function tables are not a private RAM
lowering.  Finite HOL is exact but dense.  The intensional strong CCC theorem
covers the represented STLC fragment, while Yoneda is a semantic presheaf
embedding, not a finite-field arithmetization.  Presentation-search optimality
is relative to an explicit finite candidate list and symbolic cost, not
wall-clock latency.  The interaction bridge validates receipts but does not yet
emit descriptor IR.  Robust descent gives a probabilistic finite-game bound,
not deterministic total-column extraction.  The assembly category is not
claimed to be the exact completion or associated topos, and no theorem here
proves Rust/CakeML decoder refinement, FHE security/noise, prover throughput,
or chain finality.
-/

import Dregg2.Metatheory.FOLArithmetizationCounterexamples
import Dregg2.Metatheory.FiniteHOLFormulaArithmetization
import Dregg2.Metatheory.FinitePolynomialCCC
import Dregg2.Metatheory.FinitePolynomialCategoryClassification
import Dregg2.Metatheory.GabbayMatrixBridge
import Dregg2.Metatheory.GabbayDescriptorIR2PublicBoundary
import Dregg2.Metatheory.FinitePatchCodeDescent
import Dregg2.Metatheory.RobustDescentTranscriptGame
import Dregg2.Metatheory.DirectLogicOptimizerCertificate
import Dregg2.Metatheory.CertifiedRepresentationSearch
import Dregg2.Metatheory.CertifiedPresentationFibredCCC
import Dregg2.Metatheory.SmallCCCYonedaPresheaf
import Dregg2.Logic.PredBoolGraph
import Dregg2.Logic.FiniteLogicPlan
import Dregg2.Logic.CompilationCertificateBundle
import Dregg2.Logic.FheLogicSchedule
import Dregg2.Logic.FiniteSignatureFOLDescriptorIR2
import Dregg2.Logic.CertifiedHybridProofFheBoundOpening
import Dregg2.Calculus.LinearInteractionTrace
import Dregg2.Calculus.IntensionalCCCCategory
import Dregg2.Calculus.IntensionalCCCInteractionBridge
import Dregg2.Realizability.Quantifiers
import Dregg2.Realizability.MonadicCombinatoryAlgebra
import Dregg2.Realizability.Assemblies

namespace Dregg2.Metatheory.DirectLogicArithmetization

/-- A kernel-visible marker for the integrated artifact.  The marker itself is
logically inert; importing this module is the build gate for the theorem-bearing
construction suite listed above. -/
theorem integrated_scope :
    True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True := by
  simp

#assert_axioms integrated_scope

end Dregg2.Metatheory.DirectLogicArithmetization
