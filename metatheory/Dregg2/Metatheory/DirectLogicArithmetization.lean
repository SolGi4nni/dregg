/-
# Dregg2.Metatheory.DirectLogicArithmetization

Integration root for the corrected direct-logic construction suite.

The imported modules establish seven deliberately separated layers:

* a constructive matrix-language front end for the positive Gabbay fragment,
  with exact rational semantics, certified prime-field projection, a coherent
  adapter between the two formal matrix presentations, one exact three-entry
  private-witness successor instance in live descriptor IR v2, and a separate
  six-public-input direct-table relation binding the named external table;
* executable countermodels for finite-field cancellation, connective reversal,
  and the published BitLogic swap relation, together with no-wrap and exact
  Boolean repairs;
* an exact finite-signature FOL compiler into live descriptor IR v2, supporting
  public total function tables, arbitrary finite relation signatures, equality,
  every Boolean connective, and exhaustive finite quantification, plus public
  live certificates and exact resource ledgers for four named DREGG decision
  skeletons: turn admission, upgrade authorization, credential clearance, and
  strand admission;
* two higher-order/category routes: exact but truth-table-dense finite HOL and
  finite polynomial presentations, including a degree-one family-polynomial
  Yoneda action for locally finite hom-sets, and an intensional STLC/shared-net
  category with terminal objects, products, exponentials, evaluation,
  curry/uncurry, and a structural strong-CCC compiler; Yoneda is fully faithful
  and product- and exponential-preserving, but no fixed finite coordinate budget
  can faithfully present every hom-set even in the CCC of finite sets;
* proof-producing local optimization and certified changes of presentation,
  including a live materialized quadratic Boolean-graph descriptor, a separate
  public-input-bound statement descriptor, exact layout/byte certificates for
  both, an auditable finite search over residual, Boolean-graph, and mixed
  representations, and an indexed four-mode compiler which charges conversion
  and recombination glue explicitly; the global presentation category is proved
  not cartesian, while evidence families over one fixed meaning form a genuine
  CCC;
* one-opening proof/FHE coherence: a versioned fail-closed descriptor/BFV
  bundle, an exact theorem binding both backends to the concrete openings stored
  in that bundle, and a certified hybrid plan whose regions may choose bounded
  residual or Boolean evaluation, with exact symbolic cost ledgers; exact
  zero-observation accounting proves the whole-field depth obstruction, prices
  bounded-domain conversion and threshold opening, and removes the advertised
  multiplication advantage; and
* proof-object semantics that do not privilege polynomials: commit-before-seed
  robust descent with explicit OOD, folding, query-miss, and modular-bias terms,
  a categorical coverage protocol natural under exact changes of presentation
  whose false-acceptance budget separates OOD, low degree, binding failure, and
  query miss,
  a live public IR-v2 compiler for checked interaction receipts, and
  realizability/tripos/assembly models with effective pullback-stable covers,
  kernel-pair coequalizers, and regular-image factorization.

Scope is load-bearing.  The interpolation-bearing Gabbay descriptor is a proved
fixed-size existential private-witness relation whose public-input, hash-site,
and range-site surfaces are empty.  The public-binding variant closes the
external-statement gap with six direct public table cells, six columns, seven
constraints, and three nonlinear products, but intentionally omits
interpolation and reveals the whole table.  Neither is an arbitrary-matrix
emitter or a private commitment-backed public statement.  Finite-signature
quantifiers are exhaustive and may expand exponentially; public function
tables are not a private RAM lowering.  The production DREGG workload results
compile the exact named Boolean decision skeletons, but arithmetic, membership,
lifecycle, capability lookup, and receipt comparison remain explicit atom
boundaries.  Finite HOL is exact but dense.  Family-polynomial Yoneda gives an
exact degree-one action hom-set by hom-set under local finiteness; it is not one
uniform succinct backend, and the finite-set CCC proves that no fixed finite
coordinate budget can be faithful for all of its hom-sets.  The intensional
strong CCC theorem covers the represented STLC fragment.  The indexed
presentation compiler preserves semantics and composes explicit resource
morphisms, but its finite search is only candidate-list-relative, glue is not
free, and semantic adapters are not live emitters for every backend.  On the
proved four-input
factor-sharing specimen, the abstract graph ledger moves from 30 to 13
equations, while the accepting live descriptor moves from 31 to 14 because it
adds `output = 1`.  The four-input public statement adds four linear bindings,
so its total moves from 35 to 18 constraints with four public inputs.
Multiplications move from 26 to 13, auxiliaries from 17 to 8, and total width
from 21 to 12, with every constraint of degree at most two.  The unbound
descriptor's `Satisfied2` equivalence is only about the compiler's canonical
one-row trace.  By contrast, every nonempty trace satisfying the public
descriptor proves the formula under the public residual vector, and every true
formula has a canonical satisfying public trace; the accepted public
certificate transports soundness back across optimization and pins the exact
PI layout and emitted bytes.  These are structural and symbolic cost theorems,
not a comparative wall-clock speedup.  The four production public ledgers are:
turn admission, 108 to 58 graph equations, 121 to 71 public constraints, 108 to
58 multiplications, 65 to 35 auxiliaries, and width 77 to 47; upgrade
authorization and credential clearance, each 28 to 18 graph equations, 33 to
23 public constraints, 28 to 18 multiplications, 17 to 11 auxiliaries, and
width 21 to 15; strand admission is already normal at 13 graph equations, 17
public constraints, 13 multiplications, 8 auxiliaries, and width 11.

Exact encrypted zero observation is not free.  Over the whole deployed
plaintext field its arithmetic-circuit depth is at least twenty.  On a bounded
domain the certified product conversion costs `B - 1` multiplications: the
five-equality symbolic comparison becomes 9 versus 9, not 6 versus 9.  The
paired Rust carrier executes the `B = 2` scaled conversion; at `B = 8`, full
accounting is 15 versus 15, and the captured run's final threshold observation
refused a noncanonical value under the current unproved multiplied-ciphertext
noise envelope rather than treating it as a bit.  This is not a BFV
noise/security theorem, the same-opening verifier remains external, and
threshold residual opening leaks the opened residuals.

The interaction-receipt compiler now emits a live public descriptor with
`depth + 5` public inputs, columns, and linear bindings, two endpoint hash
sites, and direct one-site support through depth fourteen at rate sixteen.
Arbitrary satisfying traces bind the exact executable receipt and preserve the
typed denotation, but receipt layout erases typed endpoint syntax: no decoder
can reconstruct every exact typed source without adding new statement data.
Robust descent gives a probabilistic finite-game bound, not deterministic
total-column extraction.  The categorical query protocol factors false
acceptance into OOD, low-degree, valid-opening binding-failure, and query-miss
budgets, and its miss event is natural under composed presentation pullbacks.
Its Fiat-Shamir/FRI/cryptographic reductions and fixed-responder sampler bounds
remain external; the transparent finite-code instantiation is reference-only,
and UFam contributes top/bottom predicate classification rather than an
associated-topos theorem.
Effective assembly covers are stable under pullback and yield kernel-pair
coequalizers and regular-image factorizations, including for compiled program
certificates; they do not construct the exact completion/associated topos or
supply commitment/query soundness.  No theorem here proves Rust/CakeML decoder
refinement, a general FHE security/noise bound, prover throughput, or chain
finality.
-/

import Dregg2.Metatheory.FOLArithmetizationCounterexamples
import Dregg2.Metatheory.FiniteHOLFormulaArithmetization
import Dregg2.Metatheory.FinitePolynomialCCC
import Dregg2.Metatheory.FinitePolynomialCategoryClassification
import Dregg2.Metatheory.FamilyPolynomialYonedaFrontier
import Dregg2.Metatheory.GabbayMatrixBridge
import Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding
import Dregg2.Metatheory.FinitePatchCodeDescent
import Dregg2.Metatheory.RobustDescentTranscriptGame
import Dregg2.Metatheory.CategoricalDescentQueryProtocol
import Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
import Dregg2.Metatheory.DirectLogicDreggWorkloads
import Dregg2.Metatheory.CertifiedRepresentationSearch
import Dregg2.Metatheory.CertifiedPresentationFibredCCC
import Dregg2.Metatheory.CertifiedIndexedPresentationCompiler
import Dregg2.Metatheory.SmallCCCYonedaPresheaf
import Dregg2.Logic.PredBoolGraph
import Dregg2.Logic.FiniteLogicPlan
import Dregg2.Logic.CompilationCertificateBundle
import Dregg2.Logic.FheLogicSchedule
import Dregg2.Logic.FiniteSignatureFOLDescriptorIR2
import Dregg2.Logic.CertifiedHybridProofFheBoundOpening
import Dregg2.Logic.CertifiedHybridProofFheZeroObservation
import Dregg2.Logic.CertifiedHybridProofFheSymmetricZeroObservation
import Dregg2.Logic.CertifiedHybridProofFhePairedRootZeroObservation
import Dregg2.Calculus.LinearInteractionTrace
import Dregg2.Calculus.IntensionalCCCCategory
import Dregg2.Calculus.IntensionalCCCInteractionBridge
import Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2
import Dregg2.Realizability.Quantifiers
import Dregg2.Realizability.MonadicCombinatoryAlgebra
import Dregg2.Realizability.Assemblies
import Dregg2.Realizability.AssemblyRegularCoverage

namespace Dregg2.Metatheory.DirectLogicArithmetization

/-- A kernel-visible marker for the integrated artifact.  The marker itself is
logically inert; importing this module is the build gate for the theorem-bearing
construction suite listed above. -/
theorem integrated_scope :
    True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True := by
  simp

#assert_axioms integrated_scope

end Dregg2.Metatheory.DirectLogicArithmetization
