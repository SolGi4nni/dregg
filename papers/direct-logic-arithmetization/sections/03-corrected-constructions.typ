#import "../section-helpers.typ": callout, theorem, boundary

= Corrected constructions: from matrices to searched proof plans

The corrected development is now a coherent compiler stack rather than a
replacement connective table. It begins with Gabbay-style integer matrices and
exact rational interpolation, proves that an independently defined source
semantics agrees with the compiled polynomial, crosses into a finite field only
through an explicit projection certificate, and reaches DREGG's live descriptor
relation. A second compiler handles arbitrary finite signatures. Above both sit
checked optimization and certified representation search.

#callout([CONSTRUCTION RESULT], [
  There is a sound version of the matrix idea. Its invariant is not "first-order
  logic is automatically a finite-field circuit." The invariant is: exact
  nonnegative rational semantics first; a proved prime and no-wrap boundary or
  an exact Boolean repair second; and a checked live relation last. Every
  transition now has a theorem, a refusal case, and a stated cost and
  public-binding boundary.
])

== Construction map

#text(size: 7.35pt)[#table(
  columns: (0.78fr, 1.35fr, 1.68fr, 1.55fr),
  inset: 4pt,
  align: (left, left, left, left),
  table.header([*Layer*], [*Construction*], [*Exact result*], [*Lean artifact*]),
  [Matrix semantics],
  [integer tables, one-based rational Lagrange rows, bounded matrix quantifiers],
  [compiled residual is zero iff the independently defined source formula holds],
  [#raw("GabbayMatrix")#linebreak()#raw("Semantics")],
  [Compiler agreement],
  [positive-arity adapter between the semantics view and the proof-carrying compiler],
  [row, term, formula, truth, residual, cost, projection certificate, and Skolem witness agree],
  [#raw("GabbayMatrix")#linebreak()#raw("Compiler / Bridge")],
  [Field boundary],
  [reduced numerator and positive denominator plus prime/no-wrap certificate],
  [field zero iff rational zero iff source truth; bad modulus is rejected],
  [#raw("GabbayFiniteField")#linebreak()#raw("Projection")],
  [Live Gabbay instance],
  [two-row, three-column successor table in DescriptorIR2],
  [17-column constructive private trace; 12 constraints; exact for the table carried by that trace, but not externally bound],
  [#raw("GabbayDescriptorIR2")],
  [General finite FOL],
  [public total functions, witness relation tables, equality, all Boolean connectives and bounded quantifiers],
  [canonical trace accepts iff the finite model satisfies the sentence],
  [#raw("FiniteSignatureFOL")#linebreak()#raw("DescriptorIR2")],
  [Optimization],
  [checked local identities, factoring, sharing, and nonempty-fold elimination],
  [source meaning and field-graph acceptance preserved; symbolic cost cannot increase],
  [#raw("DirectLogicOptimizer")#linebreak()#raw("Certificate")],
  [Representation search],
  [finite graph of exact presentation changes and per-formula plan enumeration],
  [selected composite remains exact; winner is minimal in the explicit candidate list],
  [#raw("CertifiedRepresentation")#linebreak()#raw("Search")],
)]

== Exact matrix semantics and its compiler

For a matrix with `rows` rows and `length` declared columns,
`IntMatrix.rowPolynomial` is the unique rational Lagrange interpolant through
the one-based nodes $1, ..., "length"$. The two facts needed downstream are
proved directly:

$
  P_r(j+1) = M_(r,j),
  quad "degree"(P_r) < "length".
$

Terms contain the distinguished index, rational constants, arithmetic, matrix
length, and row lookup. Formula atoms are squared equalities. Conjunction and
bounded universal quantification add nonnegative residuals; disjunction and
bounded existence multiply them. `residual_nonnegative` is the load-bearing
lemma that rules out additive cancellation over $QQ$. The central theorem,
`residual_eq_zero_iff_holds`, proves for every valuation, rational index, and
formula $phi$:

$
  rho_(M,x)(phi) = 0 quad "iff" quad M,x models phi.
$

The quantifiers range over exactly the columns declared by the selected matrix.
`quantifierExpansion_eq_length` records the exact number of body instantiations.
Because each bounded quantifier closes its index, its compiled polynomial is
constant in the outer index; `forall_degree_le_zero` and
`exists_degree_le_zero` state that fact. These are degree theorems, not claims
about prover latency.

`GabbayMatrixCompiler` independently defines its own signature, matrices,
source satisfaction, term evaluation, and polynomial compiler. Its
`eval_polynomial_eq_zero_iff` proves the same exact source/compiler relation.
`GabbayMatrixBridge` then prevents agreement-by-prose: under `PositiveArity`, it
proves equality of row polynomials, term and formula polynomials, source truth,
residuals, and exact expansion costs. `ViewCertificate.toCompiler` transports
matrix bounds, numerator and denominator bounds, and the cost equality into the
canonical compiler certificate.

#theorem([matrix/Skolem specimen], [
  The checked specimen is an actual two-row, three-column integer table. Its
  first row is the input and its second row is the chosen successor output.
  `successorTable_size` proves an exact six-cell table;
  `successorTable_row_degrees_exact` proves that both interpolants have degree
  one. Through the bridge, exhaustive universal checking costs exactly three
  equality atoms and two additions, and `successor_skolem_through_bridge`
  constructs the finite Skolem witness. The transported certificate discharges
  the $p=17$ projection theorem without repeating the bound proof.
])

#boundary([
  The bridge's only semantic mismatch is explicit: the exploratory semantics
  type permits a zero-column matrix, while the compiler signature requires
  positive arity. This stack formalizes bounded finite matrix semantics. It is
  neither ordinary unbounded first-order quantification nor a succinctness
  theorem.
])

== The field boundary is a certificate, not a cast

Let the exactly evaluated residual be the reduced rational $q=a/b$, with
$b>0$. `ProjectionCertificate q p` carries three facts:

$
  p " is prime", quad |a| < p, quad b < p.
$

`projectCleared` sends only $a$ into $ZZ / p ZZ$;
`projectRational` sends $a/b$ after proving that the denominator remains
invertible. `projectCleared_eq_zero_iff` and
`projectRational_eq_zero_iff` prove that either representation is zero in the
field exactly when $q=0$. Composing that result with matrix correctness gives
`projected_formula_zero_iff_holds` and
`projected_rational_formula_zero_iff_holds`.

The compiler emits the auditable floor

$
  "modulusFloor"(q) = max(|a|, b) + 1.
$

Any prime at least this floor constructs the certificate.
`ProjectionCost` retains four distinct quantities: formula degree, numerator
magnitude, normalized denominator, and required modulus floor. They are not
collapsed into a context-free speedup number.

#callout([EXECUTABLE COUNTEREXAMPLE], [
  The false atom $0=5$ has exact residual $25$. An unchecked projection to
  $ZZ/5ZZ$ returns zero, so `badPrime_unchecked_accepts` exhibits the failure in
  executable form. `badPrime_certificate_rejected` proves that the corrected
  compiler refuses the same case because the required strict inequality
  $25<5$ is impossible. This is the smallest useful answer to "why not just
  evaluate the rational construction in a field?"
])

For cases where a useful no-wrap certificate is unavailable, the independent
Boolean repair remains exact over every field. Atomic zero tests introduce a
bit and an inverse witness; Boolean connectives then operate on constrained
bits. `Formula.falseBit_isBit_and_correct` and `falseBit_eq_zero_iff` in the
matrix compiler prove that this alternative supports the full matrix formula
language without pretending that rational addition retained its semantics
after reduction.

== Two routes into the live DREGG relation

=== A fixed-shape private witness/semantics bridge

`GabbayDescriptorIR2` lowers a nontrivial matrix instance into the actual
`EffectVmDescriptor2` grammar used by DREGG. Its source is a two-row,
three-column graph of a unary successor function. The trace contains the six
table entries, six denominator-cleared interpolation coefficients, three
squared residuals, their numerator, and a denominator marker: exactly 17
columns.

For row values $y_1,y_2,y_3$, the compiler stores the coefficients of $2P(X)$:

$
  (6y_1-6y_2+2y_3,
   -5y_1+8y_2-3y_3,
   y_1-2y_2+y_3).
$

This avoids witness-authored division inside the interpolation checks. Six
interpolation identities, three squared-residual identities, one numerator
identity, one denominator identity, and one acceptance identity give exactly
12 live constraints. The coefficient columns are nevertheless redundant for
the current acceptance path: the residual and acceptance gates read the raw
input and output entry columns directly. This instance therefore demonstrates
a faithful fixed-shape witness/semantics bridge, not a performance advantage
from interpolation. Under `LiveProjectionCertificate`,
`trace_satisfied_iff_holds` proves a table-indexed equivalence: `traceOf table`
satisfies the emitted BabyBear relation exactly when the source formula holds
of that same `table`. The canonical successor trace is constructed, the
constructed trace of a one-cell tamper is refused, and the known modulus-five
projection cannot enter the compiler.

#boundary([
  The current descriptor is an existential private-witness statement, not an
  attestation of an externally named table. `descriptor_public_surface_empty`
  proves `piCount = 0`, `hashSites = []`, and `ranges = []`.
  `constructed_traces_publicly_indistinguishable` proves that every constructed
  table trace exposes the same empty public assignment. Most sharply,
  `accepting_trace_does_not_attest_external_table` constructs an accepting
  successor witness while a separately named tampered table is false; there is
  no contradiction because that external table is absent from `Satisfied2`.
  A public input or binding commitment is required before this relation can
  attest a claimed model. It is also not yet a generator for arbitrary matrix
  dimensions: that requires emitted interpolation, denominator management,
  range certificates, and cost accounting. IR-v2 fixes BabyBear; the witness
  does not choose its own field.
])

=== General finite-signature FOL

`FiniteSignatureFOLDescriptorIR2` takes the complementary route. A signature
may contain any finite list of relation symbols with independent arities and
any finite list of total function symbols with complete public
interpretations. Terms include constants, de Bruijn variables, and nested
function application. Formulae include equality, relation application, every
Boolean connective, and exhaustive finite universal and existential
quantification.

For a $q$-element domain and relation arities $a_r$, the canonical witness-row
width is proved exactly:

$
  W = sum_r q^(a_r).
$

The row concatenates every relation table in symbol-major, tuple-major order;
the descriptor contains $W+1$ constraints. `fol_sound`, `fol_complete`, and
`canonical_model_trace_iff` prove soundness, constructive completeness, and
the exact canonical-trace equivalence. A checked `FOLLiveCertificate` binds the
version, complete function-table signature, relation-column layout, encoded
source formula, grounded Boolean source, and the live descriptor certificate.
`checked_fol_sound` carries those bindings through to the original sentence.

#theorem([nested finite-FOL specimen], [
  The $q=2$ specimen has a public unary `flip` function, one unary relation,
  one binary relation, and the sentence
  $forall x. exists y. R_1("flip"(x),y) and
  R_0("flip"("flip"(x)))$.
  Its exact row width is $2+4=6$ and its descriptor has seven constraints. A
  canonical model trace satisfies the live relation; replacing the certified
  layout by the empty list is rejected.
])

#boundary([
  Grounding is exhaustive and can grow exponentially with quantifier depth.
  Function tables are public compilation inputs in this construction; private
  functions require a lookup or RAM lowering. The theorem is an exact finite
  model compiler, not a succinct quantifier protocol.
])

== Checked optimization with exact savings

Optimization is now proof-producing. `DirectLogicOptimizerCertificate.Rule`
contains only audited identities, nonempty-fold elimination, factorization,
and explicit fanout sharing. A local claim binds the proposed before term,
after term, rule payload, and side condition. `checkLocal` rejects a changed
endpoint or a false guard. Composite certificates additionally check that the
target of one step is the source of the next.

For every accepted certificate, the formal results are simultaneous:

- `Certificate.check_sound` preserves source truth;
- `Certificate.accepts_iff` preserves the exact field `BoolGraph` relation;
- `Certificate.check_cost_nonincrease` proves componentwise nonincrease of
  equations, multiplications, witnesses, maximum degree, and dense table cells;
- `optimize_checked` proves that the deterministic recursive optimizer always
  emits a valid certificate; and
- `optimize_accepts_iff` and `optimize_cost_nonincrease` expose the end-to-end
  semantic and cost contracts.

#text(size: 7.25pt)[#table(
  columns: (1.55fr, 0.78fr, 0.92fr, 0.78fr, 1.42fr),
  align: (left, center, center, center, left),
  table.header([*Checked specimen*], [*Equations*], [*Multiplications*],
    [*Witnesses*], [*What changed*]),
  [shared common factor], [42 -> 30], [40 -> 29], [25 -> 18],
    [one duplicated two-gate factor compiled once],
  [recursive certified optimizer], [30 -> 13], [26 -> 13], [17 -> 8],
    [identities removed, then common factor shared],
)]

Both targets retain local degree two. The optimizer's hostile specimens reject
a tampered target, an empty-fanout application, and a broken certificate
boundary. These are counts in the abstract materialized `BoolGraph` ledger.
The current live DescriptorIR2 compiler instead uses atom Booleanity gates and
nested `WindowExpr` syntax without the same intermediate columns, so these
figures do not establish a saving in the current live prover. They are neither
prover-time measurements nor an end-to-end benchmark.

== Exact presentations and finite search

`CertifiedPresentationChange.Presentation` packages source meaning, evidence,
acceptance, and a resource vector. An exact `Change P Q` maps evidence in both
semantic directions and carries a compositional resource bound. Identity and
composition form a genuine category, so a compiler can change representation
without dissolving its proof obligation.

The concrete nodes are:

- proof-carrying natural no-wrap residuals;
- exact finite-field Boolean graphs; and
- hybrid evidence selecting either representation independently at each
  positive subformula.

`HybridEvidence.accepts_iff` proves every such mixture exact. The direct
no-wrap-to-hybrid arrow agrees observationally with the route through a Boolean
graph. `CertifiedRepresentationSearch` lifts these nodes to a finite graph of
typed exact edges. Paths compose to exact changes, and their symbolic overhead
composes with them. `shortestEnumerated_minimal` proves that the selected path
has minimum scalar score among the caller-supplied candidates;
`shortestEnumerated_composite_exact` proves that selection cannot change
acceptance.

The static specimen makes the selection logic concrete. In $ZZ/5ZZ$, two true
atoms have actual residual zero but public upper bound three. The whole
conjunction has static upper bound six and is therefore refused as one no-wrap
node; each atom remains locally safe. The selected plan splits at the root and
uses no-wrap leaves. It is proved accepting and minimal in the enumeration,
with symbolic score $0$ versus $23$ for the all-Boolean graph.

#boundary([
  Search minimality is relative to an explicit finite candidate list and to
  the transparent score
  $E+M+W+D+T$; it is not global compiler optimality or a latency model. In the
  static specimen, score zero means that atomic no-wrap skeletons cost zero in
  this ledger and split acceptance is represented by meta-level conjunction.
  A concrete backend must materialize and charge any glue gates it needs. The
  theorem proves exact plan selection; it does not turn uncharged glue into
  free computation.
])

#callout([WHAT HAS BEEN RECOVERED], [
  The defensible performance thesis is local and certified: exploit a compact
  residual exactly where a range proof makes it sound; use Boolean zero tests
  where it does not; share repeated structure; and search only among
  meaning-preserving changes of presentation. The checked specimens show
  substantial symbolic reductions, but no theorem here implies a universal
  10-100x end-to-end speedup or chain finality.
])
