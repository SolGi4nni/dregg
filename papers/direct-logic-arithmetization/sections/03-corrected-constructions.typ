#import "../section-helpers.typ": callout, theorem, boundary, rust

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
  [Private Gabbay bridge],
  [two-row, three-column successor table in DescriptorIR2],
  [12-column constructive private trace; 15 constraints (9 gates plus 6 emitted 30-bit range lookups); exact for the table carried by that trace, but not externally bound],
  [#raw("GabbayDescriptorIR2")],
  [Public Gabbay statement],
  [six direct public table cells pinned to a six-column trace],
  [15 constraints (6 PI pins, 3 linear atoms, 6 range lookups) and zero nonlinear products; any accepted canonical trace attests the named external table],
  [#raw("GabbayDescriptorIR2")#linebreak()#raw("PublicBinding")],
  [Wire-hole canaries],
  [the two canonical false tables that retired the previous acceptance shape, kept armed],
  [each half of the repair refutes a table the other half admits; both refused as preselected traces and as external statements, with a positivity control],
  [#raw("DirectLogicAdversarial")#linebreak()#raw("FalsifierV2")],
  [General finite FOL],
  [public total functions, witness relation tables, equality, all Boolean connectives and bounded quantifiers],
  [canonical trace accepts iff the finite model satisfies the sentence],
  [#raw("FiniteSignatureFOL")#linebreak()#raw("DescriptorIR2")],
  [Optimization],
  [checked identities, factoring and sharing, followed by explicit materialized BoolGraph emission],
  [source meaning, public arbitrary-trace soundness and exact resource reductions are preserved],
  [#raw("DirectLogicOptimizer")#linebreak()#raw("Certificate")#linebreak()
   #raw("DirectLogicBoolGraph")#linebreak()#raw("DescriptorIR2")],
  [DREGG workloads],
  [admission, upgrade, credential clearance, and strand-admission Boolean skeletons],
  [public live soundness against named production decisions; exact before/after ledgers],
  [#raw("DirectLogicDregg")#linebreak()#raw("Workloads")],
  [Representation search],
  [finite exact-change graph plus an indexed per-subterm compiler with explicit conversion and glue costs],
  [selected composite remains exact; materialized ledger has no untracked remainder],
  [#raw("CertifiedRepresentation")#linebreak()#raw("Search")#linebreak()
   #raw("CertifiedIndexed")#linebreak()#raw("PresentationCompiler")],
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

== Routes into the live DREGG relation

=== A fixed-shape private witness/semantics bridge

`GabbayDescriptorIR2` lowers a nontrivial matrix instance into the actual
`EffectVmDescriptor2` grammar used by DREGG. Its source is a two-row,
three-column graph of a unary successor function. The trace contains the six
table entries and six denominator-cleared interpolation coefficients: exactly
12 columns (`TRACE_WIDTH = 12`). There are no residual, numerator, or
denominator columns; the repair described in _The wire hole and its repair_
below retired all three.

For row values $y_1,y_2,y_3$, the compiler stores the coefficients of $2P(X)$:

$
  (6y_1-6y_2+2y_3,
   -5y_1+8y_2-3y_3,
   y_1-2y_2+y_3).
$

This avoids witness-authored division inside the interpolation checks. Six
interpolation identities, three linear acceptance atoms
$"output"_j - "input"_j - 1$, and six 30-bit range lookups --- one on each
entry column --- give exactly 15 live constraints
(`compileDescriptor.constraints.length = 15`). The coefficient columns are
nevertheless redundant for the current acceptance path: the acceptance atoms
read the raw input and output entry columns directly. This instance therefore
demonstrates a faithful fixed-shape witness/semantics bridge, not a
performance advantage from interpolation.

`trace_satisfied_iff_holds` proves a table-indexed equivalence: `traceOf table`
satisfies the emitted BabyBear relation exactly when the source formula holds
of that same `table`. Its `WireBoundedTable` hypothesis is a premise of the
*completeness* direction only --- it names which tables this descriptor can
express. Soundness needs no side condition on the claim: the six emitted
lookups are what `accepting_trace_wire_bounded` reads the 30-bit bound off,
so a table outside the checked domain is refused rather than silently
accepted. The canonical successor trace is constructed, the constructed trace
of a one-cell tamper is refused, and the known modulus-five projection cannot
enter the compiler.

#boundary([
  The current descriptor is an existential private-witness statement, not an
  attestation of an externally named table. `descriptor_public_surface_empty`
  proves `piCount = 0`, `hashSites = []`, `ranges = []`, and
  `constraints.length = 15`. Read the third conjunct exactly: `ranges` is the
  v1 range *carrier* field, and it is empty by construction because the
  deployed v2 assembly refuses a descriptor that carries it at all. The
  no-wrap bound is enforced by the six graduated `lookup` constraints against
  the declared 30-bit range table, which the assembly lowers to a real
  byte-limb decomposition. An empty `ranges` field is not an absent range
  check. A range tooth binds no external *name*, however, so it does not close
  the statement gap this boundary records.
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

=== Direct-table public binding

`GabbayDescriptorIR2PublicBinding` closes the statement gap with a distinct,
smaller descriptor. All six cells of the claimed two-by-three table are public
inputs. Six first-row PI bindings pin them to six trace columns; three
always-on gates check the three successor equations, one equation per gate;
and six `lookup` constraints check that each bound column is a 30-bit value in
the declared range table. There are no interpolation coefficients, denominator
column, hash site, or commitment assumption. The descriptor's `ranges` field is
empty --- the enforcing instrument is the six lookups, not the v1 carrier.

The exact ledger is proved by `descriptor_public_surface_exact` and
`direct_public_cost_exact`:

#table(
  columns: (0.9fr, 0.9fr, 0.9fr, 0.85fr, 1.05fr, 1fr),
  align: (center, center, center, center, center, center),
  table.header([*Public inputs*], [*Trace columns*], [*Constraints*],
    [*Range teeth*], [*Nonlinear products*], [*Private table cells*]),
  [6], [6], [15], [6], [0], [0],
)

The 15 constraints are 6 PI pins, 3 linear acceptance atoms, and 6 range
lookups. Acceptance contains *no* nonlinear product: counting multiplication by
constants, the whole acceptance block is 6 multiplication nodes, and
`acceptanceNonlinearMulNodes = 0`. `publicLayout` pins the exact PI order,
while an executable guard pins the full emitted descriptor JSON byte-for-byte,
including `"sem":"range","bits":30` on table 2 and the six
`{"t":"lookup","table":2,...}` entries. Without that byte pin the teeth could
be deleted and the constraint count alone would not notice, since it sees how
many constraints there are and not which.

The statement theorem is now external rather than witness-relative.
`StatementSatisfied hash claim trace` is exactly three conjuncts: the trace is
nonempty, its `.range` table is the honest 30-bit table, and it satisfies the
emitted descriptor under the claimed public vector. Both surviving conjuncts
are conditions on the *witness*, not side conditions on the claim. Canonicality
of the first row is no longer among them: the descriptor's own teeth force it,
which is what `first_row_input_bounded` and `first_row_output_bounded` prove.
`statement_sound` then proves that *any* such satisfying trace implies `Holds`
of the externally named table, with the claim's only hypothesis being the
decoding convention that the six public field elements are read as canonical
BabyBear integer representatives. `statement_complete` constructs a trace for
every wire-bounded true claim, and `public_statement_satisfied_iff_holds`
packages the exact result:

$
  exists t. "StatementSatisfied"(h, M, t)
  quad "iff" quad M models phi_"successor".
$

`tampered_public_statement_refused` proves that the one-cell public tamper has
no satisfying canonical witness. This is stronger than refusing one
preselected trace: the public statement itself is impossible.

#boundary([
  Public integrity is purchased by revealing the whole table.
  `public_statement_reveals_whole_table` proves that equality of the six public
  inputs implies equality of all table cells. This descriptor therefore has
  zero table privacy. It also makes no interpolation performance claim: there
  are no coefficient columns and interpolation is not part of logical
  acceptance. The result is an exact fixed-shape public statement, not an
  arbitrary-matrix compiler.
])

=== The wire hole and its repair

Both Gabbay descriptors above are the *second* version. The first accepted a
fully canonical false table, and the counterexample that retired it is
reproduced here because it is the most instructive artifact in this section.

#callout([THE HOLE], [
  Acceptance used to be a single always-on gate on the sum of the three squared
  successor residuals, sound only under a Lean-side `LiveProjectionCertificate`
  bounding the integer numerator, plus a `CanonicalFirstRow` trace premise.
  Neither premise was ever serialized, so the emitted bytes did not enforce what
  made them sound. Over BabyBear $284861408^2 = -1$, so residuals $1$,
  $284861408$, $0$ give $1 + (-1) + 0 = 0$ in the field while two of the three
  equations fail. The table $"input" = (0,0,0)$, $"output" = (2, 284861409, 1)$
  is fully canonical, lies inside the descriptor's checked domain, is false,
  and was ACCEPTED. `wrapClaim_residual_exact` records its exact integer
  numerator $81146021767742465 = 2013265921 times 40305665$, and
  `wrapClaim_numerator_exceeds_modulus` records that the retired certificate
  demanded exactly the bound this table violates.
], tone: rust)

Two independent defects meet in that table. A field sum of squares is not a
conjunction, because a field has no order to make squares nonnegative. And the
condition that repaired the arithmetic lived in Lean rather than in the
descriptor, so no emitted byte checked it. The second is the deeper one: a
premise off the wire is not a check.

The repair puts both halves on the wire. Acceptance became three linear atoms,
one per successor equation, so no cancellation between equations is available
at all. The no-wrap condition became a 30-bit range *lookup* on each of the six
bound columns, against the declared range table. The graduated lookup form is
deliberate rather than the v1 `ranges` carrier: the deployed v2 assembly refuses
a descriptor carrying the v1 form at all, so those bytes would have enforced the
bound only in Lean --- the same mistake in a new place --- whereas a lookup is
lowered to a real byte-limb decomposition at the width pinned by the committed
table id.

With both halves emitted, the two premises stop being premises.
`statement_forces_wire_bounded` derives the retired `LiveProjectionCertificate`
from the teeth; `first_row_input_bounded` and `first_row_output_bounded` derive
the retired `CanonicalFirstRow`. `statement_sound` and
`public_statement_satisfied_iff_holds` no longer take a certificate argument.

#theorem([both halves are load-bearing], [
  A single counterexample would leave one half of the repair looking decorative,
  so a second is carried. `wrapClaim` lies inside the 30-bit domain, so it is
  refused by the linear atoms alone and the teeth do no work on it.
  `borderWrapClaim` --- $"input"_0 = 2013265920$, $"output"_0 = 0$ --- is
  canonical and false, and `borderWrap_atom_gates_all_pass` proves that all
  three linear gates evaluate to a BabyBear zero on it, since the first residual
  is exactly $-p$. The only emitted gate that refuses it is the 30-bit tooth on
  column 0 (`borderWrap_range_tooth_fires`). Each half kills a counterexample
  the other admits; deleting either turns one of these theorems red.
])

Both canaries are proved in both polarities --- refusal of the exact
preselected trace, and refusal of the external statement for *every* trace ---
and `repaired_descriptor_still_accepts_truth` is the positivity control that
the repair rejects the counterexamples rather than everything.
`DirectLogicAdversarialFalsifierV2` is imported by the trusted umbrella, so CI
builds these canaries like any other theorem; an unbuilt canary is not a canary.

The linear repair is also the cheaper circuit:

#table(
  columns: (1.35fr, 1fr, 1fr),
  align: (left, center, center),
  table.header([*Public descriptor*], [*Retired sum-of-squares*], [*Repaired*]),
  [Constraints], [7], [15],
  [of which range teeth], [0], [6],
  [Multiplication nodes], [15], [6],
  [Nonlinear products], [3], [0],
)

The three squares carried 15 multiplication nodes, 3 of them nonlinear; the
three linear atoms carry 6 constant-scaling nodes and no nonlinear product. The
added cost is two extra gates and the deployed byte-limb realization of the six
teeth, which the node count does not price.

#boundary([
  One premise moved rather than vanished. A range lookup bounds a column only
  against the table it looks into, and the abstract `Satisfied2` carrier has
  structural faithfulness conjuncts for the memory and map tables but none for
  `.range`, so a prover may choose `tf .range` freely. `StatementSatisfied`
  therefore carries `HonestRangeTable trace` explicitly, and every refusal that
  routes through a range tooth is conditional on it --- `borderWrapClaim`
  genuinely needs it, while `wrapClaim`'s refusal is table-free because linear
  atoms read no table. This premise is of a different kind from the retired one:
  it is a condition on the trace family rather than an unchecked assertion about
  the claim, it is discharged by construction for every trace built here and in
  deployment by the assembly, which constructs the limb decomposition rather
  than reading a prover-supplied table --- and it is carrier-level and uniform,
  since every range lookup in the codebase reads against `t.tf .range`. The
  structural fix already exists in shape as `Satisfied2Faithful`, which carries
  `rangeTableFaithful` as a conjunct; this descriptor has not been ported to it,
  and porting would move the obligation to the Rust assembly rather than
  discharge it inside Lean.
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

`DirectLogicBoolGraphDescriptorIR2` realizes that ledger in the live backend.
Every atomic zero test and Boolean connective receives explicit auxiliary
columns and a flat list of `windowGate` constraints. Its standalone public
variant additionally binds residual input $a$ to public input $a$ on the first
row. `public_descriptor_exact_overhead` proves that statement binding adds
exactly $n$ linear equations and $n$ public inputs, but no nonlinear
multiplication or auxiliary witness.

For the four-input factor specimen, `public_factor_emitted_exact` proves the
public statement ledger. The underlying graph equations are $30 -> 13$; the
internal accepting descriptor is $31 -> 14$; after four public bindings the
standalone public totals are:

#text(size: 7.5pt)[#table(
  columns: (1.55fr, 0.62fr, 0.62fr, 2.05fr),
  align: (left, center, center, left),
  table.header([*Live resource*], [*Before*], [*After*], [*Exact account*]),
  [public constraints], [35], [18], [four PI bindings, graph, and output-equals-one],
  [nonlinear multiplications], [26], [13], [exact emitted node ledger],
  [auxiliary witness columns], [17], [8], [postorder zero-test and connective witnesses],
  [total trace width], [21], [12], [four input residual columns plus auxiliaries],
)]

`descriptor_constraint_degree` proves that every emitted constraint has degree
at most two. `public_statement_sound` proves arbitrary-trace soundness: any
nonempty satisfying trace implies `Formula.Holds` under the verifier's public
zero-residual vector. `public_canonical_trace_complete` constructs the public
trace for every true Boolean assignment, and `public_canonical_trace_iff`
packages canonical exactness. `checked_public_statement_sound` transports any
accepted optimized public certificate back to its original source formula.

`checkPublicLive` reconstructs the optimizer proof, source and target
endpoints, PI layout, complete resource ledger, and exact emitted descriptor
JSON. The factor guards reject changed PI order, layout, or bytes.

=== Production-shaped DREGG decisions

`DirectLogicDreggWorkloads` instantiates the public compiler on four decisions
already consumed by DREGG: turn admission including receipt-head binding,
authorized program upgrade, structured credential clearance, and the
stake/vouch strand gate before finality. Each namespace proves an exact source
equivalence, an optimized equivalence, and arbitrary-trace public-descriptor
soundness: for example `AdmissionWorkload.source_iff_admissible`,
`AdmissionWorkload.optimized_iff_admissible`, and
`AdmissionWorkload.public_descriptor_sound`.

#text(size: 7.25pt)[#table(
  columns: (1.3fr, 1.1fr, 1.1fr, 1fr, 1.45fr),
  align: (left, center, center, center, left),
  table.header([*Named workload*], [*Public constraints*],
    [*Multiplications*], [*Trace width*], [*Exact theorem*]),
  [Turn admission], [121 -> 71], [108 -> 58], [77 -> 47],
    [#raw("admission_exact_")#linebreak()#raw("live_ledger")],
  [Program upgrade], [33 -> 23], [28 -> 18], [21 -> 15],
    [#raw("upgrade_exact_")#linebreak()#raw("live_ledger")],
  [Credential clearance], [33 -> 23], [28 -> 18], [21 -> 15],
    [#raw("clearance_exact_")#linebreak()#raw("live_ledger")],
  [Strand admission], [17 = 17], [13 = 13], [11 = 11],
    [#raw("strand_exact_")#linebreak()#raw("live_ledger")],
)]

The first three sources expose genuine duplicated branch prefixes; the
optimizer shares each prefix. `strand_already_normal_shape` is the negative
control: the already minimal three-way disjunction is unchanged. All four
public certificates pass their byte/layout gates, while independent guards
reject modified bytes, layout, endpoint, and version.

#boundary([
  The workload theorem is exact at the *atom boundary*. Arithmetic, hashes,
  membership, lifecycle, capability lookup, and receipt comparison remain the
  production predicates named by the atoms; this Boolean-skeleton module does
  not arithmetize their implementations. `public_certificate_sound_of_atoms`
  therefore requires the caller to prove that each public zero residual is
  equivalent to its named atom. Under that hypothesis, any nonempty satisfying
  trace proves the production decision. The tables count the public Boolean
  relation around those atoms, not the uncharged cost of implementing them.
])

#boundary([
  These are exact live DescriptorIR2 resource reductions: constraints,
  nonlinear multiplication nodes, auxiliary columns, width, and degree. They
  are not timings. Prover time, verifier time, proof size, memory traffic, and
  backend scheduling still require a controlled before/after benchmark.
])

== Exact presentations and finite search

`CertifiedPresentationChange.Presentation` packages source meaning, evidence,
acceptance, and a resource vector. An exact `Change P Q` maps evidence in both
semantic directions and carries a compositional resource bound. Identity and
composition form a genuine category, so a compiler can change representation
without dissolving its proof obligation.

The original concrete nodes are:

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

`CertifiedIndexedPresentationCompiler` closes the accounting gap left by
meta-level split acceptance. A `Fragment` is indexed by its source formula,
truth interpretation, and one of four distinct modes: dense polynomial,
materialized Boolean graph, interaction net, or natural residual. It carries
an acceptance proposition, `BackendCost`, and an exact semantic certificate.
A `Conversion` combines an exact presentation change with a separately
inspectable `ResourceMorphism`; sequential and tensor composition accumulate
conversion overhead explicitly.

An indexed `Plan` may choose one mode for a whole subformula or compile its
children independently. Every conjunction or disjunction node carries an
explicit `glueCost`. `Plan.accepts_iff` proves global semantic preservation,
while `Plan.materialization_overhead_eq_resources` proves that the recursive
materialization derivation exposes the entire ledger with no remainder.
`Boundary.fourWayPlan_modes` exhibits all four modes in one genuine per-subterm
plan.

The teeth are negative as well as positive.
`Boundary.free_glue_claim_is_false` proves that a materialized one-equation
conjunction is not bounded by the zero-cost meta-level estimate.
`Boundary.exact_semantics_but_no_free_conversion` gives two semantically exact
fragments for which no zero-overhead resource morphism can materialize the
target equation. Thus semantic equivalence cannot manufacture a performance
claim. `Search.choose_minimal_relative` still proves optimality only within the
caller-supplied finite candidates and transparent scalar score, never among an
unstated universe of compilers.

#boundary([
  The indexed calculus certifies accounting structure; backend adapters must
  still construct the dense-polynomial, BoolGraph, interaction-net, or residual
  fragments they advertise. Only the residual and Boolean adapters are
  instantiated here. Representation names alone do not emit code.
])

#callout([WHAT HAS BEEN RECOVERED], [
  The defensible performance thesis is local and certified: exploit a compact
  residual exactly where a range proof makes it sound; use Boolean zero tests
  where it does not; share repeated structure; and search only among
  meaning-preserving changes of presentation. The checked specimens now show
  substantial live relation-size reductions, but no theorem here implies a universal
  10-100x end-to-end speedup or chain finality.
])
